// -*- coding: utf-8 -*-
// Copyright (C) 2017-2020 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 3 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "config.h"
#include <spot/twaalgos/aiger.hh>

#include <cmath>
#include <map>
#include <unordered_map>
#include <vector>
#include <algorithm>
#include <cstring>

#include <spot/twa/twagraph.hh>
#include <spot/misc/minato.hh>

namespace spot
{
  namespace
  {
    static std::vector<std::string>
    name_vector(unsigned n, const std::string& prefix)
    {
      std::vector<std::string> res(n);
      for (unsigned i = 0; i != n; ++i)
        res[i] = prefix + std::to_string(i);
      return res;
    }

    // A class to represent an AIGER circuit
    class aig
    {
    private:
      unsigned max_var_;
      unsigned num_inputs_;
      unsigned num_latches_;
      unsigned num_outputs_;

      std::vector<unsigned> latches_;
      std::vector<unsigned> outputs_;
      std::vector<std::string> input_names_;
      std::vector<std::string> output_names_;
      std::vector<std::pair<unsigned, unsigned>> and_gates_;
      // Cache the function computed by each variable as a bdd.
      std::unordered_map<unsigned, bdd> var2bdd_;
      std::unordered_map<bdd, unsigned, bdd_hash> bdd2var_;

    public:
      aig(const std::vector<std::string>& inputs,
          const std::vector<std::string>& outputs,
          unsigned num_latches)
        : max_var_((inputs.size() + num_latches)*2),
          num_inputs_(inputs.size()),
          num_latches_(num_latches),
          num_outputs_(outputs.size()),
          latches_(num_latches),
          outputs_(outputs.size()),
          input_names_(inputs),
          output_names_(outputs)
      {
        bdd2var_[bddtrue] = 1;
        var2bdd_[1] = bddtrue;
        bdd2var_[bddfalse] = 0;
        var2bdd_[0] = bddfalse;

        bdd2var_.reserve(4 * (num_inputs_ + num_latches_));
        var2bdd_.reserve(4 * (num_inputs_ + num_latches_));
      }

      aig(unsigned num_inputs, unsigned num_latches, unsigned num_outputs)
        : aig(name_vector(num_inputs, "in"), name_vector(num_outputs, "out"),
              num_latches)
      {
      }

      // register the bdd corresponding the an
      // aig literal
      inline void register_new_lit(unsigned v, const bdd& b)
      {
        assert(!var2bdd_.count(v) || var2bdd_.at(v) == b);
        assert(!bdd2var_.count(b) || bdd2var_.at(b) == v);
        var2bdd_[v] = b;
        bdd2var_[b] = v;
        // Also store negation
        // Do not use aig_not as tests will fail
        var2bdd_[v ^ 1] = !b;
        bdd2var_[!b] = v ^ 1;
      }

      inline unsigned input_var(unsigned i) const
      {
        assert(i < num_inputs_);
        return (1 + i) * 2;
      }

      inline unsigned latch_var(unsigned i)
      {
        assert(i < latches_.size());
        return (1 + num_inputs_ + i) * 2;
      }

      inline unsigned gate_var(unsigned i)const
      {
        assert(i < and_gates_.size());
        return (1 + num_inputs_ + num_latches_ + i) * 2;
      }

      void set_output(unsigned i, unsigned v)
      {
        assert(v <= max_var_+1);
        outputs_[i] = v;
      }

      void set_latch(unsigned i, unsigned v)
      {
        assert(v <= max_var_+1);
        latches_[i] = v;
      }

      unsigned aig_true() const
      {
        return 1;
      }

      unsigned aig_false() const
      {
        return 0;
      }

      unsigned aig_not(unsigned v)
      {
        unsigned not_v = v ^ 1;
        assert(var2bdd_.count(v)
               && var2bdd_.count(not_v));
        return not_v;
      }

      unsigned aig_and(unsigned v1, unsigned v2)
      {
        assert(var2bdd_.count(v1));
        assert(var2bdd_.count(v2));
        bdd b = var2bdd_[v1] & var2bdd_[v2];
        auto it = bdd2var_.find(b);
        if (it != bdd2var_.end())
          return it->second;
        max_var_ += 2;
        and_gates_.emplace_back(v1, v2);
        register_new_lit(max_var_, b);
        return max_var_;
      }

      unsigned aig_and(std::vector<unsigned> vs)
      {
        if (vs.empty())
          return aig_true();
        if (vs.size() == 1)
          return vs[0];
        if (vs.size() == 2)
          return aig_and(vs[0], vs[1]);

        do
          {
            if (vs.size()&1)
              // Odd size -> make even
              vs.push_back(aig_true());
            // Sort to increase reusage gates
            std::sort(vs.begin(), vs.end());
            // Reduce two by two inplace
            for (unsigned i = 0; i < vs.size()/2; ++i)
              vs[i] = aig_and(vs[2*i], vs[2*i + 1]);
            vs.resize(vs.size()/2);
          }while (vs.size() > 1);
        return vs[0];
      }

      unsigned aig_or(unsigned v1, unsigned v2)
      {
        unsigned n1 = aig_not(v1);
        unsigned n2 = aig_not(v2);
        return aig_not(aig_and(n1, n2));
      }

      unsigned aig_or(std::vector<unsigned> vs)
      {
        for (unsigned i = 0; i < vs.size(); ++i)
          vs[i] = aig_not(vs[i]);
        return aig_not(aig_and(vs));
      }

      unsigned aig_pos(unsigned v)
      {
        return v & ~1;
      }

      void remove_unused()
      {
        // Run a DFS on the gates to collect
        // all nodes connected to the output.
        std::vector<unsigned> todo;
        std::vector<bool> used(and_gates_.size(), false);

        // The variables are numbered by first enumerating
        // inputs, latches and finally the and-gates
        // v_latch = (1+n_i+i)*2 if latch is in positive form
        // if v/2 < 1+n_i -> v is an input
        // v_gate = (1+n_i+n_l+i)*2 if gate is in positive form
        // if v/2 < 1+n_i_nl -> v is a latch
        auto v2idx = [&](unsigned v)->unsigned
        {
          assert(!(v & 1));
          const unsigned Nlatch_min = 1 + num_inputs_;
          const unsigned Ngate_min = 1 + num_inputs_ + num_latches_;

          // Note: this will at most run twice
          while (true)
            {
              unsigned i = v / 2;
              if (i >= Ngate_min)
                // v is a gate
                return i - Ngate_min;
              else if (i >= Nlatch_min)
                // v is a latch -> get gate
                v = aig_pos(latches_.at(i - Nlatch_min));
              else
                // v is a input -> nothing to do
                return -1U;
            }
        };

        auto mark = [&](unsigned v)
        {
          unsigned idx = v2idx(aig_pos(v));
          if ((idx == -1U) || used[idx])
            return;
          used[idx] = true;
          todo.push_back(idx);
        };

        for (unsigned v : outputs_)
          mark(v);

        while (!todo.empty())
          {
            unsigned idx = todo.back();
            todo.pop_back();

            mark(and_gates_[idx].first);
            mark(and_gates_[idx].second);
          }
        // Erase and_gates that were not seen in the above
        // exploration.
        // To avoid renumbering all gates, erasure is done
        // by setting both inputs to "false"
        for (unsigned idx = 0; idx < used.size(); ++idx)
          if (!used[idx])
            {
              and_gates_[idx].first = 0;
              and_gates_[idx].second = 0;
            }
      }

      // Takes a bdd, computes the corresponding literal
      // using its DNF
      unsigned bdd2DNFvar(const bdd& b,
                          const std::unordered_map<unsigned, unsigned>&
                          bddvar_to_num)
      {
        std::vector<unsigned> plus_vars;
        std::vector<unsigned> prod_vars(num_inputs_);

        minato_isop cond(b);
        bdd prod;

        while ((prod = cond.next()) != bddfalse)
          {
            prod_vars.clear();
            // Check if existing
            auto it = bdd2var_.find(prod);
            if (it != bdd2var_.end())
              plus_vars.push_back(it->second);
            else
              {
                // Create
                while (prod != bddfalse && prod != bddtrue)
                  {
                    unsigned v =
                      input_var(bddvar_to_num.at(bdd_var(prod)));
                    if (bdd_high(prod) == bddfalse)
                      {
                        v = aig_not(v);
                        prod = bdd_low(prod);
                      }
                    else
                      prod = bdd_high(prod);
                    prod_vars.push_back(v);
                  }
                plus_vars.push_back(aig_and(prod_vars));
              }
          }

        // Done building
        return aig_or(plus_vars);
      }

      // Takes a bdd, computes the corresponding literal
      // using its INF
      unsigned bdd2INFvar(bdd b)
      {
        // F = !v&low | v&high
        // De-morgan
        // !(!v&low | v&high) = !(!v&low) & !(v&high)
        // !v&low | v&high = !(!(!v&low) & !(v&high))
        auto b_it = bdd2var_.find(b);
        if (b_it != bdd2var_.end())
          return b_it->second;

        unsigned v_var = bdd2var_.at(bdd_ithvar(bdd_var(b)));

        bdd b_branch[2] = {bdd_low(b), bdd_high(b)};
        unsigned b_branch_var[2];

        for (unsigned i: {0, 1})
          {
            auto b_branch_it = bdd2var_.find(b_branch[i]);
            if (b_branch_it == bdd2var_.end())
              b_branch_var[i] = bdd2INFvar(b_branch[i]);
            else
              b_branch_var[i] = b_branch_it->second;
          }

        unsigned r = aig_not(aig_and(v_var, b_branch_var[1]));
        unsigned l = aig_not(aig_and(aig_not(v_var), b_branch_var[0]));
        return aig_not(aig_and(l, r));
      }

      void
      print(std::ostream& os) const
      {
        // Writing gates to formatted buffer speed-ups output
        // as it avoids "<<" calls
        // vars are unsigned -> 10 digits at most
        char gate_buffer[3*10+5];
        auto write_gate = [&](unsigned o, unsigned i0, unsigned i1)
        {
          std::sprintf(gate_buffer, "%u %u %u\n", o, i0, i1);
          os << gate_buffer;
        };
        // Count active gates
        unsigned n_gates=0;
        for (auto& g : and_gates_)
          if ((g.first != 0) && (g.second != 0))
            ++n_gates;
        // Note max_var_ is now an upper bound
        os << "aag " << max_var_ / 2
           << ' ' << num_inputs_
           << ' ' << num_latches_
           << ' ' << num_outputs_
           << ' ' << n_gates << '\n';
        for (unsigned i = 0; i < num_inputs_; ++i)
          os << (1 + i) * 2 << '\n';
        for (unsigned i = 0; i < num_latches_; ++i)
          os << (1 + num_inputs_ + i) * 2 << ' ' << latches_[i] << '\n';
        for (unsigned i = 0; i < outputs_.size(); ++i)
          os << outputs_[i] << '\n';
        for (unsigned i=0; i<and_gates_.size(); ++i)
          if ((and_gates_[i].first != 0) && (and_gates_[i].second != 0))
            write_gate(gate_var(i), and_gates_[i].first, and_gates_[i].second);
        for (unsigned i = 0; i < num_inputs_; ++i)
          os << 'i' << i << ' ' << input_names_[i] << '\n';
        for (unsigned i = 0; i < outputs_.size(); ++i)
          os << 'o' << i << ' ' << output_names_[i] << '\n';
      }
    };

    static void
    state_to_vec(std::vector<bool>& v, unsigned s)
    {
      for (unsigned i = 0; i < v.size(); ++i)
        {
          v[i] = s & 1;
          s >>= 1;
        };
    }

    static void
    output_to_vec(std::vector<bool>& v, bdd b,
                  const std::unordered_map<unsigned, unsigned>&
                  bddvar_to_outputnum)
    {
      std::fill(v.begin(), v.end(), false);
      while (b != bddtrue && b != bddfalse)
        {
          unsigned i = bddvar_to_outputnum.at(bdd_var(b));
          v.at(i) = (bdd_low(b) == bddfalse);
          if (v[i])
            b = bdd_high(b);
          else
            b = bdd_low(b);
        }
    }

    static bdd
    state_to_bdd(unsigned s, bdd all_latches)
    {
      bdd b = bddtrue;
      unsigned size = bdd_nodecount(all_latches);
      if (size)
        {
          unsigned st0 = bdd_var(all_latches);
          for (unsigned i = 0; i < size; ++i)
            {
              b &= (s & 1) ? bdd_ithvar(st0 + i) : bdd_nithvar(st0 + i);
              s >>= 1;
            }
        }
      return b;
    }

    // Switch initial state and 0 in the AIGER encoding, so that the
    // 0-initialized latches correspond to the initial state.
    static unsigned
    encode_init_0(unsigned src, unsigned init)
    {
      return src == init ? 0 : src == 0 ? init : src;
    }

    // Find one suitable assignment for the output
    // propositions
    std::vector<bdd> determine_outs(const const_twa_graph_ptr& aut,
                                 const bdd& all_inputs)
    {
      std::vector <bdd> used_outc(aut->num_edges() + 1, bddfalse);
      for (const auto &e : aut->edges())
        {
          assert(e.cond != bddfalse);
          assert(((bdd_exist(e.cond, all_inputs)
                   & bdd_existcomp(e.cond, all_inputs)) == e.cond) &&
                 "Precondition (in) & (out) == cond violated");
          used_outc[aut->edge_number(e)] =
              bdd_satone(bdd_exist(e.cond, all_inputs));
        }
      return used_outc;
    }

    // Transforms an automaton into an AIGER circuit
    // using irreducible sums-of-products
    // or if-then-else form
    static aig
    aut_to_aiger(const const_twa_graph_ptr& aut, const bdd& all_outputs,
                 const char* mode)
    {
      // The aiger circuit cannot encode the acceptance condition
      // Test that the acceptance condition is true
      if (!aut->acc().is_t())
        throw std::runtime_error("Cannot turn automaton into aiger circuit");

      // get the propositions
      std::vector<std::string> input_names;
      std::vector<std::string> output_names;
      bdd all_inputs = bddtrue;
      std::vector<bdd> all_inputs_vec;
      std::unordered_map<unsigned, unsigned> bddvar_to_num;
      for (const auto& ap : aut->ap())
        {
          int bddvar = aut->get_dict()->has_registered_proposition(ap, aut);
          assert(bddvar >= 0);
          bdd b = bdd_ithvar(bddvar);
          if (bdd_implies(all_outputs, b)) // ap is an output AP
            {
              bddvar_to_num[bddvar] = output_names.size();
              output_names.emplace_back(ap.ap_name());
            }
          else // ap is an input AP
            {
              bddvar_to_num[bddvar] = input_names.size();
              input_names.emplace_back(ap.ap_name());
              all_inputs &= b;
              all_inputs_vec.push_back(b);
            }
        }

      // Decide on which outcond to use
      // There are two possibilities:
      // Either the named property outcond-edge is set.
      // In this case these outcond will be used and it is assumed
      // that the conditions on the edges are defined over the inputs
      // The second option is that
      // the edges of the automaton all have the form in&out
      // due to the unsplit
      // however we need the edge to be deterministic in out too
      // So we need determinism and we also want the resulting aiger
      // to have as few gates as possible
      std::vector<bdd> used_outc;
      bool econdoverin;
      if (std::vector<bdd>* outc_ptr =
          aut->get_named_prop<std::vector<bdd>>("outcond-edge"))
        {
          econdoverin = true;
          used_outc = *outc_ptr;
          assert(used_outc.size() == aut->num_edges()+1
                 && "Number of outcond and edges does not match");
        }
      else
        {
          econdoverin = false;
          used_outc = determine_outs(aut, all_inputs);
        }

      // Encode state in log2(num_states) latches.
      unsigned log2n = std::ceil(std::log2(aut->num_states()));
      unsigned st0 = aut->get_dict()->register_anonymous_variables(log2n, aut);

      unsigned num_outputs = output_names.size();
      unsigned init = aut->get_init_state_number();
      assert(num_outputs == (unsigned) bdd_nodecount(all_outputs));
      aig circuit(input_names, output_names, log2n);

      // Register
      // latches
      for (unsigned i = 0; i < log2n; ++i)
        circuit.register_new_lit(circuit.latch_var(i), bdd_ithvar(st0+i));
      // inputs
      for (unsigned i = 0; i < all_inputs_vec.size(); ++i)
        circuit.register_new_lit(circuit.input_var(i), all_inputs_vec[i]);
      // Latches and outputs are expressed as a DNF in which each term
      // represents a transition.
      // latch[i] (resp. out[i]) represents the i-th latch (resp. output) DNF.

      std::vector<bool> out_vec(output_names.size());
      std::vector<bool> next_state_vec(log2n);
      if (strcasecmp(mode, "ISOP") == 0)
        {
          std::vector<std::vector<unsigned>> latch(log2n);
          std::vector<std::vector<unsigned>> out(num_outputs);
          // Keep track of bdd that were already transformed into a gate
          std::unordered_map<bdd, unsigned, bdd_hash> incond_map;
          std::vector<unsigned> prod_state(log2n);
          for (unsigned s = 0; s < aut->num_states(); ++s)
            {
              unsigned src = encode_init_0(s, init);
              prod_state.clear();
              unsigned src2 = src;
              for (unsigned i = 0; i < log2n; ++i)
                {
                  unsigned v = circuit.latch_var(i);
                  prod_state.push_back(src2 & 1 ? v : circuit.aig_not(v));
                  src2 >>= 1;
                }
              assert(src2 <= 1);
              unsigned state_var = circuit.aig_and(prod_state);
              // Done state var

              for (auto &e: aut->out(s))
                {
                  unsigned e_idx = aut->edge_number(e);
                  // Same outcond for all ins
                  const bdd &letter_out = used_outc[e_idx];
                  output_to_vec(out_vec, letter_out, bddvar_to_num);

                  unsigned dst = encode_init_0(e.dst, init);
                  state_to_vec(next_state_vec, dst);

                  // Get the isops over the input condition
                  // Each isop only contains variables from in
                  // -> directly compute the corresponding
                  // variable and and-gate
                  bdd incond;
                  if (econdoverin)
                    {
                      incond = e.cond;
                      assert(bdd_exist(e.cond, all_outputs) == e.cond
                             && "Edges conditions have to be defined over "
                                "inputs if using outcond-edge!");
                    }
                  else
                    incond = bdd_exist(e.cond, all_outputs);

                  auto incond_var_it = incond_map.find(incond);
                  if (incond_var_it == incond_map.end())
                    // The incond and its isops have not yet been calculated
                    {
                      bool inserted;
                      unsigned var = circuit.bdd2DNFvar(incond, bddvar_to_num);
                      std::tie(incond_var_it, inserted) =
                        incond_map.insert(std::make_pair(incond, var));
                      assert(inserted && incond_var_it->second == var);
                    }

                  // AND with state
                  unsigned t =
                    circuit.aig_and(state_var, incond_var_it->second);
                  // Set in latches/outs having "high"
                  for (unsigned i = 0; i < log2n; ++i)
                    if (next_state_vec[i])
                      latch[i].push_back(t);
                  for (unsigned i = 0; i < num_outputs; ++i)
                    if (out_vec[i])
                      out[i].push_back(t);
                } // edge
            } // state

          for (unsigned i = 0; i < log2n; ++i)
            circuit.set_latch(i, circuit.aig_or(latch[i]));
          for (unsigned i = 0; i < num_outputs; ++i)
            circuit.set_output(i, circuit.aig_or(out[i]));
          circuit.remove_unused();
        }
      else if (strcasecmp(mode, "ITE") == 0)
        {
          std::vector<bdd> latch(log2n, bddfalse);
          std::vector<bdd> out(num_outputs, bddfalse);
          bdd all_latches = bddtrue;
          for (unsigned i = 0; i < log2n; ++i)
            all_latches &= bdd_ithvar(st0 + i);
          for (unsigned s = 0; s < aut->num_states(); ++s)
            {
              // Convert state to bdd
              unsigned src = encode_init_0(s, init);
              bdd src_bdd = state_to_bdd(src, all_latches);

              for (const auto& e : aut->out(src))
                {
                  unsigned dst = encode_init_0(e.dst, init);
                  state_to_vec(next_state_vec, dst);
                  // edges have the form
                  // f(ins) & f(outs)
                  // one specific truth assignment has been selected above
                  // and stored in used_outc
                  output_to_vec(out_vec, used_outc[aut->edge_number(e)],
                                bddvar_to_num);
                  // The condition that joins in_cond and src
                  bdd tot_cond;
                  if (econdoverin)
                    {
                      tot_cond = src_bdd & e.cond;
                      assert(bdd_exist(e.cond, all_outputs) == e.cond
                             && "Edges conditions have to be defined over "
                                "inputs if using outcond-edge!");
                    }
                  else
                    tot_cond = src_bdd & bdd_exist(e.cond, all_outputs);

                  // Add to existing cond
                  for (unsigned i = 0; i < log2n; ++i)
                    if (next_state_vec[i])
                      latch[i] |= tot_cond;
                  for (unsigned i = 0; i < num_outputs; ++i)
                    if (out_vec[i])
                      out[i] |= tot_cond;
                } // e
            } // src
          // Create the vars
          for (unsigned i = 0; i < num_outputs; ++i)
            circuit.set_output(i, circuit.bdd2INFvar(out[i]));
          for (unsigned i = 0; i < log2n; ++i)
            circuit.set_latch(i, circuit.bdd2INFvar(latch[i]));
        }
      else
        {
          throw std::runtime_error
            ("print_aiger(): mode must be \"ISOP\" or \"ITE\"");
        }
      return circuit;
    } // aut_to_aiger_isop
  }

  std::ostream&
  print_aiger(std::ostream& os, const const_twa_ptr& aut, const char* mode)
  {
    auto a = down_cast<const_twa_graph_ptr>(aut);
    if (!a)
      throw std::runtime_error("aiger output is only for twa_graph");

    bdd* all_outputs = aut->get_named_prop<bdd>("synthesis-outputs");

    aig circuit =
      aut_to_aiger(a, all_outputs ? *all_outputs : bdd(bddfalse), mode);
    circuit.print(os);
    return os;
  }

  std::string
  get_aiger_string(const const_twa_ptr& aut,  const char* mode)
  {
    std::ostringstream oss;
    print_aiger(oss, aut, mode);
    return oss.str();
  }

    void
  restore_form(const twa_graph_ptr& aut, bdd all_outputs)
  {
    if (all_outputs == bddfalse)
      {
        if (bdd* out_ptr = aut->get_named_prop<bdd>("synthesis-outputs"))
          all_outputs = *out_ptr;
        else
          throw std::runtime_error("Needs either all_outputs or "
                                   "named property synthesis-outputs");
      }
    assert(all_outputs != bddfalse && "No aps are defined as outputs");

    bdd all_inputs = bddtrue;
    for (const auto& ap : aut->ap())
      {
        int bddvar = aut->get_dict()->has_registered_proposition(ap, aut);
        assert(bddvar >= 0);
        bdd b = bdd_ithvar(bddvar);
        if (!bdd_implies(all_outputs, b)) // ap is not an output AP
          all_inputs &= b;
      }

    // Loop over all edges and split those that do not have the form
    // (in)&(out)
    // Note new_edges are always appended at the end
    unsigned n_old_edges = aut->num_edges();
    // Temp storage
    // Output condition to possible input conditions
    std::map<bdd, bdd, bdd_less_than> edge_map_;
    for (unsigned i = 1; i <= n_old_edges; ++i)
      {
        auto& e = aut->edge_storage(i);
        // Check if cond already has the correct form
        if ((bdd_exist(e.cond, all_inputs) &
            bdd_existcomp(e.cond, all_inputs)) == e.cond)
          // Nothing to do here
          continue;
        // Do the actual split
        edge_map_.clear();
        bdd old_cond = e.cond;
        while (old_cond != bddfalse)
          {
            bdd minterm = bdd_satone(old_cond);
            bdd minterm_in = bdd_exist(minterm, all_outputs);
            // Get all possible valid outputs
            bdd valid_out = bdd_exist((minterm_in & e.cond), all_inputs);
            // Check if this out already exists
            auto it = edge_map_.find(valid_out);
            if (it == edge_map_.end())
              edge_map_[valid_out] = minterm_in;
            else
              // Reuse the outs for this in
              it->second |= minterm_in;
            // Remove this minterm
            old_cond -= minterm;
          }
        // Computed the splitted edges.
        // Replace the current edge cond with the first pair
        auto it = edge_map_.begin();
        e.cond = (it->first & it->second);
        ++it;
        for (; it != edge_map_.end(); ++it)
          aut->new_edge(e.src, e.dst, it->first & it->second, e.acc);
      }
    // Done
  }
}
