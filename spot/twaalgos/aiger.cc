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
#include <unordered_map>
#include <vector>
#include <algorithm>
#include <cstring>
#include <tuple>
#include <utility>
#include <fstream>

#include <spot/twa/twagraph.hh>
#include <spot/misc/bddlt.hh>
#include <spot/misc/minato.hh>

namespace
{
  template<class STREAM>
  std::tuple<std::set<std::string>, std::set<std::string>,
             std::vector<unsigned>,
             std::vector<unsigned>,
             std::vector<std::pair<unsigned, unsigned>>
             >
  parse_aag_impl_(STREAM& iss)
  {
    //rets
    std::set<std::string> input_names;
    std::set<std::string> output_names;
    std::vector<unsigned> latches;
    std::vector<unsigned> outputs;
    std::vector<std::pair<unsigned, unsigned>> gates;

    unsigned max_index, nb_inputs, nb_latches, nb_outputs, nb_and;

    std::string line;
    std::ostringstream error_oss;
    error_oss << "aig(std::string): line ";
    getline(iss, line);
    unsigned line_number = 1;
    if (sscanf(line.c_str(), "aag %u %u %u %u %u", &max_index, &nb_inputs, &nb_latches, &nb_outputs, &nb_and) != 5)
    {
      error_oss << line_number << " invalid header";
      throw std::runtime_error(error_oss.str());
    }

    if (max_index < nb_inputs + nb_latches + nb_and)
      throw std::runtime_error("More variables than indicated by max var");

    latches.reserve(nb_latches);
    outputs.reserve(nb_outputs);
    gates.reserve(nb_and);

    // FIXME:
//    unsigned max_var_ = -2U;
    for (unsigned i = 0; i < nb_inputs; ++i)
    {
      if (!iss)
      {
        error_oss << line_number << " missing input";
        throw std::runtime_error(error_oss.str());
      }
      line.clear();
      getline(iss, line);
      if ((unsigned)std::stoi(line) != 2*(i+1))
        throw std::runtime_error("Invalid input numbering\n");
      ++line_number;
    }
    for (unsigned i = 0; i < nb_latches; ++i)
    {
      if (!iss)
      {
        error_oss << line_number << " missing latch";
        throw std::runtime_error(error_oss.str());
      }
      line.clear();
      getline(iss, line);
      ++line_number;
      unsigned latch_var, next_state;
      if (sscanf(line.c_str(), "%u %u", &latch_var, &next_state) != 2)
      {
        error_oss << line_number << " invalid latch";
        throw std::runtime_error(error_oss.str());
      }
      if (latch_var != 2*(1 + nb_inputs + i))
        throw std::runtime_error("Invalid latch numbering\n");
      latches.push_back(next_state);
    }
    for (unsigned i = 0; i < nb_outputs; ++i)
    {
      if (!iss)
      {
        error_oss << line_number << " missing output";
        throw std::runtime_error(error_oss.str());
      }
      line.clear();
      getline(iss, line);
      ++line_number;
      unsigned num_out;
      if (sscanf(line.c_str(), "%u", &num_out) != 1)
      {
        error_oss << line_number << " invalid output";
        throw std::runtime_error(error_oss.str());
      }
      outputs.push_back(num_out);
    }
    for (unsigned i = 0; i < nb_and; ++i)
    {
      unsigned and_gate, lhs, rhs;
      if (!iss)
      {
        error_oss << line_number << " missing AND";
        throw std::runtime_error(error_oss.str());
      }
      line.clear();
      getline(iss, line);
      ++line_number;
      if (sscanf(line.c_str(), "%u %u %u", &and_gate, &lhs, &rhs) != 3)
      {
        error_oss << line_number << " invalid AND";
        throw std::runtime_error(error_oss.str());
      }
      if (and_gate != 2*(1 + nb_inputs +nb_latches + i))
        throw std::runtime_error("Invalid gate numbering\n");
      gates.emplace_back(lhs, rhs);
    }
    line.clear();
    // todo
    // Here we need some restrictions to get a set...
    getline(iss, line);
    ++line_number;
    while(iss)
    {
      unsigned pos_var_name;
      char first_char = line[0];
      char var_name[256];
      switch (first_char)
      {
        // latches names non supported
      case 'l':
      {
        line.clear();
        getline(iss, line);
        ++line_number;
        continue;
      }
      case 'i':
      {
        if (sscanf(line.c_str(), "i%u %255s", &pos_var_name, var_name) != 2 || pos_var_name >= nb_inputs)
        {
          error_oss << line_number << " invalid input name";
          throw std::runtime_error(error_oss.str());
        }
        input_names.emplace(var_name);
        if (*input_names.crbegin() != var_name)
          throw std::runtime_error("Input variables have to be "
                                   "lexicographically ordered!\n");
        line.clear();
        getline(iss, line);
        ++line_number;
        break;
      }
      case 'o':
      {
        if (sscanf(line.c_str(), "o%u %255s", &pos_var_name, var_name) != 2 || pos_var_name >= nb_outputs)
        {
          error_oss << line_number << " invalid output name";
          throw std::runtime_error(error_oss.str());
        }
        output_names.emplace(var_name);
        if (*output_names.crbegin() != var_name)
          throw std::runtime_error("Output variables have to be "
                                   "lexicographically ordered!\n");
        line.clear();
        getline(iss, line);
        ++line_number;
        break;
      }
      case 'c':
        break;
      default:
      {
        error_oss << line_number << " invalid line";
        throw std::runtime_error(error_oss.str());
      }
      }
    }
    if (not input_names.empty())
      {
        if (input_names.size() != nb_inputs)
          throw std::runtime_error("Either none or all inputs have to be named.\n");
      }
    else
      for (unsigned i = 0; i < nb_inputs; ++i)
        input_names.emplace("i"+std::to_string(i));
    if (not output_names.empty())
      {
        if (output_names.size() != nb_outputs)
          throw std::runtime_error("Either none or all outputs have to be named.\n");
      }
    else
      for (unsigned i = 0; i < nb_outputs; ++i)
        output_names.emplace("o"+std::to_string(i));
  return std::make_tuple(input_names, output_names, latches, outputs, gates);
  }
}

namespace spot
{

  // register the bdd corresponding the an
  // aig literal
  void aig::register_new_lit_(unsigned v, const bdd &b)
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

  void aig::register_latch(unsigned i, const bdd& b)
  {
    register_new_lit_(latch_var(i), b);
  }

  void aig::register_input(unsigned i, const bdd& b)
  {
    register_new_lit_(input_var(i), b);
  }

  unsigned aig::input_var(unsigned i) const
  {
    assert(i < num_inputs);
    return (1 + i) * 2;
  }

  unsigned aig::latch_var(unsigned i) const
  {
    assert(i < num_latches);
    return (1 + num_inputs + i) * 2;
  }

  unsigned aig::gate_var(unsigned i) const
  {
    assert(i < num_gates());
    return (1 + num_inputs + num_latches + i) * 2;
  }

  void aig::set_output(unsigned i, unsigned v)
  {
    assert(v <= max_var() + 1);
    outputs_[i] = v;
  }

  void aig::set_latch(unsigned i, unsigned v)
  {
    assert(v <= max_var() + 1);
    latches_[i] = v;
  }

  unsigned aig::aig_not(unsigned v)
  {
    unsigned not_v = v ^ 1;
    assert(var2bdd_.count(v) && var2bdd_.count(not_v));
    return not_v;
  }

  unsigned aig::aig_and(unsigned v1, unsigned v2)
  {
    assert(var2bdd_.count(v1));
    assert(var2bdd_.count(v2));
    bdd b = var2bdd_[v1] & var2bdd_[v2];
    auto it = bdd2var_.find(b);
    if (it != bdd2var_.end())
      return it->second;
    max_var_ += 2;
    and_gates_.emplace_back(v1, v2);
    register_new_lit_(max_var_, b);
    return max_var_;
  }

  unsigned aig::aig_and(std::vector<unsigned> vs)
  {
    if (vs.empty())
      return aig_true();
    if (vs.size() == 1)
      return vs[0];
    if (vs.size() == 2)
      return aig_and(vs[0], vs[1]);

    do
    {
      if (vs.size() & 1)
        // Odd size -> make even
        vs.push_back(aig_true());
      // Sort to increase reusage gates
      std::sort(vs.begin(), vs.end());
      // Reduce two by two inplace
      for (unsigned i = 0; i < vs.size() / 2; ++i)
        vs[i] = aig_and(vs[2 * i], vs[2 * i + 1]);
      vs.resize(vs.size() / 2);
    } while (vs.size() > 1);
    return vs[0];
  }

  unsigned aig::aig_or(unsigned v1, unsigned v2)
  {
    unsigned n1 = aig_not(v1);
    unsigned n2 = aig_not(v2);
    return aig_not(aig_and(n1, n2));
  }

  unsigned aig::aig_or(std::vector<unsigned> vs)
  {
    for (unsigned i = 0; i < vs.size(); ++i)
      vs[i] = aig_not(vs[i]);
    return aig_not(aig_and(vs));
  }

  unsigned aig::aig_pos(unsigned v)
  {
    return v & ~1;
  }

  void aig::remove_unused()
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
    auto v2idx = [&](unsigned v) -> unsigned {
      assert(!(v & 1));
      const unsigned Nlatch_min = 1 + num_inputs;
      const unsigned Ngate_min = 1 + num_inputs + num_latches;

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

    auto mark = [&](unsigned v) {
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

  unsigned aig::bdd2DNFvar(const bdd &b)
  {
    static std::vector<unsigned> plus_vars;
    static std::vector<unsigned> prod_vars(num_inputs);

    plus_vars.clear();
    prod_vars.clear();

    // Check if we have it already
    {
      auto it = bdd2var_.find(b);
      if (it != bdd2var_.end())
        //No need to recalc
        return it->second;
    }

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
        while (prod != bddtrue)
        {
          //Check if we know the sub-bdd
          if ((it = bdd2var_.find(prod)) != bdd2var_.end())
            {
              // We already constructed prod
              prod_vars.push_back(it->second);
              break;
            }
          // if the next lines failes,
          // it is probably due to unregistered latches or ins
          unsigned v = bdd2var_.at(bdd_ithvar(bdd_var(prod)));
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

  unsigned aig::bdd2INFvar(bdd b)
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

    for (unsigned i : {0, 1})
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

  aig_ptr
  aig::parse_aag(const std::string& aig_txt)
  {
    //result
    std::set<std::string> in_names__;
    std::set<std::string> out_names__;
    std::vector<unsigned> latches__;
    std::vector<unsigned> outputs__;
    std::vector<std::pair<unsigned, unsigned>> gates__;

    // Check if its an actual definition or a file name
    std::istringstream iss(aig_txt);
    std::string line;
    getline(iss, line);
    unsigned max_index, nb_inputs, nb_latches, nb_outputs, nb_and;
    if (sscanf(line.c_str(), "aag %u %u %u %u %u", &max_index, &nb_inputs, &nb_latches, &nb_outputs, &nb_and) == 5)
      {
        std::istringstream iss(aig_txt);
        std::tie(in_names__, out_names__, latches__, outputs__, gates__) =
            parse_aag_impl_(iss);
      }
    else
      {
        std::ifstream aigfile(aig_txt, std::ios::in);
        if (aigfile)
          {
            std::tie(in_names__, out_names__, latches__, outputs__, gates__) =
               parse_aag_impl_(aigfile);
            aigfile.close();
          }
        else
          throw std::runtime_error("Could not interpret the given string. "
                                   "Neither as aag nor as file-name");
      }
    aig_ptr res_ptr =
        std::make_shared<aig>(in_names__, out_names__, latches__.size());
    res_ptr->max_var_ =
        in_names__.size() + latches__.size() + gates__.size();
    std::swap(res_ptr->latches_, latches__);
    std::swap(res_ptr->outputs_, outputs__);
    std::swap(res_ptr->and_gates_, gates__);
    return res_ptr;
  }

  namespace
  {
    static void
    state_to_vec(std::vector<unsigned>& v, unsigned s,
                 unsigned offset)
    {
      v.clear();
      unsigned i = offset;
      while(s > 0)
        {
          if (s & 1)
            v.push_back(i);
          s >>= 1;
          ++i;
        }
    }

    static void
    output_to_vec(std::vector<unsigned>& v, bdd b,
                  const std::unordered_map<unsigned, unsigned>&
                  bddvar_to_outputnum)
    {
      v.clear();
      while (b != bddtrue)
        {
          unsigned i = bddvar_to_outputnum.at(bdd_var(b));
          if (bdd_low(b) == bddfalse)
            {
              v.push_back(i);
              b = bdd_high(b);
            }
          else
            b = bdd_low(b);
        }
    }

    // Switch initial state and 0 in the AIGER encoding, so that the
    // 0-initialized latches correspond to the initial state.
    static unsigned
    encode_init_0(unsigned src, unsigned init)
    {
      return src == init ? 0 : src == 0 ? init : src;
    }

    // Heuristic to minimize the number of gates
    // in the resulting aiger
    // the idea is to take the (valid) output with the
    // least "highs" for each transition.
    // Another idea is to chose conditions such that transitions
    // can share output conditions. Problem this is a combinatorial
    // problem and suboptimal solutions that can be computed in
    // reasonable time have proven to be not as good
    // Stores the outcondition to use in the used_outc vector
    // for each transition in aut
    std::vector<std::vector<bdd>>
    maxlow_outc(const std::vector<std::pair<const_twa_graph_ptr, bdd>>& strat_vec,
                const bdd& all_inputs)
    {
      std::vector<std::vector<bdd>> used_outc;

      for (auto&& astrat : strat_vec)
        {
          used_outc.emplace_back(astrat.first->num_edges()+1);
          auto& this_outc = used_outc.back();
          for (auto&& e: astrat.first->edges())
            {
              assert(e.cond != bddfalse);
              bdd bout = bdd_exist(e.cond, all_inputs);
              assert(((bout & bdd_existcomp(e.cond, all_inputs)) == e.cond) &&
                     "Precondition (in) & (out) == cond violated");
              // Get the minterm with least highs
              //Those that are undefined we be set to low
              this_outc[astrat.first->edge_number(e)] = bdd_satone(bout);
              assert(this_outc[astrat.first->edge_number(e)] != bddfalse);
            }
        }
      //Done
      return used_outc;
    }

    // Transforms an automaton into an AIGER circuit
    // using irreducible sums-of-products
    static aig_ptr
    auts_to_aiger(const std::vector<std::pair<const_twa_graph_ptr, bdd>>& strat_vec,
                  const char* mode)
    {
      // The aiger circuit cannot encode the acceptance condition
      // Test that the acceptance condition is true
      for (auto&& astrat : strat_vec)
        if (!astrat.first->acc().is_t())
          throw std::runtime_error("Cannot turn automaton into aiger circuit");

      // get the propositions
      std::set<std::string> input_names;
      std::set<std::string> output_names;
      bdd all_inputs = bddtrue;
      bdd all_outputs = bddtrue;

      std::vector<bdd> all_inputs_vec;
      std::unordered_map<unsigned, unsigned> bddvar_to_num;

      {
        std::unordered_map<std::string, int> stash_;
        for (auto& astrat : strat_vec)
          {
            all_outputs &= astrat.second;
            for (const auto& ap : astrat.first->ap())
              {
                int bddvar =
                  astrat.first->get_dict()->
                    has_registered_proposition(ap, astrat.first);
                assert(bddvar >= 0);
                stash_.emplace(std::make_pair(ap.ap_name(), bddvar));
                bdd b = bdd_ithvar(bddvar);
                if (bdd_implies(astrat.second, b)) // ap is an output AP
                  {
                    if (output_names.count(ap.ap_name()))
                      throw std::runtime_error("Outputs not disjoint!\n"
                                               "Problem ap: " + ap.ap_name());
                    output_names.emplace(ap.ap_name());
                  }
                else // ap is an input AP
                  {
                    input_names.emplace(ap.ap_name());
                    all_inputs &= b;
                  }
              }
          }
        // Distribute
        size_t i = 0;
        for (auto&& name : input_names)
          {
            auto bddvar = stash_[name];
            bddvar_to_num[bddvar] = i;
            all_inputs_vec.push_back(bdd_ithvar(bddvar));
            ++i;
          }
        i = 0;
        for (auto&& name : output_names)
          {
            bddvar_to_num[stash_[name]] = i;
            ++i;
          }
      }

      // Decide on which outcond to use
      // The edges of the automaton all have the form in&out
      // due to the unsplit
      // however we need the edge to be deterministic in out too
      // So we need determinism and we also want the resulting aiger
      // to have as few gates as possible
      std::vector<std::vector<bdd>> used_outc =
          maxlow_outc(strat_vec, all_inputs);

      // Encode state in log2(num_states) latches.
      // The latches of each strategy have to be separated
      // so we get latches = [latches_0, latches_1, ....]
      auto abdd_dict = strat_vec[0].first->get_dict();

      // latches per strat
      std::vector<unsigned> log2n;
      log2n.reserve(strat_vec.size());
      // First variable representing the latches
      std::vector<int> st0;
      st0.reserve(strat_vec.size());
      // cumulative sum of latches across strats
      std::vector<unsigned> latch_offset;
      latch_offset.reserve(strat_vec.size()+1);
      unsigned n_latches = 0;
      for (auto&& astrat : strat_vec)
        {
          log2n.push_back(std::ceil(std::log2(astrat.first->num_states())));
          latch_offset.push_back(n_latches);
          n_latches += log2n.back();
        }
      latch_offset.push_back(n_latches);

      st0.push_back(abdd_dict->
          register_anonymous_variables(n_latches,
                                       strat_vec[0].first));
      for (size_t i = 1; i < strat_vec.size(); ++i)
        st0.push_back(st0.back()+log2n[i]);

      assert(output_names.size() == (unsigned) bdd_nodecount(all_outputs));
      aig_ptr circuit_ptr =
          std::make_shared<aig>(input_names, output_names, n_latches);
      aig& circuit = *circuit_ptr;

      // Register
      // latches
      for (unsigned i = 0; i < n_latches; ++i)
        circuit.register_latch(i, bdd_ithvar(st0[0]+i));
//        circuit.register_new_lit(circuit.latch_var(i), bdd_ithvar(st0[0]+i));
      // inputs
      for (unsigned i = 0; i < all_inputs_vec.size(); ++i)
        circuit.register_input(i, all_inputs_vec[i]);
//        circuit.register_new_lit(circuit.input_var(i), all_inputs_vec[i]);

      // Latches and outputs are expressed as a DNF in which each term
      // represents a transition.
      // latch[i] (resp. out[i]) represents the i-th latch (resp. output) DNF.

      std::vector<unsigned> out_vec;
      out_vec.reserve(output_names.size());
      std::vector<unsigned> next_state_vec;
      next_state_vec.reserve(n_latches);
      if (strcasecmp(mode, "ISOP") == 0)
        {
          std::vector<std::vector<unsigned>> latch(n_latches);
          std::vector<std::vector<unsigned>> out(output_names.size());

          // Loop over the different strategies
          for (unsigned i = 0; i < strat_vec.size(); ++i)
            {
              auto&& [astrat, aouts] = strat_vec[i];

              auto aoff = latch_offset[i];
              auto aoff_next = latch_offset.at(i+1);

              auto enc_init =
                [inum = astrat->get_init_state_number()](auto s)
                  {
                    return encode_init_0(s, inum);
                  };
              auto state2prodvar = [&](auto s)
                {
                  static std::vector<unsigned> prod_state(n_latches);
                  prod_state.clear();

                  auto s2 = enc_init(s);
                  for (unsigned j = aoff; j < aoff_next; ++j)
                    {
                      unsigned v = circuit.latch_var(j);
                      prod_state.push_back(s2 & 1 ? v : circuit.aig_not(v));
                      s2 >>= 1;
                    }
                  assert(s2 <= 1);
                  return circuit.aig_and(prod_state);
                };

              // Loop over all statea
              for (unsigned s = 0; s < astrat->num_states(); ++s)
                {
                  // Encoding of src
                  auto src_var = state2prodvar(s);
                  //Loop over all its edges
                  for (auto&& e: astrat->out(s))
                    {
                      // Same outcond for all ins
                      output_to_vec(out_vec,
                                    used_outc[i][astrat->edge_number(e)],
                                    bddvar_to_num);
                      // out_vec holds all that have to be high,
                      // lows can be ignored

                      // Get high latches of dst state
                      state_to_vec(next_state_vec, enc_init(e.dst), aoff);

                      // Get the isops over the input condition
                      // Each isop only contains variables from in
                      // -> directly compute the corresponding
                      // variable and and-gate
                      unsigned incond_var = circuit.bdd2DNFvar(
                          bdd_exist(e.cond, aouts));
                      // todo
                      // Test that bdd_exist(e.cond, aouts)
                      // Does not contains outs of other strategies?

                      // AND with state
                      unsigned tot_cond =
                          circuit.aig_and(src_var, incond_var);
                      // Set in latches/outs having "high"
                      for (auto&& nl : next_state_vec)
                        {
                          assert (aoff <= nl && nl < aoff_next);
                          latch.at(nl).push_back(tot_cond);
                        }
                      for (auto&& ao : out_vec)
                        {
                          // todo test?
                          out.at(ao).push_back(tot_cond);
                        }
                    }//edge
                }//state
            }//strat
          // OR them all
          // As the elements are ORED,
          // we can sort the latch and out vectors and make them unique
          // This might reduce the number of gates by increasing reusage
          // and decreasing number of terms
          auto preproc = [](auto& vofvu)
            {
              for (auto& vu : vofvu)
                {
                  std::sort(vu.begin(), vu.end());
                  auto new_end = std::unique(vu.begin(), vu.end());
                  vu.erase(new_end, vu.end());
                }
            };
          preproc(latch);
          preproc(out);

          for (unsigned i = 0; i < n_latches; ++i)
            circuit.set_latch(i, circuit.aig_or(latch[i]));
          for (unsigned i = 0; i < output_names.size(); ++i)
            circuit.set_output(i, circuit.aig_or(out[i]));
          circuit.remove_unused();
        }
      else if (strcasecmp(mode, "ITE") == 0)
        {
          std::vector<bdd> latch(n_latches, bddfalse);
          std::vector<bdd> out(output_names.size(), bddfalse);

          // Loop over the different strategies
          for (unsigned i = 0; i < strat_vec.size(); ++i)
            {
              auto&& [astrat, aouts] = strat_vec[i];
              auto ast0 = st0[i];

              auto aoff = latch_offset[i];
              auto aoff_next = latch_offset.at(i+1);

              auto alog2n = log2n[i];
              auto enc_init =
                [&, inum = astrat->get_init_state_number()](auto s)
                  {
                    return encode_init_0(s, inum);
                  };
              auto state2bdd = [&](auto s)
                {
                  bdd b = bddtrue;
                  auto s2 = enc_init(s);
                  for (unsigned j = 0; j < alog2n; ++j)
                    {
                      b &= (s2 & 1) ? bdd_ithvar(ast0 + j)
                                    : bdd_nithvar(ast0 + j);
                      s2 >>= 1;
                    }
                  assert(s2 <= 1);
                  return b;
                };

              for (unsigned s = 0; s < astrat->num_states(); ++s)
                {
                  // Convert state to bdd
                  bdd src_bdd = state2bdd(s);

                  for (const auto& e : astrat->out(s))
                    {
                      // High latches of dst
                      state_to_vec(next_state_vec, enc_init(e.dst), aoff);

                      // Get high outs depending on cond
                      output_to_vec(out_vec,
                                    used_outc[i][astrat->edge_number(e)],
                                    bddvar_to_num);

                      // The condition that joins in_cond and src
                      bdd tot_cond = src_bdd & bdd_exist(e.cond, aouts);
                      // Test should not have any outs from other strats

                      // Set in latches/outs having "high"
                      for (auto&& nl : next_state_vec)
                        {
                          assert (aoff <= nl && nl < aoff_next);
                          latch.at(nl) |= tot_cond;
                        }
                      for (auto&& ao : out_vec)
                        {
                          // todo test?}
                          out.at(ao) |= tot_cond;
                        }
                    } // edges
                } // state
            } //strat
          // Create the vars
          for (unsigned i = 0; i < output_names.size(); ++i)
            circuit.set_output(i, circuit.bdd2INFvar(out[i]));
          for (unsigned i = 0; i < n_latches; ++i)
            circuit.set_latch(i, circuit.bdd2INFvar(latch[i]));
        }
      else
        {
          throw std::runtime_error
            ("print_aiger(): mode must be \"ISOP\" or \"ITE\"");
        }

      return circuit_ptr;
    } // auts_to_aiger
  }

  aig_ptr
  strategy_to_aig(const const_twa_ptr& aut, const char* mode)
  {
    if (!aut)
      throw std::runtime_error("aut cannot be null");
    auto a = down_cast<const_twa_graph_ptr>(aut);
    if (!a)
      throw std::runtime_error("aiger output is only for twa_graph");

    if (bdd* all_outputs = aut->get_named_prop<bdd>("synthesis-outputs"))
      //return aut_to_aiger(a, *all_outputs, mode);
      return auts_to_aiger({{a, *all_outputs}}, mode);
    else
      throw std::runtime_error("strategy_to_aig relies on the named property"
                               "\"synthesis-outputs\".\n");
  }

  aig_ptr
  strategies_to_aig(const std::vector<const_twa_ptr>& strat_vec,
                  const char *mode )
  {
    std::vector<std::pair<const_twa_graph_ptr, bdd>> new_vec;
    new_vec.reserve(strat_vec.size());

    for (auto&& astrat : strat_vec)
      {
        auto a = down_cast<const_twa_graph_ptr>(astrat);
        if (!a)
          throw std::runtime_error("aiger output is only for twa_graph");

        if (bdd* all_outputs =
                a->get_named_prop<bdd>("synthesis-outputs"))
          new_vec.emplace_back(a, *all_outputs);
        else
          throw std::runtime_error("strategy_to_aig relies on the named property"
                                   "\"synthesis-outputs\".\n");
      }
    return auts_to_aiger(new_vec, mode);
  }

  aig_ptr
  strategy_to_aig(const twa_ptr &aut, const char *mode,
                  const std::set<std::string>& ins,
                  const std::set<std::string>& outs)
  {
    if (!aut)
      throw std::runtime_error("aut cannot be null");
    auto a = down_cast<const_twa_graph_ptr>(aut);
    if (!a)
      throw std::runtime_error("aiger output is only for twa_graph");

    // Make sure ins and outs are disjoint
    {
      std::vector<std::string> inter;
      std::set_intersection(ins.begin(), ins.end(),
                            outs.begin(), outs.end(),
                            std::back_inserter(inter));
      if (not inter.empty())
        {
          for (auto&& e : inter)
            std::cerr << e << '\n';
          throw std::runtime_error("The above aps appear in \"ins\" and"
                                   "\"outs\"");
        }
    }
    // Register all to make sure they exist in the aut
    bdd all_outputs = bddtrue;
    for (auto&& aap : ins)
      aut->register_ap(aap);
    for (auto&& aap : outs)
      {
        all_outputs &= bdd_ithvar(aut->register_ap(aap));
        if (all_outputs == bddfalse)
          throw std::runtime_error("Inconsistency in all outputs.\n");
      }
    // todo Some additional checks?
    //return aut_to_aiger(a, all_outputs, mode);
    return auts_to_aiger({{a, all_outputs}}, mode);
  }

  aig_ptr
  strategies_to_aig(const std::vector<twa_ptr>& strat_vec, const char *mode,
                    const std::set<std::string>& ins,
                    const std::vector<std::set<std::string>>& outs)
  {
    assert(strat_vec.size() == outs.size() && "Not as many outs as strats.\n");

    std::vector<std::pair<const_twa_graph_ptr, bdd>> new_vec;

    std::set<std::string> seen_ap = ins;
    for (size_t i = 0; i < strat_vec.size(); ++i)
      {
        auto a = down_cast<const_twa_graph_ptr>(strat_vec[i]);
        if (!a)
          throw std::runtime_error("aiger output is only for twa_graph");

        // Make sure ins and former outs are disjoint
        {
          bool inserted;
          for (auto&& aout : outs[i])
            {
              std::tie(std::ignore, inserted) = seen_ap.insert(aout);
              if (not inserted)
                throw std::runtime_error("The above ap appear in either "
                                         " \"ins\" or is shared between "
                                         "multiple strategies as \"outs\"\n: "
                                         + aout);
            }
        }
        // Register all to make sure they exist in the aut
        bdd all_outputs = bddtrue;
        for (auto&& aap : ins)
          strat_vec[i]->register_ap(aap);
        for (auto&& aap : outs[i])
        {
          all_outputs &= bdd_ithvar(strat_vec[i]->register_ap(aap));
          if (all_outputs == bddfalse)
            throw std::runtime_error("Inconsistency in all outputs.\n");
        }
        // todo Some additional checks?
        new_vec.emplace_back(a, all_outputs);
      }
    return auts_to_aiger(new_vec, mode);
  }

  // TODO: Le mode n'a rien à faire là
  std::ostream &
  print_aiger(std::ostream &os, const_aig_ptr circuit, const char* mode)
  {

    if (not circuit)
      return os;//Print nothing in case of nullptr

    std::vector<std::string> in_names(circuit->input_names.begin(),
                                      circuit->input_names.end());
    std::vector<std::string> out_names(circuit->output_names.begin(),
                                       circuit->output_names.end());
    if (strcasecmp(mode, "circuit") == 0)
    {
      // Writing gates to formatted buffer speed-ups output
      // as it avoids "<<" calls
      // vars are unsigned -> 10 digits at most
      char gate_buffer[3 * 10 + 5];
      auto write_gate = [&](unsigned o, unsigned i0, unsigned i1) {
        std::sprintf(gate_buffer, "%u %u %u\n", o, i0, i1);
        os << gate_buffer;
      };
      // Count active gates
      unsigned n_gates = 0;
      for (auto &g : circuit->gates())
        if ((g.first != 0) && (g.second != 0))
          ++n_gates;
      // Note max_var_ is now an upper bound
      os << "aag " << circuit->max_var() / 2
          << ' ' << circuit->num_inputs
          << ' ' << circuit->num_latches
          << ' ' << circuit->num_outputs
          << ' ' << n_gates << '\n';
      for (unsigned i = 0; i < circuit->num_inputs; ++i)
        os << (1 + i) * 2 << '\n';
      for (unsigned i = 0; i < circuit->num_latches; ++i)
        os << (1 + circuit->num_inputs + i) * 2
           << ' ' << circuit->latches()[i] << '\n';
      for (unsigned i = 0; i < circuit->num_outputs; ++i)
        os << circuit->outputs()[i] << '\n';
      for (unsigned i = 0; i < circuit->num_gates(); ++i)
        if ((circuit->gates()[i].first != 0)
            && (circuit->gates()[i].second != 0))
          write_gate(circuit->gate_var(i),
                     circuit->gates()[i].first,
                     circuit->gates()[i].second);
      for (unsigned i = 0; i < circuit->num_inputs; ++i)
        os << 'i' << i << ' ' << in_names[i] << '\n';
      for (unsigned i = 0; i < circuit->num_outputs; ++i)
        os << 'o' << i << ' ' << out_names[i] << '\n';
    }
    else
      throw std::runtime_error
          ("print_aiger(): mode must be \"dot\" or \"circuit\"");
    return os;
  }
}
