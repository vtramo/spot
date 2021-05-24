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
#include <string>

#include <spot/twa/twagraph.hh>
#include <spot/misc/minato.hh>
#include <spot/priv/synt_utils.hh>

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
    if (sscanf(line.c_str(), "aag %u %u %u %u %u", &max_index, &nb_inputs,
               &nb_latches, &nb_outputs, &nb_and) != 5)
    {
      error_oss << line_number << " invalid header";
      throw std::runtime_error(error_oss.str());
    }

    if (max_index < nb_inputs + nb_latches + nb_and)
      throw std::runtime_error("More variables than indicated by max var");

    latches.reserve(nb_latches);
    outputs.reserve(nb_outputs);
    gates.reserve(nb_and);

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
      if (and_gate != 2*(1 + nb_inputs + nb_latches + i))
        throw std::runtime_error(std::string() +
            "Invalid gate numbering\n" +
            "Expected: " + std::to_string(2*(1 + nb_inputs + nb_latches + i)) +
            "\nGot: " + std::to_string(and_gate) + '\n');
      gates.emplace_back(lhs, rhs);
    }
    line.clear();
    // todo
    // Here we need some restrictions to get a set...
    getline(iss, line);
    ++line_number;
    bool comment_sec = false;
    while (iss && !comment_sec)
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
        if (sscanf(line.c_str(), "i%u %255s", &pos_var_name, var_name) != 2
            || pos_var_name >= nb_inputs)
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
        if (sscanf(line.c_str(), "o%u %255s", &pos_var_name, var_name) != 2
            || pos_var_name >= nb_outputs)
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
        comment_sec = true;
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
          throw std::runtime_error("Either none or all inputs "
                                   "have to be named.\n");
      }
    else
      for (unsigned i = 0; i < nb_inputs; ++i)
        input_names.emplace("i"+std::to_string(i));
    if (not output_names.empty())
      {
        if (output_names.size() != nb_outputs)
          throw std::runtime_error("Either none or all outputs "
                                   "have to be named.\n");
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

  void aig::register_latch_(unsigned i, const bdd& b)
  {
    register_new_lit_(latch_var(i), b);
  }

  void aig::register_input_(unsigned i, const bdd& b)
  {
    register_new_lit_(input_var(i), b);
  }

  // Unregisters positive and negative form of a literal
  // which has to be given in positive form
  void aig::unregister_lit_(unsigned v)
  {
    assert(((v&1) == 0) && "Expected positive form");
    unsigned n_del;
    n_del = bdd2var_.erase(var2bdd_[v]);
    assert(n_del);
    n_del = var2bdd_.erase(v);
    assert(n_del);
    v = v ^ 1;
    n_del = bdd2var_.erase(var2bdd_[v]);
    assert(n_del);
    n_del = var2bdd_.erase(v);
    assert(n_del);
  }

  aig::safe_point aig::get_safe_point_() const
  {
    return {max_var_, and_gates_.size()};
  }

  aig::safe_stash
  aig::roll_back_(safe_point sf, bool do_stash)
  {
    // todo spezialise for safe_all?
    safe_stash ss;
    if (do_stash)
      {
        unsigned dn = max_var_ - sf.first;
        assert((dn&1) == 0);
        dn /= 2;
        assert(dn == std::distance(and_gates_.begin()+sf.second,
                                   and_gates_.end()));
        ss.first.resize(dn);
        ss.second.reserve(dn);
        //Copy and erase the lits
        for (unsigned v = sf.first+2; v <= max_var_; v += 2)
            ss.second.emplace_back(v, var2bdd_[v]);
        // Copy the gates
        std::copy(and_gates_.begin()+sf.second, and_gates_.end(),
                  ss.first.begin());
      }
    // 1 Delete all literals
    // max_var_old was used before
    // max_var_ is currently used
    for (unsigned v = sf.first+2; v <= max_var_; v += 2)
      unregister_lit_(v);
    // 2 Set back the gates
    and_gates_.erase(and_gates_.begin()+sf.second, and_gates_.end());
    max_var_ = sf.first;
    return ss;
  }

  void
  aig::reapply_(safe_point sf, const safe_stash& ss)
  {
    // Do some check_ups
    assert(ss.first.size() == ss.second.size());
    assert(sf.first == max_var_);
    assert(sf.second == and_gates_.size());
    unsigned new_max_var_ = max_var_ + ss.first.size()*2;
    for (auto& p : ss.second)
      {
        assert(p.first <= new_max_var_+1);
        register_new_lit_(p.first, p.second);
      }
    and_gates_.insert(and_gates_.end(),
                      ss.first.begin(), ss.first.end());
    max_var_ = new_max_var_;
  }

  // Get propositions that are commun to all
  // possible productsso that they can be anded at the end
  bdd aig::accum_commun_(const bdd& b) const
  {
    bdd commun_bdd = bddtrue;
    for (unsigned i = 0; i < num_inputs(); ++i)
    {
      if (bdd_implies(b, input_bdd(i)))
        commun_bdd &= input_bdd(i);
      else if (bdd_implies(b, input_bdd(i, true)))
        commun_bdd &= input_bdd(i, true);
    }
    for (unsigned i = 0; i < num_latches(); ++i)
    {
      if (bdd_implies(b, latch_bdd(i)))
        commun_bdd &= latch_bdd(i);
      else if (bdd_implies(b, latch_bdd(i, true)))
        commun_bdd &= latch_bdd(i, true);
    }
    assert(commun_bdd != bddfalse);
    return commun_bdd;
  }

  void aig::set_output(unsigned i, unsigned v)
  {
    assert(v <= max_var() + 1);
    outputs_[i] = v;
  }

  void aig::set_next_latch(unsigned i, unsigned v)
  {
    assert(v <= max_var() + 1);
    next_latches_[i] = v;
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
//    if (use_and_split_)
//      left_gate_map_[v1].insert(v2);
    return max_var_;
  }

  unsigned aig::aig_and(std::vector<unsigned> vs)
  {
    if (vs.empty())
      return aig_true();
    if (vs.size() == 1)
      return vs[0];

    std::sort(vs.begin(), vs.end());
    auto new_end = std::unique(vs.begin(), vs.end());
    vs.erase(new_end, vs.end());

    if (vs.size() == 2)
      return aig_and(vs[0], vs[1]);

    unsigned add_elem = -1u;
//    if (!use_and_split_)
//    {
    do
    {

      if (vs.size() & 1)
        {
          // Odd size -> make even
          add_elem = vs.back();
          vs.pop_back();
        }

      // Reduce two by two inplace
      for (unsigned i = 0; i < vs.size() / 2; ++i)
        vs[i] = aig_and(vs[2 * i], vs[2 * i + 1]);
      vs.resize(vs.size() / 2);
      // Add the odd elem if necessary
      if (add_elem != -1u)
        {
          vs.push_back(add_elem);
          add_elem = -1u;
        }
      // Sort to increase reusage gates
      std::sort(vs.begin(), vs.end());
    } while (vs.size() > 1);
//    }
//    else
//    {
//      std::vector<unsigned> vs_[2];
//      vs_[0] = vs;
//
//      std::vector<bool> ex_(vs.size());
//
//      auto add_1 = [&](auto& vsi)
//      {
//        unsigned add_elem = -1u;
//        if (vsi.size() & 1)
//        {
//          // Odd size -> make even
//          add_elem = vsi.back();
//          vsi.pop_back();
//        }
//
//        // Reduce two by two inplace
//        unsigned svsi = vsi.size();
//        for (unsigned i = 0; i < svsi / 2; ++i)
//          vsi[i] = aig_and(vsi[2 * i], vsi[2 * i + 1]);
//        vsi.resize(vsi.size() / 2);
//        // Add the odd elem if necessary
//        if (add_elem != -1u)
//        {
//          vsi.push_back(add_elem);
//          add_elem = -1u;
//        }
//        // Sort to increase reusage gates
//        std::sort(vsi.begin(), vsi.end());
//      };
//
//      do
//      {
//        // todo, make this faster
//        std::fill(ex_.begin(), ex_.end(), false);
//        unsigned svs = vs_[0].size();
//        for (unsigned il = 0; il < svs-1; ++il)
//        {
//          auto gli = left_gate_map_.find(vs_[0][il]);
//          if (gli == left_gate_map_.end())
//            continue;
//          for (unsigned ir = il+1; ir < svs; ++ir)
//            if (gli->second.count(vs_[0][ir]))
//              {
//                ex_[il] = true;
//                ex_[ir] = true;
//              }
//        }
//        unsigned i0 = 0;
//        for (unsigned i = 0; i < svs; ++i)
//        {
//          if (ex_[i])
//          {
//            vs_[0][i0] = vs_[0][i];
//            ++i0;
//          }
//          else
//            vs_[1].push_back(vs_[0][i]);
//        }
//        vs_[0].resize(i0);
//        if (i0 == 0)
//          vs_[0].push_back(aig_true());
//
//        add_1(vs_[0]);
//      } while (vs_[0].size() > 1);
//
//      // Compress the unknown
//      if (vs_[1].size() == 0)
//        vs_[1].push_back(aig_true());
//      else
//      {
//        do
//        {
//          add_1(vs_[1]);
//        } while (vs_[1].size() > 1);
//      }
//      // Set the result
//      if (vs_[0][0] < vs_[1][0])
//        vs[0] = aig_and(vs_[0][0], vs_[1][0]);
//      else
//        vs[0] = aig_and(vs_[1][0], vs_[0][0]);
//    }

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
      const unsigned Nlatch_min = 1 + num_inputs();
      const unsigned Ngate_min = 1 + num_inputs() + num_latches();

      // Note: this will at most run twice
      while (true)
      {
        unsigned i = v / 2;
        if (i >= Ngate_min)
          // v is a gate
          return i - Ngate_min;
        else if (i >= Nlatch_min)
          // v is a latch -> get gate
          v = aig_pos(next_latches_.at(i - Nlatch_min));
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

  unsigned aig::bdd2DNFvar(bdd b)
  {
    static std::vector<unsigned> plus_vars;
    static std::vector<unsigned> prod_vars(num_inputs()
                                           +num_latches());

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

  unsigned aig::prod2partitionedDNFvar_impl_(const bdd& prodin)
  {
    static std::vector<unsigned> prod_vars_;

    auto it = bdd2var_.find(prodin);
    if (it != bdd2var_.end())
      return it->second;

    bdd prods_[2];

    unsigned vp_[2];

    // Split ins/latches
    prods_[0] = bdd_exist(prodin, all_ins_); //latch bdd
    prods_[1] = bdd_exist(prodin, all_latches_); //ins bdd

    for (int c : {0, 1})
      {
        prod_vars_.clear();
        bdd& prod = prods_[c];
        // Check if existing
        auto it = bdd2var_.find(prod);
//        if (it != bdd2var_.end())
//          vp_[c] = it->second;
//        else
//        {
          // Create
        while (prod != bddtrue)
        {
          //Check if we know the sub-bdd
          if ((it = bdd2var_.find(prod)) != bdd2var_.end())
            {
              // We already constructed prod
              prod_vars_.push_back(it->second);
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
          prod_vars_.push_back(v);
        }
        vp_[c] = aig_and(prod_vars_);
      }
//      }
    prod_vars_.clear();
    if (vp_[0] < vp_[1])
      return aig_and(vp_[0], vp_[1]);
    else
    return aig_and(vp_[1], vp_[0]);
  }


  unsigned aig::bdd2partitionedDNFvar_impl_(const bdd& b)
  {
    static std::vector<unsigned> plus_vars_;

    auto it = bdd2var_.find(b);
    if (it != bdd2var_.end())
      return it->second;

    bdd prod;
    minato_isop cond(b);

    while ((prod = cond.next()) != bddfalse)
      plus_vars_.push_back(prod2partitionedDNFvar_impl_(prod));

    // Done building
    unsigned res = aig_or(plus_vars_);
    plus_vars_.clear();
    return res; // Sum them
  }

  unsigned aig::bdd2partitionedDNFvar_(bdd b)
  {
    // Check if dual is better
//    return bdd2partitionedDNFvar_impl_(b);
//    unsigned max_var_old = max_var_;
//    unsigned gate_size_old = and_gates_.size();
    auto sf = get_safe_point_();
    unsigned res_prim = bdd2partitionedDNFvar_impl_(b);
    unsigned add_gates_pos = and_gates_.size() - sf.second;
    auto ss_prim = roll_back_(sf, true);
    unsigned v_neg = bdd2partitionedDNFvar_impl_(bdd_not(b));
    unsigned add_gates_neg = and_gates_.size() - sf.second;
    if (add_gates_neg <= add_gates_pos)
      return aig_not(v_neg);

    // Undo-Redo
    roll_back_(sf);
    reapply_(sf, ss_prim);
    return res_prim;
  }

  unsigned aig::bdd2partitionedDNFvar(bdd b)
  {
    if (split_off_)
      {


//        unsigned max_var_old = max_var_;
//        unsigned gate_size_old = and_gates_.size();
        auto sf = get_safe_point_();
        unsigned final_prim;
        {
          //Primal
          bdd commun_bdd = accum_commun_(b);
          // Remove communs
          bdd b_prim_single = bdd_exist(b, commun_bdd);
          // Combine them
          unsigned commun_var = prod2partitionedDNFvar_impl_(commun_bdd);
          // Get remaining prods
          unsigned var_p = bdd2partitionedDNFvar_(b_prim_single);
          // And the commungs and the product
          final_prim = aig_and(commun_var, var_p);
        }
        // Check, rollback, dualize, redo
        unsigned add_gates_pos = and_gates_.size() - sf.second;
        auto ss_prim = roll_back_(sf, true);

        //Dual
        unsigned final_dual;
        {
          bdd b_dual = bdd_not(b);
//          auto [communs, commun_bdd] = accum_commun_(b_dual);
          bdd commun_bdd = accum_commun_(b_dual);
          // Remove communs
          bdd b_dual_single = bdd_exist(b_dual, commun_bdd);
          // Combine them
          unsigned commun_var = prod2partitionedDNFvar_impl_(commun_bdd);
          // Get remaining prods
          unsigned var_p = bdd2partitionedDNFvar_(b_dual_single);
          // And the commungs and the product
          final_dual = aig_not(aig_and(commun_var, var_p));
        }
        // Check, rollback, dualize, redo
        unsigned add_gates_neg = and_gates_.size() - sf.second;

        if (add_gates_neg <= add_gates_pos)
          return final_dual;

        roll_back_(sf);
        reapply_(sf, ss_prim);
        return final_prim;
      }
    else
      return bdd2partitionedDNFvar_(b);
  }



  unsigned aig::bdd2INFvar_impl_1_(const bdd& b)
  {
    // F = !v&low | v&high
    // De-morgan
    // !(!v&low | v&high) = !(!v&low) & !(v&high)
    // !v&low | v&high = !(!(!v&low) & !(v&high))
    auto b_it = bdd2var_.find(b);
    if (b_it != bdd2var_.end())
      return b_it->second;

    unsigned v_var = bdd2var_.at(bdd_ithvar(bdd_var(b)));

    unsigned b_branch_var[2] = {bdd2INFvar_impl_1_(bdd_low(b)),
                                bdd2INFvar_impl_1_(bdd_high(b))};

    unsigned r = aig_not(aig_and(v_var, b_branch_var[1]));
    unsigned l = aig_not(aig_and(aig_not(v_var), b_branch_var[0]));
    return aig_not(aig_and(l, r));
  }

  unsigned aig::bdd2INFvar_impl_(const bdd& b, bool do_min)
  {
    if (!do_min)
      return bdd2INFvar_impl_1_(b);
    else
      {
        auto sf = get_safe_point_();

        unsigned var_p = bdd2INFvar_impl_1_(b);
        unsigned add_gates_pos = and_gates_.size() - sf.second;
        auto ss_prim = roll_back_(sf, true);

        unsigned var_neg = aig_not(bdd2INFvar_impl_1_(bdd_not(b)));
        unsigned add_gates_neg = and_gates_.size() - sf.second;

        if (add_gates_neg <= add_gates_pos)
          return var_neg;

        roll_back_(sf);
        reapply_(sf, ss_prim);

        return var_p;
      }
  }

  unsigned aig::bdd2INFvar(bdd b,
                           bool do_min)
  {
    if (split_off_)
      {
        auto sf = get_safe_point_();

        unsigned var_p;
        unsigned add_gates_pos;
        {
          bdd comm = accum_commun_(b);
          bdd b_single = bdd_exist(b, comm);
          unsigned comm_var = prod2partitionedDNFvar_impl_(comm);
          var_p = aig_and(comm_var, bdd2INFvar_impl_(b_single, do_min));
          add_gates_pos = and_gates_.size() - sf.second;
        }

        auto ss_prim = roll_back_(sf, true);

        unsigned var_neg;
        unsigned add_gates_neg;
        {
          bdd bn = bdd_not(b);
          bdd comm = accum_commun_(bn);
          bdd b_single = bdd_exist(bn, comm);
          unsigned comm_var = prod2partitionedDNFvar_impl_(comm);
          var_neg = aig_not(aig_and(comm_var,
                                    bdd2INFvar_impl_(b_single, do_min)));
          add_gates_neg = and_gates_.size() - sf.second;
        }

        if (add_gates_neg <= add_gates_pos)
          return var_neg;

        roll_back_(sf);
        reapply_(sf, ss_prim);
        return var_p;
      }
    else
      return bdd2INFvar_impl_(b, do_min);

  }

  void aig::build_all_bdds(const std::vector<bdd>& all_bdd)
  {

    // Build a set of all bdds needed in a "smart" way
    // We only need the bdd or its negation, never both
    std::set<bdd, bdd_less_than> needed_bdd;
    for (const auto& b : all_bdd)
      {
        if (needed_bdd.count(bdd_not(b)))
          continue;
        needed_bdd.insert(b);
      }

    std::vector<std::vector<bdd>> sum_terms;
    sum_terms.reserve(all_bdd.size());
    std::set<bdd, bdd_less_than> needed_prods;
    // Do sth smart here
    std::vector<bdd> sum_terms_pos;
    std::vector<bdd> sum_terms_neg;
    std::vector<bdd> intersect;
    for (const auto& b : needed_bdd)
      {
        sum_terms_pos.clear();
        sum_terms_neg.clear();
        // Compute the ISOP of the primal and dual
        // Use the repr that adds less terms

        bdd prod;

        minato_isop cond_isop(b);
        while ((prod = cond_isop.next()) != bddfalse)
          sum_terms_pos.push_back(prod);

        cond_isop = minato_isop(bdd_not(b));
        while ((prod = cond_isop.next()) != bddfalse)
          sum_terms_neg.push_back(prod);

        std::sort(sum_terms_pos.begin(), sum_terms_pos.end(),
                  bdd_less_than());
        std::sort(sum_terms_neg.begin(), sum_terms_neg.end(),
                  bdd_less_than());

        intersect.clear();
        std::set_intersection(needed_prods.cbegin(), needed_prods.end(),
                              sum_terms_pos.cbegin(), sum_terms_pos.cend(),
                              std::back_inserter(intersect), bdd_less_than());
//        unsigned n_add_pos = sum_terms_pos.size() - intersect.size();
        unsigned n_add_pos = 0;
        std::for_each(sum_terms_pos.begin(), sum_terms_pos.end(),
                      [&n_add_pos, &intersect](const auto& b)
                      {
                        if (std::find(intersect.cbegin(), intersect.cend(),
                                      b) == intersect.cend())
                          n_add_pos += bdd_nodecount(b);
                      });

        intersect.clear();
        std::set_intersection(needed_prods.cbegin(), needed_prods.end(),
                              sum_terms_neg.cbegin(), sum_terms_neg.cend(),
                              std::back_inserter(intersect), bdd_less_than());
//        unsigned n_add_neg = sum_terms_neg.size() - intersect.size();
        unsigned n_add_neg = 0; //sum_terms_neg.size() - intersect.size();
        std::for_each(sum_terms_neg.begin(), sum_terms_neg.end(),
                      [&n_add_neg, &intersect](const auto& b)
                      {
                        if (std::find(intersect.cbegin(), intersect.cend(),
                                      b) == intersect.cend())
                          n_add_neg += bdd_nodecount(b);
                      });

        if (n_add_pos <= n_add_neg)
          {
            needed_prods.insert(sum_terms_pos.begin(), sum_terms_pos.end());
            sum_terms.emplace_back(std::move(sum_terms_pos));
          }
        else
          {
            needed_prods.insert(sum_terms_neg.begin(), sum_terms_neg.end());
            sum_terms.emplace_back(std::move(sum_terms_neg));
          }
      }

    // Now we need to compute the prod_terms
    // todo switch to using id() to avoid ref count
    // and use a map
    std::vector<std::vector<bdd>> prod_terms;
    prod_terms.reserve(needed_prods.size());
    for (bdd aprod : needed_prods) //apord : i1&ni2...
      {
        prod_terms.emplace_back();
        auto& ptv = prod_terms.back();

        while (aprod != bddtrue)
        {
          bdd topvar = bdd_ithvar(bdd_var(aprod));
          bdd aprod_low = bdd_low(aprod);
          if (aprod_low == bddfalse)
            {
              ptv.push_back(topvar);
              aprod = bdd_high(aprod);
            }
          else
            {
              ptv.push_back(bdd_not(topvar));
              aprod = aprod_low;
            }
        }
        std::sort(ptv.begin(), ptv.end(),
                  bdd_less_than());
      }

      // Now we need to count and then create the stack
      // We start with the products
//      struct bdd_pair_hash:
//      {
//        template <class P>
//        size_t operator()(const P& p) const
//        {
//          size_t h = (size_t) p.first.id();
//          h <<= 32;
//          h += p.second.id();
//          return h;
//        }
//      };
//      struct bdd_pair_equal
//      {
//        bool operator()(const std::pair<bdd, bdd>& p1,
//                        const std::pair<bdd, bdd>& p2) const
//        {
//          return (p1.first == p2.first)
//                 && (p1.second == p2.second);
//        }
//      };
    auto bdd_pair_hash = [](const auto& p) noexcept
      {
        size_t h = (size_t) p.first.id();
        h <<= 32;
        h += p.second.id();
        return h;
      };
    auto bdd_pair_equal = [](const auto& p1, const auto& p2) noexcept
      {
          return (p1.first == p2.first)
                 && (p1.second == p2.second);
      };

    std::unordered_map<std::pair<bdd, bdd>, unsigned,
                       decltype(bdd_pair_hash),
                       decltype(bdd_pair_equal)> occur_map(prod_terms.size(),
                                                           bdd_pair_hash,
                                                           bdd_pair_equal);
    auto count_occ = [&occur_map](const auto& term)
      {
//          std::cout << "count ";
//          for (auto& e : term)
//            std::cout << e << ' ';
//          std::cout << std::endl;
        unsigned l = term.size();
        for (unsigned i = 0; i < l; ++i)
          for (unsigned j = i + 1; j < l; ++j)
          {
            auto [it, ins] =
              occur_map.try_emplace({term[i], term[j]} , 0);
            it->second += 1;
//          std::cout << term[i] << ' ' << term[j] << ' ' << it->second
                  //  << std::endl;
          }
      };
    auto uncount_occ = [&occur_map](const auto& term)
    {
//        std::cout << "uncount ";
//        for (auto& e : term)
//          std::cout << e << ' ';
//        std::cout << std::endl;
      unsigned l = term.size();
      for (unsigned i = 0; i < l; ++i)
        for (unsigned j = i + 1; j < l; ++j)
          {
            assert(occur_map.at({term[i], term[j]}) >= 1);
            occur_map[{term[i], term[j]}] -= 1;
//              std::cout << term[i] << ' ' << term[j] << ' '
                      //  << occur_map[{term[i], term[j]}] << std::endl;
          }
    };
//      std::cout << "count\n";
    for (const auto& pterm : prod_terms)
      count_occ(pterm);

//      struct prod_heap_e
//      {
//        bdd left;
//        bdd right;
//        unsigned occ;
//      };
//      auto comp_prod_heap_e = [](const prod_heap_e& l,const prod_heap_e& r)
//        {
//          return l.occ < r.occ;
//        };
//      std::deque<prod_heap_e> prod_heap;
////      prod_heap.reserve(occur_map.size());
//      std::transform(occur_map.cbegin(), occur_map.cend(),
//                     std::back_inserter(prod_heap),
//                     [](auto& it)->prod_heap_e
//                     {return {it.first.first, it.first.second, it.second};});
//      occur_map.clear();
//      std::make_heap(prod_heap.begin(), prod_heap.end(),
//                     comp_prod_heap_e);

    // Now we have the heap
    // Successively construct the largest and put in the new ones
//      auto and_ = [this](const prod_heap_e& pe)
//        {
//          assert(bdd2var_.count(pe.left));
//          assert(bdd2var_.count(pe.right));
//          // Internal creation
//          aig_and(bdd2var_[pe.left], bdd2var_[pe.right]);
//          return pe.left & pe.right;
//        };
    auto and_ = [this](const auto& mi)
      {
        assert(bdd2var_.count(mi.first.first));
        assert(bdd2var_.count(mi.first.second));
        // Internal creation
        aig_and(bdd2var_[mi.first.first], bdd2var_[mi.first.second]);
        return mi.first.first & mi.first.second;
      };

//      auto pop_heap = [&prod_heap, &comp_prod_heap_e]()
//        {
//          auto max_elem = prod_heap.front();
//          std::pop_heap(prod_heap.begin(), prod_heap.end(),
//                        comp_prod_heap_e);
//          prod_heap.pop_back();
//          return max_elem;
//        };
//
//      auto push_heap = [&prod_heap, &comp_prod_heap_e](prod_heap_e&& e)
//        {
//          prod_heap.push_back(e);
//          std::push_heap(prod_heap.begin(), prod_heap.end(),
//                         comp_prod_heap_e);
//        };

//      while (!prod_heap.empty())
    auto get_max = [&occur_map]
    {
      auto itm =
              std::max_element(occur_map.cbegin(), occur_map.cend(),
                               [](const auto& it1, const auto& it2)
                                 { return std::make_tuple(it1.second, it1.first.first.id(), it1.first.second.id())
                                         < std::make_tuple(it2.second, it2.first.first.id(), it2.first.second.id()); });
      assert(itm != occur_map.cend());
      return *itm;
    };

//      while (!occur_map.empty())
    while (!occur_map.empty())
    {
//          auto max_elem = pop_heap();
//          std::cout << "mod " << max_elem.left << ' ' << max_elem.right << ' ' << max_elem.occ << std::endl;
      auto max_elem = get_max();
          unsigned n_occur_old = max_elem.second;
//      std::cout << "mod " << max_elem.first.first << ' ' << max_elem.first.second << ' ' << max_elem.second << std::endl;
      if (max_elem.second == 0)
        break;

    // Create the gate
      bdd andcond = and_(max_elem);
      // Update
      // Check in all prods if this exists and update
      unsigned n_occur = 0;
//          occur_map.clear(); // Holds new products

      for (auto& pterm : prod_terms)
        {
//              for (auto& e : pterm)
//                std::cout << e << ' ';
//              std::cout << std::endl;
          // todo, too costly right now
          // Find left and right
          // Note, left is always to the left of right
//          auto itl = std::find(pterm.begin(), pterm.end(), max_elem.first.first);
//          auto itr = std::find(itl+1, pterm.end(), max_elem.first.second);
          auto itl = std::find(pterm.begin(), pterm.end(), max_elem.first.first);
          auto itr =
              itl == pterm.end() ? pterm.end()
                                 : std::find(itl+1, pterm.end(), max_elem.first.second);

          if ((itl != pterm.end()) && (itr != pterm.end()))
            {
              ++n_occur;
              // uncount -> modifiy -> count
              uncount_occ(pterm);
//                  std::cout << n_occur_old << std::endl;
              pterm.erase(itr); //Order matters
              pterm.erase(itl);
              pterm.push_back(andcond);
              std::sort(pterm.begin(), pterm.end(),
                        bdd_less_than());
              count_occ(pterm);
//                  for (unsigned i = 0; i < pterm.size(); ++i)
//                    {
//                      if (bdd_less_than()(pterm[i], andcond))
//                        occur_map[{pterm[i], andcond}] += 1;
//                      else if (bdd_less_than()(andcond, pterm[i]))
//                        occur_map[{andcond, pterm[i]}] += 1;
//                    }
            }
        }
      assert(n_occur_old == n_occur);
      // Insert into the heap
//          for (auto& it : occur_map)
//            push_heap({it.first.first, it.first.second, it.second});
//          occur_map.clear();
    }
    // All products should now be created
//    std::cout << "Needed p terms\n";
//    for (auto& p : needed_prods)
//      {
//        std::cout << p << " : " << p.id() << std::endl;
//      }
//    std::cout << "Generated p terms\n";
//    for (auto& pterm : prod_terms)
//    {
//      for (auto& e : pterm)
//        std::cout<< e << " : " << e.id() << ";;";
//      std::cout << std::endl;
//    }
//    std::cout << "Safed bdds\n";
//    for (const auto& it : bdd2var_)
//      std::cout << it.first << " - " << it.first.id() << " : " << it.second << '\n';
//    std::cout << std::endl;
    assert(std::all_of(needed_prods.cbegin(), needed_prods.cend(),
                       [this](const bdd& aprod)
                       { return bdd2aigvar(aprod) > 0; }));

      // We have created all products, now we need the sums
      // We basically do the same but with or
    occur_map.clear();
    for (const auto& sterm : sum_terms)
      {
        // a & b = b & a only count once
        count_occ(sterm);
//        unsigned l = sterm.size();
//        for (unsigned i = 0; i < l; ++i)
//          for (unsigned j = i + 1; j < l; ++j)
//            occur_map[{sterm[i], sterm[j]}] += 1;
      }
    // The data structures do not change
//    auto& sum_heap = prod_heap;
//    assert(sum_heap.empty());
//
////    sum_heap.reserve(occur_map.size());
//    std::transform(occur_map.cbegin(), occur_map.cend(),
//                   std::back_inserter(sum_heap),
//                   [](auto& it)->prod_heap_e
//                   {return {it.first.first, it.first.second, it.second};});
//    occur_map.clear();
//    std::make_heap(sum_heap.begin(), sum_heap.end(),
//                   comp_prod_heap_e);

//    auto or_ = [this](const prod_heap_e& pe)
//    {
//      assert(bdd2var_.count(pe.left));
//      assert(bdd2var_.count(pe.right));
//      // Internal creation
//      aig_or(bdd2var_[pe.left], bdd2var_[pe.right]);
//      return pe.left | pe.right;
//    };
    auto or_ = [this](const auto& mi)
    {
      assert(bdd2var_.count(mi.first.first));
      assert(bdd2var_.count(mi.first.second));
      // Internal creation
      aig_or(bdd2var_[mi.first.first], bdd2var_[mi.first.second]);
      return mi.first.first | mi.first.second;
    };

//    while (!sum_heap.empty())
//    while (true)
    while (!occur_map.empty())
    {
//      auto max_elem = pop_heap();
      auto max_elem = get_max();
//      std::cout << "mod " << max_elem.first.first << ' ' << max_elem.first.second << ' ' << max_elem.second << std::endl;
      unsigned n_occur_old = max_elem.second;
      if (max_elem.second == 0)
        break;
      // Create the gate
      bdd orcond = or_(max_elem);
      // Update
      // Check in all prods if this exists and update
      unsigned n_occur = 0;
//      occur_map.clear(); // Holds new products

      for (auto& sterm : sum_terms)
      {
//        for (auto& e : sterm)
//          std::cout << e << ' ';
//        std::cout << std::endl;
        // todo, too costly right now
        // Find left and right
        auto itl = std::find(sterm.begin(), sterm.end(), max_elem.first.first);
        auto itr =
            itl == sterm.end() ? sterm.end()
                : std::find(itl+1, sterm.end(), max_elem.first.second);

        if ((itl != sterm.end()) && (itr != sterm.end()))
        {
          ++n_occur;
          // uncount -> modifiy -> count
          uncount_occ(sterm);
//          std::cout << n_occur << std::endl;
          sterm.erase(itr); //Order matters
          sterm.erase(itl);
          sterm.push_back(orcond);
          std::sort(sterm.begin(), sterm.end(),
                    bdd_less_than());
          count_occ(sterm);
//          for (unsigned i = 0; i < sterm.size(); ++i)
//          {
//            if (bdd_less_than()(sterm[i], orcond))
//              occur_map[{sterm[i], orcond}] += 1;
//            else if (bdd_less_than()(orcond, sterm[i]))
//              occur_map[{orcond, sterm[i]}] += 1;
//          }
        }
      }
      assert(n_occur_old == n_occur);
      // Insert into the heap
//      for (auto& it : occur_map)
//        push_heap({it.first.first, it.first.second, it.second});
//      occur_map.clear();
    }

  }

  aig_ptr
  aig::parse_aag(const std::string& aig_txt,
                 bdd_dict_ptr dict)
  {
    //result
    std::set<std::string> in_names__;
    std::set<std::string> out_names__;
    std::vector<unsigned> next_latches__;
    std::vector<unsigned> outputs__;
    std::vector<std::pair<unsigned, unsigned>> gates__;

    // Check if its an actual definition or a file name
    std::istringstream iss(aig_txt);
    std::string line;
    getline(iss, line);
    unsigned max_index, nb_inputs, nb_latches, nb_outputs, nb_and;
    if (sscanf(line.c_str(), "aag %u %u %u %u %u", &max_index, &nb_inputs,
               &nb_latches, &nb_outputs, &nb_and) == 5)
      {
        std::istringstream iss(aig_txt);
        std::tie(in_names__, out_names__, next_latches__, outputs__, gates__) =
            parse_aag_impl_(iss);
      }
    else
      {
        std::ifstream aigfile(aig_txt, std::ios::in);
        if (aigfile)
          {
            std::tie(in_names__, out_names__, next_latches__, outputs__, gates__) =
               parse_aag_impl_(aigfile);
            aigfile.close();
          }
        else
          throw std::runtime_error("Could not interpret the given string. "
                                   "Neither as aag nor as file-name");
      }
    aig_ptr res_ptr =
        std::make_shared<aig>(in_names__, out_names__,
                              next_latches__.size(), dict);
    aig& circ = *res_ptr;
    res_ptr->max_var_ =
        (in_names__.size() + next_latches__.size() + gates__.size())*2;
    std::swap(res_ptr->next_latches_, next_latches__);
    std::swap(res_ptr->outputs_, outputs__);
    std::swap(res_ptr->and_gates_, gates__);

    // Create all the bdds/vars
    // true/false/latches/inputs already exist
    // Get the gatenumber corresponding to an output
    auto v2g = [&](unsigned v)->unsigned
      {
        v = circ.aig_pos(v);
        v /= 2;
        assert(v >= 1 + circ.num_inputs_ + circ.num_latches_
               && "Variable does not correspond to a gate");
        return v - (1 + circ.num_inputs_ + circ.num_latches_);
      };
    auto& var2bdd = circ.var2bdd_;
    auto& bdd2var = circ.bdd2var_;
    std::function<bdd(unsigned)> get_gate_bdd;
    get_gate_bdd = [&](unsigned g)->bdd
      {
        assert((v2g(circ.gate_var(g)) == g));

        unsigned v = circ.gate_var(g);
        auto it = var2bdd.find(v);
        if (it != var2bdd.end())
        {
          assert(bdd2var.at(var2bdd.at(v)) == v
                 && "Inconsistent bdd!\n");
          return it->second;
        }
        //get the vars of the input to the gates
        bdd gsbdd[2];
        unsigned gsv[2] = {circ.and_gates_.at(g).first,
                           circ.and_gates_.at(g).second};
        // Check if the exist
        for (size_t i : {0, 1})
        {
          it = var2bdd.find(gsv[i]);
          if (it != var2bdd.end())
            gsbdd[i] = it->second;
          else
          {
            // Construct it
            gsbdd[i] = get_gate_bdd(v2g(circ.aig_pos(gsv[i])));
            // Odd idx -> negate
            if (gsv[i]&1)
              gsbdd[i] = bdd_not(gsbdd[i]);
          }
        }
        bdd gbdd = bdd_and(gsbdd[0], gsbdd[1]);
        circ.register_new_lit_(v, gbdd);
        return gbdd;
      };
    // Do this for each gate then everything should exist
    // Also it should be consistent
    for (unsigned g = 0; g < res_ptr->num_gates(); ++g)
    {
      get_gate_bdd(g);
    }
    //Check that all outputs and next_latches exist
    auto check = [&var2bdd](unsigned v)
      {
        if (not (var2bdd.count(v)))
          throw std::runtime_error("variable " + std::to_string(v)
                                   + " has no bdd associated!\n");
      };
    std::for_each(circ.next_latches_.begin(), circ.next_latches_.end(),
                  check);
    std::for_each(circ.outputs_.begin(), circ.outputs_.end(),
                  check);
    return res_ptr;
  }

  twa_graph_ptr aig::aig2aut(bool keepsplit) const
  {
    static_assert(sizeof(int) == 4);
    static_assert(sizeof(unsigned long long) == 8);

    auto aut = make_twa_graph(dict_);

    unsigned n_max_states = 2 << num_latches_;
    aut->new_states(n_max_states);


    auto s2bdd = [&](unsigned s)
      {
        bdd b = bddtrue;
        for (unsigned j = 0; j < num_latches_; ++j)
          {
            // Get the j-th latch in this partial strategy
            // If high -> not negated
            b &= latch_bdd(j, !(s & 1));
            s >>= 1;
          }
        return b;
      };
//
//    auto sprime2bdd = [&](unsigned s)
//    {
//      bdd b = bddtrue;
//      for (unsigned j = 0; j < num_latches_; ++j)
//      {
//        // Get the j-th latch in this partial strategy
//        // If high -> not negated
//        b &= aigvar2bdd(next_latches_[j], !(s & 1));
//        s >>= 1;
//      }
//      return b;
//    };

    std::vector<bdd> outbddvec;
    for (auto& ao : output_names_)
      outbddvec.push_back(bdd_ithvar(aut->register_ap(ao)));
    // Also register the ins
    for (auto& ai : input_names_)
      aut->register_ap(ai);

    std::vector<bdd> outcondbddvec;
    for (auto ov : outputs_)
      outcondbddvec.push_back(aigvar2bdd(ov));

    auto get_out = [&](const bdd& sbdd, const bdd& insbdd)
      {
        bdd out = bddtrue;
        for (unsigned i = 0; i < num_outputs_; ++i)
          {
            if ((outcondbddvec[i] & sbdd & insbdd) != bddfalse)
              out &= outbddvec[i];
            else
              out &= bdd_not(outbddvec[i]);
          }
        return out;
      };


    //Nextlatch is a fonction of latch and input
    std::vector<bdd> nxtlbddvec(num_latches_);
    for (unsigned i = 0; i < num_latches_; ++i)
      nxtlbddvec[i] = aigvar2bdd(next_latches_[i]);

    auto get_dst = [&](const bdd& sbdd, const bdd& insbdd)
      {
        // the first latch corresponds to the most significant digit
        unsigned dst = 0;
        unsigned off = 1;
        for (unsigned i = 0; i < num_latches_; ++i)
          {
            bdd ilatch = nxtlbddvec[i];
            // evaluate
            ilatch = (ilatch & sbdd & insbdd);
            dst += (ilatch != bddfalse)*off;
            off *= 2;
          }
        return dst;
      };

    bdd alli = bddtrue;
    std::vector<bdd> ibddvec(num_inputs_);
    for (unsigned i = 0; i < num_inputs_; ++i)
      {
        ibddvec[i] = input_bdd(i);
        alli &= ibddvec[i];
      }

    std::deque<unsigned> todo;
    todo.push_back(0);
    std::vector<bool> seen(n_max_states, false);
    seen[0] = true;

    std::unordered_map<unsigned long long, unsigned> splayer_map;
    //dst + cond -> state
    auto get_id = [](const bdd& ocond, unsigned dst)
    {
      unsigned long long u = dst;
      u <<= 32;
      u += std::abs(ocond.id());
      return u;
    };

    while (!todo.empty())
      {
        unsigned s = todo.front();
        todo.pop_front();

        // bdd of source state
        bdd srcbdd = s2bdd(s);
        // All possible inputs
        // Note that for unspecified input sequences the
        // result is unspecified as well

        //todo change to new format
        bdd remin = bddtrue;
        while (remin != bddfalse)
          {
            bdd inbdd = bdd_satoneset(remin, alli, bddfalse);
            remin -= inbdd;

            // Get the target state
            unsigned sprime = get_dst(srcbdd, inbdd);
            // Get the associated cout cond
            bdd outbdd = get_out(srcbdd, inbdd);

            if (keepsplit)
              {
                auto id = get_id(outbdd, sprime);
                auto it = splayer_map.find(id);
                if (it == splayer_map.end())
                  {
                    unsigned ntarg = aut->new_state();
                    splayer_map[id] = ntarg;
                    aut->new_edge(s, ntarg, inbdd);
                    aut->new_edge(ntarg, sprime, outbdd);
                  }
                else
                  aut->new_edge(s, it->second, inbdd);
              }
            else
              aut->new_edge(s, sprime, inbdd & outbdd);
            if (!seen[sprime])
              {
                seen[sprime] = true;
                todo.push_back(sprime);
              }
          }
      }
    aut->purge_unreachable_states();
    aut->merge_edges();
    return aut;
  }

  namespace
  {
    using namespace spot;
    using namespace minutils;

    static void
    state_to_vec(std::vector<unsigned>& v, unsigned s,
                 unsigned offset)
    {
      v.clear();
      unsigned i = offset;
      while (s > 0)
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
//    static unsigned
//    encode_init_0(unsigned src, unsigned init)
//    {
//      return src == init ? 0 : src == 0 ? init : src;
//    }

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
    maxlow_outc(const std::vector<std::pair<const_twa_graph_ptr, bdd>>&
                    strat_vec,
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

    std::vector<std::vector<bdd>>
    reuse_outc(const std::vector<std::pair<const_twa_graph_ptr, bdd>>&
                    strat_vec,
                const bdd& all_inputs)
    {

      //todo filter out minterms!

      //edge outcond -> used outcond (minterm)
      std::unordered_map<bdd, bdd, bdd_hash> cond_map;

      std::vector<std::vector<bdd>> used_outc;
      // First fill with base out cond, then replace by minterm
      for (auto&& astrat : strat_vec)
        {
          used_outc.emplace_back(astrat.first->num_edges()+1, bddfalse);
          auto& this_outc = used_outc.back();
          for (auto&& e: astrat.first->edges())
            {
              assert(e.cond != bddfalse);
              bdd bout = bdd_exist(e.cond, all_inputs);
              assert(((bout & bdd_existcomp(e.cond, all_inputs)) == e.cond) &&
                     "Precondition (in) & (out) == cond violated");
              this_outc[astrat.first->edge_number(e)] = bout;
              cond_map[bout] = bddfalse;
            }
        }
      // All conditions are stored in cond_map
      const size_t n_cond = cond_map.size();
      std::vector<bdd> bddvec;
      bddvec.reserve(n_cond);
      for (auto& it : cond_map)
        bddvec.push_back(it.first);

//      std::cout << "Conditions:\n";
//      for (size_t i = 0; i < bddvec.size(); ++i)
//        std::cout << i << " : " << bddvec[i] << '\n';

      // todo symmetric specialisation?
      // todo vectorized functions?
      square_matrix<char> incomp_mat(n_cond, false);

      // Compute pair-wise compatibility
      for (size_t i = 0; i < n_cond; ++i)
        for (size_t j = i+1; j < n_cond; ++j)
          if ((bddvec[i] & bddvec[j]) == bddfalse)
            {
              incomp_mat(i, j) = true;
              incomp_mat(j, i) = true;
            }

//      std::cout << "Incomp:\n";
//      incomp_mat.print();


      // Here the "states" are infact the out edge conditions
      auto psol = get_part_sol(incomp_mat);
      if (psol.psol_v.size() == n_cond)
        return maxlow_outc(strat_vec, all_inputs); //todo

      const auto& psol_v = psol.psol_v;
      const auto& psol_s = psol.psol_s;
      const unsigned n_psol = psol_v.size();
      std::vector<unsigned> free_v;
      free_v.reserve(n_cond - psol_v.size());
      for (unsigned i = 0; i < n_cond; ++i)
        if (psol_s.count(i) == 0)
          free_v.push_back(i);
      const unsigned n_free = free_v.size();
//      std::cout << "p sol\n";
//      for (auto v : psol_v)
//        std::cout << v << ' ';
//      std::cout << '\n';
//      std::cout << "free\n";
//      for (auto v : free_v)
//        std::cout << v << ' ';
//      std::cout << '\n';

      // Covering condition -> each condition needs to be
      // update when a new class is added
      std::deque<std::deque<int>> cover_cond(n_cond); // Those for psol are emtpy
      std::deque<int> incomp_cond;

      // The lit mapper
      // We have to create a new satsolver each time
      // n_env_ <-> n_cond
      auto Sptr = std::make_shared<satsolver>();
      lit_mapper lm(Sptr, n_psol, n_cond, 0);

      // Create the initial/partial solution
      // This reamins unchanged -> incomp_cond
      lm.unfreeze_xi();
      // Cover cond: we can assign free edges
      // only to partial solutions if they are compatible
      for (auto fe : free_v)
        for (unsigned i = 0; i < n_psol; ++i)
          if (!incomp_mat(psol_v[i], fe))
            cover_cond[fe].push_back(lm.sxi2lit({fe, i}));
      lm.freeze_xi();

      // Incompatible conditions:
      // If fi and fj are both compatible with
      // a partial solution k, but incompatible with one another -> add
      for (unsigned k = 0; k < n_psol; ++k)
      {
        unsigned fk = psol_v[k];
        for (unsigned i = 0; i < n_free; ++i)
        {
          unsigned fi = free_v[i];
          if (incomp_mat(fi, fk))
            continue; //fi can not be in k
          for (unsigned j = i + 1; j < n_free; ++j)
          {
            unsigned fj = free_v[j];
            if (incomp_mat(fj, fk))
              continue;
            if (incomp_mat(fi, fj))
            {
              incomp_cond.push_back(-lm.sxi2lit({fi, k}));
              incomp_cond.push_back(-lm.sxi2lit({fj, k}));
              incomp_cond.push_back(0);
            }
          }
        }
      }


//      for (unsigned i = 0; i < n_psol; ++i)
//        {
//          incomp_cond.push_back(lm.sxi2lit({psol_v[i], i}));
//          incomp_cond.push_back(0);
//        }
//      // covering cond for partial solutions
//      for (unsigned x = 0; x < n_cond; ++x)
//        {
//          if (psol_s.count(x))
//            continue; // No need, it has its own class
//          for (unsigned i = 0; i < n_psol; ++i)
//          {
//            if (incomp_mat(psol_v[i], x))
//              // Skip this literal as they are incomp
//              continue;
//            cover_cond[x].push_back(lm.sxi2lit({x, i}));
//            // The partial solution edges are exactly in its own class
//
//            // Note this has to be finalised with 0
//          }
//        }
//
//      // Incomp condition for partial solution
//      // No finalise needed
//      for (unsigned i = 0; i < n_psol; ++i)
//        for (unsigned x = 0; x < n_cond; ++x)
//          if (incomp_mat(psol_v[i], x))
//          {
//            incomp_cond.push_back(-lm.sxi2lit({x, i})); // x can not be in class i
//            incomp_cond.push_back(0);
//          }
//      lm.freeze_xi();

      //Base conditions done
      std::vector<bool> satsol;
      unsigned n_classes = n_psol;
      while (true)
        {
//          std::cout << n_classes << '\n';
          lm.print();

          // Search a solution for current instance
          // Get a fresh solver and adjust
          Sptr = std::make_shared<satsolver>();
          lm.Sw_ = Sptr;
          Sptr->adjust_nvars(lm.next_var_ - 1);
          //Add
          // The incomp-conditions are already proper clauses
          Sptr->add(incomp_cond);
//          std::cout << "inc\n";
//          for (auto e : incomp_cond)
//            std::cout << e << (e == 0 ? '\n' : ' ');
//          std::cout << '\n';
          // The others need to be zero terminated
          for (auto& dq : cover_cond)
            {
              if (dq.empty())
              {
//                std::cout << "jump\n";
                continue;
              }
              dq.push_back(0);
//              for (auto e : dq)
//                std::cout << e << ' ';
//              std::cout << '\n';
              Sptr->add(dq);
              dq.pop_back();
            }
          std::cerr << "### " << n_cond << ' ' << n_classes << ' ' << Sptr->get_nb_vars() << ' ' << Sptr->get_nb_clauses() << '\n';
          auto solpair = Sptr->get_solution();
          if (!solpair.second.empty())
            {
              // We have a solution
              satsol.reserve(solpair.second.size()+1);
              satsol.push_back(0);
              satsol.insert(satsol.end(), solpair.second.begin(),
                            solpair.second.end());
              break;
            }

          // Increase the number of classes
          // A solution has to exist for n_classes == n_cond
          assert(n_classes < n_cond);
          // New class has index n_classes, increment afterwards
          unsigned idx_c = n_classes;
          ++n_classes;
          lm.n_classes_ = n_classes;
          if (n_classes == n_cond)
            return maxlow_outc(strat_vec, all_inputs); //todo
          // Update cover cond of existing classes
          // The new class is apriori compatible with all states
          // Note, only free states need to be distributed
          lm.unfreeze_xi();
//          for (unsigned x = 0; x < n_cond; ++x)
          for (unsigned x : free_v)
            cover_cond[x].push_back(lm.sxi2lit({x, idx_c}));
          lm.freeze_xi();
          //Add all new incomps
          for (unsigned i = 0; i < n_free; ++i)
          {
            unsigned fi = free_v[i];
            for (unsigned j = i + 1; j < n_free; ++j)
            {
              unsigned fj = free_v[j];
              if (incomp_mat(fi, fj))
              {
                incomp_cond.push_back(-lm.sxi2lit({fi, idx_c}));
                incomp_cond.push_back(-lm.sxi2lit({fj, idx_c}));
                incomp_cond.push_back(0);
              }
            }
          }
//          for (unsigned x = 0; x < n_cond; ++x)
//            for (unsigned y = x + 1; y < n_cond; ++y)
//              if (incomp_mat(x,y))
//                {
//                  incomp_cond.push_back(-lm.sxi2lit({x, idx_c}));
//                  incomp_cond.push_back(-lm.sxi2lit({y, idx_c}));
//                  incomp_cond.push_back(0);
//                }
      }
      assert(!satsol.empty());
      // Each class at least one member
      // Find the intersection and assign
      // Attention, a cond may be in multiple classes
      // -> Use only in first class (heuristic?) in order to
      // minimize highs
      std::vector<bool> assigned(n_cond, false);
      std::vector<unsigned> in_class;
      for (unsigned i = 0; i < n_classes; ++i)
        {
          in_class.clear();
          bdd cond_class = bddtrue;
          bool has_one = false;

          // Adding the partial solution
          if (i < n_psol)
          {
            unsigned x = psol_v[i];
            cond_class = bddvec[x];
            has_one = true;
            assigned[x] = true;
            in_class.push_back(x);
          }

          for (unsigned x = 0; x < n_cond; ++x)
          {
            if (assigned[x])
              continue;
            int lxi = lm.get_sxi({x, i});
            //std::cout << cond_class << ' ' << x << ' ' << i << ' ' << lxi << ' ' << std::endl;
            assert((i >=n_psol) || ((psol_s.count(x) == 1) && lxi == 0)
                   || (psol_s.count(x) == 0)); //psol has no lit
            if ((lxi != 0) && satsol.at(lxi))
              {
                has_one = true;
                assigned[x] = true;
                cond_class &= bddvec[x];
                assert(cond_class != bddfalse);
                in_class.push_back(x);
              }
          }
          assert(has_one);
          // Get the minterm with least highs
          cond_class = bdd_satone(cond_class);
          //std::cout << cond_class << std::endl;
          // Set them
          for (unsigned x : in_class)
            cond_map.at(bddvec[x]) = cond_class;
        }

      // "0" edge is bddfalse
      cond_map[bddfalse] = bddfalse;

//      std::cout << "Res\n";
//      for (auto& it : cond_map)
//        std::cout << it.first << " -> " << it.second << '\n';
//      std::cout << std::endl;

      // Assign the results
      for (auto& bvec : used_outc)
        {
          std::transform(bvec.begin(), bvec.end(), bvec.begin(),
                         [&cond_map](const bdd& b){ return cond_map.at(b); });
          assert(std::none_of(bvec.begin()+1, bvec.end(),
                              [](const bdd& b){ return b == bddfalse; }));
        }

      // Done
      return used_outc;
    }

    // Transforms an automaton into an AIGER circuit
    // using irreducible sums-of-products
    static aig_ptr
    auts_to_aiger(const std::vector<std::pair<const_twa_graph_ptr, bdd>>&
                      strat_vec,
                  const char* mode)
    {
      if (not ((strcasecmp(mode, "ITE") == 0)
               or (strcasecmp(mode, "ITEMIN") == 0)
               or (strcasecmp(mode, "ISOP") == 0)
               or (strcasecmp(mode, "ISOPMIN") == 0)
               or (strcasecmp(mode, "OPTIM") == 0)
               or (strcasecmp(mode, "BEST") == 0)))
        throw std::runtime_error("mode must be \"ITE\", \"ISOP\", "
                                 "\"ISOPMIN\" or \"OPTIM\"!\n");
      // The aiger circuit cannot encode the acceptance condition
      // Test that the acceptance condition is true
      for (auto&& astrat : strat_vec)
        if (!astrat.first->acc().is_t())
          {
            std::cerr << "Acc cond must be true not " << astrat.first->acc()
                      << std::endl;
            throw std::runtime_error("Cannot turn automaton into "
                                     "aiger circuit");
          }

      // get the propositions
      std::set<std::string> input_names;
      std::set<std::string> output_names;
      bdd all_inputs = bddtrue;
      bdd all_outputs = bddtrue;

      // Join all the outputs
      for (auto& astrat : strat_vec)
        all_outputs &= astrat.second;

      std::vector<bdd> all_inputs_vec;
      std::unordered_map<unsigned, unsigned> bddvar_to_num;

      {
        std::unordered_map<std::string, int> stash_;
        for (auto& astrat : strat_vec)
          {
            for (const auto& ap : astrat.first->ap())
              {
                int bddvar =
                  astrat.first->get_dict()->
                    has_registered_proposition(ap, astrat.first);
                assert(bddvar >= 0);
                stash_.emplace(std::make_pair(ap.ap_name(), bddvar));
                bdd b = bdd_ithvar(bddvar);
                if (bdd_implies(all_outputs, b)) // ap is an output AP
                  {
//                    if (output_names.count(ap.ap_name()))
//                      throw std::runtime_error("Outputs not disjoint!\n"
//                                               "Problem ap: " + ap.ap_name());
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

      std::vector<std::vector<bdd>> used_outc;
      if (strat_vec.size() < 10000) //Dummy
        used_outc = maxlow_outc(strat_vec, all_inputs);
      else
        used_outc = reuse_outc(strat_vec, all_inputs); //Still a bug?

      // Encode state in log2(num_states) latches.
      // The latches of each strategy have to be separated
      // so we get latches = [latches_0, latches_1, ....]

      // latches per strat
      // If the states in the automaton are named,
      // it is assumed that they are named by integers
      // and these values will be used for encoding
      // This coding has to ensure that the initial state
      // is zero
      // attention : least significant bit -> left / idx 0
      std::vector<std::vector<unsigned>> state_numbers;
      std::vector<unsigned> log2n;
      log2n.reserve(strat_vec.size());
      // cumulative sum of latches across strats
      std::vector<unsigned> latch_offset;
      latch_offset.reserve(strat_vec.size()+1);
      unsigned n_latches = 0;
      for (auto&& astrat : strat_vec)
        {
          state_numbers.emplace_back();
          state_numbers.back().reserve(astrat.first->num_states());
          unsigned max_index = 0;
          // Check if named
          if (const auto* s_names =
                  astrat.first->get_named_prop<std::vector<std::string>>("state-names"))
            {
              std::transform(s_names->cbegin(), s_names->cend(),
                             std::back_inserter(state_numbers.back()),
                             [&max_index](const auto& sn)
                             {
                               unsigned su = std::stoul(sn);
                               max_index = std::max(max_index, su);
                               return su;
                             });
              ++max_index;
            }
          else
            {
              max_index = astrat.first->num_states();
              state_numbers.back().resize(astrat.first->num_states());
              std::iota(state_numbers.back().begin(),
                        state_numbers.back().end(), 0);
              std::swap(state_numbers.back()[0],
                        state_numbers.back()[astrat.first->get_init_state_number()]);
            }
          // Largest index to encode -> num_states()-1
          log2n.push_back(std::ceil(std::log2(max_index)));
          latch_offset.push_back(n_latches);
          n_latches += log2n.back();
        }
      latch_offset.push_back(n_latches);

      assert(output_names.size() == (unsigned) bdd_nodecount(all_outputs));
      aig_ptr circuit_ptr =
          std::make_shared<aig>(input_names, output_names,
                                n_latches, strat_vec[0].first->get_dict());
      aig& circuit = *circuit_ptr;

      // Latches and outputs are expressed as a bdd
      // The bdd are then translated into aiger circuits
      // relying on different strategies
      std::vector<bdd> latch(n_latches, bddfalse);
      std::vector<bdd> out(output_names.size(), bddfalse);

      std::vector<unsigned> out_vec;
      out_vec.reserve(output_names.size());
      std::vector<unsigned> next_state_vec;
      next_state_vec.reserve(n_latches);

      // Loop over the different strategies
      for (unsigned i = 0; i < strat_vec.size(); ++i)
      {
        auto&& [astrat, aouts] = strat_vec[i];

        auto latchoff = latch_offset[i];
        auto latchoff_next = latch_offset.at(i+1);

        auto alog2n = log2n[i];
//        auto enc_init =
//            [&, inum = astrat->get_init_state_number()](auto s)
//            {
//              return encode_init_0(s, inum);
//            };
        auto enc_init =
            [&sn = state_numbers.at(i)](unsigned s)
            {
              return sn[s];
            };
        auto state2bdd = [&](auto s)
        {
          auto s2 = enc_init(s);
          bdd b = bddtrue;
          for (unsigned j = 0; j < alog2n; ++j)
          {
            // Get the j-th latch in this partial strategy
            // If high -> not negated
            b &= circuit.latch_bdd(latchoff + j, !(s2 & 1));
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
            state_to_vec(next_state_vec, enc_init(e.dst), latchoff);

            // Get high outs depending on cond
            output_to_vec(out_vec,
                          used_outc[i][astrat->edge_number(e)],
                          bddvar_to_num);

            // The condition that joins in_cond and src
            // Note that the circuit and the strategy share a
            // bdd_dict
            bdd tot_cond = src_bdd & bdd_exist(e.cond, aouts);
            // Test should not have any outs from other strats

            // Set in latches/outs having "high"
            for (auto&& nl : next_state_vec)
            {
              assert (latchoff <= nl && nl < latchoff_next);
              latch.at(nl) |= tot_cond;
            }
            for (auto&& ao : out_vec)
            {
              // todo test?
              out.at(ao) |= tot_cond;
            }
          } // edges
        } // state
      } //strat

      //todo make this more beautiful
      auto sf = circuit.get_safe_point_();
      unsigned min_gates = -1u;
      aig::safe_stash ss;

      auto to_treat
          = (strcasecmp(mode, "BEST") == 0) ? std::vector<std::string>{"ite", "isopmin"}
                                            : std::vector<std::string>{mode};
      for (const auto& amodestr : to_treat)
        {
          auto amodearr = amodestr.c_str();
          circuit.use_split_off(isupper(amodearr[0]));
          std::function<unsigned(bdd)> bdd2var;
          if (strcasecmp(amodearr, "ITE") == 0)
            bdd2var = [&circuit](auto b)->unsigned{return circuit.bdd2INFvar(b, false); };
          else if (strcasecmp(amodearr, "ITEMIN") == 0)
            bdd2var = [&circuit](auto b)->unsigned{return circuit.bdd2INFvar(b, true); };
          else if (strcasecmp(amodearr, "ISOP") == 0)
            bdd2var = [&circuit](auto b)->unsigned{return circuit.bdd2DNFvar(b); };
          else if (strcasecmp(amodearr, "ISOPMIN") == 0)
            bdd2var = [&circuit](auto b)->unsigned{return circuit.bdd2partitionedDNFvar(b); };
          else
            {
              // Here it is more tricky
              // First get a vector with all conditions needed in the
              // strategy
              std::vector<bdd> all_cond;
              all_cond.reserve(out.size() + latch.size());
              all_cond.insert(all_cond.end(), out.cbegin(), out.cend());
              all_cond.insert(all_cond.end(), latch.cbegin(), latch.cend());
              // Then construct it
              circuit.build_all_bdds(all_cond);
              bdd2var = [&circuit](auto b)->unsigned
                { return circuit.bdd2aigvar(b); };
            }

          // Create the vars
          for (unsigned i = 0; i < output_names.size(); ++i)
            circuit.set_output(i, bdd2var(out[i]));
          for (unsigned i = 0; i < n_latches; ++i)
            circuit.set_next_latch(i, bdd2var(latch[i]));

          // Overwrite the stash if we generated less gates
          if (circuit.num_gates() < min_gates)
            {
              min_gates = circuit.num_gates();
              ss = circuit.roll_back_(sf, true);
            }
          else
            circuit.roll_back_(sf, false);
        }
      circuit.reapply_(sf, ss); //Use the best sol
      return circuit_ptr;
    } // auts_to_aiger
  }

  aig_ptr
  strategy_to_aig(const const_twa_graph_ptr& aut, const char* mode)
  {
    if (!aut)
      throw std::runtime_error("aut cannot be null");

    if (bdd* all_outputs = aut->get_named_prop<bdd>("synthesis-outputs"))
      //return aut_to_aiger(a, *all_outputs, mode);
      return auts_to_aiger({{aut, *all_outputs}}, mode);
    else
      throw std::runtime_error("strategy_to_aig relies on the named property "
                               "\"synthesis-outputs\".\n");
  }

  aig_ptr
  strategies_to_aig(const std::vector<const_twa_graph_ptr>& strat_vec,
                  const char *mode)
  {
    std::for_each(strat_vec.begin()+1, strat_vec.end(),
                  [usedbdd = strat_vec.at(0)->get_dict()](auto&& it)
                  {
                    if (usedbdd != it->get_dict())
                      throw std::runtime_error("All strategies have to "
                                               "share a bdd_dict!\n");
                  });

    std::vector<std::pair<const_twa_graph_ptr, bdd>> new_vec;
    new_vec.reserve(strat_vec.size());

    bdd all_outputs = bddtrue;
    for (auto&& astrat : strat_vec)
      {
        if (bdd* this_outputs =
                astrat->get_named_prop<bdd>("synthesis-outputs"))
          {
            // Check if outs do not overlap
            if (bdd_and(bdd_not(*this_outputs), all_outputs) == bddfalse)
              throw std::runtime_error("\"outs\" of strategies are not "
                                       "distinct!.\n");
            all_outputs &= *this_outputs;
            new_vec.emplace_back(astrat, *this_outputs);
          }
        else
          throw std::runtime_error("strategy_to_aig relies on the named "
                                   "property \"synthesis-outputs\".\n");
      }
    return auts_to_aiger(new_vec, mode);
  }

  aig_ptr
  strategy_to_aig(const twa_graph_ptr &aut, const char *mode,
                  const std::set<std::string>& ins,
                  const std::set<std::string>& outs)
  {
    if (!aut)
      throw std::runtime_error("aut cannot be null");

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
    std::for_each(ins.begin(), ins.end(),
                  [s = aut](auto&& e){s->register_ap(e); });
    bdd all_outputs = bddtrue;
    std::for_each(outs.begin(), outs.end(),
                  [&ao = all_outputs, s=aut](auto&& e)
                  {ao &= bdd_ithvar(s->register_ap(e)); });
    // todo Some additional checks?
    //return aut_to_aiger(a, all_outputs, mode);
    return auts_to_aiger({{aut, all_outputs}}, mode);
  }

  // Note: This ignores the named property
  aig_ptr
  strategies_to_aig(const std::vector<twa_graph_ptr>& strat_vec, const char *mode,
                    const std::set<std::string>& ins,
                    const std::vector<std::set<std::string>>& outs)
  {
    if (strat_vec.size() != outs.size())
      throw std::runtime_error("Expected as many outs as strategies!\n");

    std::for_each(strat_vec.begin()+1, strat_vec.end(),
                  [usedbdd = strat_vec.at(0)->get_dict()](auto&& it)
                  {
                    if (usedbdd != it->get_dict())
                      throw std::runtime_error("All strategies have to "
                                               "share a bdd_dict!\n");
                  });

    std::vector<std::pair<const_twa_graph_ptr, bdd>> new_vec;
    new_vec.reserve(strat_vec.size());

    std::set<std::string> seen_ap = ins;
    for (size_t i = 0; i < strat_vec.size(); ++i)
      {
        // Make sure ins and former outs are disjoint
        {
          bool inserted;
          for (auto&& aout : outs[i])
            {
              std::tie(std::ignore, inserted) = seen_ap.insert(aout);
              if (not inserted)
                throw std::runtime_error("The ap " + aout + " appears either "
                                         " in \"ins\" or is shared between "
                                         "multiple strategies as \"outs\".\n");
            }
        }
        // Register all to make sure they exist in the aut
        std::for_each(ins.begin(), ins.end(),
                      [s=strat_vec[i]](auto&& e){s->register_ap(e); });
        bdd this_outputs = bddtrue;
        std::for_each(outs[i].begin(), outs[i].end(),
                      [&to = this_outputs, s=strat_vec[i]](auto&& e)
                      {to &= bdd_ithvar(s->register_ap(e)); });
        if (this_outputs == bddfalse)
          throw std::runtime_error("Inconsistency in outputs of strat "
                                   + std::to_string(i) + ".\n");
        // todo Some additional checks?
        new_vec.emplace_back(strat_vec[i], this_outputs);
      }
    return auts_to_aiger(new_vec, mode);
  }

  // TODO: Le mode n'a rien à faire là
  std::ostream &
  print_aiger(std::ostream &os, const_aig_ptr circuit, const char* mode)
  {

    if (not circuit)
      return os; //Print nothing in case of nullptr

    std::vector<std::string> in_names(circuit->input_names().begin(),
                                      circuit->input_names().end());
    std::vector<std::string> out_names(circuit->output_names().begin(),
                                       circuit->output_names().end());
    auto n_inputs = circuit->num_inputs();
    auto n_outputs = circuit->num_outputs();
    auto n_latches = circuit->num_latches();
    auto gates = circuit->gates();

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
      for (auto &g : gates)
        if ((g.first != 0) && (g.second != 0))
          ++n_gates;
      // Note max_var_ is now an upper bound
      os << "aag " << circuit->max_var() / 2
          << ' ' << n_inputs
          << ' ' << n_latches
          << ' ' << n_outputs
          << ' ' << n_gates << '\n';
      for (unsigned i = 0; i < n_inputs; ++i)
        os << (1 + i) * 2 << '\n';
      for (unsigned i = 0; i < n_latches; ++i)
        os << (1 + n_inputs + i) * 2
           << ' ' << circuit->next_latches()[i] << '\n';
      for (unsigned i = 0; i < n_outputs; ++i)
        os << circuit->outputs()[i] << '\n';
      for (unsigned i = 0; i < n_gates; ++i)
        if ((gates[i].first != 0)
            && (gates[i].second != 0))
          write_gate(circuit->gate_var(i),
                     gates[i].first,
                     gates[i].second);
      for (unsigned i = 0; i < n_inputs; ++i)
        os << 'i' << i << ' ' << in_names[i] << '\n';
      for (unsigned i = 0; i < n_outputs; ++i)
        os << 'o' << i << ' ' << out_names[i] << '\n';
    }
    else
      throw std::runtime_error
          ("print_aiger(): mode must be \"dot\" or \"circuit\"");
    return os;
  }
}
