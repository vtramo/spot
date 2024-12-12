// -*- coding: utf-8 -*-
// Copyright (C) by the Spot authors, see the AUTHORS file for details.
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

#pragma once

#include <spot/twa/twagraph.hh>
#include <spot/misc/bddlt.hh>

namespace spot
{

  class SPOT_API ltlf_translator
  {
  public:
    ltlf_translator(const bdd_dict_ptr& dict);

    bdd ltlf_to_mtbdd(formula f);
    std::pair<formula, bool>  leaf_to_formula(int t) const;

    formula terminal_to_formula(int t) const;
    int formula_to_terminal(formula f, bool may_stop = false);
    bdd formula_to_terminal_bdd(formula f, bool may_stop = false);

    bdd combine_and(bdd left, bdd right);
    bdd combine_or(bdd left, bdd right);

    bdd combine_implies(bdd left, bdd right);
    bdd combine_equiv(bdd left, bdd right);
    bdd combine_xor(bdd left, bdd right);
    bdd combine_not(bdd b);

    formula propeq_representative(formula f);

    bddExtCache* get_cache()
    {
      return &cache_;
    }

    ~ltlf_translator();
  private:
    std::unordered_map<formula, int> formula_to_var_;
    std::unordered_map<bdd, formula, bdd_hash> propositional_equiv_;

    std::unordered_map<formula, bdd> formula_to_bdd_;
    std::unordered_map<formula, int> formula_to_terminal_;
    std::vector<formula> terminal_to_formula_;
    bdd_dict_ptr dict_;
    bddExtCache cache_;
  };


  struct SPOT_API mtdfa
  {
  public:
    mtdfa(const bdd_dict_ptr& dict)
      : dict_(dict)
     {
     }

    ~mtdfa()
    {
      dict_->unregister_all_my_variables(this);
    }

    std::vector<bdd> states;
    std::vector<formula> names;
    bdd_dict_ptr dict_;

    unsigned num_roots() const
    {
      return states.size();
    }

    unsigned num_states() const
    {
      bool has_true = false;
      // FIXME: I'd like a BuDDy function that checks if a BDD node
      // can be reached from a given set of BDD nodes.  Returning just
      // a boolean will be more efficient than creating the array of
      // leaves.
      for (bdd b: leaves_of(states))
        if (b == bddtrue)
          {
            has_true = true;
            break;
          }
      return states.size() + has_true;
    }

    // FIXME: This assumes that all states are reachable, so
    // we just have to check if one terminal is accepting.
    bool is_empty() const
    {
      for (bdd b: leaves_of(states))
        {
          if (b == bddfalse)
            continue;
          if (b == bddtrue || (bdd_get_terminal(b) & 1))
            return false;
        }
      return true;
    }


    // Print the MTBDD.  If index >= 0, print only one state.
    std::ostream& print_dot(std::ostream& os,
                            int index = -1,
                            bool labels = true) const;

    // convert to twa
    twa_graph_ptr as_twa(bool state_based = false, bool labels = true) const;
};

  typedef std::shared_ptr<mtdfa> mtdfa_ptr;
  typedef std::shared_ptr<const mtdfa> const_mtdfa_ptr;

  SPOT_API mtdfa_ptr
  ltlf_to_mtdfa(formula f, const bdd_dict_ptr& dict,
                bool fuse_same_bdds = true);

  SPOT_API mtdfa_ptr minimize_mtdfa(const mtdfa_ptr& dfa);

  SPOT_API mtdfa_ptr product(const mtdfa_ptr& dfa1,
                             const mtdfa_ptr& dfa2);
  SPOT_API mtdfa_ptr product_or(const mtdfa_ptr& dfa1,
                                const mtdfa_ptr& dfa2);
  SPOT_API mtdfa_ptr product_xor(const mtdfa_ptr& dfa1,
                                 const mtdfa_ptr& dfa2);
  SPOT_API mtdfa_ptr product_xnor(const mtdfa_ptr& dfa1,
                                  const mtdfa_ptr& dfa2);
  SPOT_API mtdfa_ptr product_implies(const mtdfa_ptr& dfa1,
                                     const mtdfa_ptr& dfa2);

  SPOT_API mtdfa_ptr complement(const mtdfa_ptr& dfa);

  // Convert a TWA (representing a DFA) into an MTDFA.
  SPOT_API mtdfa_ptr twadfa_to_mtdfa(const twa_graph_ptr& twa);
}
