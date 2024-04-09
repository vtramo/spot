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

#include "config.h"
#include <spot/twaalgos/relabel.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/tl/formula.hh>
#include <spot/misc/partitioned_relabel.hh>

#include <cmath>
#include <algorithm>
#include <iostream>
#include <deque>
#include <optional>


namespace spot
{
  namespace
  {
    relabeling_map
    partitioned_relabel_here_(const twa_graph_ptr& autp, bool split,
                              unsigned max_letter,
                              unsigned max_letter_mult,
                              const bdd& concerned_ap,
                              bool treat_all,
                              const std::string& var_prefix,
                              bool sort)
    {
      if (!autp)
        throw std::runtime_error("partitioned_relabel_here_(): given aut "
                                 "is null.");
      auto abandon = []()
        {
          return relabeling_map{};
        };

      auto& aut = *autp;

      // Get all concerned conditions present in the automaton
      std::set<bdd, bdd_less_than> all_cond_conc; // Most efficient?
      bdd ignoredcon = bddtrue;

      // Map for all supports
      // and whether or not they are to be relabeled
      std::unordered_map<bdd, std::pair<bool, bdd>, bdd_hash> all_supports;

      for (const auto& e : aut.edges())
        {
          auto it = all_supports.find(e.cond);
          if (it != all_supports.end())
            continue; // Already treated
          bdd se = bddtrue;
          bool is_concerned = true;
          if (!treat_all)
            {
              se = bdd_support(e.cond);
              is_concerned = bdd_implies(concerned_ap, se);
            }

          all_supports.emplace(e.cond,
                               std::make_pair(is_concerned, se));

          if (!is_concerned)
            {
              assert(bdd_existcomp(se, concerned_ap) == bddtrue
                     && "APs are not partitioned");
              continue;
            }

          all_cond_conc.insert(e.cond);
        }

      // try_partition_me expects a vector
      auto all_cond = std::vector<bdd>(all_cond_conc.size());
      std::copy(all_cond_conc.begin(), all_cond_conc.end(), all_cond.begin());


      unsigned stop = max_letter;
      if (max_letter_mult != -1u)
        {
          // Make sure it does not overflow
          if (max_letter_mult <= (-1u / ((unsigned) all_cond.size())))
            stop = std::min(stop,
                            (unsigned) (max_letter_mult*all_cond.size()));
        }

      // Get the concerned propositions as formula
      std::vector<formula> concerned_ap_formula;
      if (treat_all)
        concerned_ap_formula = aut.ap();
      else
        {
          for (const auto& ap : aut.ap())
            {
              bdd ap_prop = bdd_ithvar(aut.register_ap(ap));
              if (bdd_implies(concerned_ap, ap_prop))
                concerned_ap_formula.push_back(ap);
            }
        }
      auto this_partition
          = try_partition_me(aut.get_dict(), all_cond,
                             concerned_ap_formula, stop);

      if (this_partition.is_empty())
        return abandon();

      // Compute the new letters
      this_partition.lock(var_prefix, sort);

      this_partition.relabel_edges_here(autp, split);

      return this_partition.to_relabeling_map(true);
    }

    void
    relabel_here_ap_(const twa_graph_ptr& aut_ptr, relabeling_map relmap)
    {
      assert(aut_ptr);
      twa_graph& aut = *aut_ptr;

      std::unique_ptr<bddPair> pairs(bdd_newpair());
      auto d = aut.get_dict();
      std::vector<int> vars;
      std::set<int> newvars;
      vars.reserve(relmap.size());
      bool bool_subst = false;
      auto aplist = aut.ap();

      for (auto& p: relmap)
        {
          // Don't attempt to rename APs that are not used.
          if (std::find(aplist.begin(), aplist.end(), p.first) == aplist.end())
            continue;

          int oldv = aut.register_ap(p.first);
          vars.emplace_back(oldv);
          if (p.second.is(op::ap))
            {
              int newv = aut.register_ap(p.second);
              newvars.insert(newv);
              bdd_setpair(pairs.get(), oldv, newv);
            }
          else
            {
              p.second.traverse([&](const formula& f)
                                {
                                  if (f.is(op::ap))
                                    newvars.insert(aut.register_ap(f));
                                  return false;
                                });
              bdd newb = formula_to_bdd(p.second, d, aut_ptr);
              bdd_setbddpair(pairs.get(), oldv, newb);
              bool_subst = true;
            }
      }

    bool need_cleanup = false;
    typedef bdd (*op_t)(const bdd&, bddPair*);
    op_t op = bool_subst ?
      static_cast<op_t>(bdd_veccompose) : static_cast<op_t>(bdd_replace);
    for (auto& t: aut.edges())
      {
        bdd c = (*op)(t.cond, pairs.get());
        t.cond = c;
        if (c == bddfalse)
          need_cleanup = true;
      }

    // Erase all the old variables that are not reused in the new set.
    // (E.g., if we relabel a&p0 into p0&p1 we should not unregister
    // p0)
    for (auto v: vars)
      if (newvars.find(v) == newvars.end())
        aut.unregister_ap(v);

    // If some of the edges were relabeled false, we need to clean the
    // automaton.
    if (need_cleanup)
      {
        aut.merge_edges();     // remove any edge labeled by 0
        aut.purge_dead_states(); // remove useless states
      }
    }

  void
  relabel_here_gen_(const twa_graph_ptr& aut_ptr, relabeling_map relmap)
    {
      assert(aut_ptr);
      twa_graph& aut = *aut_ptr;
      // PSC why
      //auto form2bdd = [d = aut.get_dict(), me = aut_ptr](const formula& f)
      auto form2bdd = [d = aut.get_dict()](const formula& f)
        {
          return formula_to_bdd(f, d, d);
        };

      auto bdd2form = [bdddict = aut.get_dict()](const bdd& cond)
        {
          return bdd_to_formula(cond, bdddict);
        };


      // translate formula -> bdd
      std::unordered_map<bdd, bdd, bdd_hash> base_letters;
      base_letters.reserve(relmap.size());

      std::unordered_map<bdd, bdd, bdd_hash> comp_letters;
      std::unordered_set<bdd, bdd_hash> ignored_letters;

      // Necessary to detect unused
      bdd new_var_supp = bddtrue;
      bdd old_var_supp = bddtrue; // PSC why do I need this

      auto translate = [&](bdd& cond)
        {
          // Check if known
          for (const auto& map : {base_letters, comp_letters})
            {
              auto it = map.find(cond);
              if (it != map.end())
                {
                  cond = it->second;
                  return;
                }
            }

          // Check if known to be ignored
          if (auto it = ignored_letters.find(cond);
                it != ignored_letters.end())
            return;

          // Check if ignored
          bdd cond_supp = bdd_support(cond);
          if (!bdd_implies(new_var_supp, cond_supp))
            {
              ignored_letters.insert(cond);
              assert(bdd_existcomp(cond_supp, new_var_supp) == bddtrue
                     && "APs are not partitioned");
              return;
            }

          // Compute
          // compose the given cond from a disjunction of base_letters
          bdd old_cond = bddfalse;
          for (const auto& [k, v] : base_letters)
            {
              if (bdd_implies(k, cond))
                old_cond |= v;
            }
          comp_letters[cond] = old_cond;
          cond = old_cond;
          return;
        };

      for (const auto& [new_f, old_f] : relmap)
        {
          bdd new_cond = form2bdd(new_f);
          new_var_supp &= bdd_support(new_cond);
          bdd old_cond = form2bdd(old_f);
          old_var_supp &= bdd_support(old_cond);
          base_letters[new_cond] = old_cond;
        }

      // Make sure that the old_var_supp exist in the automaton
      {
      formula old_var_supp_form = bdd2form(old_var_supp);
      for (const auto& ap_f : old_var_supp_form)
        aut.register_ap(ap_f);
      }

      // Save the composed letters? With a special seperator like T/F?
      // Is swapping between formula <-> bdd expensive
      for (auto& e : aut.edges())
        translate(e.cond);

      // Remove the new auxilliary variables from the aut
      bdd c_supp = new_var_supp;
      while (c_supp != bddtrue)
        {
          aut.unregister_ap(bdd_var(c_supp));
          c_supp = bdd_high(c_supp);
        }

      return;
    }

  } // Namespace

  void
  relabel_here(const twa_graph_ptr& aut, relabeling_map* relmap)
  {
    if (!relmap || relmap->empty())
      return;

    // There are two different types of relabeling maps:
    // 1) The "traditional":
    // New atomic propositions (keys) correspond to general formulas over
    // the original propositions (values)
    // 2) The one resulting from partitioned_relabel_here
    // Here general (boolean) formulas over new propositions (keys)
    // are associated to general formulas over
    // the original propositions (values)

    if (!std::all_of(relmap->begin(), relmap->end(),
                    [](const auto& it){return it.first.is_boolean()
                                              && it.second.is_boolean(); }))
      throw std::runtime_error
            ("relabel_here: old labels and new labels "
             "should be Boolean formulas");

    bool only_ap = std::all_of(relmap->cbegin(), relmap->cend(),
                               [](const auto& p)
                                 {
                                   return p.first.is(op::ap);
                                 });

    if (only_ap)
      relabel_here_ap_(aut, *relmap);
    else
      relabel_here_gen_(aut, *relmap);
  }

  relabeling_map
  partitioned_relabel_here(const twa_graph_ptr& aut,
                           bool split,
                           unsigned max_letter,
                           unsigned max_letter_mult,
                           const bdd& concerned_ap,
                           std::string var_prefix,
                           bool sort)
  {
    if (!aut)
      throw std::runtime_error("aut is null!");

    if (std::find_if(aut->ap().cbegin(), aut->ap().cend(),
                     [var_prefix](const auto& ap)
                      {
                        return ap.ap_name().find(var_prefix) == 0;
                      }) != aut->ap().cend())
      throw std::runtime_error("partitioned_relabel_here(): "
          "The given prefix for new variables may not appear as "
          "a prefix of existing variables.");

    // If concerned_ap == bddtrue -> all aps are concerned
    bool treat_all = (concerned_ap == bddtrue)
                     || (concerned_ap == aut->ap_vars());
    bdd concerned_ap_
      = treat_all ? aut->ap_vars() : concerned_ap;
    // Automata can become "pseudo-nondeterministic" if not all
    // variables are used for relabeling
    if (!treat_all)
      aut->prop_universal(trival()); // May remain deterministic

    return partitioned_relabel_here_(aut, split,
                                     max_letter, max_letter_mult,
                                     concerned_ap_,
                                     treat_all,
                                     var_prefix,
                                     sort);
  }
}
