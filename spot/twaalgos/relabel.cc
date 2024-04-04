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

    // Recursive traversal of implication graph
    void
    replace_label_(unsigned si,
                   unsigned esrc, unsigned edst,
                   const acc_cond::mark_t& m,
                   bdd& econd,
                   const bdd_partition::implication_graph& ig,
                   twa_graph& aut)
    {
      auto& sstore = ig.state_storage(si);
      if (sstore.succ == 0)
        {
          if (econd == bddfalse)
            econd = sstore.new_label;
          else
            aut.new_edge(esrc, edst, sstore.new_label, m);
        }
      else
        {
          for (const auto& e_ig : ig.out(si))
            replace_label_(e_ig.dst, esrc, edst, m, econd, ig, aut);
        }
    }

    void
    relabel_no_split_(twa_graph& aut,
                      const unsigned Nt,
                      const std::unordered_map<bdd,
                                               unsigned,
                                              bdd_hash>& orig_cond,
                      const bdd_partition::implication_graph& ig)
    {
      for (auto& e : aut.edges())
        {
          unsigned ne = aut.edge_number(e);
          if (ne > Nt)
            break; // New edge -> edges are traversed in order
          if (auto itc = orig_cond.find(e.cond);
              itc != orig_cond.end())
              e.cond = ig.state_storage(itc->second).new_label;
          // else: skipped condition
        }
    }

    void
    relabel_split_no_sort_(twa_graph& aut,
                           const unsigned Nt,
                           const bdd_partition& bdd_part)
    {
      auto& ig = bdd_part.get_graph();
      auto& orig_cond = bdd_part.orig_conditions();

      for (auto& e : aut.edges())
        {
          unsigned ne = aut.edge_number(e);
          if (ne > Nt)
            break; // New edge -> edges are traversed in order
          if (orig_cond.count(e.cond))
            {
              // initial call
              // We can not hold a ref to the edge
              // as the edgevector might get reallocated
              bdd econd = bddfalse;
              replace_label_(itc->second, e.src, e.dst, e.acc,
                              econd, ig, aut);
              aut.edge_storage(ne).cond = econd;
            }
          // else: skipped condition
        }
    }

    struct edge_repl_
    {
      using e_it = bdd_partition::implication_graph::const_iterator;
      std::optional<e_it> it_;
      unsigned ost_;

      unsigned dst_;
      acc_cond::mark_t acc_;

      edge_repl_(const e_it& it,
                 unsigned dst,
                 acc_cond::mark_t acc) noexcept
        : it_(it)
        , ost_{-1u}
        , dst_{dst}
        , acc_{acc}
      {
      }
      edge_repl_(unsigned ostate,
                 unsigned dst,
                 acc_cond::mark_t acc) noexcept
        : it_{}
        , ost_{ostate}
        , dst_{dst}
        , acc_{acc}
      {
      }

      edge_repl_&
      operator++() noexcept
      {
        if (it_)
          ++(*it_);
        else
          ost_ = -1u;
        return *this;
      }

      unsigned
      ostate() const
      {
        assert(*this);
        if (it_)
          return (*it_)->dst;
        else
          return ost_;
      }

      operator bool() const noexcept
      {
        if (it_)
          return (bool) (*it_);
        else
          return ost_ != -1u;
      }

      unsigned
      dst() const noexcept
      {
        return dst_;
      }

      acc_cond::mark_t
      acc() const noexcept
      {
        return acc_;
      }
    };

    void
    relabel_split_sort_(twa_graph& aut,
                        const std::unordered_map<bdd,
                                                unsigned,
                                                bdd_hash>& orig_cond,
                        const bdd_partition::implication_graph& ig)
    {

      auto edge_it = std::vector<edge_repl_>();

      auto repl_edge = std::deque<unsigned>();
      auto used = std::vector<unsigned>();

      auto cmp = [](const auto& cl, const auto& cr)
        {
          return bdd_stable_cmp(cl, cr);
        };

      auto gc = [&ig](unsigned s)
        {
          return ig.state_storage(s).new_label;
        };

      for (unsigned s = 0; s < aut.num_states(); ++s)
        {
          assert(edge_it.empty() && repl_edge.empty());
          // Get all concerned edges of this state
          for (const auto& e: aut.out(s))
            {
              if (auto itc = orig_cond.find(e.cond);
                  itc != orig_cond.end())
                {
                  repl_edge.push_back(aut.edge_number(e));
                  unsigned ostate = itc->second;
                  if (ig.state_storage(ostate).succ == 0)
                    edge_it.emplace_back(ostate,
                                         e.dst,
                                         e.acc);
                  else
                    edge_it.emplace_back(ig.out(ostate).begin(),
                                         e.dst,
                                         e.acc);
                }
            }
          // Now replace them
          while (!edge_it.empty())
            {
              assert(std::all_of(edge_it.cbegin(), edge_it.cend(),
                  [](const auto& er) -> bool {return er; }));
              unsigned c_idx = 0;
              unsigned m_idx = edge_it.size();
              bdd smallest = gc(edge_it[0].ostate());
              used.clear();
              used.push_back(c_idx);
              ++c_idx;
              for (; c_idx < m_idx; ++c_idx)
                {
                  const bdd& dst_cond = gc(edge_it[c_idx].ostate());
                  auto res = cmp(dst_cond, smallest);
                  if (res > 0)
                    continue; // Larger -> ignored
                  else if (res == 0)
                    used.push_back(c_idx); // Same -> use as well
                  else
                    {
                      // Smaller -> use this and ignore other
                      smallest = dst_cond;
                      used.clear();
                      used.push_back(c_idx);
                    }
                }

              // Replace and advance
              for (auto u_idx : used)
                {
                  if (repl_edge.empty())
                    // Create the new edge
                    aut.new_edge(s, edge_it[u_idx].dst(),
                                 gc(edge_it[u_idx].ostate()),
                                 edge_it[u_idx].acc());
                  else
                    {
                      unsigned eidx = repl_edge.front();
                      repl_edge.pop_front();
                      auto& e = aut.edge_storage(eidx);
                      e.dst = edge_it[u_idx].dst();
                      e.cond = gc(edge_it[u_idx].ostate());
                      e.acc = edge_it[u_idx].acc();
                    }
                  ++edge_it[u_idx];
                }
              // Check if done with some of the edge_it
              for (auto uit = used.crbegin(); uit != used.crend(); ++uit)
                {
                  if (!edge_it[*uit])
                    {
                      if (edge_it.size() >= 2)
                        edge_it[*uit] = edge_it.back();
                      edge_it.pop_back();
                    }
                }
            }
        }
    }

    relabeling_map
    partitioned_relabel_here_(twa_graph& aut, bool split,
                              unsigned max_letter,
                              unsigned max_letter_mult,
                              const bdd& concerned_ap,
                              bool treat_all,
                              const std::string& var_prefix,
                              bool sort)
    {
      auto abandon = []()
        {
          return relabeling_map{};
        };

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

      // Unregister old aps and register new ones
      for (const auto& ap : concerned_ap_formula)
        aut.unregister_ap(aut.register_ap(ap));
      // Register new ones
      for (const auto& ap : this_partition.new_ap())
        aut.register_ap(ap);

      // An original condition is represented by either
      // The new label: split == false
      // The disjunction over all leaves implying it
      // In this case a new edge is created for each leave
      const auto& ig = this_partition.get_graph();
      // Edges are only appended, never reused
      const unsigned Nt = aut.edge_vector().size();

      // Loop over all edges, check if the condition appears
      // in orig_conditions, if so it needs
      // to be replaced, skipped otherwise
      const auto& orig_conditions = this_partition.orig_conditions();
      if (split)
        {
          if (sort)
            relabel_split_sort_(aut, orig_conditions, ig);
          else
            relabel_split_no_sort_(aut, Nt, orig_conditions, ig);
        }
      else
        relabel_no_split_(aut, Nt, orig_conditions, ig);

      return this_partition.to_relabeling_map(true);
    }

    void
    relabel_here_ap_(twa_graph_ptr& aut_ptr, relabeling_map relmap)
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
  relabel_here_gen_(twa_graph_ptr& aut_ptr, relabeling_map relmap)
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
  relabel_here(twa_graph_ptr& aut, relabeling_map* relmap)
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
  partitioned_relabel_here(twa_graph_ptr& aut,
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

    return partitioned_relabel_here_(*aut, split,
                                     max_letter, max_letter_mult,
                                     concerned_ap_,
                                     treat_all,
                                     var_prefix,
                                     sort);
  }
}
