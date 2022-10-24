// -*- coding: utf-8 -*-
// Copyright (C) 2015-2018, 2020 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
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

#include <cmath>
#include <algorithm>
#include <iostream>


namespace spot
{
  namespace
  {
    struct bdd_partition
    {
      struct S
      {
        bdd new_label = bddfalse;
      };
      struct T
      {
      };
      using implication_graph = digraph<S, T>;

      // A pointer to the conditions to be partitioned
      const std::vector<bdd>* all_cond_ptr;
      // Graph with the invariant that
      // children imply parents
      // Leaves from the partition
      // original conditions are "root" nodes
      std::unique_ptr<implication_graph> ig;
      // todo: technically there are at most two successors, so a graph
      // is "too" generic
      // All conditions currently part of the partition
      // unsigned corresponds to the associated node
      std::vector<std::pair<bdd, unsigned>> treated;
      std::vector<formula> new_aps;
      bool relabel_succ = false;

      bdd_partition() = default;
      bdd_partition(const std::vector<bdd>& all_cond)
        : all_cond_ptr(&all_cond)
        , ig{std::make_unique<implication_graph>(2*all_cond.size(),
                                                 2*all_cond.size())}
      {
        // Create the roots of all old conditions
        // Each condition is associated to the state with
        // the same index
        const unsigned Norig = all_cond.size();
        ig->new_states(Norig);
      }

      // Facilitate conversion
      // This can only be called when letters have already
      // been computed
      operator partition_relabel_dict() const
      {
        partition_relabel_dict::l_map orig_letters;
        partition_relabel_dict::l_map computed_conditions;

        orig_letters.reserve(treated.size());
        for (const auto& [old_letter, s] : treated)
          orig_letters[ig->state_storage(s).new_label] = old_letter;

        if (ig->state_storage(0).new_label != bddfalse)
          {
            // split option was false, so we can store further info
            auto& all_cond = *all_cond_ptr;
            const unsigned Norig = all_cond.size();
            computed_conditions.reserve(Norig);

            for (unsigned i = 0; i < Norig; ++i)
              computed_conditions[ig->state_storage(i).new_label]
                = all_cond[i];
          }
        return partition_relabel_dict{new_aps,
                                      std::move(orig_letters),
                                      std::move(computed_conditions)};
      }
    };

    bdd_partition
    try_partition_me(const std::vector<bdd>& all_cond, unsigned max_letter)
    {
      // We create vector that will be succesively filled.
      // Each entry corresponds to a "letter", of the partition
      const size_t Norig = all_cond.size();

      bdd_partition result(all_cond);

      auto& treated = result.treated;
      auto& ig = *result.ig;

      for (unsigned io = 0; io < Norig; ++io)
        {
          bdd cond = all_cond[io];
          const auto Nt = treated.size();
          for (size_t in = 0; in < Nt; ++in)
            {
              if (cond == bddfalse)
                break;
              if (treated[in].first == cond)
                {
                  // Found this very condition -> make transition
                  ig.new_edge(io, treated[in].second);
                  cond = bddfalse;
                  break;
                }
              if (bdd_have_common_assignment(treated[in].first, cond))
                {
                  bdd inter = treated[in].first & cond;
                  // Create two new states
                  unsigned ssplit = ig.new_states(2);
                  // ssplit becomes the state without the intersection
                  // ssplit + 1 becomes the intersection
                  // Both of them are implied by the original node,
                  // Only inter is implied by the current letter
                  ig.new_edge(treated[in].second, ssplit);
                  ig.new_edge(treated[in].second, ssplit+1);
                  ig.new_edge(io, ssplit+1);
                  treated.emplace_back(inter, ssplit+1);
                  // Update
                  cond -= inter;
                  treated[in].first -= inter;
                  treated[in].second = ssplit;
                  if (treated.size() > max_letter)
                    return bdd_partition{};
                }
            }
            if (cond != bddfalse)
              {
                unsigned sc = ig.new_state();
                treated.emplace_back(cond, sc);
                ig.new_edge(io, sc);
              }
        }

      result.relabel_succ = true;
      return result;
    }

    void
    comp_new_letters(bdd_partition& part,
                    twa_graph& aut,
                    const std::string& var_prefix,
                    bool split)
    {
      auto& ig = *part.ig;
      const auto& treated = part.treated;
      auto& new_aps = part.new_aps;
      // Get the new variables and their negations
      const unsigned Nnl = treated.size();
      const unsigned Nnv = std::ceil(std::log2(Nnl));
      std::vector<std::array<bdd, 2>> Nv_vec(Nnv);

      new_aps.reserve(Nnv);
      for (unsigned i = 0; i < Nnv; ++i)
        {
          // todo check if it does not exist / use anonymous?
          new_aps.push_back(formula::ap(var_prefix+std::to_string(i)));
          int v = aut.register_ap(new_aps.back());
          Nv_vec[i] = {bdd_nithvar(v), bdd_ithvar(v)};
        }

      auto leaveidx2label = [&](unsigned idx)
        {
          unsigned c = 0;
          unsigned rem = idx;
          bdd thisbdd = bddtrue;
          while (rem)
            {
              thisbdd &= Nv_vec[c][rem & 1];
              ++c;
              rem >>= 1;
            }
          for (; c < Nnv; ++c)
            thisbdd &= Nv_vec[c][0];
          return thisbdd;
        };

      // Compute only labels of leaves
      for (unsigned idx = 0; idx < Nnl; ++idx)
        ig.state_storage(treated[idx].second).new_label = leaveidx2label(idx);

      // We will label the implication graph with the new letters
      auto relabel_impl = [&](unsigned s, auto&& relabel_impl_rec)
        {
          auto& ss = ig.state_storage(s);
          if (ss.new_label != bddfalse)
            return ss.new_label;
          else
            {
              assert((ss.succ != 0) && "Should not be a leave");
              bdd thisbdd = bddfalse;
              for (const auto& e : ig.out(s))
                thisbdd |= relabel_impl_rec(e.dst, relabel_impl_rec);
              ss.new_label = thisbdd;
              return thisbdd;
            }
        };

      if (!split)
        {
          // For split only leaves is ok,
          // disjunction is done via transitions
          // This will compute the new_label for all states in the ig
          const unsigned Norig = part.all_cond_ptr->size();
          for (unsigned i = 0; i < Norig; ++i)
            relabel_impl(i, relabel_impl);
        }
    } // comp_new_letters
  } // Namespace


  void
  relabel_here(twa_graph_ptr& aut, relabeling_map* relmap)
  {
    bddPair* pairs = bdd_newpair();
    auto d = aut->get_dict();
    std::vector<int> vars;
    std::set<int> newvars;
    vars.reserve(relmap->size());
    bool bool_subst = false;
    auto aplist = aut->ap();

    for (auto& p: *relmap)
      {
        if (!p.first.is(op::ap))
          throw std::runtime_error
            ("relabel_here: old labels should be atomic propositions");
        if (!p.second.is_boolean())
          throw std::runtime_error
            ("relabel_here: new labels should be Boolean formulas");

        // Don't attempt to rename APs that are not used.
        if (std::find(aplist.begin(), aplist.end(), p.first) == aplist.end())
          continue;

        int oldv = aut->register_ap(p.first);
        vars.emplace_back(oldv);
        if (p.second.is(op::ap))
          {
            int newv = aut->register_ap(p.second);
            newvars.insert(newv);
            bdd_setpair(pairs, oldv, newv);
          }
        else
          {
            p.second.traverse([&](const formula& f)
                              {
                                if (f.is(op::ap))
                                  newvars.insert(aut->register_ap(f));
                                return false;
                              });
            bdd newb = formula_to_bdd(p.second, d, aut);
            bdd_setbddpair(pairs, oldv, newb);
            bool_subst = true;
          }
      }

    bool need_cleanup = false;
    typedef bdd (*op_t)(const bdd&, bddPair*);
    op_t op = bool_subst ?
      static_cast<op_t>(bdd_veccompose) : static_cast<op_t>(bdd_replace);
    for (auto& t: aut->edges())
      {
        bdd c = (*op)(t.cond, pairs);
        t.cond = c;
        if (c == bddfalse)
          need_cleanup = true;
      }

    // Erase all the old variables that are not reused in the new set.
    // (E.g., if we relabel a&p0 into p0&p1 we should not unregister
    // p0)
    for (auto v: vars)
      if (newvars.find(v) == newvars.end())
        aut->unregister_ap(v);

    // If some of the edges were relabeled false, we need to clean the
    // automaton.
    if (need_cleanup)
      {
        aut->merge_edges();     // remove any edge labeled by 0
        aut->purge_dead_states(); // remove useless states
      }
  }

  bdd partition_relabel_dict::compute_(const bdd& new_cond)
  {
    // todo test if new_cond is a disjunction of new_letters?
    // Otherwise this is incorrect
    bdd old_cond = bddfalse;
    for (const auto& [k,v] : orig_letters_)
      {
        if (bdd_implies(k, new_cond))
          old_cond |= v;
        else
          assert(!bdd_have_common_assignment(new_cond, k)
                 && "Either k implies new_cond or disjoint."
                    " Otherwise its not part of the partition");
      }
    if (store_results_)
      computed_conditions_[new_cond] = old_cond;
    return old_cond;
  }

  // todo swig and std::optional?
  partition_relabel_dict
  try_partitioned_relabel_here(twa_graph_ptr& aut,
                               bool split,
                               unsigned max_letter,
                               unsigned max_letter_mult,
                               std::function<bool(unsigned)> select_states,
                               std::string var_prefix)
  {
    auto abandon = []()
      {
        return partition_relabel_dict();
      };


    // When split we need to distiguish effectively new and old edges
    if (split)
      {
        aut->get_graph().remove_dead_edges_();
        aut->get_graph().sort_edges_();
        aut->get_graph().chain_edges_();
      }

    // Get all conditions present in the automaton
    std::vector<bdd> all_cond;
    bdd ignoredcon = bddtrue;
    std::unordered_map<int, unsigned> all_cond_id2idx;

    all_cond.reserve(0.1*aut->num_edges());
    all_cond_id2idx.reserve(all_cond.size());

    for (const auto& e : aut->edges())
      if (!select_states || select_states(e.src))
        {
          auto [_, ins] =
              all_cond_id2idx.try_emplace(e.cond.id(), all_cond.size());
          if (ins)
            {
              all_cond.push_back(e.cond);
              if (all_cond.size() > max_letter)
                return abandon();
            }
        }
      else
        ignoredcon &= bdd_support(e.cond);

    const unsigned stop =
        std::min(max_letter,
                 (unsigned) (max_letter_mult*all_cond.size()));

    auto this_partition = try_partition_me(all_cond, stop);

    if (!this_partition.relabel_succ)
      return abandon();

    comp_new_letters(this_partition, *aut, var_prefix, split);

    // A original condition is represented by all leaves that imply it
    auto& ig = *this_partition.ig;
    const unsigned Ns = aut->num_states();
    const unsigned Nt = aut->num_edges();
    for (unsigned s = 0; s < Ns; ++s)
      {
        if (select_states && !select_states(s))
            continue;
        for (auto& e : aut->out(s))
          {
            if (aut->edge_number(e) > Nt)
              continue;
            unsigned idx = all_cond_id2idx[e.cond.id()];

            if (split)
              {
                auto replace_label =
                  [&aut, &ig, &econd = e.cond,
                  esrc=e.src, edst=e.dst](unsigned si,
                                          auto&& replace_label_)->void
                  {

                    auto sstore = ig.state_storage(si);
                    if (sstore.succ == 0)
                      {
                        if (econd == bddfalse)
                          econd = sstore.new_label;
                        else
                          aut->new_edge(esrc, edst, sstore.new_label);
                      }
                    else
                      {
                        for (const auto& e_ig : ig.out(si))
                          replace_label_(e_ig.dst, replace_label_);
                      }
                  };

                // initial call
                e.cond = bddfalse;
                replace_label(idx, replace_label);
              }
            else
              e.cond = ig.state_storage(idx).new_label;
          } // for edge
      } // for state
    return this_partition;
  }
}
