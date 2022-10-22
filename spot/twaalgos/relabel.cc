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
      using pou = std::array<unsigned, 2>;
      std::vector<bdd> treated;
      std::vector<pou> offsprings;
      std::vector<pou> offsprings_list;
      std::vector<formula> new_aps;
      bool relabel_succ = false;
    };

    bdd_partition
    try_partition_me(const std::vector<bdd>& all_cond, unsigned max_letter)
    {
      // We create vector that will be succesively filled.
      // Each entry corresponds to a "letter", of the partition
      bdd_partition result;

      const size_t Norig = all_cond.size();
      auto& treated = result.treated;
      treated.reserve(Norig);
      auto& offsprings = result.offsprings;
      offsprings = std::vector<bdd_partition::pou>(Norig, {-1u,-1u});
      auto& offsprings_list = result.offsprings_list;
      offsprings_list.reserve(Norig);

      auto add_idx = [&](unsigned old_cond_idx, unsigned letter_idx)
        {
          unsigned tail = offsprings[old_cond_idx][1];
          unsigned oIdx = offsprings_list.size();
          offsprings_list.push_back({letter_idx, -1u});
          if (tail == -1u)
            offsprings[old_cond_idx] = {oIdx, oIdx};
          else
            {
              offsprings_list[tail][1] = oIdx;
              offsprings[old_cond_idx][1] = oIdx;
            }
        };

      // Partition while keeping track who is an ancestor
      // Also change to handmade linked list?
      std::vector<std::pair<bdd, std::vector<unsigned>>> treated_inter;
      treated_inter.reserve(Norig);

      for (unsigned io = 0; io < Norig; ++io)
        {
          bdd cond = all_cond[io];
          const auto Nt = treated_inter.size();
          for (size_t in = 0; in < Nt; ++in)
            {
              if (cond == bddfalse)
                break;
              if (treated_inter[in].first == cond)
                {
                  // Found this very condition -> done
                  treated_inter[in].second.push_back(io);
                  cond = bddfalse;
                  break;
                }
              if (bdd_have_common_assignment(treated_inter[in].first, cond))
                {
                  bdd inter = treated_inter[in].first & cond;
                  treated_inter[in].first -= inter;
                  cond -= inter;
                  treated_inter.emplace_back(std::make_pair(
                                             inter,
                                             treated_inter[in].second));
                  treated_inter.back().second.push_back(io);
                  if (treated_inter.size() > max_letter)
                    return bdd_partition{};
                }
            }
            if (cond != bddfalse)
              treated_inter.emplace_back(std::make_pair(
                                         cond,
                                         std::vector<unsigned>{io}));
        }

      // Redistribute
      const size_t Nnc = treated_inter.size();
      treated.reserve(Nnc);
      for (size_t i = 0; i < Nnc; ++i)
        {
          std::cout << i << " : " << treated_inter[i].first << '\n';
          treated.push_back(treated_inter[i].first);
          for (auto o : treated_inter[i].second)
            add_idx(o, i);
        }
      result.relabel_succ = true;
      return result;
    }

    std::vector<bdd>
    comp_new_letters(bdd_partition& part,
                    twa_graph& aut,
                    const std::string& var_prefix)
    {
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

      std::vector<bdd> treated_newcond(treated.size());

      for (unsigned i = 0; i < Nnl; ++i)
        {
          unsigned c = 0;
          unsigned rem = i;
          bdd thisbdd = bddtrue;
          while (rem)
            {
              thisbdd &= Nv_vec[c][rem & 1];
              ++c;
              rem >>= 1;
            }
          for (; c < Nnv; ++c)
            thisbdd &= Nv_vec[c][0];
          treated_newcond[i] = thisbdd;
        }
      return treated_newcond;
    }
  }


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

  partition_relabel_dict::partition_relabel_dict(const std::vector<bdd>&
                                                    old_letters,
                                                 const std::vector<bdd>&
                                                    new_letters,
                                                  std::vector<formula>
                                                    new_aps)
    : relabel_succ_{true}
    , new_aps_(std::move(new_aps))
  {
    if (old_letters.size() != new_letters.size())
      throw std::runtime_error("Letters need to be bijective, "
                               "trivially non-verified");
    const auto N = old_letters.size();
    orig_letters_.reserve(N);
    for (size_t i = 0; i < N; ++i)
      orig_letters_[new_letters[i]] = old_letters[i];
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

    all_cond.reserve(0.1*aut->num_states());
    all_cond_id2idx.reserve(all_cond.size());

    for (const auto& e : aut->edges())
      if (!select_states || select_states(e.src))
        {
          auto [_, ins] =
              all_cond_id2idx.try_emplace(e.cond.id(), all_cond.size());
          if (ins)
            all_cond.push_back(e.cond);
        }
      else
        ignoredcon &= bdd_support(e.cond);

    if (all_cond.size() > max_letter)
      return abandon();

    const unsigned stop =
        std::min(max_letter,
                 (unsigned) (max_letter_mult*all_cond.size()));

    auto this_partition = try_partition_me(all_cond, stop);

    if (!this_partition.relabel_succ)
      return abandon();

    std::vector<bdd> new_letters =
      comp_new_letters(this_partition, *aut, var_prefix);

    //auto& treated = this_partition->treated;
    auto& offsprings = this_partition.offsprings;
    auto& offsprings_list = this_partition.offsprings_list;

    // Replace all treated transitions in the original automaton
    // with all offsprings in the new variables
    if (split)
      {
        // All edges are sorted, no dead edges etc
        const unsigned Neold = aut->num_edges();
        for (unsigned e_idx = 1; e_idx <= Neold; ++e_idx)
          {
            auto& e = aut->edge_storage(e_idx);

            unsigned idx = all_cond_id2idx[e.cond.id()];
            unsigned of_idx = offsprings[idx][0];
            e.cond = new_letters[offsprings_list[of_idx][0]];
            of_idx = offsprings_list[of_idx][1];
            while (of_idx != -1u)
              {
                unsigned of = offsprings_list[of_idx][0];
                aut->new_edge(e.src, e.dst,
                              new_letters.at(of), e.acc);
                of_idx = offsprings_list[of_idx][1];
              }
          }
        return partition_relabel_dict(this_partition.treated,
                                      new_letters, this_partition.new_aps);
      }
    else
      {
        const size_t Nc = all_cond.size();
        // Relabel edges by disjunctions over all offsprings
        auto resdict =
          partition_relabel_dict(this_partition.treated, new_letters,
                                 this_partition.new_aps);
        auto& cond_map_n2o = resdict.computed_conditions_;
        cond_map_n2o.reserve(Nc);

        // Translate all (old) conditions into new_ones
        std::vector<bdd> new_all_cond(Nc);
        for (size_t i = 0; i < Nc; ++i)
          {
            unsigned of_idx = offsprings[i][0];
            bdd new_cond = new_letters[offsprings_list[of_idx][0]];
            of_idx = offsprings_list[of_idx][1];
            while (of_idx != -1u)
              {
                unsigned of = offsprings_list[of_idx][0];
                new_cond |= new_letters[of];
                of_idx = offsprings_list[of_idx][1];
              }
            new_all_cond[i] = new_cond;
            cond_map_n2o[new_cond] = all_cond[i];
          }

        const unsigned Nstates = aut->num_states();
        for (unsigned n = 0; n < Nstates; ++n)
          {
            if (!select_states || select_states(n))
              for (auto& e : aut->out(n))
                e.cond = new_all_cond[all_cond_id2idx[e.cond.id()]];
          }
        return resdict;
      }
    SPOT_UNREACHABLE();
  }
}
