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

#include <spot/misc/bddlt.hh>
#include <spot/misc/hash.hh>
#include <spot/misc/timer.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/mealy_machine.hh>
#include <spot/twaalgos/sbacc.hh>
#include <spot/twaalgos/synthesis.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/twaalgos/zlktree.hh>
#include <spot/twaalgos/toparity.hh>
#include <spot/tl/parse.hh>
#include <algorithm>
#include <cassert>
#include <cmath>
#include <string>
#include <stack>
#include <variant>

#ifndef NDEBUG
#include <spot/twaalgos/hoa.hh>
#endif
// Helper function/structures for split_2step
namespace{
  using namespace spot;
  // Computes and stores the restriction
  // of each cond to the input domain and the support
  // This is useful as it avoids recomputation
  // and often many conditions are mapped to the same
  // restriction
  struct small_cacher_t
  {
    //e to e_in and support
    std::unordered_map<bdd, std::pair<bdd, bdd>, bdd_hash> cond_hash_;

    void fill(const const_twa_graph_ptr& aut, bdd output_bdd)
    {
      cond_hash_.reserve(aut->num_edges()/5+1);
      // 20% is about lowest number of different edge conditions
      // for benchmarks taken from syntcomp

      for (const auto& e : aut->edges())
        {
          // Check if stored
          if (cond_hash_.find(e.cond) != cond_hash_.end())
            continue;

          cond_hash_[e.cond] =
              std::pair<bdd, bdd>(
                  bdd_exist(e.cond, output_bdd),
                  bdd_exist(bdd_support(e.cond), output_bdd));
        }
    }

    // Get the condition restricted to input and support of a condition
    const std::pair<bdd, bdd>& operator[](const bdd& econd) const
    {
      return cond_hash_.at(econd);
    }
  };

  // Struct to locally store the information of all outgoing edges
  // of the state.
  struct e_info_t
  {
    e_info_t(const twa_graph::edge_storage_t& e,
             const small_cacher_t& sm)
        : dst(e.dst),
          econd(e.cond),
          einsup(sm[e.cond]),
          acc(e.acc)
    {
      pre_hash = (wang32_hash(dst)
                 ^ std::hash<acc_cond::mark_t>()(acc))
                 * fnv<size_t>::prime;
    }

    inline size_t hash() const
    {
      return wang32_hash(bdd_hash()(econdout)) ^ pre_hash;
    }

    unsigned dst;
    bdd econd;
    mutable bdd econdout;
    std::pair<bdd, bdd> einsup;
    acc_cond::mark_t acc;
    size_t pre_hash;
  };
  // We define an order between the edges to avoid creating multiple
  // states that in fact correspond to permutations of the order of the
  // outgoing edges
  struct less_info_t
  {
    // Note: orders via !econd!
    inline bool operator()(const e_info_t &lhs, const e_info_t &rhs) const
    {
      const int l_id = lhs.econd.id();
      const int r_id = rhs.econd.id();
      return std::tie(lhs.dst, lhs.acc, l_id)
             < std::tie(rhs.dst, rhs.acc, r_id);
    }
  }less_info;

  struct less_info_ptr_t
  {
    // Note: orders via !econdout!
    inline bool operator()(const e_info_t* lhs, const e_info_t* rhs)const
    {
      const int l_id = lhs->econdout.id();
      const int r_id = rhs->econdout.id();
      return std::tie(lhs->dst, lhs->acc, l_id)
             < std::tie(rhs->dst, rhs->acc, r_id);
    }
  }less_info_ptr;

  // Improved apply strat, that reduces the number of edges/states
  // while keeping the needed edge-properties
  // Note, this only deals with deterministic strategies
  // Note, assumes that env starts playing
  twa_graph_ptr
  apply_strategy(const const_twa_graph_ptr& arena,
                 bool unsplit, bool keep_acc)
  {
    const region_t& win = get_state_winners(arena);
    const strategy_t& strat = get_strategy(arena);
    const region_t& sp = get_state_players(arena);
    auto outs = get_synthesis_outputs(arena);

    if (!win[arena->get_init_state_number()])
      throw std::runtime_error("Player does not win initial state, strategy "
                               "is not applicable");

    assert((sp[arena->get_init_state_number()] == false)
           && "Env needs to have first turn!");
    (void)sp;

    assert(std::none_of(arena->edges().begin(), arena->edges().end(),
           [&sp](const auto& e)
             { bool same_player = sp.at(e.src) == sp.at(e.dst);
               if (same_player)
                 std::cerr << e.src << " and " << e.dst << " belong to same "
                           << "player, arena not alternating!\n";
               return same_player; }));

    auto strat_split = make_twa_graph(arena->get_dict());
    strat_split->copy_ap_of(arena);
    if (keep_acc)
      strat_split->copy_acceptance_of(arena);
    else
      strat_split->acc().set_acceptance(acc_cond::acc_code::t());

    std::stack<unsigned> todo;
    todo.push(arena->get_init_state_number());

    struct dca{
      unsigned dst;
      unsigned condvar;
      acc_cond::mark_t acc;
    };
    struct dca_hash
    {
      size_t operator()(const dca& d) const noexcept
      {
        return pair_hash()(std::make_pair(d.dst, d.condvar))
               ^ wang32_hash(d.acc.hash());
      }
    };
    struct dca_equal
    {
      bool operator()(const dca& d1, const dca& d2) const noexcept
      {
        return std::tie(d1.dst, d1.condvar, d1.acc)
              == std::tie(d2.dst, d2.condvar, d2.acc);
      }
    };

    //env dst + player cond + acc -> p stat
    std::unordered_map<dca,
                       unsigned,
                       dca_hash,
                       dca_equal> p_map;

    constexpr unsigned unseen_mark = std::numeric_limits<unsigned>::max();
    std::vector<unsigned> env_map(arena->num_states(), unseen_mark);
    strat_split->set_init_state(strat_split->new_state());
    env_map[arena->get_init_state_number()] =
        strat_split->get_init_state_number();

    // The states in the new graph are qualified local
    // Get a local environment state
    auto get_sel = [&](unsigned s)
      {
        if (SPOT_UNLIKELY(env_map[s] == unseen_mark))
          env_map[s] = strat_split->new_state();
        return env_map[s];
      };

    // local dst
    // Check if there exists already a local player state
    // that has the same dst, cond and (if keep_acc is true) acc
    auto get_spl = [&](unsigned dst, const bdd& cond, acc_cond::mark_t acc)
      {
        dca d{dst, (unsigned) cond.id(), acc};
        auto it = p_map.find(d);
        if (it != p_map.end())
          return it->second;
        unsigned ns = strat_split->new_state();
        p_map[d] = ns;
        strat_split->new_edge(ns, dst, cond, acc);
        return ns;
      };

    while (!todo.empty())
      {
        unsigned src_env = todo.top();
        unsigned src_envl = get_sel(src_env);
        todo.pop();
        // All env edges
        for (const auto& e_env : arena->out(src_env))
          {
            // Get the corresponding strat
            const auto& e_strat = arena->edge_storage(strat[e_env.dst]);
            // Check if already explored
            if (env_map[e_strat.dst] == unseen_mark)
              todo.push(e_strat.dst);
            unsigned dst_envl = get_sel(e_strat.dst);
            // The new env edge, player is constructed automatically
            auto used_acc = keep_acc ? e_strat.acc : acc_cond::mark_t({});
            strat_split->new_edge(src_envl,
                                  get_spl(dst_envl, e_strat.cond, used_acc),
                                  e_env.cond, used_acc);
          }
      }
    // All states exists, we can try to further merge them
    // Specialized merge
    std::vector<bool> spnew(strat_split->num_states(), false);
    for (const auto& p : p_map)
      spnew[p.second] = true;

    // Sorting edges in place
    auto comp_edge = [](const auto& e1, const auto& e2)
      {
        return std::tuple(e1.dst, e1.acc, e1.cond.id())
              < std::tuple(e2.dst, e2.acc, e2.cond.id());
      };
    // todo, replace with sort_edges_of_ in graph
    auto sort_edges_of =
        [&, &split_graph = strat_split->get_graph()](unsigned s)
      {
        static std::vector<unsigned> edge_nums;
        edge_nums.clear();

        auto eit = strat_split->out(s);
        const auto eit_e = eit.end();
        // 0 Check if it is already sorted
        if (std::is_sorted(eit.begin(), eit_e, comp_edge))
          return false; // No change
        // 1 Get all edges numbers and sort them
        std::transform(eit.begin(), eit_e, std::back_inserter(edge_nums),
                       [&](const auto& e)
                         { return strat_split->edge_number(e); });
        std::sort(edge_nums.begin(), edge_nums.end(),
                  [&](unsigned ne1, unsigned ne2)
                  { return comp_edge(strat_split->edge_storage(ne1),
                                    strat_split->edge_storage(ne2)); });
        // 2 Correct the order
        auto& sd = split_graph.state_storage(s);
        sd.succ = edge_nums.front();
        sd.succ_tail = edge_nums.back();
        const unsigned n_edges_p = edge_nums.size()-1;
        for (unsigned i = 0; i < n_edges_p; ++i)
          split_graph.edge_storage(edge_nums[i]).next_succ = edge_nums[i+1];
        split_graph.edge_storage(edge_nums.back()).next_succ = 0; //terminal
        // All nicely chained
        return true;
      };
    auto merge_edges_of = [&](unsigned s)
      {
        // Call this after sort edges of
        // Mergeable edges are nicely chained
        bool changed = false;
        auto eit = strat_split->out_iteraser(s);
        unsigned idx_last = strat_split->edge_number(*eit);
        ++eit;
        while (eit)
          {
            auto& e_last = strat_split->edge_storage(idx_last);
            if (std::tie(e_last.dst, e_last.acc)
                == std::tie(eit->dst, eit->acc))
              {
                //Same dest and acc -> or condition
                e_last.cond |= eit->cond;
                eit.erase();
                changed = true;
              }
            else
              {
                idx_last = strat_split->edge_number(*eit);
                ++eit;
              }
          }
        return changed;
      };
    auto merge_able = [&](unsigned s1, unsigned s2)
      {
        auto eit1 = strat_split->out(s1);
        auto eit2 = strat_split->out(s2);
        // Note: No self-loops here
        return std::equal(eit1.begin(), eit1.end(),
                          eit2.begin(), eit2.end(),
                          [](const auto& e1, const auto& e2)
                          {
                            return std::tuple(e1.dst, e1.acc, e1.cond.id())
                                   == std::tuple(e2.dst, e2.acc, e2.cond.id());
                          });
      };

    const unsigned n_sstrat = strat_split->num_states();
    std::vector<unsigned> remap(n_sstrat, -1u);
    bool changed_any;
    std::vector<unsigned> to_check;
    to_check.reserve(n_sstrat);
    // First iteration -> all env states are candidates
    for (unsigned i = 0; i < n_sstrat; ++i)
      if (!spnew[i])
        to_check.push_back(i);

    while (true)
    {
      changed_any = false;
      std::for_each(to_check.begin(), to_check.end(),
                    [&](unsigned s){ sort_edges_of(s); merge_edges_of(s); });
      // Check if we can merge env states
      for (unsigned s1 : to_check)
        for (unsigned s2 = 0; s2 < n_sstrat; ++s2)
          {
            if (spnew[s2] || (s1 == s2))
              continue; // Player state or s1 == s2
            if ((remap[s2] < s2))
              continue; //s2 is already remapped
            if (merge_able(s1, s2))
              {
                changed_any = true;
                if (s1 < s2)
                  remap[s2] = s1;
                else
                  remap[s1] = s2;
                break;
              }
          }

      if (!changed_any)
        break;
      // Redirect changed targets and set possibly mergeable states
      to_check.clear();
      for (auto& e : strat_split->edges())
        if (remap[e.dst] != -1u)
          {
            e.dst = remap[e.dst];
            to_check.push_back(e.src);
            assert(spnew[e.src]);
          }

      // Now check the player states
      // We can skip sorting -> only one edge
      // todo change when multistrat
      changed_any = false;
      for (unsigned s1 : to_check)
        for (unsigned s2 = 0; s2 < n_sstrat; ++s2)
          {
            if (!spnew[s2] || (s1 == s2))
              continue; // Env state or s1 == s2
            if ((remap[s2] < s2))
              continue; //s2 is already remapped
            if (merge_able(s1, s2))
              {
                changed_any = true;
                if (s1 < s2)
                  remap[s2] = s1;
                else
                  remap[s1] = s2;
                break;
              }
          }

      if (!changed_any)
        break;
      // Redirect changed targets and set possibly mergeable states
      to_check.clear();
      for (auto& e : strat_split->edges())
        if (remap[e.dst] != -1u)
          {
            e.dst = remap[e.dst];
            to_check.push_back(e.src);
            assert(!spnew[e.src]);
          }
    }

    // Defrag and alternate
    if (remap[strat_split->get_init_state_number()] != -1u)
      strat_split->set_init_state(remap[strat_split->get_init_state_number()]);
    unsigned st = 0;
    for (auto& s: remap)
      if (s == -1U)
        s = st++;
      else
        s = -1U;

    strat_split->defrag_states(remap, st);

    alternate_players(strat_split, false, false);
    // What we do now depends on whether we unsplit or not
    if (unsplit)
      {
        auto final = unsplit_2step(strat_split);
        set_synthesis_outputs(final, outs);
        return final;
      }

    set_synthesis_outputs(strat_split, outs);
    return strat_split;
  }
}

namespace spot
{
  namespace
  {
  twa_graph_ptr
  split_2step_expl_impl(const const_twa_graph_ptr& aut,
                        const bdd& output_bdd, bool complete_env)
  {
    assert(!aut->get_named_prop<region_t>("state-player")
           && "aut is already split!");
    auto split = make_twa_graph(aut->get_dict());

    auto [has_unsat, unsat_mark] = aut->acc().unsat_mark();
    bool max_par, odd_par, color_env;
    color_env = aut->acc().is_parity(max_par, odd_par, true);

    split->copy_ap_of(aut);
    split->new_states(aut->num_states());
    split->set_init_state(aut->get_init_state_number());
    set_synthesis_outputs(split, output_bdd);

    const auto use_color = has_unsat;
    color_env &= use_color;
    if (has_unsat)
      split->copy_acceptance_of(aut);
    else
      {
        if (complete_env)
          {
            split->set_co_buchi(); // Fin(0)
            unsat_mark = acc_cond::mark_t({0});
            has_unsat = true;
          }
        else
          split->acc().set_acceptance(acc_cond::acc_code::t());
      }

    bdd input_bdd = bddtrue;
    {
      bdd allbdd = aut->ap_vars();
      while (allbdd != bddtrue)
        {
          bdd l = bdd_ithvar(bdd_var(allbdd));
          if (not bdd_implies(output_bdd, l))
            // Input
            input_bdd &= l;
          allbdd = bdd_high(allbdd);
          assert(allbdd != bddfalse);
        }
    }

    // The environment has all states
    // with num <= aut->num_states();
    // So we can first loop over the aut
    // and then deduce the owner

    // a sort of hash-map for all new intermediate stat
    // second is the color of the incoming env trans
    std::unordered_multimap<size_t,
                            std::pair<unsigned, acc_cond::mark_t>> env_hash;
    env_hash.reserve((int) (1.5 * aut->num_states()));
    // a local map for edges leaving the current src
    // this avoids creating and then combining edges for each minterm
    // Note there are usually "few" edges leaving a state
    // and map has shown to be faster than unordered_map for
    // syntcomp examples
    std::map<unsigned, std::pair<unsigned, bdd>> env_edge_hash;
    typedef std::map<unsigned, std::pair<unsigned, bdd>>::mapped_type eeh_t;

    small_cacher_t small_cacher;
    small_cacher.fill(aut, output_bdd);

    // Cache vector for all outgoing edges of this states
    std::vector<e_info_t> e_cache;

    // Vector of destinations actually reachable for a given
    // minterm in ins
    // Automatically "almost" sorted due to the sorting of e_cache
    std::vector<const e_info_t*> dests;

    // If a completion is demanded we might have to create sinks
    // Sink controlled by player
    unsigned sink_con = -1u;
    unsigned sink_env = -1u;
    auto get_sink_con_state = [&split, &sink_con, &sink_env,
                               um = unsat_mark, hu = has_unsat]
                              (bool create = true)
      {
        assert(hu);
        if (SPOT_UNLIKELY((sink_con == -1u) && create))
          {
            sink_con = split->new_state();
            sink_env = split->new_state();
            split->new_edge(sink_con, sink_env, bddtrue, um);
            split->new_edge(sink_env, sink_con, bddtrue, um);
          }
        return sink_con;
      };

    // Loop over all states
    const auto n_states = aut->num_states();
    for (unsigned src = 0; src < n_states; ++src)
      {
        env_edge_hash.clear();
        e_cache.clear();

        auto out_cont = aut->out(src);

        // Avoid looping over all minterms
        // we only loop over the minterms that actually exist
        bdd all_letters = bddfalse;
        bdd support = bddtrue;

        for (const auto& e : out_cont)
          {
            e_cache.emplace_back(e, small_cacher);
            all_letters |= e_cache.back().einsup.first;
            support &= e_cache.back().einsup.second;
          }
        // Complete for env
        if (complete_env && (all_letters != bddtrue))
            split->new_edge(src, get_sink_con_state(), bddtrue - all_letters);

        // Sort to avoid that permutations of the same edges
        // get different intermediate states
        std::sort(e_cache.begin(), e_cache.end(), less_info);

        for (auto one_letter : minterms_of(all_letters, input_bdd))
          {

            dests.clear();
            for (const auto& e_info : e_cache)
              // implies is faster than and
              if (bdd_implies(one_letter, e_info.einsup.first))
                {
                  e_info.econdout = bdd_restrict(e_info.econd, one_letter);
                  dests.push_back(&e_info);
                  assert(e_info.econdout != bddfalse);
                }
            // By construction this should not be empty
            assert(!dests.empty());
            // # dests is almost sorted -> insertion sort
            if (dests.size()>1)
              for (auto it = dests.begin(); it != dests.end(); ++it)
                std::rotate(std::upper_bound(dests.begin(), it, *it,
                                             less_info_ptr),
                            it, it + 1);

            bool to_add = true;
            size_t h = fnv<size_t>::init;
            for (const auto& t: dests)
              h ^= t->hash();

            auto range_h = env_hash.equal_range(h);
            for (auto it_h = range_h.first; it_h != range_h.second; ++it_h)
              {
                const auto& [i, this_color] = it_h->second;
                auto out = split->out(i);
                if (std::equal(out.begin(), out.end(),
                               dests.begin(), dests.end(),
                               [uc = use_color]
                               (const twa_graph::edge_storage_t& x,
                                  const e_info_t* y)
                               {
                                 // If there is no unsat -> we do not care
                                 // about color
                                 // todo further optim?
                                 return   x.dst == y->dst
                                          &&  (!uc
                                               || x.acc == y->acc)
                                          &&  x.cond.id() == y->econdout.id();
                               }))
                  {
                    to_add = false;
                    auto it = env_edge_hash.find(i);
                    if (it != env_edge_hash.end())
                      it->second.second |= one_letter;
                    else
                      env_edge_hash.emplace(i,
                        eeh_t(split->new_edge(src, i, bddtrue,
                                              this_color),
                              one_letter));
                    break;
                  }
              }

            if (to_add)
              {
                unsigned d = split->new_state();
                auto this_color = acc_cond::mark_t({});
                bool has_uncolored = false;
                 for (const auto &t: dests)
                  {
                    split->new_edge(d, t->dst, t->econdout,
                                    use_color ? t->acc
                                              : acc_cond::mark_t({}));
                    this_color |= t->acc;
                    has_uncolored |= !t->acc;
                  }

                if (!color_env | has_uncolored)
                  this_color = acc_cond::mark_t({});
                else if (max_par)
                  this_color =
                    acc_cond::mark_t({this_color.min_set()-1});
                else // min_par
                  this_color =
                    acc_cond::mark_t({this_color.max_set()-1});

                unsigned n_e = split->new_edge(src, d, bddtrue, this_color);
                env_hash.emplace(std::piecewise_construct,
                                 std::forward_as_tuple(h),
                                 std::forward_as_tuple(d, this_color));
                env_edge_hash.emplace(d, eeh_t(n_e, one_letter));
              }
          } // letters
        // save locally stored condition
        for (const auto& elem : env_edge_hash)
          split->edge_data(elem.second.first).cond = elem.second.second;
      } // v-src

    split->merge_edges();
    split->prop_universal(trival::maybe());

    // The named property
    // compute the owners
    // env is equal to false
    auto owner = std::vector<bool>(split->num_states(), false);
    // All "new" states belong to the player
    std::fill(owner.begin()+aut->num_states(), owner.end(), true);
    // Check if sinks have been created
    if (sink_env != -1u)
      owner.at(sink_env) = false;

    // !use_color -> all words accepted
    // complete_env && sink_env == -1u
    // complet. for env demanded but already
    // satisfied -> split is also all true
    if (complete_env && sink_env == -1u && !use_color)
      split->acc() = acc_cond::acc_code::t();

    set_state_players(split, std::move(owner));

    // Done
    return split;
  } // End split old impl

  std::vector<bdd>
  do_bin_encode_(unsigned N, int var0, unsigned Nvar)
  {
    auto bddvec = std::vector<std::array<bdd, 2>>(Nvar);
    for (unsigned i = 0; i < Nvar; ++i)
      bddvec[i] = {bdd_nithvar(var0+i), bdd_ithvar(var0+i)};

    auto do_bin_encode_1 = [&bddvec, Nvar](unsigned s) -> bdd {
      bdd res = bddtrue;

      for (unsigned i = 0; i < Nvar; ++i)
        {
          res &= bddvec[i][s&1];
          s >>= 1;
        }
      return res;
    };

    auto s2bdd = std::vector<bdd>(N);
    for (unsigned s = 0; s < N; ++s)
      s2bdd[s] = do_bin_encode_1(s);

    return s2bdd;
  }

  struct bitVectDecodeIterator{
    const std::vector<unsigned>& v_;
    unsigned u_, idx_ = 0u, vsize_;
    bool first_ = true;

    bitVectDecodeIterator(const std::vector<unsigned>& v, unsigned init)
        : v_{v}
        , u_{init}
        , vsize_(v_.size())
    {
    }

    // Sets to zero all variable bits before the current idx
    void small_reset_() noexcept {
      // Skip current idx
      for (--idx_; idx_!= -1u; --idx_)
        u_ ^= (1u << v_[idx_]);
      idx_ = 0;
    }

    bitVectDecodeIterator& operator++() noexcept {
      first_ = false;
      // Search for the next variable bit to increase
      while (idx_ < vsize_)
        {
          auto curr = 1u << v_[idx_];
          if (!(u_ & curr)){
            u_ |= curr;
            small_reset_();
            return *this;
          }
          ++idx_;
        }
      return *this;
    }

    unsigned operator*() const noexcept {
      return u_;
    }

    explicit operator bool() const noexcept{
      // There is always at least one element
      return idx_ < vsize_ || first_;
    }

  };

  class bitVectDecodeRange
  {
  private:
    const std::vector<unsigned>& v_;
    const unsigned initval_;

  public:
    bitVectDecodeRange(const std::vector<unsigned>& v, unsigned init)
        : v_{v}
        , initval_{init}
    {
    }

    auto
    begin() const
    {
      return bitVectDecodeIterator(v_, initval_);
    }

  };

  template<bool FULLYSYM>
  twa_graph_ptr
  split_2step_sym_impl(const const_twa_graph_ptr& aut,
                       const bdd& output_bdd, bool complete_env)
  {

    assert(!aut->get_named_prop<region_t>("state-player")
           && "aut is already split!");

    auto split = make_twa_graph(aut->get_dict());

    auto [has_unsat, unsat_mark] = aut->acc().unsat_mark();
    bool max_par, odd_par, color_env;
    color_env = aut->acc().is_parity(max_par, odd_par, true);
    const unsigned Ncolor = aut->acc().all_sets().max_set();

    split->copy_ap_of(aut);
    split->new_states(aut->num_states());
    split->set_init_state(aut->get_init_state_number());
    set_synthesis_outputs(split, output_bdd);
    //split->prop_copy(aut, twa::prop_set::all()); // todo why?

    const auto use_color = has_unsat;
    color_env &= use_color;
    if (has_unsat)
      split->copy_acceptance_of(aut);
    else
      {
        if (complete_env)
          {
            split->set_co_buchi(); // Fin(0)
            unsat_mark = acc_cond::mark_t({0});
            has_unsat = true;
          }
        else
          split->acc().set_acceptance(acc_cond::acc_code::t());
      }

    // Reserve all the necessary variables
    const unsigned N = split->num_states();
    const unsigned Nstvars = std::ceil(std::log2(N));
    // we use one hot encoding for colors
    constexpr unsigned Ncolorvars = SPOT_MAX_ACCSETS;
    // Last one is for no color

    auto var_in = std::vector<int>();
    auto var_out = std::vector<int>();

    {
    bdd allbdd = split->ap_vars();
    while (allbdd != bddtrue)
      {
        int lvar = bdd_var(allbdd);
        bdd l = bdd_ithvar(lvar);
        if (bdd_implies(output_bdd, l))
          var_out.push_back(lvar);
        else
          var_in.push_back(lvar);
        allbdd = bdd_high(allbdd);
        assert(allbdd != bddfalse);
      }
    }

    const unsigned Nin = var_in.size();
    const unsigned Nout = var_out.size();

    // Register the vars
    // Need to be released
    // Two possibilities for the need of variables:
    // 1) FULLYSYM == false
    // in conditions, (dst) states, color x out
    // [(dst) states, color x out] is a player state
    // 2) FULLYSYM == true
    // (src) states, in conditions, (dst) states, color x out
    // [(dst) states, color x out] is a player state

    int zeroIdx = aut->get_dict()
                    ->register_anonymous_variables(Nstvars*(1+FULLYSYM)+Nout
                                                   +Nin+Ncolorvars, &N);

    int srcStIdx = zeroIdx;
    int inIdx = srcStIdx + Nstvars*FULLYSYM;
    int dstStIdx = inIdx + Nin;
    int colorIdx = dstStIdx + Nstvars;
    int outIdx = colorIdx + Ncolorvars;

    // Construct the pairs
    bddPair* replace_fwd = bdd_newpair();
    bddPair* replace_bkwd = bdd_newpair();
    bddPair* replace_in_fwd = bdd_newpair();
    bddPair* replace_in_bkwd = bdd_newpair();
    bddPair* replace_out_fwd = bdd_newpair();
    bddPair* replace_out_bkwd = bdd_newpair();

    if (not replace_fwd || not replace_in_fwd || not replace_out_fwd
        || not replace_bkwd || not replace_in_bkwd || not replace_out_bkwd)
      throw std::runtime_error("split_2step(): bddpair alloc error.");

    { // Map old and contiguous inputs and outputs
    auto var_new = std::vector<int>(Nin);
    std::iota(var_new.begin(), var_new.end(), inIdx);
    bdd_setpairs(replace_fwd, var_in.data(), var_new.data(), Nin);
    bdd_setpairs(replace_in_fwd, var_in.data(), var_new.data(), Nin);
    bdd_setpairs(replace_bkwd, var_new.data(), var_in.data(), Nin);
    bdd_setpairs(replace_in_bkwd, var_new.data(), var_in.data(), Nin);

    var_new.resize(Nout);
    std::iota(var_new.begin(), var_new.end(), outIdx);
    bdd_setpairs(replace_fwd, var_out.data(), var_new.data(), Nout);
    bdd_setpairs(replace_out_fwd, var_out.data(), var_new.data(), Nout);
    bdd_setpairs(replace_bkwd, var_new.data(), var_out.data(), Nout);
    bdd_setpairs(replace_out_bkwd, var_new.data(), var_out.data(), Nout);
    }

    // Encode states -> binary encoding (gray code for faster encode?)
    auto dstEnvs2bdd = do_bin_encode_(N, dstStIdx, Nstvars);
    //Source states are only needed once

    // Last bdd is no color
    auto color2bdd = std::vector<std::array<bdd, 2>>(Ncolorvars);
    for (int i = 0; i < (int) Ncolorvars; ++i)
      color2bdd[i] = {bdd_nithvar(colorIdx + i), bdd_ithvar(colorIdx + i)};

    // There are no colors -> All False
    const bdd noColorBdd
      = std::accumulate(color2bdd.begin(), color2bdd.end(),
                        (bdd) bddtrue,
                        [](const bdd& l, const auto& r) -> bdd
                        {return l & r[0]; });

    // Each player state corresponds to a set of (dst_state, colors, outs)
    // We also store the "least accepting" color
    auto playbdd2st
      = std::unordered_map<bdd,
                           std::pair<acc_cond::mark_t, unsigned>,
                           bdd_hash>();
    playbdd2st.reserve(N);

    // Encode (in, out, state) and split<
    auto invar2bdd = std::vector<std::array<bdd, 2>>(Nin);
    for (int i = 0; i < (int) Nin; ++i)
      invar2bdd[i] = {bdd_nithvar(inIdx+i), bdd_ithvar(inIdx+i)};

    enum class ctask{
      PUT = 0,
      VISIT,
      POP
    };

    // Fwd map complete condition
    // We could work with int, the bdd will stay in the graph
    auto fwd_comp_repl = std::unordered_map<bdd, bdd, bdd_hash>();

    // Encode a single edge in from aut with the new variables
    auto encode_edge = [&](const auto& e) -> bdd
      {
        // Build color cond
        // No color -> No bdd
        bdd color_cond = noColorBdd;
        if (use_color && e.acc != acc_cond::mark_t{})
          {
            color_cond = bddtrue;

            for (unsigned acolor = 0; acolor < Ncolor; ++acolor)
              color_cond &= color2bdd[acolor][e.acc.has(acolor)];
          }
        // The whole edge; Order the and? N-ary and?

        auto [itc, insc]
            = fwd_comp_repl.try_emplace(e.cond, bddfalse);
        if (insc)
          itc->second = bdd_replace(e.cond, replace_fwd);
        return itc->second & color_cond & dstEnvs2bdd[e.dst];
      };

    auto abstract_traverse
        = [](auto& stack, auto&& fput, auto&& fpop, auto&& fvisit) -> void
      {
        while (not stack.empty())
          {
            auto [ct, current] = std::move(stack.back());

            stack.pop_back();

            switch (ct)
            {
              case ctask::PUT:
                fput(current);
                break;
              case ctask::POP:
                fpop(current);
                break;
              case ctask::VISIT:
                fvisit(current);
                break;
            }
          }
      };

    auto abstract_put = [](auto& stack, const bdd& ccond, auto&& metaf)
      {
        for (int polprime : {0, 1})
          {
            bdd cprime = polprime == 0 ? bdd_low(ccond) : bdd_high(ccond);

            if (cprime != bddfalse)
              {
                stack.emplace_back(ctask::POP, metaf(polprime));
                stack.emplace_back(ctask::VISIT, cprime);
                stack.emplace_back(ctask::PUT, metaf(polprime));
              }
          }
      };

    // Bkwd replace map
    auto bkwd_out_repl = std::unordered_map<bdd, bdd, bdd_hash>();

    // Final step construct colors and conditions
    // cond is a bdd over color variables and new outputs
    auto construct_colorcond
      = [&](bdd cond)
      {
        // We need to do a final traversal of the color
        // It is similar to the traversal of the states

        // The result
        auto all_comb = std::vector<std::pair<acc_cond::mark_t, bdd>>();

        // int[2] is relative lvl and polarity
        using stack_type = std::variant<bdd, unsigned>;
        auto stack_colors = std::vector<std::pair<ctask, stack_type>>();
        // Variables that do not appear can take both values
        auto current_colors = acc_cond::mark_t{};


        auto fputCC = [&](const stack_type& ccond) -> void
        {
          auto lvl = std::get<unsigned>(ccond);
          //if (lvl != Ncolorvars - 1)
          //  current_colors.set(lvl);  // One hot
          assert(lvl < Ncolorvars || lvl == -1u);
          if (lvl != -1u)
            current_colors.set(lvl);  // One hot
        };

        auto fpopCC = [&](const stack_type& ccond) -> void
        {
          auto lvl = std::get<unsigned>(ccond);
          //if (lvl != Ncolorvars - 1)
          //  current_colors.clear(lvl); // One cold
          assert(lvl < Ncolorvars || lvl == -1u);
          if (lvl != -1u)
            current_colors.clear(lvl);  // One cold
        };

        auto fvisitCC = [&](const stack_type& ccondin) -> void
        {
          bdd ccond = std::get<bdd>(ccondin);
          //if (ccond == bddfalse)
          //  return;  // Nothing to do

          int clvl = ccond == bddtrue ? outIdx : bdd_var(ccond);
          // We either have a out condition or true
          if (clvl >= outIdx)
            {
              // We have found a new color comb
              // Leading to ccond -> add
              auto [itc, insc]
                = bkwd_out_repl.try_emplace(ccond, bddfalse);
              if (insc)
                itc->second = bdd_replace(ccond,
                                          replace_out_bkwd);
              all_comb.emplace_back(current_colors,
                                    itc->second);

            }
          else
            {
              int rel_lvl = clvl - colorIdx;
              // If the no color mark appears -> mark must be empty
              auto metaf = [&, ulvl = (unsigned) rel_lvl](int pol)
                {
                  // If the polarity is negative ("one cold")
                  // Then ignore it
                  assert(!pol || !current_colors.has(ulvl));
                  return pol == 0 ? -1u : ulvl;
                };
              abstract_put(stack_colors, ccond, metaf);
            }

        };

        stack_colors.emplace_back(ctask::VISIT, cond);
        abstract_traverse(stack_colors, fputCC, fpopCC, fvisitCC);

        return all_comb;
      };


    // The condition contains variables of dst_state, color x cond
    // In a much similar manner we need to traverse the states, as we traversed
    // the inputs
    // Mapping bdd(color x new outs) -> [mark x old outs]
    auto bdd2colorCond
      = std::unordered_map<bdd,
                           std::vector<std::pair<acc_cond::mark_t, bdd>>,
                           bdd_hash>();

    struct unsigedItDescr {
      unsigned val;
      std::array<char, 32> canChange;
      std::vector<unsigned> idx;

      unsigedItDescr()
        : val{0u}
        , idx{32, -1u}
      {
        canChange.fill(true);
      }
    };

    auto construct_ply_state
      = [&](bdd cond) -> std::pair<acc_cond::mark_t, unsigned>
      {

        // Needed to determine "least" accepting color for this state
        // That is the color that we can put on all incoming transitions
        auto thiscolor = acc_cond::mark_t{};
        bool has_uncolored = false;
        unsigned thisstate = split->new_state();

        // int[2] is relative lvl and polarity
        using stack_type = std::variant<bdd, std::array<int, 2>>;
        auto stack_states = std::vector<std::pair<ctask, stack_type>>();
        auto current_dst_states = unsigedItDescr{};

        auto fputPlySt
          = [&current_dst_states](const stack_type& ccond) -> void
          {
            assert((std::holds_alternative<std::array<int, 2>>(ccond)));
            auto [lvl, pol] = std::get<std::array<int, 2>>(ccond);
            // Fix the corresponding bit
            // Not changeable
            current_dst_states.canChange[lvl] = false;
            if (pol)
              // Set the bit true
              current_dst_states.val |= (1u << lvl);
            else
              // Unset it
              current_dst_states.val &= ~(1u << lvl);
          };

        auto fpopPlySt
          = [&current_dst_states](const stack_type& ccond) -> void
          {
            assert((std::holds_alternative<std::array<int, 2>>(ccond)));
            // We need to unset the bit and mark it as changeable
            auto lvl = std::get<std::array<int, 2>>(ccond)[0];
            current_dst_states.val &= ~(1u << lvl);
            current_dst_states.canChange[lvl] = true;
          };

        auto fvisitPlySt = [&](const stack_type& ccondin) -> void
          {
            assert(std::holds_alternative<bdd>(ccondin));
            const bdd& ccond = std::get<bdd>(ccondin);
            int clvl = ccond == bddtrue ? colorIdx : bdd_var(ccond);
            if (clvl >= colorIdx)
              {
                // We have found a new "cube of states"
                // Leading to ccond
                auto [it_cc, ins_cc]
                  = bdd2colorCond.try_emplace(ccond,
                                              std::vector<
                                                std::pair<acc_cond::mark_t,
                                                          bdd>>());
                if (ins_cc)
                  it_cc->second = construct_colorcond(ccond);

                // Loop over all the states in the "cube"
                //auto state_range = bitVectDecodeRange(current_dst_states);
                //for (auto it_s = state_range.begin(); (bool) it_s; ++it_s)
                // Get all the modifiable idx
                current_dst_states.idx.clear();
                for (unsigned i = 0; i < Nstvars; ++i)
                  if (current_dst_states.canChange[i])
                    current_dst_states.idx.push_back(i);
                // Loop over them
                auto state_range = bitVectDecodeRange(current_dst_states.idx,
                                                      current_dst_states.val);
                for (auto it_s = state_range.begin(); (bool) it_s; ++it_s)
                  // Loop over all edges
                  for (const auto& [acolor, acond] : it_cc->second)
                    {
                      split->new_edge(thisstate, *it_s, acond, acolor);
                      // Update color
                      thiscolor |= acolor;
                      has_uncolored |= !acolor;
                    }

              }
            else
              {
                int rel_lvl = clvl - dstStIdx;
                auto metaf = [rel_lvl](int pol)
                {
                  return std::array<int, 2>{rel_lvl, pol};
                };
                abstract_put(stack_states, ccond, metaf);
              }

          };

        stack_states.emplace_back(ctask::VISIT, cond);
        abstract_traverse(stack_states, fputPlySt, fpopPlySt, fvisitPlySt);

        // Adjust the color depending on options and acceptance conditions
        // Todo: check if dead ends are treated correctly
        if (!color_env | has_uncolored)
          // Do something smart for TELA?
          thiscolor = acc_cond::mark_t({});
        else if (max_par)
          thiscolor =
              acc_cond::mark_t({thiscolor.min_set()-1});
        else // min_par
          thiscolor =
              acc_cond::mark_t({thiscolor.max_set()-1});

        return std::make_pair(thiscolor, thisstate);
    };

    // Fwd map for replacing
    // Todo is this a good idea?
    auto bkwd_in_repl = std::unordered_map<bdd, bdd, bdd_hash>();

    auto stack_inputs = std::vector<std::pair<ctask, bdd>>();

    bdd current_in = bddtrue;

    // Define the abstract traverse
    auto fputInTrav = [&current_in](const bdd& ccond) -> void
      {
        current_in &= ccond;
      };

    auto fpopInTrav = [&current_in](const bdd& ccond) -> void
      {
        // At the end, exist is cheap (I hope)
        current_in = bdd_exist(current_in, ccond);
      };



    unsigned sink_env = -1u;

    if constexpr (FULLYSYM)
      {
        // First we need to encode the complete automaton
        // Create the symbolic aut
        // To avoid reencoding, swap
        bddPair* replace_dstSt_srcSt = bdd_newpair();
        {
          auto varSrc = std::vector<int>(Nstvars);
          auto varDst = std::vector<int>(Nstvars);
          std::iota(varSrc.begin(), varSrc.end(), srcStIdx);
          std::iota(varDst.begin(), varDst.end(), dstStIdx);
          bdd_setpairs(replace_dstSt_srcSt, varDst.data(),
                       varSrc.data(), Nstvars);
        }
        auto getSrc = [&](unsigned s)
          {return bdd_replace(dstEnvs2bdd[s], replace_dstSt_srcSt); };

        bdd sym_aut = bddfalse;
        for (unsigned s = 0; s < N; ++s)
          {
            bdd enc_out_s = bddfalse;
            for (const auto& e : aut->out(s))
              enc_out_s |= encode_edge(e);
            sym_aut |= getSrc(s)&enc_out_s;
          }

        // Define how to construct an extended player state
        // An extended player is constructing the list
        // of (player state, input condition) from a bdd
        // containing (in const, dst state, color cond)
        // This function needs to traverse the incondition
        // put and pop can be reused
        auto construct_ext_ply_state
          = [&](auto& plystatedict, const bdd& ccond)
          {
            current_in = bddtrue;

            auto fvisitInTrav
              = [&](const bdd& ccond) -> void
              {
                auto& [plyconddict, plycondvect] = plystatedict;

                int clvl = bdd_var(ccond);
                assert(clvl >= inIdx);
                if (clvl >= dstStIdx) // States come after input
                  {
                    // We have found a new in cube
                    // Add to the existing ones if necessary
                    // Translate to old variables
                    auto [itc, insc]
                        = bkwd_in_repl.try_emplace(current_in, bddfalse);
                    if (insc)
                      itc->second = bdd_replace(current_in, replace_in_bkwd);
                    const bdd& current_in_old = itc->second;

                    // treat it
                    auto [it_s, ins_s]
                        = playbdd2st.try_emplace(
                            ccond,
                            std::make_pair(acc_cond::mark_t{},
                                           -1u));
                    if (ins_s)
                      // A new player state and the corresponding least
                      // accepting color
                      it_s->second = construct_ply_state(ccond);

                    // Add the condition
                    auto [it_e, ins_e]
                        = plyconddict.try_emplace(ccond, -1u);
                    // Add the input
                    if (ins_e)
                      {
                        it_e->second = plycondvect.size();
                        plycondvect.emplace_back(ccond, bddfalse);
                      }
                    // The second is the in
                    plycondvect[it_e->second].second |= current_in_old;
                    assert(plycondvect[it_e->second].second != bddfalse
                           && "bddfalse is not allowed as condition");
                  }
                else
                  {
                    auto metaf = [&bddopts = invar2bdd[clvl - inIdx]](int pol)
                      {
                        return bddopts[pol];
                      };
                    abstract_put(stack_inputs, ccond, metaf);
                  }
              };

            // Do the actual visit
            assert(stack_inputs.empty());
            stack_inputs.emplace_back(ctask::VISIT, ccond);
            abstract_traverse(stack_inputs, fputInTrav,
                              fpopInTrav, fvisitInTrav);
          }; // construct_ext_ply_state

        // What we want is
        // dict[bdd (in, dst, cc) -> dict[ ply state bdd -> input bdd]]
        // However this is not possible as it would possibly
        // reorder the transitions
        // So we need an additional vector and idx only into it
        // The vector holds the player state cond
        // (same as the key of the unordered_map)
        // To ensure efficient iteration
        auto ext_ply_dict
          = std::unordered_map<bdd,
              std::pair<std::unordered_map<bdd, unsigned, bdd_hash>,
                        std::vector<std::pair<bdd, bdd>>>, bdd_hash>();
        // bdd over new variables -> bdd over old variables, player state

        // Vist the src states
        using stack_type = std::variant<bdd, std::array<int, 2>>;
        auto stack_states = std::vector<std::pair<ctask, stack_type>>();
        // Variables that do not appear can take both values
        auto current_src_states = unsigedItDescr{};

        auto fputSrcSt
          = [&current_src_states](const stack_type& ccond) -> void
          {
            assert((std::holds_alternative<std::array<int, 2>>(ccond)));
            auto [lvl, pol] = std::get<std::array<int, 2>>(ccond);
            // Fix the corresponding bit
            // Not changeable
            current_src_states.canChange[lvl] = false;
            if (pol)
              // Set the bit true
              current_src_states.val |= (1u << lvl);
            else
              // Unset it
              current_src_states.val &= ~(1u << lvl);
          };

        auto fpopSrcSt
          = [&current_src_states](const stack_type& ccond) -> void
          {
            assert((std::holds_alternative<std::array<int, 2>>(ccond)));
            // We need to unset the bit and mark it as changeable
            auto lvl = std::get<std::array<int, 2>>(ccond)[0];
            current_src_states.val &= ~(1u << lvl);
            current_src_states.canChange[lvl] = true;
          };

        auto fvisitSrcSt = [&](const stack_type& ccondin) -> void
          {
            assert(std::holds_alternative<bdd>(ccondin));
            const bdd& ccond = std::get<bdd>(ccondin);
            int clvl = ccond == bddtrue ? inIdx : bdd_var(ccond);
            if (clvl >= inIdx)
              {
                // We have found a new "cube of states"
                // Leading to ccond
                auto [it_cc, ins_cc]
                    = ext_ply_dict.try_emplace(
                        ccond,
                        decltype(ext_ply_dict)::mapped_type{});
                if (ins_cc)
                  // Construct "in place"
                  construct_ext_ply_state(it_cc->second, ccond);

                assert(!it_cc->second.second.empty()
                       && "Dead ends should not be splitted");

                // Get all the modifiable idx
                current_src_states.idx.clear();
                for (unsigned i = 0; i < Nstvars; ++i)
                  if (current_src_states.canChange[i])
                    current_src_states.idx.push_back(i);
                // Loop over them
                auto state_range = bitVectDecodeRange(current_src_states.idx,
                                                      current_src_states.val);
                for (auto it_s = state_range.begin(); (bool) it_s; ++it_s)
                  // Loop over all edges
                  for (const auto& [plystcond, incond] : it_cc->second.second)
                    {
                      const auto& [acolor, plyst] = playbdd2st[plystcond];
                      split->new_edge(*it_s, plyst, incond, acolor);
                    }
              }
            else
              {
                int rel_lvl = clvl - srcStIdx;
                auto metaf = [rel_lvl](int pol)
                  {
                    return std::array<int, 2>{rel_lvl, pol};
                  };
                abstract_put(stack_states, ccond, metaf);
              }

          };

        stack_states.emplace_back(ctask::VISIT, sym_aut);
        abstract_traverse(stack_states, fputSrcSt, fpopSrcSt, fvisitSrcSt);

        // Free the pairs
        bdd_freepair(replace_dstSt_srcSt);
      }
    else
      {
        // If a completion is demanded we might have to create sinks
        // Sink controlled by player
        unsigned sink_con = -1u;
        auto get_sink_con_state = [&split, &sink_con, &sink_env,
            um = unsat_mark, hu = has_unsat]
            (bool create = true)
          {
            assert(hu);
            if (SPOT_UNLIKELY((sink_con == -1u) && create))
              {
                sink_con = split->new_state();
                sink_env = split->new_state();
                split->new_edge(sink_con, sink_env, bddtrue, um);
                split->new_edge(sink_env, sink_con, bddtrue, um);
              }
            return sink_con;
          };

        // envstate -> edge number for current state
        auto s_edge_dict = std::unordered_map<unsigned, unsigned>();

        for (unsigned s = 0; s < N; ++s)
          {
            s_edge_dict.clear(); // "Local" dict, outgoing for this state

            // Encode the edge as new bdd over (input, state, color, out) vars
            bdd enc_out_s = bddfalse;
            for (const auto &e: aut->out(s))
              enc_out_s |= encode_edge(e);  // Switch to new ins and outs

            // Can only be false if there is no outgoing edge
            // In this case: Nothing to do
            assert(enc_out_s != bddfalse
                   || (!(aut->out(s).begin())));

            if (enc_out_s == bddfalse)
            {
              std::cerr << "Dead end state: " << s << '\n';
#ifndef NDEBUG
              print_hoa(std::cerr, aut);
#endif
              continue;
            }

            // traverse the ins to do the actual split
            assert(stack_inputs.empty());
            stack_inputs.emplace_back(ctask::VISIT, enc_out_s);
            current_in = bddtrue;

            bdd all_in = bddfalse;  // Only needed for completion

            auto fvisitInTravS
              = [&](const bdd& ccond) -> void
              {
                int clvl = bdd_var(ccond);
                if (clvl >= dstStIdx) // States come after input
                  {
                    // We have found a new in cube
                    // Add to the existing ones if necessary
                    // Translate to old variables
                    auto [itc, insc]
                        = bkwd_in_repl.try_emplace(current_in, bddfalse);
                    if (insc)
                      itc->second = bdd_replace(current_in, replace_in_bkwd);
                    const bdd& current_in_old = itc->second;

                    if (complete_env)
                      all_in |= current_in_old;
                    // treat it
                    auto [it_s, ins_s]
                        = playbdd2st.try_emplace(
                            ccond,
                            std::make_pair(acc_cond::mark_t{},
                                           -1u));
                    if (ins_s)
                      // A new player state and the corresponding least
                      // accepting color
                      it_s->second = construct_ply_state(ccond);

                    // Add the condition
                    auto [it_e, ins_e]
                        = s_edge_dict.try_emplace(it_s->second.second, -1u);
                    if (ins_e)  // Create a new edge
                      it_e->second
                          = split->new_edge(s, it_s->second.second,
                                            current_in_old,
                                            it_s->second.first);
                    else  // Disjunction over input
                      split->edge_storage(it_e->second).cond
                        |= current_in_old;
                  }
                else
                  {
                    auto metaf = [&bddopts = invar2bdd[clvl - inIdx]](int pol)
                    {
                      return bddopts[pol];
                    };
                    abstract_put(stack_inputs, ccond, metaf);
                  }
              };

            // Traverse all the ins
            abstract_traverse(stack_inputs, fputInTrav,
                              fpopInTrav, fvisitInTravS);

            // Complete if necessary
            if (complete_env && (all_in != bddtrue))
              split->new_edge(s, get_sink_con_state(), bddtrue - all_in);

          }  // Current state is now split
      } // Else

    split->prop_universal(trival::maybe());

    // The named property
    // compute the owners
    // env is equal to false
    auto owner = std::vector<bool>(split->num_states(), false);
    // All "new" states belong to the player
    std::fill(owner.begin()+aut->num_states(), owner.end(), true);
    // Check if sinks have been created
    if (sink_env != -1u)
      owner.at(sink_env) = false;

    // !use_color -> all words accepted
    // complete_env && sink_env == -1u
    // complet. for env demanded but already
    // satisfied -> split is also all true
    if (complete_env && sink_env == -1u && !use_color)
      split->acc() = acc_cond::acc_code::t();

    set_state_players(split, std::move(owner));

    // release the variables
    // Release the pairs
    for (auto pair_ptr : {replace_fwd,
                                    replace_bkwd,
                                    replace_in_fwd,
                                    replace_in_bkwd,
                                    replace_out_fwd,
                                    replace_out_bkwd})
      bdd_freepair(pair_ptr);
    aut->get_dict()->unregister_all_my_variables(&N);

    // Done
    return split;
  }  // New split impl

  twa_graph_ptr
  split_2step_(const const_twa_graph_ptr& aut,
               const bdd& output_bdd, bool complete_env,
               synthesis_info::splittype sp
                = synthesis_info::splittype::AUTO)
  {
    // Heuristic for AUTO goes here
    // For the moment semisym is almost always best except if there are
    // really few inputs
    unsigned nIns = aut->ap().size() - bdd_nodecount(output_bdd);
    sp = sp == synthesis_info::splittype::AUTO ?
         (nIns < 4 ? synthesis_info::splittype::EXPL
                   : synthesis_info::splittype::SEMISYM)
         : sp;

    switch (sp)
    {
      case (synthesis_info::splittype::EXPL):
        return split_2step_expl_impl(aut, output_bdd, complete_env);
      case (synthesis_info::splittype::SEMISYM):
        return split_2step_sym_impl<false>(aut, output_bdd, complete_env);
      case (synthesis_info::splittype::FULLYSYM):
        return split_2step_sym_impl<true>(aut, output_bdd, complete_env);
      default:
        throw std::runtime_error("split_2step_(): "
                                 "Expected explicit splittype.");
    }
  }

  }  // End anonymous


  twa_graph_ptr
  split_2step(const const_twa_graph_ptr& aut,
              const bdd& output_bdd, bool complete_env,
              synthesis_info::splittype sp)
  {
    return split_2step_(aut, output_bdd, complete_env, sp);
  }

  twa_graph_ptr
  split_2step(const const_twa_graph_ptr& aut, bool complete_env,
              synthesis_info::splittype sp)
  {
    return split_2step_(aut,
                        get_synthesis_outputs(aut),
                        complete_env, sp);
  }

  twa_graph_ptr
  split_2step(const const_twa_graph_ptr& aut,
              synthesis_info& gi)
  {
    return split_2step_(aut,
                        get_synthesis_outputs(aut),
                        true,
                        gi.sp);
  }

  twa_graph_ptr
  unsplit_2step(const const_twa_graph_ptr& aut)
  {
    constexpr unsigned unseen_mark = std::numeric_limits<unsigned>::max();

    twa_graph_ptr out = make_twa_graph(aut->get_dict());
    out->copy_acceptance_of(aut);
    out->copy_ap_of(aut);

    // split_2step is guaranteed to produce an alternating arena
    auto owner = get_state_players(aut);
#ifndef NDEGUB
    (void) owner;
#endif

    std::vector<unsigned> state_map(aut->num_states(), unseen_mark);
    auto seen = [&](unsigned s){return state_map[s] != unseen_mark; };
    auto map_s = [&](unsigned s)
      {
        if (!seen(s))
          state_map[s] = out->new_state();
        return state_map[s];
      };

    std::deque<unsigned> todo;
    todo.push_back(aut->get_init_state_number());
    map_s(aut->get_init_state_number());
    while (!todo.empty())
      {
        unsigned cur = todo.front();
        unsigned cur_m = map_s(cur);
        todo.pop_front();

        for (const auto& i : aut->out(cur))
          for (const auto& o : aut->out(i.dst))
            {
              assert((owner.at(cur) != owner.at(o.src))
                     && (owner.at(cur) == owner.at(o.dst)
                     && "Arena is not alternating!"));
              if (!seen(o.dst))
                todo.push_back(o.dst);
              out->new_edge(cur_m, map_s(o.dst),
                            i.cond & o.cond, i.acc | o.acc);
            }
      }
    out->set_init_state(map_s(aut->get_init_state_number()));
    // Try to set outputs
    if (bdd* outptr = aut->get_named_prop<bdd>("synthesis-outputs"))
      set_synthesis_outputs(out, *outptr);
    return out;
  }

  std::ostream& operator<<(std::ostream& os, synthesis_info::algo s)
  {
    using algo = synthesis_info::algo;
    const char* name = nullptr;
    switch (s)
    {
      case (algo::DET_SPLIT):
        name = "ds";
        break;
      case (algo::SPLIT_DET):
        name = "sd";
        break;
      case (algo::DPA_SPLIT):
        name = "ps";
        break;
      case (algo::LAR):
        name = "lar";
        break;
      case (algo::LAR_OLD):
        name = "lar.old";
        break;
      case (algo::ACD):
        name = "acd";
        break;
    }
    return os << name;
}

  std::ostream&
  operator<<(std::ostream& os, const synthesis_info& gi)
  {
    os << "force sbacc: " << gi.force_sbacc << '\n'
       << "solver: " << gi.s << '\n'
       << "minimization-lvl: " << gi.minimize_lvl << '\n'
       << (gi.verbose_stream ? "Is verbose\n" : "Is not verbose\n")
       << "the bdd_dict used is " << gi.dict.get();
    return os;
  }


  namespace // Anonymous ltl_to_game
  {
    static translator
    create_translator(synthesis_info& gi)
    {
      using algo = synthesis_info::algo;

      option_map& extra_options = gi.opt;
      auto sol = gi.s;
      const bdd_dict_ptr& dict = gi.dict;

      extra_options.set_if_unset("simul", 0);
      extra_options.set_if_unset("tls-impl", 1);
      extra_options.set_if_unset("wdba-minimize", 2);

      translator trans(dict, &extra_options);
      switch (sol)
      {
      case algo::ACD:
        SPOT_FALLTHROUGH;
      case algo::LAR:
        SPOT_FALLTHROUGH;
      case algo::LAR_OLD:
        trans.set_type(postprocessor::Generic);
        trans.set_pref(postprocessor::Deterministic);
        break;
      case algo::DPA_SPLIT:
        trans.set_type(postprocessor::ParityMaxOdd);
        trans.set_pref(postprocessor::Deterministic | postprocessor::Colored);
        break;
      case algo::DET_SPLIT:
        SPOT_FALLTHROUGH;
      case algo::SPLIT_DET:
        break;
      }
      return trans;
    }

    twa_graph_ptr
    ntgba2dpa(const twa_graph_ptr& aut, bool force_sbacc)
    {
      // if the input automaton is deterministic, degeneralize it to be sure to
      // end up with a parity automaton
      auto dpa = tgba_determinize(degeneralize_tba(aut),
                                        false, true, true, false);
      dpa->merge_edges();
      if (force_sbacc)
        dpa = sbacc(dpa);
      reduce_parity_here(dpa, true);
      assert((
                 [&dpa]() -> bool {
                   bool max, odd;
                   return dpa->acc().is_parity(max, odd);
                 }()));
      assert(is_deterministic(dpa));
      return dpa;
    }
  } // anonymous

  twa_graph_ptr
  ltl_to_game(const formula& f,
              const std::vector<std::string>& all_outs,
              synthesis_info& gi)
  {
    using algo = synthesis_info::algo;

    [](std::vector<std::string> sv, std::string msg)
      {
        if (sv.size() < 2)
          return;
        std::sort(sv.begin(), sv.end());
        const unsigned svs = sv.size() - 1;
        for (unsigned i = 0; i < svs; ++i)
          if (sv[i] == sv[i+1])
            throw std::runtime_error(msg + sv[i]);
      }(all_outs, "Output propositions are expected to appear once "
                  "in all_outs. Violating: ");

    auto trans = create_translator(gi);
    // Shortcuts
    auto& bv = gi.bv;
    auto& vs = gi.verbose_stream;

    stopwatch sw;

    if (bv)
      sw.start();
    auto aut = trans.run(f);
    if (bv)
      bv->trans_time += sw.stop();

    if (vs)
      {
        assert(bv);
        *vs << "translating formula done in "
            << bv->trans_time << " seconds\n";
        *vs << "automaton has " << aut->num_states()
            << " states and " << aut->num_sets() << " colors\n";
      }
    auto tobdd = [&aut](const std::string& ap_name)
      {
        return bdd_ithvar(aut->register_ap(ap_name));
      };
    auto is_out = [&all_outs](const std::string& ao)->bool
      {
        return std::find(all_outs.begin(), all_outs.end(),
                         ao) != all_outs.end();
      };

    // Check for each ap that actually appears in the graph
    // whether its an in or out
    bdd ins = bddtrue;
    bdd outs = bddtrue;
    for (auto&& aap : aut->ap())
      {
        if (is_out(aap.ap_name()))
          outs &= tobdd(aap.ap_name());
        else
          ins &= tobdd(aap.ap_name());
      }

    twa_graph_ptr dpa = nullptr;

    auto set_split = [&outs, &gi](auto& g)
      {
        set_synthesis_outputs(g, outs);
        return split_2step(g, gi);
      };

    switch (gi.s)
    {
      case algo::DET_SPLIT:
      {
        if (bv)
          sw.start();
        auto tmp = ntgba2dpa(aut, gi.force_sbacc);
        if (vs)
          *vs << "determinization done\nDPA has "
              << tmp->num_states() << " states, "
              << tmp->num_sets() << " colors\n";
        tmp->merge_states();
        if (bv)
          bv->paritize_time += sw.stop();
        if (vs)
          *vs << "simplification done\nDPA has "
              << tmp->num_states() << " states\n"
              << "determinization and simplification took "
              << bv->paritize_time << " seconds\n";
        if (bv)
          sw.start();

        dpa = set_split(tmp);
        if (bv)
          bv->split_time += sw.stop();
        if (vs)
          *vs << "split inputs and outputs done in " << bv->split_time
              << " seconds\nautomaton has "
              << tmp->num_states() << " states\n";
        break;
      }
      case algo::DPA_SPLIT:
      {
        if (bv)
          sw.start();
        aut->merge_states();
        if (bv)
          bv->paritize_time += sw.stop();
        if (vs)
          *vs << "simplification done in " << bv->paritize_time
              << " seconds\nDPA has " << aut->num_states()
              << " states\n";
        if (bv)
          sw.start();
        dpa = set_split(aut);
        if (bv)
          bv->split_time += sw.stop();
        if (vs)
          *vs << "split inputs and outputs done in " << bv->split_time
              << " seconds\nautomaton has "
              << dpa->num_states() << " states\n";
        break;
      }
      case algo::SPLIT_DET:
      {
        sw.start();
        auto split = set_split(aut);
        if (bv)
          bv->split_time += sw.stop();
        if (vs)
          *vs << "split inputs and outputs done in " << bv->split_time
              << " seconds\nautomaton has "
              << split->num_states() << " states\n";
        if (bv)
          sw.start();
        dpa = ntgba2dpa(split, gi.force_sbacc);
        if (vs)
          *vs << "determinization done\nDPA has "
              << dpa->num_states() << " states, "
              << dpa->num_sets() << " colors\n";
        // The named property "state-player" is set in split_2step
        // but not propagated by ntgba2dpa
        alternate_players(dpa);
        // Merge states knows about players
        dpa->merge_states();
        if (bv)
          bv->paritize_time += sw.stop();
        if (vs)
          *vs << "simplification done\nDPA has "
              << dpa->num_states() << " states\n"
              << "determinization and simplification took "
              << bv->paritize_time << " seconds\n";
        break;
      }
      case algo::ACD:
        SPOT_FALLTHROUGH;
      case algo::LAR:
        SPOT_FALLTHROUGH;
      case algo::LAR_OLD:
      {
        if (bv)
          sw.start();
        if (gi.s == algo::LAR)
          {
            dpa = to_parity(aut);
            reduce_parity_here(dpa, false);
          }
        else if (gi.s == algo::LAR_OLD)
          {
            dpa = to_parity_old(aut);
            reduce_parity_here(dpa, true);
          }
        else
          dpa = acd_transform(aut);
        if (bv)
          bv->paritize_time += sw.stop();
        if (vs)
          *vs << (gi.s == algo::ACD ? "ACD" : "LAR")
              << " construction done in " << bv->paritize_time
              << " seconds\nDPA has "
              << dpa->num_states() << " states, "
              << dpa->num_sets() << " colors\n";

        if (bv)
          sw.start();
        dpa = set_split(dpa);
        if (bv)
          bv->split_time += sw.stop();
        if (vs)
          *vs << "split inputs and outputs done in " << bv->split_time
              << " seconds\nautomaton has "
              << dpa->num_states() << " states\n";
        break;
      }
    } //end switch solver
    // Set the named properties
    assert(dpa->get_named_prop<std::vector<bool>>("state-player")
           && "DPA has no \"state-player\"");
    set_synthesis_outputs(dpa, outs);
    return dpa;
  }

  twa_graph_ptr
  ltl_to_game(const formula& f,
              const std::vector<std::string>& all_outs)
  {
    synthesis_info dummy;
    return ltl_to_game(f, all_outs, dummy);
  }

  twa_graph_ptr
  ltl_to_game(const std::string& f,
              const std::vector<std::string>& all_outs)
  {
    return ltl_to_game(parse_formula(f), all_outs);
  }

  twa_graph_ptr
  ltl_to_game(const std::string& f,
              const std::vector<std::string>& all_outs,
              synthesis_info& gi)
  {
    return ltl_to_game(parse_formula(f), all_outs, gi);
  }

  twa_graph_ptr
  solved_game_to_mealy(twa_graph_ptr arena, synthesis_info& gi)
  {
    // This currently always produces either separated or split mealy machines
    // if this changes, change also the other functions accordingly
    assert(arena->get_named_prop<region_t>("state-player")
           && "Need prop \"state-player\"");
    if (!arena)
      throw std::runtime_error("Arena can not be null");

    stopwatch sw;

    if (gi.bv)
      sw.start();

    if (!get_state_winner(arena, arena->get_init_state_number()))
      return nullptr;

    auto m = apply_strategy(arena, false, false);

    m->prop_universal(true);

    if (gi.bv)
      {
        auto sp = get_state_players(m);
        auto n_s_env = sp.size() - std::accumulate(sp.begin(),
                                                   sp.end(),
                                                   0u);
        auto n_e_env = 0u;
        std::for_each(m->edges().begin(), m->edges().end(),
                      [&n_e_env, &sp](const auto& e)
                        {
                          n_e_env += sp[e.src];
                        });
        gi.bv->strat2aut_time += sw.stop();
        gi.bv->nb_strat_states += n_s_env;
        gi.bv->nb_strat_edges += n_e_env;
      }

    assert(is_mealy(m));
    return m;
  }

  twa_graph_ptr
  solved_game_to_mealy(twa_graph_ptr arena)
  {
    synthesis_info dummy;
    return solved_game_to_mealy(arena, dummy);
  }

  twa_graph_ptr
  solved_game_to_separated_mealy(twa_graph_ptr arena, synthesis_info& gi)
  {
    auto m = solved_game_to_mealy(arena, gi);

    if (m->get_named_prop<region_t>("state-player"))
      m = unsplit_mealy(m);
    assert(is_separated_mealy(m));
    return m;
  }

  twa_graph_ptr
  solved_game_to_separated_mealy(twa_graph_ptr arena)
  {
    synthesis_info dummy;
    return solved_game_to_separated_mealy(arena, dummy);
  }

  twa_graph_ptr
  solved_game_to_split_mealy(twa_graph_ptr arena, synthesis_info& gi)
  {
    auto m = solved_game_to_mealy(arena, gi);

    if (!m->get_named_prop<region_t>("state-player"))
      {
        assert(is_separated_mealy(m));
        split_separated_mealy_here(m);
      }
    assert(is_split_mealy(m));
    return m;
  }

  twa_graph_ptr
  solved_game_to_split_mealy(twa_graph_ptr arena)
  {
    synthesis_info dummy;
    return solved_game_to_split_mealy(arena, dummy);
  }

}

namespace spot
{
  //Anonymous for try_create_strat
  namespace
  {
    // Checks that 2 sets have a common element. Use it instead
    // of set_intersection when we just want to check if they have a common
    // element because it avoids going through the rest of the sets after an
    // element is found.
    static bool
    are_intersecting(const std::set<formula> &v1,
                    const std::set<formula> &v2)
    {
      auto v1_pos = v1.begin(), v2_pos = v2.begin(), v1_end = v1.end(),
          v2_end = v2.end();
      while (v1_pos != v1_end && v2_pos != v2_end)
        {
          if (*v1_pos < *v2_pos)
            ++v1_pos;
          else if (*v2_pos < *v1_pos)
            ++v2_pos;
          else
            return true;
        }
      return false;
    }
    class formula_2_inout_props
    {
    private:
      std::map<formula, std::pair<std::set<formula>, std::set<formula>>> data_;
      std::vector<std::string> outs_;

    public:

      formula_2_inout_props(std::vector<std::string> outs) : outs_(outs)
      {}

      std::pair<std::set<formula>, std::set<formula>>
      aps_of(formula f)
      {
        auto cache_value = data_.find(f);
        if (cache_value != data_.end())
          return cache_value->second;
        std::set<formula> ins_f, outs_f;
        f.traverse([&](const formula& f)
                  {
                    if (f.is(op::ap))
                    {
                      auto cache_value =
                        std::find(outs_.begin(), outs_.end(), f.ap_name());
                      if (cache_value != outs_.end())
                        outs_f.insert(f);
                      else
                        ins_f.insert(f);
                    }
                    return false;
                  });
        std::pair<std::set<formula>, std::set<formula>> res({ins_f, outs_f});
        data_.insert({f, res});
        return res;
      }
    };
  }

  mealy_like
  try_create_direct_strategy(formula f,
                             const std::vector<std::string>& output_aps,
                             synthesis_info &gi, bool want_strategy)
  {
    auto vs = gi.verbose_stream;
    auto& bv = gi.bv;
    bdd_dict_ptr& dict = gi.dict;
    int tmp;

    if (vs)
      *vs << "trying to create strategy directly for " << f << '\n';

    auto ret_sol_maybe = [&vs, &tmp, &dict]()
      {
        dict->unregister_all_my_variables(&tmp);
        if (vs)
          *vs << "direct strategy might exist but was not found.\n";
        return mealy_like{
                  mealy_like::realizability_code::UNKNOWN,
                  nullptr,
                  bddfalse};
      };
    auto ret_sol_none = [&vs, &tmp, &dict]()
      {
        dict->unregister_all_my_variables(&tmp);
        if (vs)
          *vs << "no strategy exists.\n";
        return mealy_like{
                  mealy_like::realizability_code::UNREALIZABLE,
                  nullptr,
                  bddfalse};
      };

    auto ret_sol_exists =
      [&vs, &want_strategy, &tmp, &dict, &output_aps]
      (twa_graph_ptr strat)
      {
        dict->unregister_all_my_variables(&tmp);
        if (strat)
          {
            strat->merge_edges();
            bdd outputs = bddtrue;
            std::for_each(
                  output_aps.begin(),
                  output_aps.end(),
                  [&strat, &outputs](const std::string& ap) -> void
                  { outputs &= bdd_ithvar(strat->register_ap(ap)); });

            set_synthesis_outputs(strat, outputs);
          }
        if (vs)
          {
            *vs << "direct strategy was found.\n";
            if (strat && want_strategy)
              *vs << "direct strategy has " << strat->num_states()
                  << " states and " << strat->num_edges() << " edges\n";
          }
        return mealy_like{
                  mealy_like::realizability_code::REALIZABLE_REGULAR,
                  strat,
                  bddfalse};
      };
    formula_2_inout_props form2props(output_aps);

    formula f_g, f_other;
    // If it is G(α) ∧ G(β) ∧ …
    if (f.is(op::And))
    {
      std::vector<formula> gs;
      std::vector<formula> others;
      for (auto child : f)
        if (child.is(op::G) && child[0].is_boolean())
          gs.push_back(child[0]);
        else
          others.push_back(child);

      f_g = formula::And(gs);
      f_other = formula::And(others);
    }
    else if (f.is(op::G) && f[0].is_boolean())
    {
      f_g = f[0];
      f_other = formula::tt();
    }
    else
    {
      f_g = formula::tt();
      f_other = f;
    }

    // We have to check if the content of G is realizable (input-complete)
    bdd output_bdd_tmp = bddtrue;
    for (auto& out : output_aps)
      output_bdd_tmp &= bdd_ithvar(
        dict->register_proposition(formula::ap(out), &tmp));

    if (!f_g.is_tt())
    {
      auto g_bdd = formula_to_bdd(f_g, dict, &tmp);
      if (bdd_exist(g_bdd, output_bdd_tmp) != bddtrue)
        return ret_sol_none();
    }

    if (f_other.is(op::Equiv))
    {
      // Check if FG or GF
      auto is_general = [&tmp, &output_bdd_tmp, &dict](const formula &f,
                                                       op first, op second)
      {
        if (!f.is({first, second}) || !f[0][0].is_boolean())
          return false;
        auto f_bdd = formula_to_bdd(f[0][0], dict, &tmp);
        if (bdd_exist(f_bdd, output_bdd_tmp) != bddtrue)
          return false;
        f_bdd = formula_to_bdd(formula::Not(f[0][0]), dict, &tmp);
        bool res = (bdd_exist(f_bdd, output_bdd_tmp) == bddtrue);
        return res;
      };

      auto is_gf = [is_general](const formula& f)
      {
        return is_general(f, op::G, op::F);
      };

      auto is_fg = [is_general](const formula& f)
      {
        return is_general(f, op::F, op::G);
      };

      auto is_co_bu = [](const formula &f, const std::set<formula>& outs)
      {
        return outs.empty() && f.is_syntactic_obligation();
      };

      auto is_buchi = [](const formula &f, const std::set<formula>& outs)
      {
        return outs.empty() && f.is_syntactic_recurrence();
      };

      auto properties_vector = [&](const formula &f,
                            const std::set<formula> &outs)
      {
        auto is_lgf = is_gf(f);
        auto is_lfg = is_fg(f);
        return std::vector<bool>{
            // f is GF(ins + outs) <-> buchi(ins)
            is_lgf,
            is_buchi(f, outs),
            // f is FG(ins + outs) <-> co-buchi(ins)
            is_lfg,
            is_co_bu(f, outs)};
      };


      auto [left_ins, left_outs] = form2props.aps_of(f_other[0]);
      auto [right_ins, right_outs] = form2props.aps_of(f_other[1]);

      auto left_properties = properties_vector(f_other[0], left_outs);
      auto right_properties = properties_vector(f_other[1], right_outs);

      unsigned combin = -1U;
      for (unsigned i = 0; i < 4; ++i)
        if (left_properties[i] && right_properties[(i % 2) ? (i - 1) : (i + 1)])
        {
          combin = i;
          break;
        }

      // If we don't match, we don't know
      if (combin == -1U)
        return ret_sol_maybe();

      formula f_left = f_other[(combin + 1) % 2];
      formula f_right = f_other[combin % 2];
      if (!(combin % 2))
      {
        std::swap(left_ins, right_ins);
        std::swap(left_outs, right_outs);
      }

      std::set<formula> g_outs = form2props.aps_of(f_g).second;
      if (are_intersecting(g_outs, right_outs))
        return ret_sol_maybe();

      // We know that a strategy exists and we don't want to construct it.
      if (!want_strategy)
        return ret_sol_exists(nullptr);

      auto trans = create_translator(gi);

      trans.set_pref(postprocessor::Deterministic | postprocessor::Complete);
      if (combin < 2)
        trans.set_type(postprocessor::Buchi);
      else
        trans.set_type(postprocessor::CoBuchi);

      stopwatch sw;
      if (bv)
        sw.start();
      auto res = trans.run(f_left);

      if (!is_deterministic(res))
        {
          if (bv)
            {
              auto delta = sw.stop();
              bv->trans_time += delta;
              if (vs)
                *vs << "translating formula done in " << delta
                    << " seconds...\n... but it gave a "
                    << "non-deterministic automaton (rejected)\n";
            }
          return ret_sol_maybe();
        }

      res->prop_complete(trival::maybe());

      bdd output_bdd = bddtrue;
      auto [is, os] = form2props.aps_of(f);
      for (auto i : is)
        res->register_ap(i);
      for (auto o : os)
        output_bdd &= bdd_ithvar(res->register_ap(o));

      bdd right_bdd = formula_to_bdd(f_right[0][0], dict, res);
      bdd neg_right_bdd = bdd_not(right_bdd);
      bdd g_bdd = formula_to_bdd(f_g, dict, res);

      if (combin > 1)
        std::swap(right_bdd, neg_right_bdd);

      right_bdd = bdd_and(right_bdd, g_bdd);
      neg_right_bdd = bdd_and(neg_right_bdd, g_bdd);

      scc_info si(res, scc_info_options::NONE);

      bool is_true_acc = ((combin < 2) && res->acc().is_t())
                || ((combin > 1) && res->acc().is_f());
      auto prop_vector = propagate_marks_vector(res);
      auto& ev = res->edge_vector();
      for (unsigned i = 1; i < ev.size(); ++i)
      {
        auto &edge = ev[i];
        if (si.scc_of(edge.src) == si.scc_of(edge.dst))
        {
          if (edge.acc || is_true_acc)
            edge.cond &= right_bdd;
          // If we have a GF and an edge is not colored but prop_vector says
          // that this edge could be colored, it means that we can do what we
          // want
          else if (!prop_vector[i])
            edge.cond &= neg_right_bdd;
          else
            edge.cond &= g_bdd;
        }
        else
          edge.cond &= g_bdd;
        edge.acc = {};
      }
      res->set_acceptance(acc_cond::acc_code::t());
      res->prop_weak(true);
      if (res->prop_terminal().is_false())
        res->prop_terminal(trival::maybe());
      res->set_named_prop<bdd>("synthesis-outputs", new bdd(output_bdd));

      if (bv)
        {
          auto delta = sw.stop();
          bv->trans_time += delta;
          if (vs)
            *vs << "translating formula done in " << delta << " seconds\n";
        }
      return ret_sol_exists(res);
    }
    else if (f_other.is_tt())
    {
      if (!want_strategy)
        return ret_sol_exists(nullptr);
      stopwatch sw;
      if (bv)
        sw.start();

      auto res = make_twa_graph(dict);
      res->prop_weak(true);

      bdd output_bdd = bddtrue;
      std::set<formula> ins_f = form2props.aps_of(f_g).first;
      for (auto &out : output_aps)
        output_bdd &= bdd_ithvar(res->register_ap(out));

      for (auto &in : ins_f)
        res->register_ap(in);

      res->set_named_prop<bdd>("synthesis-outputs", new bdd(output_bdd));
      bdd g_bdd = formula_to_bdd(f_g, dict, res);
      res->new_state();
      res->new_edge(0, 0, g_bdd);
      if (bv)
        {
          auto delta = sw.stop();
          bv->trans_time += delta;
          if (vs)
            *vs << "translating formula done in " << delta << " seconds\n";
        }
      return ret_sol_exists(res);
    }
    return ret_sol_maybe();
  }

} // spot

namespace // anonymous for subsformula
{
  using namespace spot;
  static std::pair<std::set<formula>, std::set<formula>>
  algo4(const std::vector<formula> &assumptions,
        const std::set<std::string> &outs,
        formula_2_inout_props& form2props)
  {
    // Two variables are "connected" if they share an assumption.
    // It creates a dependency graph and our goal is to find the propositions
    // that are in the same connected components as outputs.
    const auto ass_size = assumptions.size();
    std::vector<bool> done(ass_size, false);
    std::pair<std::set<formula>, std::set<formula>> result;
    // // An output is in the result.
    for (auto &o : outs)
      result.second.insert(formula::ap(o));
    std::stack<unsigned> todo;
    unsigned first_free = 0;

    auto next_free = [&]()
      {
        while (first_free < ass_size)
          {
            if (done[first_free])
              {
                ++first_free;
                continue;
              }
            auto f = assumptions[first_free];
            auto o = form2props.aps_of(f).second;
            if (!o.empty())
              return true;
            ++first_free;
          }
        return false;
      };
    while (next_free())
      {
        todo.push(first_free);
        while (!todo.empty())
          {
            unsigned current_index = todo.top();
            todo.pop();
            formula current_form = assumptions[current_index];
            done[current_index] = true;
            auto [ins_current, outs_current]
              = form2props.aps_of(current_form);
            result.first.insert(ins_current.begin(), ins_current.end());
            result.second.insert(outs_current.begin(), outs_current.end());
            for (unsigned i = 0; i < ass_size; ++i)
              {
                if (done[i])
                  continue;
                auto other_form = assumptions[i];
                auto [ins_other, outs_other]
                  = form2props.aps_of(other_form);
                if (are_intersecting(ins_current, ins_other) ||
                    are_intersecting(outs_other, outs_other))
                  todo.push(i);
              }
          }
      }
    return result;
  }

  static formula
  split_implication(const formula &f, const std::set<std::string> &outs,
                    formula_2_inout_props& form2props)
  {
    assert(f.is(op::Implies));
    assert(f[0].is(op::And));
    if (!(f[1].is(op::And)))
      return f;
    std::vector<formula> assumptions, guarantees;
    for (auto a : f[0])
      assumptions.push_back(a);
    for (auto g : f[1])
      guarantees.push_back(g);
    // Set of input/output props that cannot be shared between
    // subspecifications
    auto decRelProps = algo4(assumptions, outs, form2props);
    auto &decRelProps_ins = decRelProps.first;
    auto &decRelProps_outs = decRelProps.second;
    // Assumptions that don't contain an atomic proposition in decRelProps
    auto free_assumptions = formula::tt();
    // The set of subspecifications described as [(assum, guar), (assum, guar)]
    std::vector<std::pair<formula, formula>> specs;
    // We merge two assumpt or guar. that share a proposition from decRelProps
    std::vector<formula> assumptions_split, guarantees_split;

    auto fus = [&](std::vector<formula> &forms,
                                                 std::vector<formula> &res)
    {
      std::stack<unsigned> todo;
      todo.emplace(0);
      unsigned first_free = 1;
      const unsigned forms_size = forms.size();
      std::vector<bool> done(forms_size, false);
      while (!todo.empty())
        {
          auto current_res = formula::tt();
          while (!todo.empty())
            {
              auto current_index = todo.top();
              todo.pop();
              done[current_index] = true;
              auto current_form = forms[current_index];
              current_res = formula::And({current_res, current_form});
              auto [ins_f, outs_f] = form2props.aps_of(current_form);
              std::set<formula> ins_f_dec, outs_f_dec;
              std::set_intersection(ins_f.begin(), ins_f.end(),
                                    decRelProps_ins.begin(),
                                    decRelProps_ins.end(),
                                    std::inserter(ins_f_dec,
                                                  ins_f_dec.begin()));
              std::set_intersection(outs_f.begin(), outs_f.end(),
                                    decRelProps_outs.begin(),
                                    decRelProps_outs.end(),
                                    std::inserter(ins_f_dec,
                                                  ins_f_dec.begin()));
              for (unsigned i = 0; i < forms_size; ++i)
                {
                  if (done[i])
                    continue;
                  auto [ins_i, outs_i] = form2props.aps_of(forms[i]);
                  if (are_intersecting(ins_i, ins_f_dec)
                   || are_intersecting(outs_i, outs_f_dec))
                    todo.emplace(i);
                }
            }
          res.push_back(current_res);
          while (first_free < forms_size && done[first_free])
            ++first_free;
          if (first_free < forms_size)
            {
              todo.emplace(first_free);
              ++first_free;
            }
        }
    };

    fus(assumptions, assumptions_split);
    fus(guarantees, guarantees_split);

    // Now we just have to find connected components in a bipartite graph
    std::function<void(formula f, std::vector<formula> &,
                       std::vector<formula> &,
                       std::set<formula> &,
                       std::set<formula> &,
                       formula &, formula &,
                       std::vector<bool> &,
                       std::vector<bool> &)> bip;
    bip = [&bip, &form2props](formula f, std::vector<formula> &src_vect,
                        std::vector<formula> &dst_vect,
                        std::set<formula> &ins_dec,
                        std::set<formula> &outs_dec,
                        formula &left_res, formula &right_res,
                        std::vector<bool> &done_left,
                        std::vector<bool> &done_right)
    {
      left_res = formula::And({left_res, f});
      auto [ins_f, outs_f] = form2props.aps_of(f);
      std::set<formula> f_ins_dec, f_outs_dec;
      std::set_intersection(ins_f.begin(), ins_f.end(), ins_dec.begin(),
                            ins_dec.end(), std::inserter(f_ins_dec,
                            f_ins_dec.begin()));
      std::set_intersection(outs_f.begin(), outs_f.end(), outs_dec.begin(),
                            outs_dec.end(),
                            std::inserter(f_outs_dec, f_outs_dec.begin()));
      std::stack<unsigned> todo;
      for (unsigned i = 0; i < dst_vect.size(); ++i)
      {
        if (done_right[i])
          continue;
        auto f2 = dst_vect[i];
        auto [f2_ins, f2_outs] = form2props.aps_of(f2);
        if (are_intersecting(f2_ins, f_ins_dec)
          || are_intersecting(f2_outs, f_outs_dec))
        {
          todo.push(i);
          right_res = formula::And({right_res, f2});
          done_right[i] = true;
        }
      }
      while (!todo.empty())
      {
        auto right_index = todo.top();
        todo.pop();
        bip(dst_vect[right_index], dst_vect, src_vect, ins_dec, outs_dec,
            right_res, left_res, done_right, done_left);
      }
    };

    std::vector<bool> done_ass(assumptions_split.size(), false),
        done_gua(guarantees_split.size(), false);
    for (unsigned i = 0; i < assumptions_split.size(); ++i)
      {
        if (done_ass[i])
          continue;
        done_ass[i] = true;
        auto &ass = assumptions_split[i];
        std::set<formula> left_aps = form2props.aps_of(ass).first;
        // If an assumption hasn't any decRelProp, it is considered as
        // a free assumption.
        if (!are_intersecting(left_aps, decRelProps_ins))
          free_assumptions = formula::And({free_assumptions, ass});
        else
          {
            auto left = formula::tt(), right = formula::tt();
            bip(ass, assumptions_split, guarantees_split, decRelProps_ins,
                decRelProps_outs, left, right, done_ass, done_gua);
            specs.push_back({left, right});
          }
      }

    for (unsigned i = 0; i < guarantees_split.size(); ++i)
      if (!done_gua[i])
        specs.push_back({formula::tt(), guarantees_split[i]});

    if (!free_assumptions.is_tt())
      for (auto &sp : specs)
        sp.first = formula::And({sp.first, free_assumptions});
    std::vector<formula> elems;
    for (auto &[ass, gua] : specs)
      {
        auto new_impl = formula::Implies(ass, gua);
        elems.push_back(new_impl);
      }
    return formula::And(elems);
  }

  static formula
  extract_and(const formula& f, const std::set<std::string>& outs,
              bool can_extract_impl, formula_2_inout_props& form2props)
  {
    if (f.is(op::And))
      {
        std::vector<formula> children;
        for (auto fi : f)
          children.push_back(
            extract_and(fi, outs, false, form2props));
        return formula::And(children);
      }
    if (f.is(op::Not))
    {
      auto child = extract_and(f[0], outs, false, form2props);
      // ¬(⋀¬xᵢ) ≡ ⋁xᵢ
      if (child.is(op::And))
        {
          bool ok = true;
          for (auto sub : child)
            if (!(sub.is(op::Not)))
              {
                ok = false;
                break;
              }
          if (ok)
            {
              std::vector<formula> children;
              for (auto fi : child)
                children.push_back(
                  extract_and(formula::Not(fi), outs, false, form2props));
              return formula::Or(children);
            }
        }
      // ¬Fφ ≡ G¬φ
      if (child.is(op::F))
        {
          // The result can be G(And).
          return
            extract_and(
              formula::G(
                extract_and(formula::Not(child[0]), outs, false, form2props)),
              outs, false, form2props);
        }
      // ¬(φ→ψ) ≡ φ ∧ ¬ψ
      else if (child.is(op::Implies))
        {
          return formula::And({
            extract_and(child[0], outs, false, form2props),
            extract_and(formula::Not(child[1]), outs, false, form2props)
          });
        }
      // ¬(φ ∨ ψ) ≡ ¬φ ∧ ¬ψ
      else if (child.is(op::Or))
        {
          std::vector<formula> children;
          for (auto fi : child)
            children.push_back(
              extract_and(formula::Not(fi), outs, false, form2props));
          return formula::And(children);
        }
    }
    // G(⋀φᵢ) = ⋀(G(φᵢ))
    // X(⋀φᵢ) = ⋀(X(φᵢ))
    if (f.is(op::G, op::X))
      {
        auto child_ex = extract_and(f[0], outs, false, form2props);
        if (child_ex.is(op::And))
          {
            std::vector<formula> children;
            const auto f_kind = f.kind();
            for (auto fi : child_ex)
              children.push_back(
                extract_and(
                  formula::unop(f_kind, fi), outs, false, form2props));
            return formula::And(children);
          }
      }
    // ⋀φᵢ U ψ ≡ ⋀(φᵢ U ψ)
    if (f.is(op::U))
      {
        auto left_child_ex = extract_and(f[0], outs, false, form2props);
        if (left_child_ex.is(op::And))
          {
            std::vector<formula> children;
            for (auto fi : left_child_ex)
              children.push_back(formula::U(fi, f[1]));
            return formula::And(children);
          }
      }
    if (f.is(op::Implies))
      {
        auto right_extr = extract_and(f[1], outs, false, form2props);
        auto left_extr = extract_and(f[0], outs, false, form2props);
        // φ → (⋀ψᵢ) ≡ ⋀(φ → ψᵢ)
        if (!(left_extr.is(op::And)))
          {
            if (right_extr.is(op::And))
              {
                std::vector<formula> children;
                for (auto fi : right_extr)
                  children.push_back(formula::Implies(left_extr, fi));
                return formula::And(children);
              }
          }
        // ⋀φᵢ → ⋀ψᵢ
        else if (right_extr.is(op::And) && can_extract_impl)
          {
            auto extr_f = formula::Implies(left_extr, right_extr);
            return split_implication(extr_f, outs, form2props);
          }
      }
    return f;
  }

}

namespace spot
{
  std::pair<std::vector<formula>, std::vector<std::set<formula>>>
  split_independent_formulas(formula f, const std::vector<std::string>& outs)
  {
    formula_2_inout_props form2props(outs);
    std::set<std::string> outs_set(outs.begin(), outs.end());

    f = extract_and(f, outs_set, true, form2props);
    if (!(f.is(op::And)))
      return { {f}, { form2props.aps_of(f).second } };
    // Atomics prop of children
    std::vector<std::set<formula>> children_outs;
    // Independent formulas
    std::vector<formula> res;
    // And the appearing propositions
    std::vector<std::set<formula>> res_outs;
    // For each conj, we calculate the set of output AP
    for (auto child : f)
      children_outs.push_back(form2props.aps_of(child).second);
    unsigned nb_children = f.size();
    // flag to test if a conj is in a "class"
    std::vector<bool> children_class(nb_children, false);
    // The first element not in a class
    unsigned first_free = 0;
    std::stack<unsigned> todo;
    while (first_free < nb_children)
      {
        todo.emplace(first_free);
        std::vector<formula> current_and;
        std::set<formula> current_outs;
        while (!todo.empty())
          {
            auto current = todo.top();
            todo.pop();
            children_class[current] = true;
            current_and.push_back(f[current]);
            current_outs.insert(children_outs[current].begin(),
                                children_outs[current].end());
            for (unsigned i = 0; i < nb_children; ++i)
              if (!children_class[i]
                    && are_intersecting(children_outs[current],
                                      children_outs[i]))
                {
                  todo.emplace(i);
                  children_class[i] = true;
                }
          }
        auto elem = formula::And(current_and);
        res.push_back(elem);
        res_outs.push_back(current_outs);

        while (first_free < nb_children && children_class[first_free])
          ++first_free;
      }
    assert(res.size() == res_outs.size());

    return {res, res_outs};
  }

  std::pair<std::vector<formula>, std::vector<std::set<formula>>>
  split_independent_formulas(const std::string& f,
                             const std::vector<std::string>& outs)
  {
    return split_independent_formulas(parse_formula(f), outs);
  }

  bool
  solve_game(twa_graph_ptr arena, synthesis_info& gi)
  {
    stopwatch sw;
    if (gi.bv)
      sw.start();
    if (gi.verbose_stream)
      {
        *(gi.verbose_stream) << "solving game with acceptance: ";
        std::string name = arena->acc().name();
        if (!name.empty())
          *(gi.verbose_stream) << name;
        else
          *(gi.verbose_stream) << arena->get_acceptance();
        *(gi.verbose_stream) << '\n';
      }
    bool res = solve_game(arena);
    if (gi.bv)
      gi.bv->solve_time += sw.stop();
    if (gi.verbose_stream)
      *(gi.verbose_stream) << "game solved in "
                           << gi.bv->solve_time << " seconds\n";
    return res;
  }

  namespace
  {
    const std::string in_mark_s("__AP_IN__");
    const std::string out_mark_s("__AP_OUT__");
  }

  game_relabeling_map
  partitioned_game_relabel_here(twa_graph_ptr& arena,
                                bool relabel_env,
                                bool relabel_play,
                                bool split_env,
                                bool split_play,
                                unsigned max_letter,
                                unsigned max_letter_mult)
  {
    if (!arena)
      throw std::runtime_error("arena is null.");
    auto& arena_r = *arena;

    const region_t& sp = get_state_players(arena);
    bdd all_ap = arena->ap_vars();

    if (std::find_if(arena->ap().cbegin(), arena->ap().cend(),
                     [](const auto& ap)
                       {
                         return ap.ap_name() == out_mark_s
                                || ap.ap_name() == in_mark_s;
                       }) != arena->ap().cend())
      throw std::runtime_error("partitioned_game_relabel_here(): "
                               "You can not use "
                               + in_mark_s + " or " + out_mark_s +
                               " as propositions if relabeling.");

    bdd out_mark = bdd_ithvar(arena_r.register_ap(out_mark_s));
    bdd in_mark = bdd_ithvar(arena_r.register_ap(in_mark_s));

    bdd outs = get_synthesis_outputs(arena) & out_mark;
    bdd ins = bdd_exist(all_ap, outs) & in_mark;

    for (auto& e : arena_r.edges())
      e.cond = e.cond & (sp[e.src] ? out_mark : in_mark);

    game_relabeling_map res;

    if (relabel_env)
      res.env_map
        = partitioned_relabel_here(arena, split_env, max_letter,
                                   max_letter_mult, ins, "__nv_in");
    if (relabel_play)
      res.player_map
        = partitioned_relabel_here(arena, split_play, max_letter,
                                   max_letter_mult, outs, "__nv_out");
    return res;
  }

  void
  relabel_game_here(twa_graph_ptr& arena,
                    game_relabeling_map& rel_maps)
  {
    if (!arena)
      throw std::runtime_error("arena is null.");
    auto& arena_r = *arena;

    // Check that it was partitioned_game_relabel_here
    if (!((std::find_if(arena->ap().cbegin(), arena->ap().cend(),
                        [](const auto& ap)
                          { return ap.ap_name() == out_mark_s; })
             != arena->ap().cend())
          && (std::find_if(arena->ap().cbegin(), arena->ap().cend(),
                           [](const auto& ap)
                             { return ap.ap_name() == in_mark_s; }))
               != arena->ap().cend()))
      throw std::runtime_error("relabel_game_here(): " +
                               in_mark_s + " or " + out_mark_s +
                               " not registered with arena. "
                               "Not relabeled?");

    if (!rel_maps.env_map.empty())
      relabel_here(arena, &rel_maps.env_map);
    if (!rel_maps.player_map.empty())
      relabel_here(arena, &rel_maps.player_map);

    bdd dummy_ap = bdd_ithvar(arena_r.register_ap(in_mark_s))
                   & bdd_ithvar(arena_r.register_ap(out_mark_s));

    for (auto& e : arena_r.edges())
      e.cond = bdd_exist(e.cond, dummy_ap);

    arena_r.unregister_ap(arena_r.register_ap(in_mark_s));
    arena_r.unregister_ap(arena_r.register_ap(out_mark_s));

    return;
  }

} // spot
