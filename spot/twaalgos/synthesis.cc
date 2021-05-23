// -*- coding: utf-8 -*-
// Copyright (C) 2020 Laboratoire de Recherche et
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

#include <spot/tl/apcollect.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/synthesis.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/twa/fwd.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/complete.hh>
#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/game.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/minimize.hh>
#include <spot/twaalgos/parity.hh>
#include <spot/twaalgos/toparity.hh>
#include <spot/twaalgos/sbacc.hh>
#include <spot/twaalgos/sepsets.hh>
#include <spot/twa/bddprint.hh>
#include <spot/tl/parse.hh>
#include <spot/misc/timer.hh>

#include <algorithm>
#include <string>
#include <queue>

#define KEEP_STRAT_UNSPLIT


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
  // We define a order between the edges to avoid creating multiple
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

  static twa_graph_ptr
  ntgba2dpa(const twa_graph_ptr &split, bool force_sbacc)
  {
    // if the input automaton is deterministic, degeneralize it to be sure to
    // end up with a parity automaton
    auto dpa = tgba_determinize(degeneralize_tba(split),
                                      false, true, true, false);
    dpa->merge_edges();
    if (force_sbacc)
      dpa = sbacc(dpa);
    reduce_parity_here(dpa, true);
    change_parity_here(dpa, parity_kind_max,
                             parity_style_odd);
    assert((
               [&dpa]() -> bool {
                 bool max, odd;
                 dpa->acc().is_parity(max, odd);
                 return max && odd;
               }()));
    assert(is_deterministic(dpa));
    return dpa;
  }

  static void
  minimize_strategy_here(twa_graph_ptr& strat, option_map& opt)
  {
    strat->set_acceptance(acc_cond::acc_code::t());
    unsigned simplification_level =
        opt.get("minimization-level", 1);
    // 0 -> No minimization
    // 1 -> Regular monitor minimization
    // 2 -> Mealy minimization based on language inclusion
    // 3 -> Exact mealy minimization
    // 4 -> Monitor min then exact minimization
    // 5 -> Mealy minimization based on language inclusion then exact
    //      minimization
    bdd *obddptr = strat->get_named_prop<bdd>("synthesis-outputs");
    assert(obddptr);
    bdd obdd = *obddptr;
    if (simplification_level > 0 && simplification_level < 3)
      strat->set_named_prop("synthesis-outputs", nullptr);
    switch (simplification_level)
    {
      case 0:
        return;
      case 1:
        {
          minimize_mealy_fast_here(strat, true);
          break;
        }
      case 2:
        {
          minimize_mealy_fast_here(strat, false);
          break;
        }
      case 3:
        {
          strat = minimize_mealy(strat, -1);
          break;
        }
      case 4:
        {
          strat = minimize_mealy(strat, 0);
          break;
        }
      case 5:
        {
          strat = minimize_mealy(strat, 1);
          break;
        }
      default:
          throw std::runtime_error("Unknown minimization option");
    }
    opt.report_unused_options();

    strat->set_named_prop("synthesis-outputs", new bdd(obdd));
    // restore_form(strat, *new_bdd);
//    std::cout << "After \n";
//    print_hoa(std::cout, strat) << '\n';
    // print_hoa(std::cout, copy) << '\n';
  }
}

namespace spot
{
  std::ostream& operator<<(std::ostream& os, solver s)
  {
    switch (s)
    {
    case (solver::DET_SPLIT):
      os << "ds";
      break;
    case (solver::SPLIT_DET):
      os << "sd";
      break;
    case (solver::DPA_SPLIT):
      os << "ps";
      break;
    case (solver::LAR):
      os << "lar";
      break;
    case (solver::LAR_OLD):
      os << "lar.old";
      break;
    }
    return os;
  }

  std::ostream&
  operator<<(std::ostream& os, const game_info& gi)
  {
    os << "force sbacc: " << gi.force_sbacc << '\n'
      << "solver: " << gi.s << '\n'
      << (gi.verbose_stream ? "Is verbose\n" : "Is not verbose\n");
    return os;
  }


  twa_graph_ptr
  split_2step(const const_twa_graph_ptr& aut,
              const bdd& output_bdd, bool complete_env,
              bool do_simplify)
  {
    auto split = make_twa_graph(aut->get_dict());
    split->copy_ap_of(aut);
    split->copy_acceptance_of(aut);
    split->new_states(aut->num_states());
    split->set_init_state(aut->get_init_state_number());
    split->set_named_prop<bdd>("synthesis-output", new bdd(output_bdd));

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

    // a sort of hash-map for all new intermediate states
    std::unordered_multimap<size_t, unsigned> env_hash;
    env_hash.reserve((int) 1.5 * aut->num_states());
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
    auto get_sink_con_state = [&split]()
      {
        static unsigned sink_con=0;
        if (SPOT_UNLIKELY(sink_con == 0))
          sink_con = split->new_state();
        return sink_con;
      };

    // Loop over all states
    for (unsigned src = 0; src < aut->num_states(); ++src)
      {
        env_edge_hash.clear();
        e_cache.clear();

        auto out_cont = aut->out(src);
        // Short-cut if we do not want to
        // split the edges of nodes that have
        // a single outgoing edge
        if (do_simplify
            && (++out_cont.begin()) == out_cont.end())
          {
            // "copy" the edge
            const auto& e = *out_cont.begin();
            split->new_edge(src, e.dst, e.cond, e.acc);
            // Check if it needs to be completed
            if (complete_env)
              {
                bdd missing = bddtrue - bdd_exist(e.cond, output_bdd);
                if (missing != bddfalse)
                  split->new_edge(src, get_sink_con_state(), missing);
              }
            // We are done for this state
            continue;
          }

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

        while (all_letters != bddfalse)
          {
            bdd one_letter = bdd_satoneset(all_letters, support, bddtrue);
            all_letters -= one_letter;

            dests.clear();
            for (const auto& e_info : e_cache)
              // implies is faster than and
              if (bdd_implies(one_letter, e_info.einsup.first))
                {
                  e_info.econdout =
                      bdd_appex(e_info.econd, one_letter,
                                bddop_and, input_bdd);
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
                unsigned i = it_h->second;
                auto out = split->out(i);
                if (std::equal(out.begin(), out.end(),
                               dests.begin(), dests.end(),
                               [](const twa_graph::edge_storage_t& x,
                                  const e_info_t* y)
                               {
                                 return   x.dst == y->dst
                                          &&  x.acc == y->acc
                                          &&  x.cond.id() == y->econdout.id();
                               }))
                  {
                    to_add = false;
                    auto it = env_edge_hash.find(i);
                    if (it != env_edge_hash.end())
                      it->second.second |= one_letter;
                    else
                      env_edge_hash.emplace(i,
                          eeh_t(split->new_edge(src, i, bddtrue), one_letter));
                    break;
                  }
              }

            if (to_add)
              {
                unsigned d = split->new_state();
                unsigned n_e = split->new_edge(src, d, bddtrue);
                env_hash.emplace(h, d);
                env_edge_hash.emplace(d, eeh_t(n_e, one_letter));
                for (const auto &t: dests)
                  split->new_edge(d, t->dst, t->econdout, t->acc);
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
    std::vector<bool>* owner =
        new std::vector<bool>(split->num_states(), false);
    // All "new" states belong to the player
    std::fill(owner->begin()+aut->num_states(), owner->end(), true);
    split->set_named_prop("state-player", owner);
    // Done
    return split;
  }

  twa_graph_ptr
  unsplit_2step(const const_twa_graph_ptr& aut)
  {
    constexpr unsigned unseen_mark = std::numeric_limits<unsigned>::max();

    twa_graph_ptr out = make_twa_graph(aut->get_dict());
    out->copy_acceptance_of(aut);
    out->copy_ap_of(aut);

    // split_2step is not guaranteed to produce
    // states that alternate between env and player do to do_simplify
    auto owner_ptr = aut->get_named_prop<std::vector<bool>>("state-player");
    if (!owner_ptr)
      throw std::runtime_error("unsplit requires the named prop "
                               "state-player as set by split_2step");

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
          {
            // if the dst is also owned env
            if (!(*owner_ptr)[i.dst])
              {
                // This can only happen if there is only
                // one outgoing edges for cur
                assert(([&aut, cur]()->bool
                          {
                            auto out_cont = aut->out(cur);
                            return (++(out_cont.begin()) == out_cont.end());
                          })());
                if (!seen(i.dst))
                  todo.push_back(i.dst);
                out->new_edge(cur_m, map_s(i.dst), i.cond, i.acc);
                continue; // Done with cur
              }
            for (const auto& o : aut->out(i.dst))
              {
                if (!seen(o.dst))
                  todo.push_back(o.dst);
                out->new_edge(cur_m, map_s(o.dst),
                              i.cond & o.cond, i.acc | o.acc);
              }
          }
      }
    out->set_init_state(map_s(aut->get_init_state_number()));
//    out->merge_edges();
//    out->merge_states();
    // Try to set outputs
    if (bdd* outptr = aut->get_named_prop<bdd>("synthesis-outputs"))
      out->set_named_prop("synthesis-outputs", new bdd(*outptr));
    return out;
  }

//  spot::twa_graph_ptr
//  apply_strategy(const spot::twa_graph_ptr& arena,
//                 bool unsplit, bool keep_acc)
//  {
//    std::vector<bool>* w_ptr =
//      arena->get_named_prop<std::vector<bool>>("state-winner");
//    std::vector<unsigned>* s_ptr =
//      arena->get_named_prop<std::vector<unsigned>>("strategy");
//    std::vector<bool>* sp_ptr =
//      arena->get_named_prop<std::vector<bool>>("state-player");
//
//    if (!w_ptr || !s_ptr || !sp_ptr)
//      throw std::runtime_error("Arena missing state-winner, strategy "
//                               "or state-player");
//
//    if (!(w_ptr->at(arena->get_init_state_number())))
//      throw std::runtime_error("Player does not win initial state, strategy "
//                               "is not applicable");
//
//    std::vector<bool>& w = *w_ptr;
//    std::vector<unsigned>& s = *s_ptr;
//
//    auto strat_aut = spot::make_twa_graph(arena->get_dict());
//    strat_aut->copy_ap_of(arena);
//    if (keep_acc)
//      strat_aut->copy_acceptance_of(arena);
//
//    constexpr unsigned unseen_mark = std::numeric_limits<unsigned>::max();
//    std::vector<unsigned> todo{arena->get_init_state_number()};
//    std::vector<unsigned> pg2aut(arena->num_states(), unseen_mark);
//    strat_aut->set_init_state(strat_aut->new_state());
//    pg2aut[arena->get_init_state_number()] =
//        strat_aut->get_init_state_number();
//
//    while (!todo.empty())
//      {
//        unsigned v = todo.back();
//        todo.pop_back();
//
//        // Check if a simplification occurred
//        // in the aut and we have env -> env
//
//        // Env edge -> keep all
//        for (auto &e1: arena->out(v))
//          {
//            assert(w.at(e1.dst));
//            // Check if a simplification occurred
//            // in the aut and we have env -> env
//            if (!(*sp_ptr)[e1.dst])
//              {
//                assert(([&arena, v]()
//                         {
//                           auto out_cont = arena->out(v);
//                           return (++(out_cont.begin()) == out_cont.end());
//                         })());
//                // If so we do not need to unsplit
//                if (pg2aut[e1.dst] == unseen_mark)
//                  {
//                    pg2aut[e1.dst] = strat_aut->new_state();
//                    todo.push_back(e1.dst);
//                  }
//                // Create the edge
//                strat_aut->new_edge(
//                              pg2aut[v],
//                              pg2aut[e1.dst],
//                              e1.cond,
//                              keep_acc ? e1.acc : spot::acc_cond::mark_t({}));
//                // Done
//                continue;
//              }
//
//            if (!unsplit)
//              {
//                if (pg2aut[e1.dst] == unseen_mark)
//                  pg2aut[e1.dst] = strat_aut->new_state();
//                strat_aut->new_edge(
//                              pg2aut[v], pg2aut[e1.dst], e1.cond,
//                              keep_acc ? e1.acc : spot::acc_cond::mark_t({}));
//              }
//            // Player strat
//            auto &e2 = arena->edge_storage(s[e1.dst]);
//            if (pg2aut[e2.dst] == unseen_mark)
//              {
//                pg2aut[e2.dst] = strat_aut->new_state();
//                todo.push_back(e2.dst);
//              }
//            if (!unsplit)
//              {
//                auto eit = strat_aut->out(pg2aut[e1.dst]);
//                if (eit.begin()==eit.end())
//                  strat_aut->new_edge(
//                    pg2aut[e1.dst],
//                    pg2aut[e2.dst],
//                    e2.cond,
//                    keep_acc ? e2.acc
//                             : spot::acc_cond::mark_t({}));
//              }
//            else
//              strat_aut->new_edge(
//                            pg2aut[v],
//                            pg2aut[e2.dst],
//                            (e1.cond & e2.cond),
//                            keep_acc ? (e1.acc | e2.acc)
//                                     : spot::acc_cond::mark_t({}));
//          }
//      }
//
//      if (bdd* obdd = arena->get_named_prop<bdd>("synthesis-outputs"))
//        strat_aut->set_named_prop("synthesis-outputs", new bdd(*obdd));
//      else
//        throw std::runtime_error("Missing named property "
//                                 "\"synthesis-outputs\".\n");
//
//    // If no unsplitting is demanded, it remains a two-player arena
//    // We do not need to track winner as this is a
//    // strategy automaton
//    if (!unsplit)
//      {
//        const std::vector<bool>& sp_pg = * sp_ptr;
//        std::vector<bool> sp_aut(strat_aut->num_states());
//        std::vector<unsigned> str_aut(strat_aut->num_states());
//        for (unsigned i = 0; i < arena->num_states(); ++i)
//          {
//            if (pg2aut[i] == unseen_mark)
//              // Does not appear in strategy
//              continue;
//            sp_aut[pg2aut[i]] = sp_pg[i];
//            str_aut[pg2aut[i]] = s[i];
//          }
//        strat_aut->set_named_prop(
//            "state-player", new std::vector<bool>(std::move(sp_aut)));
//        strat_aut->set_named_prop(
//            "state-winner", new std::vector<bool>(strat_aut->num_states(),
//                                                  true));
//        strat_aut->set_named_prop(
//            "strategy", new std::vector<unsigned>(std::move(str_aut)));
//      }
//    return strat_aut;
//  }

  // Improved apply strat, that reduces the number of edges/states
  // while keeping the needed edge-properties
  // Note, this only deals with deterministic strategies
  // Note, assumes that env starts playing
  spot::twa_graph_ptr
  apply_strategy(const spot::twa_graph_ptr& arena,
                 bool unsplit, bool keep_acc)
  {
    std::vector<bool>* w_ptr =
        arena->get_named_prop<std::vector<bool>>("state-winner");
    std::vector<unsigned>* s_ptr =
        arena->get_named_prop<std::vector<unsigned>>("strategy");
    std::vector<bool>* sp_ptr =
        arena->get_named_prop<std::vector<bool>>("state-player");
    bdd* syntouts =
        arena->get_named_prop<bdd>("synthesis-outputs");

    if (!w_ptr || !s_ptr || !sp_ptr)
      throw std::runtime_error("Arena missing state-winner, strategy "
                               "or state-player");

    if (!(w_ptr->at(arena->get_init_state_number())))
      throw std::runtime_error("Player does not win initial state, strategy "
                               "is not applicable");

    assert((sp_ptr->at(arena->get_init_state_number()) == false)
           && "Env needs to have first turn!");

    assert(std::all_of(arena->edges().begin(), arena->edges().end(),
           [&sp_ptr](const auto& e){ return sp_ptr->at(e.src) != sp_ptr->at(e.dst); }));

    auto strat_split = spot::make_twa_graph(arena->get_dict());
    strat_split->copy_ap_of(arena);
    if (keep_acc)
      strat_split->copy_acceptance_of(arena);

    std::stack<unsigned> todo;
    todo.push(arena->get_init_state_number());

    struct dca{
      unsigned dst;
      int condvar;
      acc_cond::mark_t acc;
    };
    struct dca_hash
    {
      size_t operator()(const dca& d) const noexcept
      {
        size_t r = d.dst;
        r <<= 32;
        r += (size_t) d.condvar;
        return r ^ d.acc.hash();
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
    std::unordered_map<dca,
                       unsigned,
                       dca_hash,
                       dca_equal> p_map; //env dst + player cond + acc -> p state

    constexpr unsigned unseen_mark = std::numeric_limits<unsigned>::max();
    std::vector<unsigned> env_map(arena->num_states(), unseen_mark);
    strat_split->set_init_state(strat_split->new_state());
    env_map[arena->get_init_state_number()] =
        strat_split->get_init_state_number();

    auto get_sel = [&](unsigned s)
    {
      if (env_map[s] == unseen_mark)
        env_map[s] = strat_split->new_state();
      return env_map[s];
    };

    // local dst
    auto get_spl = [&](unsigned dst, const bdd& cond, acc_cond::mark_t acc)
    {
      dca d{dst, cond.id(), acc};
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
          const auto& e_strat = arena->edge_storage((*s_ptr)[e_env.dst]);
          // the target
          if (env_map[e_strat.dst] == unseen_mark)
            todo.push(e_strat.dst);
          unsigned dst_envl = get_sel(e_strat.dst);
          // The new env edge, player is is constructed automatically
          strat_split->new_edge(src_envl,
                                get_spl(dst_envl, e_strat.cond,
                                        keep_acc ? e_strat.acc
                                                 : acc_cond::mark_t({})),
                                e_env.cond,
                                keep_acc ? e_env.acc
                                         : acc_cond::mark_t({}));
        }
      }
    // Specialized merge
    std::vector<bool> sp(strat_split->num_states(), false);
    for (const auto& p : p_map)
      sp[p.second] = true;

    // Sorting edges in place
    auto comp_edge = [](const auto& e1, const auto& e2)
    {
      return std::tuple(e1.dst, e1.acc, e1.cond.id())
             < std::tuple(e2.dst, e2.acc, e2.cond.id());
    };
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
                       [&](const auto& e){return strat_split->edge_number(e);});
        std::sort(edge_nums.begin(), edge_nums.end(),
                  [&](unsigned ne1, unsigned ne2)
                  {return comp_edge(strat_split->edge_storage(ne1),
                                    strat_split->edge_storage(ne2));});
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

//    print_hoa(std::cout, strat_split) << "\n";

    const unsigned n_sstrat = strat_split->num_states();
    std::vector<unsigned> remap(n_sstrat, -1u);
    bool changed_any;
    std::vector<unsigned> to_check;
    to_check.reserve(n_sstrat);
    // First iteration -> all env states are candidates
    for (unsigned i = 0; i < n_sstrat; ++i)
      if (!sp[i])
        to_check.push_back(i);

    while (true)
    {
      changed_any = false;
      std::for_each(to_check.begin(), to_check.end(),
                    [&](unsigned s){sort_edges_of(s); merge_edges_of(s);});
      // Check if we can merge env states
      for (unsigned s1 : to_check)
        for (unsigned s2 = 0; s2 < n_sstrat; ++s2)
          {
            if (sp[s2] || (s1 == s2))
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

//      std::for_each(remap.begin(), remap.end(), [](auto e){std::cout << e << " ";});
//      std::cout << std::endl;

      if (!changed_any)
        break;
      // Redirect changed targets and set possibly mergeable states
      to_check.clear();
      for (auto& e : strat_split->edges())
        if (remap[e.dst] != -1u)
          {
            e.dst = remap[e.dst];
            to_check.push_back(e.src);
            assert(sp[e.src]);
          }

      // Now check the player states
      // We can skip sorting -> only one edge
      // todo change when multistrat
      changed_any = false;
      for (unsigned s1 : to_check)
        for (unsigned s2 = 0; s2 < n_sstrat; ++s2)
          {
            if (!sp[s2] || (s1 == s2))
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

//      std::for_each(remap.begin(), remap.end(), [](auto e){std::cout << e << " ";});
//      std::cout << std::endl;

      if (!changed_any)
        break;
      // Redirect changed targets and set possibly mergeable states
      to_check.clear();
      for (auto& e : strat_split->edges())
        if (remap[e.dst] != -1u)
          {
            e.dst = remap[e.dst];
            to_check.push_back(e.src);
            assert(!sp[e.src]);
          }
    }

//    print_hoa(std::cout, strat_split) << std::endl;

    // Defrag and alternate
    if (remap[strat_split->get_init_state_number()] != -1u)
      strat_split->set_init_state(remap[strat_split->get_init_state_number()]);
    unsigned st = 0;
    for (auto& s: remap)
      if (s == -1U)
        s = st++;
      else
        s = -1U;

    strat_split->defrag_states(std::move(remap), st);

//    unsigned n_old;
//    do
//    {
//      n_old = strat_split->num_edges();
//      strat_split->merge_edges();
//      strat_split->merge_states();
//    } while (n_old != strat_split->num_edges());

    alternate_players(strat_split, false, false);
//    print_hoa(std::cout, strat_split) << std::endl;
    // What we do now depends on whether we unsplit or not
    if (unsplit)
      {
        auto final = unsplit_2step(strat_split);
        if (syntouts)
          final->set_named_prop("synthesis-outputs", new bdd(*syntouts));
        return final;
      }
    // Keep the splitted version
    strat_split->set_named_prop(
        "state-winner", new std::vector<bool>(strat_split->num_states(),
                                              true));
    std::vector<unsigned> new_strat(strat_split->num_states(), -1u);
    sp_ptr =
        strat_split->get_named_prop<std::vector<bool>>("state-player");
    for (unsigned i = 0; i < strat_split->num_states(); ++i)
      {
        if (!(*sp_ptr)[i])
          continue;
        new_strat[i] = strat_split->edge_number(*strat_split->out(i).begin());
      }
    strat_split->set_named_prop(
        "strategy", new std::vector<unsigned>(std::move(new_strat)));
    if (syntouts)
      strat_split->set_named_prop("synthesis-outputs", new bdd(*syntouts));
    return strat_split;
  }

  static translator
  create_translator(option_map& extra_options, solver sol,
                    const bdd_dict_ptr& dict)
  {
    for (auto&& p : std::vector<std::pair<const char*, int>>
                      {{"simul", 0},
                       {"ba-simul", 0},
                       {"det-simul", 0},
                       {"tls-impl", 1},
                       {"wdba-minimize", 2}})
      extra_options.set(p.first, extra_options.get(p.first, p.second));

    translator trans(dict, &extra_options);
    // extra_options.report_unused_options();
    switch (sol)
    {
    case solver::LAR:
      SPOT_FALLTHROUGH;
    case solver::LAR_OLD:
      trans.set_type(postprocessor::Generic);
      trans.set_pref(postprocessor::Deterministic);
      break;
    case solver::DPA_SPLIT:
      trans.set_type(postprocessor::ParityMaxOdd);
      trans.set_pref(postprocessor::Deterministic | postprocessor::Colored);
      break;
    case solver::DET_SPLIT:
      SPOT_FALLTHROUGH;
    case solver::SPLIT_DET:
      break;
    }
    return trans;
  }

  twa_graph_ptr
  create_game(const formula& f,
              const std::set<std::string>& all_outs,
              option_map& extra_opt,
              game_info& gi)
  {
    auto trans = create_translator(extra_opt, gi.s, gi.dict);
    // Shortcuts
    auto& bv = gi.bv;
    auto& vs = gi.verbose_stream;

    stopwatch sw;

    if (bv)
      sw.start();
    auto aut = trans.run(f);
    // TODO: += ?
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

    // Check for each ap that actually appears in the graph
    // whether its an in or out
    bdd ins = bddtrue;
    bdd outs = bddtrue;
    for (auto&& aap : aut->ap())
      {
        if (all_outs.count(aap.ap_name()) != 0)
          outs &= tobdd(aap.ap_name());
        else
          ins &= tobdd(aap.ap_name());
      }

    twa_graph_ptr dpa = nullptr;

    switch (gi.s)
    {
      case solver::DET_SPLIT:
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
        dpa = split_2step(tmp, outs, true, false);
        colorize_parity_here(dpa, true);
        if (bv)
          bv->split_time += sw.stop();
        if (vs)
          *vs << "split inputs and outputs done in " << bv->split_time
              << " seconds\nautomaton has "
              << tmp->num_states() << " states\n";
        break;
      }
      case solver::DPA_SPLIT:
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
        dpa = split_2step(aut, outs, true, false);
        colorize_parity_here(dpa, true);
        if (bv)
          bv->split_time += sw.stop();
        if (vs)
          *vs << "split inputs and outputs done in " << bv->split_time
              << " seconds\nautomaton has "
              << dpa->num_states() << " states\n";
        break;
      }
      case solver::SPLIT_DET:
      {
        sw.start();
        auto split = split_2step(aut, outs,
                                true, false);
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
        dpa->merge_states();
        if (bv)
          bv->paritize_time += sw.stop();
        if (vs)
          *vs << "simplification done\nDPA has "
              << dpa->num_states() << " states\n"
              << "determinization and simplification took "
              << bv->paritize_time << " seconds\n";
        // The named property "state-player" is set in split_2step
        // but not propagated by ntgba2dpa
        alternate_players(dpa);
        break;
      }
      case solver::LAR:
        SPOT_FALLTHROUGH;
      case solver::LAR_OLD:
      {
        if (bv)
          sw.start();
        if (gi.s == solver::LAR)
          {
            dpa = to_parity(aut);
            // reduce_parity is called by to_parity(),
            // but with colorization turned off.
            colorize_parity_here(dpa, true);
          }
        else
          {
            dpa = to_parity_old(aut);
            dpa = reduce_parity_here(dpa, true);
          }
        change_parity_here(dpa, parity_kind_max,
                                 parity_style_odd);
        if (bv)
          bv->paritize_time += sw.stop();
        if (vs)
          *vs << "LAR construction done in " << bv->paritize_time
              << " seconds\nDPA has "
              << dpa->num_states() << " states, "
              << dpa->num_sets() << " colors\n";

        if (bv)
          sw.start();
        dpa = split_2step(dpa, outs, true, false);
        colorize_parity_here(dpa, true);
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
           && "DPA has no state-players");
    dpa->set_named_prop<bdd>("synthesis-outputs", new bdd(outs));
    return dpa;
  }

  twa_graph_ptr
  create_game(const formula& f,
              const std::set<std::string>& all_outs)
  {
    option_map dummy1;
    game_info dummy2;
    return create_game(f, all_outs, dummy1, dummy2);
  }

  twa_graph_ptr
  create_game(const std::string& f,
              const std::set<std::string>& all_outs)
  {
    return create_game(parse_formula(f), all_outs);
  }

  twa_graph_ptr
  create_game(const std::string& f,
              const std::set<std::string>& all_outs,
              option_map& opt,
              game_info& gi)
  {
    return create_game(parse_formula(f), all_outs, opt, gi);
  }



  bool solve_game(twa_graph_ptr arena, game_info& gi)
  {
    // todo adapt to new interface
    stopwatch sw;
    if (gi.bv)
      sw.start();
    auto ret = solve_parity_game(arena);
    if (gi.bv)
      gi.bv->solve_time += sw.stop();
    if (gi.verbose_stream)
      *(gi.verbose_stream) << "parity game solved in "
                           << gi.bv->solve_time << " seconds\n";
    return ret;
  }

  bool
  solve_game(twa_graph_ptr arena)
  {
    game_info dummy1;
    return solve_game(arena, dummy1);
  }

  twa_graph_ptr
  create_strategy(twa_graph_ptr arena, option_map& opt, game_info& gi)
  {
    if (!arena)
      throw std::runtime_error("Arena can not be null");

    spot::stopwatch sw;

    if (gi.bv)
      sw.start();

    if (auto* sw = arena->get_named_prop<std::vector<bool>>("state-winner"))
      {
        if (not (*sw)[arena->get_init_state_number()])
          return nullptr;
      }
    else
      throw std::runtime_error("Arena has no named property "
                                "\"state-winner\". Game not solved?\n");

    // todo check what is more expensive:
    // minimizing unsplitted strategy or resplitting in aiger

    // Depending on the minimization we need it split or unsplit
    // 0 -> No minimization -> unsplit
    // 1 -> Regular monitor minimization -> unsplit
    // 2 -> Mealy minimization based on language inclusion -> unsplit
    // 3 -> Exact mealy minimization -> split
    // 4 -> Monitor min then exact minimization -> split
    // 5 -> Mealy minimization based on language inclusion
    //      then exact minimization -> split
    bool do_unsplit = opt.get("minimization-level", 1) < 3;
    twa_graph_ptr strat_aut = apply_strategy(arena, do_unsplit, false);

    strat_aut->prop_universal(true);
//    if (!do_unsplit)
//      {
//        unsigned n_old;
//        // todo this could be done in apply_strat
//        do
//          {
//            n_old = strat_aut->num_states();
//            strat_aut->merge_edges();
//            strat_aut->merge_states();
//          }while(n_old != strat_aut->num_states());
//        strat_aut->merge_edges();
//        alternate_players(strat_aut, false, false);
//      }
    minimize_strategy_here(strat_aut, opt);
    assert(do_unsplit
           || strat_aut->get_named_prop<std::vector<bool>>("state-player"));
    if (!do_unsplit)
      strat_aut = unsplit_2step(strat_aut);

    if (gi.bv)
      {
        gi.bv->strat2aut_time += sw.stop();
        gi.bv->nb_strat_states += strat_aut->num_states();
        gi.bv->nb_strat_edges += strat_aut->num_edges();
      }

    return strat_aut;
  }

  twa_graph_ptr
  create_strategy(twa_graph_ptr arena)
  {
    option_map dummy1;
    game_info dummy2;
    return create_strategy(arena, dummy1, dummy2);
  }

  // Test if f has an atomic proposition contained in aps (complement = false)
  // or in its complement.
  // static bool
  // share_props(formula& f, std::set<std::string> aps, bool complement)
  // {
  //   bool res = false;
  //   f.traverse(
  //     [&res, &aps, &complement](const formula& f)
  //     {
  //       if (!res)
  //         return true;
  //       if (f.is(op::ap))
  //       {
  //         if ((aps.find(f.ap_name()) == aps.end()) == complement)
  //           res = true;
  //         return true;
  //       }
  //       return false;
  //     }
  //   );
  //   return res;
  // }

  std::map<formula,
           std::pair<std::set<formula>, std::set<formula>>> ap_cache;

  static std::pair<std::set<formula>, std::set<formula>>
  aps_of(formula f, const std::set<std::string> &outs)
  {
    auto cache_value = ap_cache.find(f);
    if (cache_value != ap_cache.end())
      return cache_value->second;

    std::set<formula> ins_f, outs_f;
    f.traverse([&](const formula& f)
               {
                 if (f.is(op::ap))
                 {
                  if (outs.find(f.ap_name()) != outs.end())
                    outs_f.insert(f);
                  else
                    ins_f.insert(f);
                 }
                 return false;
               });
    std::pair<std::set<formula>, std::set<formula>> res({ins_f, outs_f});
    ap_cache.insert({f, res});
    return res;
  }

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
  }

  // Returns a strategy and a code:
  //  -1 : Unrealizable
  //  0 : Unknown
  //  1 : Realizable
  std::pair<twa_graph_ptr, int>
  try_create_strategy_from_simple(formula f,
                              const std::set<std::string>& output_aps,
                              option_map &extra_opt,
                              game_info &gi)
  {
    bool is_and = f.is(op::And);
    formula f_g, f_equiv;
    // Rewrite a conjunction as G(…) ∧ …
    if (is_and)
    {
      if (f.size() != 2)
        return {nullptr, 0};
      if (f[1].is(op::G))
        f = formula::And({f[1], f[0]});
      f_equiv = f[1];
      f_g = f[0];
    }
    else
      f_equiv = f;
    if (!f_equiv.is(op::Equiv))
      return {nullptr, 0};
    // TODO: game_info not updated
    auto trans = create_translator(extra_opt, gi.s, gi.dict);
    trans.set_type(postprocessor::Buchi);
    trans.set_pref(postprocessor::Deterministic | postprocessor::Complete);
    // TODO: Update gi.bv
    // auto &bv = gi.bv;
    stopwatch sw;
    if (gi.bv)
      sw.start();
    twa_graph_ptr res;

    formula left = f_equiv[0],
            right = f_equiv[1];

    auto [left_ins, left_outs] = aps_of(left, output_aps);
    auto [right_ins, right_outs] = aps_of(right, output_aps);

    bool has_left_outs = !left_outs.empty();
    bool has_left_ins = !left_ins.empty();
    bool has_right_outs = !right_outs.empty();
    bool has_right_ins = !right_ins.empty();

    // Try to rewrite the equivalence as f(b1) <-> f(b2) where b2 has not any
    // input
    if (has_right_ins)
    {
      std::swap(left, right);
      std::swap(has_left_ins, has_right_ins);
      std::swap(has_left_outs, has_right_outs);
      std::swap(left_ins, right_ins);
      std::swap(left_outs, right_outs);
    }
    // We need to have f(inputs) <-> f(outputs)
    if (has_right_ins || has_left_outs || !has_right_outs)
      return {nullptr, 0};

    bool right_bool = right[0][0].is_boolean();
    bool is_gf_bool_right = right.is({op::G, op::F}) && right_bool;
    bool is_fg_bool_right = right.is({op::F, op::G}) && right_bool;

    // Now we have to detect if we have persistence(ins/outs) <-> FG(outs)
    // or Büchi(ins/outs) <-> GF(outs).

    bool is_ok = ((is_gf_bool_right && left.is_syntactic_recurrence())
                || (is_fg_bool_right && left.is_syntactic_guarantee()));

    // TODO: game_info not updated
    if (is_ok)
    {
      auto trans = create_translator(extra_opt, gi.s, gi.dict);
      trans.set_type(postprocessor::Buchi);
      trans.set_pref(postprocessor::Deterministic | postprocessor::Complete);
      // TODO: Update gi.bv
      // auto &bv = gi.bv;
      auto right_sub = right[0][0];
      res = trans.run(left);
      for (auto& out : right_outs)
        res->register_ap(out.ap_name());
      if (!is_deterministic(res))
        return {nullptr, 0};
      bdd form_bdd = bddtrue;
      if (is_and)
      {
        bdd output_bdd = bddtrue;
        for (auto &out : output_aps)
          output_bdd &= bdd_ithvar(res->register_ap(out));
        form_bdd = formula_to_bdd(f_g[0], res->get_dict(), res);
        if (bdd_exist(form_bdd, output_bdd) != bddtrue)
          return {nullptr, 0};
      }
      bdd right_bdd = formula_to_bdd(right_sub, res->get_dict(), res);
      bdd neg_right_bdd = bdd_not(right_bdd);
      assert(right_ins.empty());
      const bool is_true = res->acc().is_t();
      scc_info si(res, scc_info_options::NONE);
      for (auto& e : res->edges())
      {
        // Here the part describing the outputs is based on the fact that
        // they must be seen infinitely often. As these edges are seen
        // finitely often, we can let the minimization choose the value.
        if (si.scc_of(e.src) == si.scc_of(e.dst))
        {
          if (e.acc || is_true)
            e.cond &= (right_bdd);
          else
            e.cond &= (neg_right_bdd);
        }
        // form_bdd has to be true all the time. So we cannot only do it
        // between SCCs.
        e.cond &= form_bdd;
        if (e.cond == bddfalse)
          return {nullptr, -1};
        e.acc = {};
      }

      bdd output_bdd = bddtrue;
      for (auto &out : output_aps)
        output_bdd &= bdd_ithvar(res->register_ap(out));

      res->set_named_prop("synthesis-outputs", new bdd(output_bdd));
      res->set_acceptance(acc_cond::acc_code::t());

      res->prop_complete(trival::maybe());
//      print_hoa(std::cout, res);
      // Take only the time if succesful, the rest should be almost "free"
      if (gi.bv)
        gi.bv->trans_time += sw.stop();//todo count states?
      return {res, 1};
    }
    return {nullptr, 0};
  }

  static std::pair<std::set<formula>, std::set<formula>>
  algo4(const std::vector<formula> &assumptions,
        const std::set<std::string> &outs)
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

    auto next_free = [&first_free, &assumptions, &outs, &ass_size, &done]()
    {
      while (first_free < ass_size)
      {
        if (done[first_free])
        {
          ++first_free;
          continue;
        }
        auto f = assumptions[first_free];
        auto [_, o] = aps_of(f, outs);
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
        auto [ins_current, outs_current] = aps_of(current_form, outs);
        result.first.insert(ins_current.begin(), ins_current.end());
        result.second.insert(outs_current.begin(), outs_current.end());
        for (unsigned i = 0; i < ass_size; ++i)
        {
          if (done[i])
            continue;
          auto other_form = assumptions[i];
          auto [ins_other, outs_other] = aps_of(other_form, outs);
          if (are_intersecting(ins_current, ins_other) ||
              are_intersecting(outs_other, outs_other))
            todo.push(i);
        }
      }
    }
    return result;
  }

  static formula
  split_implication(const formula &f, const std::set<std::string> &outs)
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
    // subspectifications
    auto decRelProps = algo4(assumptions, outs);
    auto &decRelProps_ins = decRelProps.first;
    auto &decRelProps_outs = decRelProps.second;
    // Assumptions that don't contain an atomic proposition in decRelProps
    auto free_assumptions = formula::tt();
    // The set of subspecifications described as [(assum, guar), (assum, guar)]
    std::vector<std::pair<formula, formula>> specs;
    // We merge two assumpt or guar. that share a proposition from decRelProps
    std::vector<formula> assumptions_split, guarantees_split;

    auto fus = [&](std::vector<formula> &forms, std::vector<formula> &res)
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
          auto [ins_f, outs_f] = aps_of(current_form, outs);
          std::set<formula> ins_f_dec, outs_f_dec;
          std::set_intersection(ins_f.begin(), ins_f.end(),
                                decRelProps_ins.begin(), decRelProps_ins.end(),
                                std::inserter(ins_f_dec, ins_f_dec.begin()));
          std::set_intersection(outs_f.begin(), outs_f.end(),
                                decRelProps_outs.begin(),
                                decRelProps_outs.end(),
                                std::inserter(ins_f_dec, ins_f_dec.begin()));
          for (unsigned i = 0; i < forms_size; ++i)
          {
            if (done[i])
              continue;
            auto [ins_i, outs_i] = aps_of(forms[i], outs);
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
    bip = [&outs, &bip](formula f, std::vector<formula> &src_vect,
                        std::vector<formula> &dst_vect,
                        std::set<formula> &ins_dec,
                        std::set<formula> &outs_dec,
                        formula &left_res, formula &right_res,
                        std::vector<bool> &done_left,
                        std::vector<bool> &done_right)
    {
      left_res = formula::And({left_res, f});
      auto [ins_f, outs_f] = aps_of(f, outs);
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
        auto [f2_ins, f2_outs] = aps_of(f2, outs);
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
      auto [left_aps, right_aps] = aps_of(ass, outs);
      // If an assumption hasn't any decRelProp, it is considered as
      // a free assumption.
      if (!are_intersecting(left_aps, decRelProps_ins))
      {
        free_assumptions = formula::And({free_assumptions, ass});
      }
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

  // Use LTL rewritings to have as many conjunctions as possible
  static formula
  extract_and(const formula& f, const std::set<std::string>& outs)
  {
    if (f.is(op::And))
    {
      std::vector<formula> children;
      for (auto fi : f)
        children.push_back(extract_and(fi, outs));
      return formula::And(children);
    }
    if (f.is(op::Not))
    {
      auto child = extract_and(f[0], outs);
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
            children.push_back(extract_and(formula::Not(fi), outs));
          return formula::Or(children);
        }
      }
      // ¬Fφ ≡ G¬φ
      if (child.is(op::F))
      {
        // The result can be G(And).
        auto f2 = formula::G(extract_and(formula::Not(child[0]), outs));
        // What ?
        return f2;
      }
      // ¬(φ→ψ) ≡ φ ∧ ¬ψ
      else if (child.is(op::Implies))
      {
        return formula::And({extract_and(child[0], outs),
                             extract_and(formula::Not(child[1]), outs)});
      }
      // ¬(φ ∨ ψ) ≡ ¬φ ∧ ¬ψ
      else if (child.is(op::Or))
      {
        std::vector<formula> children;
        for (auto fi : child)
          children.push_back(extract_and(formula::Not(fi), outs));
        return formula::And(children);
      }
    }
    // G(⋀φᵢ) = ⋀(G(φᵢ))
    // X(⋀φᵢ) = ⋀(X(φᵢ))
    if (f.is(op::G, op::X))
    {
      auto child_ex = extract_and(f[0], outs);
      if (child_ex.is(op::And))
      {
        std::vector<formula> children;
        const auto f_kind = f.kind();
        for (auto fi : child_ex)
          children.push_back(extract_and(formula::unop(f_kind, fi), outs));
        return formula::And(children);
      }
    }
    // ⋀φᵢ U ψ ≡ ⋀(φᵢ U ψ)
    if (f.is(op::U))
    {
      auto left_child_ex = extract_and(f[0], outs);
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
      auto right_extr = extract_and(f[1], outs);
      auto left_extr = extract_and(f[0], outs);
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
      else if (right_extr.is(op::And))
      {
        auto extr_f = formula::Implies(left_extr, right_extr);
        return split_implication(extr_f, outs);
      }
    }
    return f;
  }

  std::pair<std::vector<formula>, std::vector<std::set<formula>>>
  split_independant_formulas(formula f, const std::set<std::string>& outs)
  {
    f = extract_and(f, outs);
    if (!(f.is(op::And)))
    {
      auto [_, outs_f] = aps_of(f, outs);
      return
      {
        {f},
        {outs_f}
      };
    }
    // Atomics prop of children
    std::vector<std::set<formula>> children_outs;
    // Independent formulas
    std::vector<formula> res;
    // And the appearing propositions
    std::vector<std::set<formula>> res_outs;
    // For each conj, we calculate the set of output AP
    for (auto child : f)
      children_outs.push_back(aps_of(child, outs).second);
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
                && are_intersecting(children_outs[current], children_outs[i]))
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

    return { res, res_outs };
  }

} // spot