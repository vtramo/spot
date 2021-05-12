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
#include <spot/tl/hierarchy.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/synthesis.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/twa/fwd.hh>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/complete.hh>
#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/game.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/minimize.hh>
#include <spot/twaalgos/strength.hh>
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

namespace spot
{
//  static void
//  restore_form(const twa_graph_ptr &aut, bdd all_outputs)
//  {
//    bdd all_inputs = bddtrue;
//    for (const auto &ap : aut->ap())
//    {
//      int bddvar = aut->get_dict()->has_registered_proposition(ap, aut);
//      assert(bddvar >= 0);
//      bdd b = bdd_ithvar(bddvar);
//      if (!bdd_implies(all_outputs, b)) // ap is not an output AP
//        all_inputs &= b;
//    }
//
//    // Loop over all edges and split those that do not have the form
//    // (in)&(out)
//    // Note new_edge are always appended at the end
//    unsigned n_old_edges = aut->num_edges();
//    // Temp storage
//    // Output condition to possible input conditions
//    std::map<bdd, bdd, bdd_less_than> edge_map_;
//    for (unsigned i = 1; i <= n_old_edges; ++i)
//    {
//      // get the edge
//      auto &e = aut->edge_storage(i);
//      // Check if cond already has the correct form
//      if ((bdd_exist(e.cond, all_inputs) & bdd_existcomp(e.cond, all_inputs)) == e.cond)
//        // Nothing to do here
//        continue;
//      // Do the actual split
//      edge_map_.clear();
//      bdd old_cond = e.cond;
//      while (old_cond != bddfalse)
//      {
//        bdd minterm = bdd_satone(old_cond);
//        bdd minterm_in = bdd_exist(minterm, all_outputs);
//        // Get all possible valid outputs
//        bdd valid_out = bdd_exist((minterm_in & e.cond), all_inputs);
//        // Check if this out already exists
//        auto it = edge_map_.find(valid_out);
//        if (it == edge_map_.end())
//          edge_map_[valid_out] = minterm_in;
//        else
//          // Reuse the outs for this in
//          it->second |= minterm_in;
//
//        // Remove this minterm
//        old_cond -= minterm;
//      }
//      // Computed the splitted edges.
//      // Replace the current edge cond with the first pair
//      auto it = edge_map_.begin();
//      e.cond = (it->first & it->second);
//      ++it;
//      for (; it != edge_map_.end(); ++it)
//        aut->new_edge(e.src, e.dst, it->first & it->second, e.acc);
//    }
//    // Done
//  }

} // namespace spot

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

//  static twa_graph_ptr
//  change_init_to_0(twa_graph_ptr& a)
//  {
//    auto res = make_twa_graph(a->get_dict());
//    res->copy_ap_of(a);
//    res->new_states(a->num_states());
//    res->set_init_state(0);
//    auto change = [&a](const unsigned state) {
//      if (state == 0) return a->get_init_state_number();
//      if (state == a->get_init_state_number()) return 0U;
//      return state;
//    };
//    for (auto& e : a->edges())
//    {
//      res->new_edge(change(e.src), change(e.dst), e.cond, e.acc);
//    }
//    a->set_acceptance(acc_cond::acc_code::t());
//    return res;
//  }

  static void
  minimize_strategy_here(twa_graph_ptr& strat, option_map& opt)
  {
    strat->set_acceptance(acc_cond::acc_code::t());
    unsigned simplification_level =
        opt.get("minimization-level", 1);
//    std::cout << "Before " << simplification_level << "\n";
//    print_hoa(std::cout, strat) << '\n';
    // 0 -> No minimization
    // 1 -> Regular monitor minimization
    // 2 -> Mealy minimization based on language inclusion
    // 3 -> Exact mealy minimization
    // 4 -> Monitor min then exact minimization
    // 5 -> Fast mealy then exact minimization
    bdd *obddptr = strat->get_named_prop<bdd>("synthesis-outputs");
    assert(obddptr);
    bdd obdd = *obddptr;
    if (simplification_level < 3)
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
    split->prop_universal(spot::trival::maybe());

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

    if (!w_ptr || !s_ptr || !sp_ptr)
      throw std::runtime_error("Arena missing state-winner, strategy "
                               "or state-player");

    if (!(w_ptr->at(arena->get_init_state_number())))
      throw std::runtime_error("Player does not win initial state, strategy "
                               "is not applicable");

    std::vector<bool>& w = *w_ptr;
    std::vector<unsigned>& s = *s_ptr;

    auto strat_aut = spot::make_twa_graph(arena->get_dict());
    strat_aut->copy_ap_of(arena);
    if (keep_acc)
      strat_aut->copy_acceptance_of(arena);

    constexpr unsigned unseen_mark = std::numeric_limits<unsigned>::max();
    std::vector<unsigned> todo{arena->get_init_state_number()};
    std::vector<unsigned> pg2aut(arena->num_states(), unseen_mark);
    strat_aut->set_init_state(strat_aut->new_state());
    pg2aut[arena->get_init_state_number()] =
        strat_aut->get_init_state_number();

    while (!todo.empty())
      {
        unsigned v = todo.back();
        todo.pop_back();

        // Check if a simplification occurred
        // in the aut and we have env -> env

        // Env edge -> keep all
        for (auto &e1: arena->out(v))
          {
            assert(w.at(e1.dst));
            // Check if a simplification occurred
            // in the aut and we have env -> env
            if (!(*sp_ptr)[e1.dst])
              {
                assert(([&arena, v]()
                         {
                           auto out_cont = arena->out(v);
                           return (++(out_cont.begin()) == out_cont.end());
                         })());
                // If so we do not need to unsplit
                if (pg2aut[e1.dst] == unseen_mark)
                  {
                    pg2aut[e1.dst] = strat_aut->new_state();
                    todo.push_back(e1.dst);
                  }
                // Create the edge
                strat_aut->new_edge(
                              pg2aut[v],
                              pg2aut[e1.dst],
                              e1.cond,
                              keep_acc ? e1.acc : spot::acc_cond::mark_t({}));
                // Done
                continue;
              }

            if (!unsplit)
              {
                if (pg2aut[e1.dst] == unseen_mark)
                  pg2aut[e1.dst] = strat_aut->new_state();
                strat_aut->new_edge(
                              pg2aut[v], pg2aut[e1.dst], e1.cond,
                              keep_acc ? e1.acc : spot::acc_cond::mark_t({}));
              }
            // Player strat
            auto &e2 = arena->edge_storage(s[e1.dst]);
            if (pg2aut[e2.dst] == unseen_mark)
              {
                pg2aut[e2.dst] = strat_aut->new_state();
                todo.push_back(e2.dst);
              }
            if (!unsplit)
              {
                auto eit = strat_aut->out(pg2aut[e1.dst]);
                if (eit.begin()==eit.end())
                  strat_aut->new_edge(
                    pg2aut[e1.dst],
                    pg2aut[e2.dst],
                    e2.cond,
                    keep_acc ? e2.acc
                             : spot::acc_cond::mark_t({}));
              }
            else
              strat_aut->new_edge(
                            pg2aut[v],
                            pg2aut[e2.dst],
                            (e1.cond & e2.cond),
                            keep_acc ? (e1.acc | e2.acc)
                                     : spot::acc_cond::mark_t({}));
          }
      }

      if (bdd* obdd = arena->get_named_prop<bdd>("synthesis-outputs"))
        strat_aut->set_named_prop("synthesis-outputs", new bdd(*obdd));
      else
        throw std::runtime_error("Missing named property "
                                 "\"synthesis-outputs\".\n");

    // If no unsplitting is demanded, it remains a two-player arena
    // We do not need to track winner as this is a
    // strategy automaton
    if (!unsplit)
      {
        const std::vector<bool>& sp_pg = * sp_ptr;
        std::vector<bool> sp_aut(strat_aut->num_states());
        std::vector<unsigned> str_aut(strat_aut->num_states());
        for (unsigned i = 0; i < arena->num_states(); ++i)
          {
            if (pg2aut[i] == unseen_mark)
              // Does not appear in strategy
              continue;
            sp_aut[pg2aut[i]] = sp_pg[i];
            str_aut[pg2aut[i]] = s[i];
          }
        strat_aut->set_named_prop(
            "state-player", new std::vector<bool>(std::move(sp_aut)));
        strat_aut->set_named_prop(
            "state-winner", new std::vector<bool>(strat_aut->num_states(),
                                                  true));
        strat_aut->set_named_prop(
            "strategy", new std::vector<unsigned>(std::move(str_aut)));
      }
    return strat_aut;

  }

  static spot::translator
  create_translator(spot::option_map& extra_options, spot::solver sol,
                    const spot::bdd_dict_ptr& dict)
  {
    for (auto&& p : std::vector<std::pair<const char*, int>>
                      {{"simul", 0},
                       {"ba-simul", 0},
                       {"det-simul", 0},
                       {"tls-impl", 1},
                       {"wdba-minimize", 2}})
      extra_options.set(p.first, extra_options.get(p.first, p.second));

    spot::translator trans(dict, &extra_options);
    // extra_options.report_unused_options();
    switch (sol)
    {
    case spot::solver::LAR:
      SPOT_FALLTHROUGH;
    case spot::solver::LAR_OLD:
      trans.set_type(spot::postprocessor::Generic);
      trans.set_pref(spot::postprocessor::Deterministic);
      break;
    case spot::solver::DPA_SPLIT:
      trans.set_type(spot::postprocessor::ParityMaxOdd);
      trans.set_pref(spot::postprocessor::Deterministic | spot::postprocessor::Colored);
      break;
    case spot::solver::DET_SPLIT:
      SPOT_FALLTHROUGH;
    case spot::solver::SPLIT_DET:
      break;
    }
    return trans;
  }

  spot::twa_graph_ptr
  create_game(const spot::formula& f,
              const std::set<std::string>& all_outs,
              option_map& extra_opt,
              game_info& gi)
  {
    auto trans = create_translator(extra_opt, gi.s, gi.dict);
    // Shortcuts
    auto& bv = gi.bv;
    auto& vs = gi.verbose_stream;

    spot::stopwatch sw;

    if (bv)
      sw.start();
    auto aut = trans.run(f);
    if (bv)
      bv->trans_time = sw.stop();

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

    spot::twa_graph_ptr dpa = nullptr;

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
          bv->paritize_time = sw.stop();
        if (vs)
          *vs << "simplification done\nDPA has "
              << tmp->num_states() << " states\n"
              << "determinization and simplification took "
              << bv->paritize_time << " seconds\n";
        if (bv)
          sw.start();
        dpa = split_2step(tmp, outs, true, false);
        spot::colorize_parity_here(dpa, true);
        if (bv)
          bv->split_time = sw.stop();
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
          bv->paritize_time = sw.stop();
        if (vs)
          *vs << "simplification done in " << bv->paritize_time
              << " seconds\nDPA has " << aut->num_states()
              << " states\n";
        if (bv)
          sw.start();
        dpa = split_2step(aut, outs, true, false);
        spot::colorize_parity_here(dpa, true);
        if (bv)
          bv->split_time = sw.stop();
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
          bv->split_time = sw.stop();
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
          bv->paritize_time = sw.stop();
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
            dpa = spot::to_parity(aut);
            // reduce_parity is called by to_parity(),
            // but with colorization turned off.
            spot::colorize_parity_here(dpa, true);
          }
        else
          {
            dpa = spot::to_parity_old(aut);
            dpa = reduce_parity_here(dpa, true);
          }
        spot::change_parity_here(dpa, spot::parity_kind_max,
                                 spot::parity_style_odd);
        if (bv)
          bv->paritize_time = sw.stop();
        if (vs)
          *vs << "LAR construction done in " << bv->paritize_time
              << " seconds\nDPA has "
              << dpa->num_states() << " states, "
              << dpa->num_sets() << " colors\n";

        if (bv)
          sw.start();
        dpa = split_2step(dpa, outs, true, false);
        spot::colorize_parity_here(dpa, true);
        if (bv)
          bv->split_time = sw.stop();
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

  spot::twa_graph_ptr
  create_game(const formula& f,
              const std::set<std::string>& all_outs)
  {
    option_map dummy1;
    game_info dummy2;
    return create_game(f, all_outs, dummy1, dummy2);
  }

  spot::twa_graph_ptr
  create_game(const std::string& f,
              const std::set<std::string>& all_outs)
  {
    return create_game(spot::parse_formula(f), all_outs);
  }

  SPOT_API spot::twa_graph_ptr
  create_game(const std::string& f,
              const std::set<std::string>& all_outs,
              option_map& opt,
              game_info& gi)
  {
    return create_game(spot::parse_formula(f), all_outs, opt, gi);
  }



  bool solve_game(twa_graph_ptr arena, game_info& gi)
  {
    // todo adapt to new interface
    spot::stopwatch sw;
    if (gi.bv)
      sw.start();
    auto ret = spot::solve_parity_game(arena);
    if (gi.bv)
      gi.bv->solve_time = sw.stop();
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

    auto& bv = gi.bv;
    spot::stopwatch sw;

    if (auto* sw = arena->get_named_prop<std::vector<bool>>("state-winner"))
      {
        if (not (*sw)[arena->get_init_state_number()])
          return nullptr;
      }
    else
      throw std::runtime_error("Arena has no named property"
                                "\"state-winner\". Game not solved?\n");

    if (bv)
      sw.start();
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
    twa_graph_ptr strat_aut = apply_strategy(arena, do_unsplit,
                                             false);
    strat_aut->prop_universal(true);
    minimize_strategy_here(strat_aut, opt);
    if (!do_unsplit)
      strat_aut = unsplit_2step(strat_aut);

    if (bv)
        bv->strat2aut_time = sw.stop();

    return strat_aut;
  }

  spot::twa_graph_ptr
  create_strategy(twa_graph_ptr arena)
  {
    option_map dummy1;
    game_info dummy2;
    return create_strategy(arena, dummy1, dummy2);
  }

  // TODO:
  // In the context of synthesis, we have more LTL equivalences. For example
  // if 'a' is the input and 'b' the output, GF(a) <-> GF(b) is equivalent to
  // GF(a <-> b). It is false for subformulas. For example
  // (GF(a) <-> GF(b)) & (G(a <-> !b)) is not equivalent to
  // GF(a <-> b) & G(a <-> !b).
  // static formula
  // simplify_ltl_for_synthesis(formula f, std::vector<std::string> ins,
  //                           std::vector<std::string> outs)
  // {
  //   (void) f;
  //   (void) ins;
  //   (void) outs;
  //   SPOT_UNIMPLEMENTED();
  // }

  static bool
  has_props(formula f, std::vector<std::string> in_aps, bool in)
  {
    auto f_props = atomic_prop_collect(f);
    for (auto& prop : *f_props)
    {
      auto name = prop.ap_name();
      if ((std::find(in_aps.begin(), in_aps.end(), name) == in_aps.end()) == in)
        return false;
    }
    free(f_props);
    return true;
  }

  // TODO:
  // If a formula is G(o₀ <-> o₁) & G(i₁ <-> o₀), we can create a strategy for
  // G(i₁ <-> o₀) and assign o₁ to the edges with o₀.
  // bdd
  // get_output_constrains(formula f, std::vector<std::string> outs)
  // {
  //   if (f.kind() != op::G)
  //     return bddfalse;
  //   bdd result = bddtrue;
  //   if (f[0].kind() == op::Or)
  //   {
  //     for (auto elem : f[0])
  //     {
  //       TODO: Args?
  //       result &= formula_to_bdd(elem);
  //     }
  //   }
  //   else if (f[0].is_boolean())
  //     return formula_to_bdd(f[0]);
  //   else
  //     return bddfalse;
  // }

  twa_graph_ptr
  try_create_strategy_from_simple(formula f,
                              std::vector<std::string> output_aps,
                              option_map &extra_opt,
                              game_info &gi)
  {
    // TODO: game_info not updated
    auto trans = create_translator(extra_opt, gi.s, gi.dict);
    trans.set_type(postprocessor::Buchi);
    trans.set_pref(postprocessor::Deterministic | postprocessor::Complete);
    auto &bv = gi.bv;
    spot::stopwatch sw;

    if (f.kind() == op::Equiv)
    {
      // A strategy for recurrence <-> GF(bool) can be created by translating
      // the left part to a deterministic Büchi automaton and adding
      // bool to the transitions with {0}.
      // TODO: It is the same for persistence <-> FG(bool)
      // FIXME: Dans le cas GFa <-> GFb on peut se retrouver avec GFb à droite
      formula left, right;
      if ((f[0].kind() == op::G) && (f[0][0].kind() == op::F)
                                       && f[0][0][0].is_boolean())
      {
        left = f[1];
        right = f[0];
      }
      else
      {
        left = f[0];
        right = f[1];
      }
      if (right.kind() == op::G && right[0].kind() == op::F && right[0][0].is_boolean())
      {
        // If left has an output or right has an input, we stop
        if (!has_props(left, output_aps, false) || !has_props(right, output_aps, true))
          return nullptr;
        // We want a deterministic Büchi automaton. Do we want to translate?
        if (!left.is_syntactic_recurrence())
          return nullptr;
        if (bv)
          sw.start();
        auto left_aut = trans.run(left);
        if (bv)
          bv->trans_time = sw.stop();

        if (!spot::is_deterministic(left_aut))
        {
          left_aut = tgba_determinize(left_aut);
          if (!left_aut->acc().is_buchi())
            return nullptr;
        }

        bdd right_bdd = formula_to_bdd(right[0][0], left_aut->get_dict(), left_aut);
        bdd neg_right_bdd = bdd_not(right_bdd);

        bdd output_bdd = bddtrue;
        for (auto& out : output_aps)
          output_bdd &= bdd_ithvar(left_aut->register_ap(out));

        spot::scc_info si(left_aut, spot::scc_info_options::NONE);
        for (auto& e : left_aut->edges())
        {
          // A transition between 2 SCC is seen finitely often so it does not
          // influence the right part of the equivalence. We don't assign an
          // output and it will be decided later.
          if (si.scc_of(e.src) == si.scc_of(e.dst))
            e.cond &= e.acc ? right_bdd : neg_right_bdd;
          e.acc = {};
        }

        left_aut->set_named_prop("synthesis-outputs", new bdd(output_bdd));
        left_aut->set_acceptance(spot::acc_cond::acc_code::t());
        return left_aut;
      }
    }
    return nullptr;
  }

  namespace
  {
    // Checks that 2 sets have a common element. Use it instead
    // of set_intersection when we just want to check if they have a common
    // element because it avoids going through the rest of the sets after an
    // element is found.
    static bool
    are_intersecting(const std::set<spot::formula> &v1,
                     const std::set<spot::formula> &v2)
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

    static std::pair<std::set<std::string>, std::set<std::string>>
    split_set(std::set<std::string>& orig_set, const std::set<std::string>& outs)
    {
      // TODO: Can be faster.
      std::set<std::string> left, right;
      for (auto& x : orig_set)
        if (outs.find(x) != outs.end())
          right.insert(x);
        else
          left.insert(x);
      return { left, right };
    }
  }

  std::map<formula,
           std::pair<std::set<formula>, std::set<formula>>> ap_cache;

  static std::pair<std::set<formula>, std::set<formula>>
  aps_of(const formula &f, const std::set<std::string>& outs)
  {
    auto cache_value = ap_cache.find(f);
    if (cache_value != ap_cache.end())
      return cache_value->second;
    auto f_aps = atomic_prop_collect(f);
    std::set<std::string> f_aps_str;
    for (auto& x : *f_aps)
      f_aps_str.insert(x.ap_name());
    delete(f_aps);
    auto [ins_f_str, outs_f_str] = split_set(f_aps_str, outs);
    std::set<formula> ins_f, outs_f;
    for (auto& x : ins_f_str)
      ins_f.insert(formula::ap(x));
    for (auto& x : outs_f_str)
      outs_f.insert(formula::ap(x));
    std::pair<std::set<formula>, std::set<formula>> res({ins_f, outs_f});
    ap_cache.insert({f, res});
    return res;
  }

  // Use LTL rewritings to have as many conjunctions as possible
  formula
  extract_and(formula f, const std::set<std::string> &outs)
  {
    if (f.kind() == spot::op::And)
    {
      std::vector<spot::formula> children;
      std::transform(f.begin(), f.end(), std::back_inserter(children),
                     [outs](const spot::formula f)
                     { return extract_and(f, outs); });
      auto res = spot::formula::And(children);
      // assert(spot::are_equivalent(res, f));
      return res;
    }
    if (f.kind() == spot::op::Not)
    {
      auto child = extract_and(f[0], outs);
      // ¬(⋀¬xᵢ) ≡ ⋁xᵢ
      if (child.kind() == spot::op::And)
      {
        bool ok = true;
        for (auto sub : child)
          if (sub.kind() != op::Not)
          {
            ok = false;
            break;
          }
        if (ok)
        {
          std::vector<spot::formula> children;
          std::transform(child.begin(), child.end(), std::back_inserter(children),
                        [outs](spot::formula f) { return extract_and(spot::formula::Not(f), outs); });
          return formula::Or(children);
        }
      }
      // ¬Fφ ≡ G¬φ
      if (child.kind() == spot::op::F)
      {
        // The result can be G(And).
        auto f2 = spot::formula::G(extract_and(spot::formula::Not(child[0]), outs));
        // assert(spot::are_equivalent(f, f2));
        // What ?
        return f2;
      }
      // ¬(φ→ψ) ≡ φ ∧ ¬ψ
      else if (child.kind() == spot::op::Implies)
      {
        auto res = spot::formula::And({extract_and(child[0], outs),
                                       extract_and(spot::formula::Not(child[1]), outs)});
        // assert(spot::are_equivalent(res, f));
        return res;
      }
      // ¬(φ ∨ ψ) ≡ ¬φ ∧ ¬ψ
      else if (child.kind() == spot::op::Or)
      {
        std::vector<spot::formula> children;
        std::transform(child.begin(), child.end(), std::back_inserter(children),
                       [outs](spot::formula f)
                       { return extract_and(spot::formula::Not(f), outs); });
        auto res = spot::formula::And(children);
        // assert(spot::are_equivalent(res, f));
        // A ajouter ?
        return res;
      }
    }
    // φ ∨ ψ ≡ ¬(¬φ ∧ ¬ψ), can be used in a recursive call
    // if (f.kind() == spot::op::Or)
    // {
    //   std::vector<spot::formula> children;
    //   std::transform(f.begin(), f.end(), std::back_inserter(children),
    //                  [outs](const spot::formula f)
    //                   { return extract_and(spot::formula::Not(f), outs); });
    //   auto res = spot::formula::Not(spot::formula::And(children));
    //   // assert(spot::are_equivalent(res, f));
    //   return res;
    // }
    // G(⋀φᵢ) = ⋀(G(φᵢ))
    // X(⋀φᵢ) = ⋀(X(φᵢ))
    if (f.is(spot::op::G, spot::op::X))
    {
      auto child_ex = extract_and(f[0], outs);
      if (child_ex.kind() == spot::op::And)
      {
        std::vector<spot::formula> children;
        std::transform(child_ex.begin(), child_ex.end(), std::back_inserter(children),
                       [f, outs](const spot::formula fi)
                        { return extract_and(spot::formula::unop(f.kind(), fi),
                                             outs); });
        auto res = spot::formula::And(children);
        // assert(spot::are_equivalent(f, res));
        return res;
      }
    }
    // ⋀φᵢ U ψ ≡ ⋀(φᵢ U ψ)
    if (f.kind() == spot::op::U)
    {
      auto left_child_ex = extract_and(f[0], outs);
      if (left_child_ex.kind() == spot::op::And)
      {
        std::vector<spot::formula> children;
        std::transform(left_child_ex.begin(), left_child_ex.end(),
                       std::back_inserter(children),
                       [&f](const spot::formula fi)
                          { return spot::formula::U(fi, f[1]); });
        auto res = spot::formula::And(children);
        // assert(spot::are_equivalent(res, f));
        return res;
      }
    }
    if (f.kind() == spot::op::Implies)
    {
      auto right_extr = extract_and(f[1], outs);
      // assert(spot::are_equivalent(right_extr, f[1]));
      auto left_extr = extract_and(f[0], outs);
      // assert(spot::are_equivalent(left_extr, f[0]));
      // φ → (⋀ψᵢ) ≡ ⋀(φ → ψᵢ)
      if (left_extr.kind() != spot::op::And)
      {
        if (right_extr.kind() == spot::op::And)
        {
          std::vector<spot::formula> children;
          std::transform(right_extr.begin(), right_extr.end(),
                         std::back_inserter(children),
                         [f, left_extr](const spot::formula fi)
                          { return spot::formula::Implies(left_extr, fi); });

          auto res = spot::formula::And(children);
          // assert(spot::are_equivalent(f, res));
          return res;
        }
      }
      // ⋀φᵢ → ⋀ψᵢ
      else if (right_extr.kind() == op::And)
      {
        auto extr_f = spot::formula::Implies(left_extr, right_extr);
        auto extr_f_2 = split_implication(extr_f, outs);
        return extr_f_2;
      }
    }
    return f;
  }

  static std::pair<std::set<formula>, std::set<formula>>
  algo4(std::vector<formula> assumptions, std::set<std::string> outs)
  {
    // Two variables are "connected" if they share an assumption.
    // It creates a dependency graph and our goal is to find the propositions
    // that are in the same connected components as outputs.
    const auto ass_size = assumptions.size();
    std::vector<bool> done(ass_size, false);
    std::pair<std::set<formula>, std::set<formula>> result;
    // // An output is in the result.
    for (auto& o : outs)
      result.second.insert(formula::ap(o));
    std::stack<unsigned> todo;
    unsigned first_free = 0;

    auto next_free = [&first_free, &assumptions, &outs, &ass_size, &done]() {
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
      while(!todo.empty())
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

  formula
  split_implication(formula f, const std::set<std::string> outs)
  {
    assert(f.kind() == op::Implies);
    assert(f[0].kind() == op::And);
    // FIXME: Le cas (a & b) -> c ça peut devenir (a -> c) & (b -> c)
    assert(f[1].kind() == op::And);
    std::vector<formula> assumptions, guarantees;
    for (auto a : f[0])
    {
      assumptions.push_back(a);
    }
    for (auto g : f[1])
    {
      guarantees.push_back(g);
    }
    // Set of input/output props that cannot be shared between subspectifications
    auto [decRelProps_ins, decRelProps_outs] = algo4(assumptions, outs);
    // Assumptions that don't contain an atomic proposition in decRelProps
    auto free_assumptions = formula::tt();
    // The set of subspecifications described as [(assum, guar), (assum, guar)]
    std::vector<std::pair<formula, formula>> specs;
    // We merge two assumpt or guar. that share a proposition from decRelProps
    std::vector<spot::formula> assumptions_split, guarantees_split;

    auto fus = [&outs, decRelProps_ins, decRelProps_outs](std::vector<spot::formula>& forms, std::vector<spot::formula>& res)
    {
      std::stack<unsigned> todo;
      todo.emplace(0);
      unsigned first_free = 1;
      const unsigned forms_size = forms.size();
      std::vector<bool> done(forms_size, false);
      while(!todo.empty())
      {
        auto current_res = spot::formula::tt();
        while (!todo.empty())
        {
          auto current_index = todo.top();
          todo.pop();
          done[current_index] = true;
          auto current_form = forms[current_index];
          current_res = spot::formula::And({current_res, current_form});
          auto [ins_f, outs_f] = aps_of(current_form, outs);
          std::set<formula> ins_f_dec, outs_f_dec;
          std::set_intersection(ins_f.begin(), ins_f.end(),
                                decRelProps_ins.begin(), decRelProps_ins.end(),
                                std::inserter(ins_f_dec, ins_f_dec.begin()));
          std::set_intersection(outs_f.begin(), outs_f.end(),
                                decRelProps_outs.begin(), decRelProps_outs.end(),
                                std::inserter(ins_f_dec, ins_f_dec.begin()));
          for (unsigned i = 0; i < forms_size; ++i)
          {
            if (done[i])
            {
              continue;
            }
            auto [ins_i, outs_i] = aps_of(forms[i], outs);
            if (are_intersecting(ins_i, ins_f_dec) || are_intersecting(outs_i, outs_f_dec))
            {
              todo.emplace(i);
            }
          }
        }
        res.push_back(current_res);
        while(first_free < forms_size && done[first_free])
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
    std::function<void(formula f, std::vector<formula>&,
                                  std::vector<spot::formula>&,
                                  std::set<formula>&,
                                  std::set<formula>&,
                                  formula&, formula&,
                                  std::vector<bool>&,
                                  std::vector<bool>&)> bip;
    bip = [&outs, &bip](formula f, std::vector<formula>& src_vect,
                                  std::vector<spot::formula>& dst_vect,
                                  std::set<formula>& ins_dec,
                                  std::set<formula>& outs_dec,
                                  formula& left_res, formula& right_res,
                                  std::vector<bool>& done_left,
                                  std::vector<bool>& done_right)
    {
      left_res = formula::And({left_res, f});
      auto [ins_f, outs_f] = aps_of(f, outs);
      std::set<formula> f_ins_dec, f_outs_dec;
      std::set_intersection(ins_f.begin(), ins_f.end(), ins_dec.begin(), ins_dec.end(), std::inserter(f_ins_dec, f_ins_dec.begin()));
      std::set_intersection(outs_f.begin(), outs_f.end(), outs_dec.begin(), outs_dec.end(), std::inserter(f_outs_dec, f_outs_dec.begin()));
      std::stack<unsigned> todo;
      for (unsigned i = 0; i < dst_vect.size(); ++i)
      {
        if (done_right[i])
          continue;
        auto f2 = dst_vect[i];
        auto [f2_ins, f2_outs] = aps_of(f2, outs);
        if (are_intersecting(f2_ins, f_ins_dec) || are_intersecting(f2_outs, f_outs_dec))
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
        bip(dst_vect[right_index], dst_vect, src_vect, ins_dec, outs_dec, right_res, left_res, done_right, done_left);
      }
    };

    std::vector<bool> done_ass(assumptions_split.size(), false),
                      done_gua(guarantees_split.size(), false);
    for (unsigned i = 0; i < assumptions_split.size(); ++i)
    {
      if (done_ass[i])
        continue;
      done_ass[i] = true;
      auto& ass = assumptions_split[i];
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
        bip(ass, assumptions_split, guarantees_split, decRelProps_ins, decRelProps_outs, left, right, done_ass, done_gua);
        specs.push_back({left, right});
      }
    }
    auto other_outs = formula::tt();
    for (unsigned i = 0; i < guarantees.size(); ++i)
      if (!done_gua[i])
        other_outs = formula::And({other_outs, guarantees[i]});
    if (!other_outs.is_tt())
      specs.push_back({formula::tt(), other_outs});

    if (!free_assumptions.is_tt())
      for (auto& [a, _] : specs)
        a = formula::And({a, free_assumptions});
    std::vector<formula> elems;
    for (auto [ass, gua] : specs)
    {
      auto new_impl = formula::Implies(ass, gua);
      elems.push_back(new_impl);
    }
    // FIXME: Dans le cas où il y a à droite un truc qui n'a pas de
    // decRelProps, il n'est jamais fait
    return formula::And(elems);
  }

  std::pair<std::vector<formula>, std::vector<std::set<spot::formula>>>
  split_independant_formulas(formula f, const std::set<std::string> outs)
  {
    f = extract_and(f, outs);
    if (f.kind() != op::And)
    {
      auto [_, outs_f] = aps_of(f, outs);
      return { {f}, { outs_f } };
    }
    // Atomics prop of children
    std::vector<std::set<spot::formula>> children_outs;
    // Independent formulas
    std::vector<spot::formula> res;
    // And the appearing propositions
    std::vector<std::set<spot::formula>> res_outs;
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
      std::vector<spot::formula> current_and;
      std::set<spot::formula> current_outs;
      while (!todo.empty())
      {
        auto current = todo.top();
        todo.pop();
        children_class[current] = true;
        current_and.push_back(f[current]);
        current_outs.insert(children_outs[current].begin(),
                            children_outs[current].end());
        // TODO: Start with i = current + 1?
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
    // std::cout << res.size() << " sous formules : " << std::endl;
    // for (unsigned i = 0; i < res.size(); ++i)
    // {
    //   auto x = res[i];
    //   std::cout << x << " [";
    //   for (auto y : res_outs[i])
    //     std::cout << y << ", ";
    //   std::cout << "]" << std::endl;
    // }


    return { res, res_outs };
  }

} // spot