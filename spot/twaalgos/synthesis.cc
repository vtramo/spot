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

#include <spot/twaalgos/synthesis.hh>
#include <spot/twa/fwd.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/game.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/minimize.hh>
#include <spot/twaalgos/parity.hh>
#include <spot/twaalgos/toparity.hh>
#include <spot/twaalgos/sbacc.hh>
#include <spot/misc/timer.hh>

#include <algorithm>
#include <string>

// Helper function/structures for split_2step
namespace{
  // Computes and stores the restriction
  // of each cond to the input domain and the support
  // This is useful as it avoids recomputation
  // and often many conditions are mapped to the same
  // restriction
  struct small_cacher_t
  {
    //e to e_in and support
    std::unordered_map<bdd, std::pair<bdd, bdd>, spot::bdd_hash> cond_hash_;

    void fill(const spot::const_twa_graph_ptr& aut, bdd output_bdd)
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
    e_info_t(const spot::twa_graph::edge_storage_t& e,
             const small_cacher_t& sm)
        : dst(e.dst),
          econd(e.cond),
          einsup(sm[e.cond]),
          acc(e.acc)
    {
      pre_hash = (spot::wang32_hash(dst)
                 ^ std::hash<spot::acc_cond::mark_t>()(acc))
                 * spot::fnv<size_t>::prime;
    }

    inline size_t hash() const
    {
      return spot::wang32_hash(spot::bdd_hash()(econdout)) ^ pre_hash;
    }

    unsigned dst;
    bdd econd;
    mutable bdd econdout;
    std::pair<bdd, bdd> einsup;
    spot::acc_cond::mark_t acc;
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

  static spot::twa_graph_ptr
  ntgba2dpa(const spot::twa_graph_ptr &split, bool force_sbacc)
  {
    // if the input automaton is deterministic, degeneralize it to be sure to
    // end up with a parity automaton
    auto dpa = spot::tgba_determinize(spot::degeneralize_tba(split),
                                      false, true, true, false);
    dpa->merge_edges();
    if (force_sbacc)
      dpa = spot::sbacc(dpa);
    spot::reduce_parity_here(dpa, true);
    spot::change_parity_here(dpa, spot::parity_kind_max,
                             spot::parity_style_odd);
    assert((
               [&dpa]() -> bool {
                 bool max, odd;
                 dpa->acc().is_parity(max, odd);
                 return max && odd;
               }()));
    assert(spot::is_deterministic(dpa));
    return dpa;
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

  twa_graph_ptr unsplit_2step(const const_twa_graph_ptr& aut)
  {
    twa_graph_ptr out = make_twa_graph(aut->get_dict());
    out->copy_acceptance_of(aut);
    out->copy_ap_of(aut);
    out->new_states(aut->num_states());
    out->set_init_state(aut->get_init_state_number());

    // split_2step is not guaranteed to produce
    // states that alternate between env and player do to do_simplify
    auto owner_ptr = aut->get_named_prop<std::vector<bool>>("state-player");
    if (!owner_ptr)
      throw std::runtime_error("unsplit requires the named prop "
                               "state-player as set by split_2step");

    std::vector<bool> seen(aut->num_states(), false);
    std::deque<unsigned> todo;
    todo.push_back(aut->get_init_state_number());
    seen[aut->get_init_state_number()] = true;
    while (!todo.empty())
      {
        unsigned cur = todo.front();
        todo.pop_front();
        seen[cur] = true;

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
                out->new_edge(cur, i.dst, i.cond, i.acc);
                if (!seen[i.dst])
                  todo.push_back(i.dst);
                continue; // Done with cur
              }
            for (const auto& o : aut->out(i.dst))
              {
                out->new_edge(cur, o.dst, i.cond & o.cond, i.acc | o.acc);
                if (!seen[o.dst])
                  todo.push_back(o.dst);
              }
            }
      }
    out->merge_edges();
    out->merge_states();
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

            strat_aut->new_edge(
                          unsplit ? pg2aut[v] : pg2aut[e1.dst],
                          pg2aut[e2.dst],
                          unsplit ? (e1.cond & e2.cond) : e2.cond,
                          keep_acc ? e2.acc : spot::acc_cond::mark_t({}));
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
  create_translator(spot::option_map& extra_options, spot::solver sol)
  {
    for (auto&& p : std::vector<std::pair<const char*, int>>
                      {{"simul", 0},
                       {"ba-simul", 0},
                       {"det-simul", 0},
                       {"tls-impl", 1},
                       {"wdba-minimize", 2}})
      extra_options.set(p.first, extra_options.get(p.first, p.second));

    spot::bdd_dict_ptr dict = spot::make_bdd_dict();
    spot::translator trans(dict, &extra_options);
    extra_options.report_unused_options();
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
    auto trans = create_translator(extra_opt, gi.s);
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
        dpa = split_2step(tmp, outs, true, true);
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
        dpa = split_2step(aut, outs, true, true);
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
        dpa = split_2step(dpa, outs, true, true);
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

  // TODO: Est-ce qu'on en fait une option --minimize=[int] où
  // 0 => pas de minim
  // 1 => minimize_monitor
  // 2 => 1 + implication des signatures
  // ?
  static void
  minimize_strategy_here(twa_graph_ptr& strat)
  {
    // (void) strat;
    strat->set_acceptance(spot::acc_cond::acc_code::t());
    bdd *obdd = strat->get_named_prop<bdd>("synthesis-outputs");
    assert(obdd);
    auto new_bdd = new bdd(*obdd);
    strat = spot::minimize_monitor(strat);
    strat->set_named_prop("synthesis-outputs", new_bdd);
  }

  twa_graph_ptr
  create_strategy(twa_graph_ptr arena, game_info& gi)
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
    twa_graph_ptr strat_aut = apply_strategy(arena, true, false);
    (void)minimize_strategy_here;
    // minimize_strategy_here(strat_aut);
    if (bv)
        bv->strat2aut_time = sw.stop();

    return strat_aut;
  }

} // spot