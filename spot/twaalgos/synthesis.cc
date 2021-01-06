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
#include <spot/misc/minato.hh>
#include <spot/twaalgos/totgba.hh>
#include <spot/misc/bddlt.hh>

#include <algorithm>
#include <map>
#include <unordered_map>

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

  unsigned count(bdd b)
  {
    unsigned high = 0;
    while (b != bddtrue)
      {
        if (bdd_low(b) == bddfalse)
          {
            assert(bdd_low(b) == bddfalse);
            ++high;
            b = bdd_high(b);
          }
        else
          {
            assert(bdd_high(b) == bddfalse);
            b = bdd_low(b);
          }
      }
    return high;
  }
}

namespace spot
{
  twa_graph_ptr
  split_2step(const const_twa_graph_ptr& aut, const bdd& input_bdd,
              const bdd& output_bdd, bool complete_env,
              bool do_simplify)
  {
    auto split = make_twa_graph(aut->get_dict());
    split->copy_ap_of(aut);
    split->copy_acceptance_of(aut);
    split->new_states(aut->num_states());
    split->set_init_state(aut->get_init_state_number());

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
                 bdd all_outputs,
                 bool unsplit, bool keep_acc,
                 int out_mode, bool sep_out)
  {
    if (sep_out and !unsplit)
      throw std::runtime_error("Outconditions can only be separated if "
                               "the automaton is also unsplit.");

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

    auto aut = spot::make_twa_graph(arena->get_dict());
    aut->copy_ap_of(arena);
    if (keep_acc)
      aut->copy_acceptance_of(arena);

    constexpr unsigned unseen_mark = std::numeric_limits<unsigned>::max();
    std::vector<unsigned> todo{arena->get_init_state_number()};
    std::vector<unsigned> pg2aut(arena->num_states(), unseen_mark);
    aut->set_init_state(aut->new_state());
    pg2aut[arena->get_init_state_number()] = aut->get_init_state_number();

    std::vector<bdd> used_outc({bddfalse});

    std::function<bdd(bdd)> proc_out = [](bdd out)noexcept{return out; };
    switch (out_mode)
    {
      case 0:
        proc_out = [](bdd out)noexcept{return out; };
        break;
      case 1:
        proc_out = [all_outputs](bdd out)
            {return bdd_satone(bdd_existcomp(out, all_outputs)); };
        break;
      case 2:
        proc_out = [&all_outputs](bdd out)->bdd
          {
            static std::map<unsigned, std::vector<bdd>> ex_map_;
            // Checks if there exists an out that satisfies out
            // If so use it, else use this out
            // We moreover want to use the bdd having the least highs
            for (const auto& kv : ex_map_)
              {
                auto res = std::find_if(kv.second.begin(), kv.second.end(),
                                        [out](const bdd&aout)
                                        {
                                          return bdd_implies(aout, out);
                                        });
                if (res != kv.second.end())
                  return *res;
              }
            // No minterm that is already in use satisfies this bdd
            // Take the minterm with the least highs
            auto outmin = bdd_satone(bdd_existcomp(out, all_outputs));
            ex_map_[count(outmin)].push_back(outmin);
            return outmin;
          };
        break;
      default:
        throw std::runtime_error("Unknown outcond mode");
    }

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
                    pg2aut[e1.dst] = aut->new_state();
                    todo.push_back(e1.dst);
                  }
                // Create as many edges as necessary to satisfy
                // Todo this is redundant code with
                // the one in restore_form. Put in a private file?
                // (incond)&(outcond)
                std::map<bdd, bdd, bdd_less_than> edge_map_;
                bdd old_cond = e1.cond;
                while (old_cond != bddfalse)
                {
                  bdd minterm = bdd_satone(old_cond);
                  bdd minterm_in = bdd_exist(minterm, all_outputs);
                  // Get all possible valid outputs
                  bdd valid_out = bdd_existcomp((minterm_in & e1.cond),
                                                all_outputs);
                  // Check if this out already exists
                  auto it = edge_map_.find(valid_out);
                  if (it == edge_map_.end())
                    edge_map_[valid_out] = minterm_in;
                  else
                    // Reuse the outs for this in
                    it->second |= minterm_in;
                  // Remove this minterm
                  old_cond -= minterm;
                }
                // Add all of these edges
                auto this_acc = keep_acc ? e1.acc : spot::acc_cond::mark_t({});
                for (auto it = edge_map_.begin(); it != edge_map_.end(); ++it)
                  {
                    // Apply heuristic on out
                    auto this_out = proc_out(it->first);
                    if (sep_out)
                      {
                        aut->new_edge(pg2aut[v],
                                      pg2aut[e1.dst],
                                      it->second, // Only incond
                                      this_acc);
                        used_outc.push_back(this_out);
                      }
                    else
                      aut->new_edge(pg2aut[v],
                                    pg2aut[e1.dst],
                                    this_out & it->second, // AND the conds
                                    this_acc);
                  }
                // Done
                continue;
              }

            if (!unsplit)
              {
                if (pg2aut[e1.dst] == unseen_mark)
                  pg2aut[e1.dst] = aut->new_state();
                aut->new_edge(pg2aut[v], pg2aut[e1.dst], e1.cond,
                              keep_acc ? e1.acc : spot::acc_cond::mark_t({}));
              }
            // Player strat
            auto &e2 = arena->edge_storage(s[e1.dst]);
            if (pg2aut[e2.dst] == unseen_mark)
              {
                pg2aut[e2.dst] = aut->new_state();
                todo.push_back(e2.dst);
              }

            auto this_out = proc_out(e2.cond);
            if (sep_out)
              {
                aut->new_edge(pg2aut[v],
                              pg2aut[e2.dst],
                              e1.cond,
                              keep_acc ? e2.acc : spot::acc_cond::mark_t({}));
                used_outc.push_back(this_out);
              }
            else
              aut->new_edge(unsplit ? pg2aut[v] : pg2aut[e1.dst],
                            pg2aut[e2.dst],
                            unsplit ? (e1.cond & this_out) : this_out,
                            keep_acc ? e2.acc : spot::acc_cond::mark_t({}));
          }
      }

    aut->set_named_prop("synthesis-outputs", new bdd(all_outputs));
    // If no unsplitting is demanded, it remains a two-player arena
    // We do not need to track winner as this is a
    // strategy automaton
    if (!unsplit)
      {
        const std::vector<bool>& sp_pg = * sp_ptr;
        std::vector<bool> sp_aut(aut->num_states());
        std::vector<unsigned> str_aut(aut->num_states());
        for (unsigned i = 0; i < arena->num_states(); ++i)
          {
            if (pg2aut[i] == unseen_mark)
              // Does not appear in strategy
              continue;
            sp_aut[pg2aut[i]] = sp_pg[i];
            str_aut[pg2aut[i]] = s[i];
          }
        aut->set_named_prop(
            "state-player", new std::vector<bool>(std::move(sp_aut)));
        aut->set_named_prop(
            "state-winner", new std::vector<bool>(aut->num_states(), true));
        aut->set_named_prop(
            "strategy", new std::vector<unsigned>(std::move(str_aut)));
      }
    if (sep_out)
      {
//        std::cout << "setting outcond\n";
        assert(used_outc.size()== aut->num_edges()+1);
        aut->set_named_prop(
            "outcond-edge", new std::vector<bdd>(std::move(used_outc)));
      }
    return aut;

  }

} // spot