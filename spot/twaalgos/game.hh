// -*- coding: utf-8 -*-
// Copyright (C) 2017-2020 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#include <algorithm>
#include <memory>
#include <ostream>
#include <unordered_map>
#include <vector>
#include <deque>
#include <limits>

#include <bddx.h>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/parity.hh>
#include <spot/twa/acc.hh>

namespace spot
{

  /// \brief Edge data used in the transposed graph
  struct trans_edge_data_t
  {
    trans_edge_data_t() noexcept = default;
    trans_edge_data_t(acc_cond::mark_t m, int i) noexcept
        : acc{m}, add_info{i}, is_active{false}, is_accepting{false}
    {
    }
    trans_edge_data_t(std::pair<acc_cond::mark_t, int> ap) noexcept
    {
      acc = ap.first;
      add_info = ap.second;
    }
    acc_cond::mark_t acc;
    int add_info;
    bool is_active, is_accepting;
  };
  typedef digraph<void, trans_edge_data_t> transposed_graph_t;

  /// \brief Transform an automaton into a parity game by propagating
  /// players
  ///
  /// This propagate state players, assuming the initial state belong
  /// to \a first_player, and alternating players on each transitions.
  /// If an odd cycle is detected, a runtime_exception is raised.
  ///
  /// If \a complete0 is set, ensure that states of player 0 are
  /// complete.
  SPOT_API
  void alternate_players(spot::twa_graph_ptr& arena,
                         bool first_player = false,
                         bool complete0 = true);


  // false -> env, true -> player
  typedef std::vector<bool> region_t;
  // state idx -> global edge number
  typedef std::vector<unsigned> strategy_t;
  // state idx -> Attractor lvl
  // Player 0 (env) has negative lvls
  // In order to win he has to "go up"
  // His "best" lvl is -1
  // Player 1 (system) has positive lvls
  // In order to win he has to "go down"
  // His best lvl is -1
  typedef std::vector<int> attr_strategy_t;


  // Note: These are functions in order to have
  // automatic python bindings
  // Values for players
  /// \brief Value associated to player 0
  SPOT_API
  constexpr region_t::value_type p0_val()
  {
    return false;
  }
  /// \brief Value associated to player 1
  SPOT_API
  constexpr region_t::value_type p1_val()
  {
    return true;
  }
  /// \brief Winning lvl for player 0
  SPOT_API
  constexpr attr_strategy_t::value_type best_lvl_p0()
  {
    return -1;
  }
  /// \brief Value used to say "not in set"
  SPOT_API
  constexpr attr_strategy_t::value_type game_unseen_lvl()
  {
    return 0;
  }
  /// \brief Winning lvl for player 1
  SPOT_API
  constexpr attr_strategy_t::value_type best_lvl_p1()
  {
    return 1;
  }
  /// \brief Token to indicate no strategy
  SPOT_API
  constexpr strategy_t::value_type no_strat()
  {
    return std::numeric_limits<strategy_t::value_type>::max();
  }

  /// \brief solve a parity-game
  ///
  /// The arena is a deterministic parity automaton with a
  /// "state-player" property.
  ///
  /// Player 1 tries to satisfy the acceptance condition, while player
  /// 0 tries to prevent that.
  ///
  /// This computes the winning strategy and winning region using
  /// Zielonka's recursive algorithm.  \cite zielonka.98.tcs
  ///
  /// Also includes some inspiration from Oink.
  /// \cite vandijk.18.tacas
  ///
  /// Returns the player winning in the initial state, and sets
  /// the state-winner and strategy named properties.
  SPOT_API
  bool solve_parity_game(const twa_graph_ptr& arena);

  /// \brief Solve a safety game.
  ///
  /// The arena should be represented by an automaton with true
  /// acceptance.
  ///
  /// Player 1 tries to satisfy the acceptance condition, while player
  /// 0 tries to prevent that.   The only way for player 0 to win is
  /// to find a way to move the play toward a state without successor.
  /// If there no state without successors, then the game is necessarily
  /// winning for player 1.
  ///
  /// Returns the player winning in the initial state, and sets
  /// the state-winner and strategy named properties.
  SPOT_API
  bool solve_safety_game(twa_graph_ptr game);

  /// \brief Print a max odd parity game using PG-solver syntax
  SPOT_API
  void pg_print(std::ostream& os, const const_twa_graph_ptr& arena);


  /// \brief Highlight the edges of a strategy on an automaton.
  ///
  /// Pass a negative color to not display the corresponding strategy.
  /// Set \a use_attractor in order to also show the attractor levels
  /// for each player
  SPOT_API
      twa_graph_ptr highlight_strategy(twa_graph_ptr& arena,
  int player0_color = 5,
  int player1_color = 4,
  bool use_attractor = false);

  /// \brief Set the owner for all the states.
  SPOT_API
  void set_state_players(twa_graph_ptr arena, region_t owners);
  SPOT_API
  void set_state_players(twa_graph_ptr arena, region_t* owners);
  /// \brief Set the owner of a state.
  SPOT_API
  void set_state_player(twa_graph_ptr arena, unsigned state,
      region_t::value_type owner);

  /// \brief Get the owner of all the states.
  SPOT_API
  const region_t& get_state_players(const_twa_graph_ptr arena);
  /// \brief Get the owner of a state.
  SPOT_API
      region_t::value_type
  get_state_player(const_twa_graph_ptr arena, unsigned state);

  /// \brief Get the strategy of all the states.
  SPOT_API
  const strategy_t& get_strategy(const_twa_graph_ptr arena);
  /// \brief Get the strategy of a state.
  SPOT_API
      strategy_t::value_type
  get_strategy_of(const_twa_graph_ptr arena, unsigned state);

  /// \brief Get the attractor strategy of all the states.
  SPOT_API
  const attr_strategy_t& get_attractor_strategy(const_twa_graph_ptr arena);
  /// \brief Get the attractor strategy of a state.
  SPOT_API
      attr_strategy_t::value_type
  get_attractor_strategy_of(const_twa_graph_ptr arena, unsigned state);

  /// \brief Get the winning regions
  SPOT_API
  const region_t& get_state_winner(const const_twa_graph_ptr& arena);
  /// \brief Get the winner of a specific state
  SPOT_API
      region_t::value_type
  get_state_winner_of(const const_twa_graph_ptr& arena, unsigned state);

  /// \brief Add or modify the transposed graph as named property to \a arena
  ///
  /// \note The edge index in the transposed and actual graph is the same
  SPOT_API
  void add_transposed_here(const twa_graph_ptr& arena);

  /// \brief Dualizing the \a arena is equal to exchange the state-players
  ///
  /// \note If the game is already (partially) solved,
  ///       the information will be updated to reflect this change if possible
  SPOT_API
  void dualize_arena_here(const twa_graph_ptr& arena);


  /// \brief Computes the controlled predescessors with applied filters
  ///
  /// \param arena : Game arena
  /// \param s_player : region of each player
  /// \param gt : transposed graph of the arena
  /// \param attr_strat : Initial attractor strategy. If values are different
  ///                     to game_unseen_lvl() it is assumed that they
  ///                     already belong to some player
  /// \param new_num : number assigned to controlled predescessors
  /// \tparam player : Active player
  /// \tparam FFE : function taking an edge and a transposed edge
  ///               returning a bool
  /// An edge is *ignored* if the filter returns false
  /// \tparam FFA : function taking an edge and a transposed edge
  ///               returning a bool
  /// An edge is accepting if it returns true
  /// \note The arena restricted by the filters must still be a proper arena
  ///       If not you are "abusing" edge cases
  /// \note An edge is winning for player if it either leads to the set
  ///       or is accepting by it self
  template <bool player, class FFE, class FFA>
  SPOT_API
  unsigned cpre_filt(const const_twa_graph_ptr& arena,
                     const region_t& s_player,
                     const transposed_graph_t& gt, attr_strategy_t& attr_strat,
                     attr_strategy_t::value_type new_num,
                     FFE ffe, FFA ffa)
  {
    SPOT_ASSERT((arena->num_edges() == gt.num_edges())
                && (arena->num_states() == gt.num_states())
                && "Original and transposed graph are not consistent."
                   "Called add_transpose_here()?");
    if (attr_strat.size() != arena->num_states())
      throw std::runtime_error("Invalid attr_strat size!");

    auto get_tedge = [&gt, &arena](const auto& e)
    {
      return gt.edge_storage(arena->edge_number(e));
    };

    // todo: use c++20 ranges views?
    unsigned n_attracted = 0;
    // Edge into player attr_strat?
    // attr_strat :
    // smaller than best_lvl_p0 ->  env state
    // 0 : unseen
    // larger than best_lvl_p1 -> player state
    auto is_attracted = [&](unsigned s)
    {
      if constexpr (player)
        return best_lvl_p1() <= attr_strat[s] and attr_strat[s] < new_num;
      else
        return new_num < attr_strat[s] and attr_strat[s] <= best_lvl_p0();
    };
    auto to_attracted = [&](const auto& e)
    {
      return is_attracted(e.dst);
    };
    // true for active edge to the set or accepting
    auto c_edge_owned = [&](const auto& e)
    {
      auto te = get_tedge(e);
      return (to_attracted(e) or ffa(e, te)) and ffe(e, te);
    };
    // Winning a player state
    // Note that the player automatically wins a state if it has no
    // active edges
    auto proc_player = [&](unsigned s)
    {
      auto beg = arena->out(s).begin();
      auto end = arena->out(s).end();
      if ((beg == end)
          || std::any_of(beg, end,
                         c_edge_owned))
      {
        ++n_attracted;
        attr_strat[s] = new_num;
      }
    };
    // true for active, non-accepting edge outside the set
    // Attention, states having new_num level do not count!
    auto nc_edge_nowned = [&](const auto& e)
    {
      auto te = get_tedge(e);
      return (not (to_attracted(e) or ffa(e, te))) and ffe(e, te);
    };
    // Winning an env state
    // -> There is no escape
    // Note that no (active) edge also counts as no escape
    auto proc_env = [&](unsigned s)
    {
      if (not std::any_of(arena->out(s).begin(), arena->out(s).end(),
                          nc_edge_nowned))
      {
        ++n_attracted;
        attr_strat[s] = new_num;
      }
    };
    // All states
    for (unsigned s=0; s < arena->num_states(); ++s)
      if (not is_attracted(s))
        // Check
        s_player[s] == player ? proc_player(s)
                              : proc_env(s);
    return n_attracted;
  }

  /// \brief Like cprefilt but relying on named properties
  template <class FFE, class FFA, bool player>
  SPOT_API
  unsigned cpre_filt(const const_twa_graph_ptr& arena,
                     attr_strategy_t& attr_strat,
                     attr_strategy_t::value_type new_num,
                     FFE ffe, FFA ffa)
  {
    const region_t * const s_player =
        arena->get_named_prop<region_t>("state-player");
    if (!s_player)
      throw std::runtime_error("Arena does not have state-player!");
    const transposed_graph_t * gt =
        arena->get_named_prop<transposed_graph_t>("transposed");
    if (!gt)
      throw std::runtime_error("Arena has no transposed graph!");

    return cpre_filt<player>(arena, *s_player, *gt, attr_strat,
                             new_num, ffe, ffa);
  }

  /// \brief Computes the controlled predescessors of a set of states
  ///
  /// A predescessor is controlled if it either belongs to player i
  /// and has at least one successor in the given set of states
  /// or if the state belongs to player i-1 and has only successors
  /// in the given set.
  /// The set being defined as all states for which the player already
  /// has an attractor strategy.
  /// See \cite infinitegames
  ///
  /// \param arena : game graph, needs named prop "state-player"
  /// \param attr_strat : Initial attractor strategy. If values are different
  ///                     to game_unseen_lvl() it is assumed that they
  ///                     already belong to some player
  /// \param s_player : region of each player
  /// \param gt : Transposed graph
  /// set.size() == arena.num_states(); 0 for vertices not in neither set.
  /// \param player : Active player
  /// \param new_num : Number associated to the newly controlled states.
  /// \return : Number of vertices added to the set
  /// \Note : This function expects a proper arena, if not dead end states
  ///         are considered winning for player
  SPOT_API
  unsigned cpre(const const_twa_graph_ptr& arena, const region_t& s_player,
                const transposed_graph_t& gt, attr_strategy_t& attr_strat,
                bool player, attr_strategy_t::value_type new_num);

  /// \brief Version relying on named properties
  SPOT_API
  unsigned cpre(const const_twa_graph_ptr& arena, attr_strategy_t& attr_strat,
                bool player, attr_strategy_t::value_type new_num);


  /// \brief Computes the attractor of a set of states under additional
  ///        constraints defined by the filter functions
  ///
  /// Like calling repeatedly cprefilt but more efficient
  /// See \cite infinitegames
  ///
  /// \param arena : game graph
  /// \param s_player : region of each player
  /// \param gt : Transposed graph of the arena
  /// \param attr_strat : Initial attr_strat of vertices. Expected
  /// attr_strat.size() == arena.num_states();
  /// game_unseen_lvl for undecided vertices, best_lvl_p1 otherwise.
  /// \return : Number of additional vertices that the player could attract
  /// \Note : This function expects a proper arena
  ///          Dead end states are considered winning for player
  ///
  /// \tparam player : Active player
  /// \tparam FFE : function taking an edge and a transposed edge
  ///               returning a bool
  /// An edge is ignored if the filter returns false
  /// \tparam FFA : function taking an edge and a transposed edge
  ///               returning a bool
  /// An edge is accepting if it returns true
  /// \Note The arena restricted by the filters must still be a proper arena
  template <bool player, class FFE, class FFA>
  SPOT_API
  unsigned attractor_filt(const const_twa_graph_ptr& arena,
                          const region_t& s_player,
                          transposed_graph_t& gt,
                          attr_strategy_t& attr_strat,
                          FFE ffe, FFA ffa)
  {
    SPOT_ASSERT((arena->num_edges() == gt.num_edges())
           && (arena->num_states() == gt.num_states())
           && "Original and transposed graph are not consistent."
              "Called add_transpose_here()?");

    using lvl_t = decltype(best_lvl_p0());

    constexpr auto best_lvl = player ? best_lvl_p1() : best_lvl_p0();
    const auto worst_lvl = player ? std::numeric_limits<lvl_t>::max()
                                  : std::numeric_limits<lvl_t>::min();
    const auto incr_lvl = player ? 1 : -1;
    const auto pending_mark_lvl =
        not player ? std::numeric_limits<lvl_t>::max()
                   : std::numeric_limits<lvl_t>::min();

    // Note that "unseen" is always "worse" than any attracted value
    auto lvl_min = [](const auto& lhs, const auto& rhs)
    {
      if (lhs == game_unseen_lvl())
        return rhs;
      if (rhs == game_unseen_lvl())
        return lhs;
      if constexpr (player)
        return std::min(lhs, rhs);
      else
        return std::max(lhs, rhs);
    };
    auto lvl_max = [](const auto& lhs, const auto& rhs)
    {
      if (lhs == game_unseen_lvl())
        return lhs;
      if (rhs == game_unseen_lvl())
        return rhs;
      if constexpr (not player)
        return std::min(lhs, rhs);
      else
        return std::max(lhs, rhs);
    };


    std::vector<unsigned> out_degree(arena->num_states(), 0);
    std::deque<unsigned> queue_env;

    // node -> nbr of open dependencies
    std::unordered_map<unsigned, unsigned> pending_map;

    unsigned n_added = 0;

    auto queue_push = [&queue_env, &n_added](unsigned s)
    {
      ++n_added;
      queue_env.push_back(s);
    };
    auto queue_pop = [&queue_env]()
    {
      auto s = queue_env.front();
      queue_env.pop_front();
      return s;
    };
    auto pending_pop = [&pending_map]()
    {
      // We need a state that has no pending dependencies
      // Infact circular dependencies can arise if there are
      // two player states having a direct circle
      // We can either check for (safe but slow)
      // Or simply pop the state with the least dangling dependencies
      // as this is only called once all free non-player states
      // have been processed
      // todo use a better data structure here
      auto best_it = pending_map.begin();
      for (auto it = pending_map.begin(); it != pending_map.end(); ++it)
        {
          if (it->second < best_it->second)
            best_it = it;
          if (best_it->second == 0)
            break;
        }
      SPOT_ASSERT(best_it != pending_map.end() && "Found no item! Empty?\n");
      decltype(pending_map)::value_type ret = *best_it;
      pending_map.erase(best_it);
      return ret;
    };
    auto pending_push = [&pending_map](unsigned s)
    {
      pending_map[s] += 0;
    };
    auto pending_incr = [&pending_map](unsigned s)
      {
        pending_map[s] += 1;
      };
    auto pending_decr = [&pending_map](unsigned s)
      {
        SPOT_ASSERT((pending_map.find(s) != pending_map.end())
               and (pending_map[s] > 0));
        return (--pending_map[s]) == 0;
      };
    auto pending_mark = [&attr_strat, &n_added](unsigned s)
      {
        SPOT_ASSERT(attr_strat[s] == game_unseen_lvl()
                    && "Expected state to be unseen before marking");
        ++n_added;
        attr_strat[s] = pending_mark_lvl;
        //std::cout << "pending mark " << s << std::endl;
      };
    auto get_tedge = [&gt, &arena](const auto& e)->trans_edge_data_t&
      {
        return gt.edge_storage(arena->edge_number(e));
      };
    auto in_attr_strat = [&attr_strat](unsigned s)
      {
        if constexpr (player)
          return best_lvl_p1() <= attr_strat[s];
        else
          return attr_strat[s] <= best_lvl_p0();
      };
    auto to_attr_strat = [in_attr_strat](const auto& e)
      {
        return in_attr_strat(e.dst);
      };
    auto is_pending = [&attr_strat](unsigned s)
      {
        return attr_strat[s] == pending_mark_lvl;
      };

    auto tag_dangling2 = [&](unsigned tedst)
      {
        for (const auto& teprime : gt.out(tedst))
          {
            if (not teprime.is_active
                or(s_player[teprime.dst] != player)
                or to_attr_strat(teprime))
              // Ignored edge or not player
              // or Vertex already attracted
              continue;
            pending_incr(teprime.dst);
          }
      };

    auto unseen = [&attr_strat](unsigned s)
      {
        return attr_strat[s] == game_unseen_lvl();
      };
    auto seen = [unseen](unsigned s){return not unseen(s); };

    // Determine outdeg and mark edges
    // Note that a state without successors (before or after filtering)
    // is also considered winning for player
    // If this is the case, then arena is in fact not a game arena
    // however this is useful for some finite games
    // like deadlock game
    for (unsigned s = 0; s < arena->num_states(); ++s)
    {
      if (seen(s))
        continue;
      lvl_t this_lvl = game_unseen_lvl();
      if (s_player[s] == player)
        {
          this_lvl = worst_lvl;
          for (const auto& e : arena->out(s))
            {
              auto& te = get_tedge(e);
              te.is_accepting = ffa(e, te);
              te.is_active = ffe(e, te);
              if (not te.is_active)
                continue;
              ++out_degree[s];
              if (te.is_accepting)
                {
                  this_lvl = best_lvl;
                  break;
                }
              else if (to_attr_strat(e))
                this_lvl = lvl_min(this_lvl, attr_strat[e.dst] + incr_lvl);
            }//edges
          // Edge case: No edge -> winning
          this_lvl = out_degree[s] == 0 ? best_lvl : this_lvl;
          if (this_lvl != worst_lvl)
            // Winning without pending
            out_degree[s] = 0;
          else
            {
              out_degree[s] = 1;
              this_lvl = game_unseen_lvl();
            }
        }
      else
        {
          this_lvl = best_lvl;
          for (const auto& e : arena->out(s))
            {
              auto& te = get_tedge(e);
              te.is_accepting = ffa(e, te);
              te.is_active = ffe(e, te);
              // Restricting to active edges
              // Accepting edges can't be taken by the env
              if (te.is_active and not te.is_accepting)
                {
                  // Player-1 seeks the "worst" successsor
                  // Measured in his lvl
                  this_lvl = lvl_max(this_lvl,
                                     attr_strat[e.dst] + incr_lvl);
                  // The outdegree increase if the edge is not leading
                  // to the attr as this is then an "escape route"
                  out_degree[s] += (not to_attr_strat(e));
                }
            }
          // Note that if all edges are either inactive, accepting or
          // leading to the attractor -> out_degree = 0 and best_lvl
        }
      if (out_degree[s] == 0)
        {
          SPOT_ASSERT(this_lvl != game_unseen_lvl()
                      && "If \"winning\" unseen tag is not allowed");
          // No escape found
          attr_strat[s] = this_lvl;
          // All predesc. have to be checked
          queue_push(s);
        }
    }

    // todo : this is not very "left leaning"
    while (not (queue_env.empty() and pending_map.empty()))
      {
        // First empty all env states (non pending states)
        while (not queue_env.empty())
          {
            auto s = queue_pop();
            for (const auto& te : gt.out(s))
              {
                if (not te.is_active
                    or to_attr_strat(te)
                    or is_pending(te.dst))
                  // Ignored edge or Vertex already
                  // attracted or pending
                  continue;
                if (s_player[te.dst] == player)
                  {
                    // Controlled state
                    // -> Pending without incr dangling references
                    // tag state itself
                    pending_push(te.dst);
                    pending_mark(te.dst);
                    // Tag its pred (but only once)
                    tag_dangling2(te.dst);
                  }
                else
                  {
                    // Only decrement if not accepting
                    out_degree[te.dst] -= (not te.is_accepting);
                    SPOT_ASSERT(out_degree[te.dst] != -1u
                                && "Sth is wrong, decremented too far");
                    if (out_degree[te.dst] == 0)
                      {
                        // Attracted
                        attr_strat[te.dst] = attr_strat[s] + incr_lvl;
                        queue_push(te.dst);
                      }
                  }
              }//transposed edge
          }//inner while 1
        // Now remove pending until we can continue with regular states
        while (queue_env.empty() and not pending_map.empty())
          {
            // Get the state with the minimal number of dependencies
            // By construction they all have to be circular
            auto [s, n_dep] = pending_pop();
            (void)n_dep;
            attr_strat[s] = best_lvl;
            // The lvl of this state is the incremented max of its
            // (active and attracted) successors
            for (const auto& e: arena->out(s))
              if (get_tedge(e).is_active and to_attr_strat(e))
                attr_strat[s] = lvl_max(attr_strat[s],
                                        attr_strat[e.dst] + incr_lvl);
            SPOT_ASSERT((attr_strat[s] != best_lvl)
                        && "No active edge existed or incorrect lvl before");
            // Treat the predescessors
            // If the predescessor is controlled by player,
            // then it becomes pending
            for (const auto& te: gt.out(s))
              {
                if (not te.is_active
                    or to_attr_strat(te))
                  // Ignored edge or
                  // vertex already attracted
                  continue;
                if (s_player[te.dst] == player)
                  {
                    // Controlled state
                    // -> Remove this dangling reference
                    pending_decr(te.dst);
                    // Mark this one as pending and treat the predescessors
                    // if necessary
                    if (not is_pending(te.dst))
                      {
                        pending_mark(te.dst);
                        tag_dangling2(te.dst);
                      }
                  }
                else
                  {
                    // Only decrement if not accepting
                    out_degree[te.dst] -= (not te.is_accepting);
                    SPOT_ASSERT(out_degree[te.dst] != -1u
                                && "Sth is wrong, decremented too far");
                    if (out_degree[te.dst] == 0)
                      {
                        // Attracted
                        attr_strat[te.dst] = attr_strat[s] + incr_lvl;
                        queue_push(te.dst);
                      }
                  }
              } //transposed edge
          }//inner while 2
      }//outer while
    return n_added;
  }

  /// \brief Like attractor_filt, with ffe(e, te) = true and ffa(e, te) = false
  ///        for all edges
  SPOT_API
  unsigned attractor(const const_twa_graph_ptr& arena,
                     const region_t& s_player, transposed_graph_t& gt,
                     attr_strategy_t& attr_strat, bool player);

  /// \brief Like attractor but relying on the named properties
  SPOT_API
  unsigned attractor(const const_twa_graph_ptr& arena,
                     attr_strategy_t& attr_strat, bool player);


  /// \brief Highlevel function to solve a game. This function will dispatch
  ///        to the best algorithm for the game at hand
  ///
  /// Currently supported are games with trivial acceptance,
  /// (co-)Buchi acceptance and parity acceptance.
  /// Buchi and Co-Buchi can be reinterpreted as reach/avoid games
  /// \param arena : Arena to be solved
  /// \param use_buechi_as_reach : If (0) in Inf(0) means infinite
  ///                              visits or not. If true :
  ///                              Buchi becomes reaching (0)
  ///                              Co-Buchi becomes avoiding (0)
  /// \return : Whether player 1 is winning the initial vertex or not
  /// \pre Must be a valid arena
  /// \post Adds the named properties state-winner and either
  ///       strategy or attr-strategy and the transposed graph
  /// \note In game arenas, every state needs to have a successor.
  ///       This is not checked as sometimes it is useful to break this rule,
  ///       but consider the following: States without successors are
  ///       considered to be winning for the player
  SPOT_API
  bool solve(const twa_graph_ptr& arena,
             bool use_buechi_as_reach = false);


}