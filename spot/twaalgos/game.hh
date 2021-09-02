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
#include <optional>

#include <bddx.h>
#include <spot/misc/optionmap.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/parity.hh>

namespace spot
{

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


  /// \brief solve a parity-game
  ///
  /// The arena is a deterministic max odd parity automaton with a
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

  /// \brief Benchmarking and options structure for games and synthesis
  ///
  /// \note This structure is designed to interface with the algorithms
  /// found in spot/twaalgos/synthesis.hh and spot/twaalgos/game.hh
  struct SPOT_API game_info
  {
    enum class solver
    {
      DET_SPLIT=0,
      SPLIT_DET,
      DPA_SPLIT,
      LAR,
      LAR_OLD,
    };

    struct bench_var
    {
      double total_time = 0.0;
      double trans_time = 0.0;
      double split_time = 0.0;
      double paritize_time = 0.0;
      double solve_time = 0.0;
      double strat2aut_time = 0.0;
      double aig_time = 0.0;
      unsigned nb_states_arena = 0;
      unsigned nb_states_arena_env = 0;
      unsigned nb_strat_states = 0;
      unsigned nb_strat_edges = 0;
      unsigned nb_latches = 0;
      unsigned nb_gates = 0;
      bool realizable = false;
    };

    game_info()
      : force_sbacc{false},
        s{solver::LAR},
        minimize_lvl{0},
        bv{},
        verbose_stream{nullptr},
        dict(make_bdd_dict())
    {
    }

    bool force_sbacc;
    solver s;
    int minimize_lvl;
    std::optional<bench_var> bv;
    std::ostream* verbose_stream;
    option_map opt;
    bdd_dict_ptr dict;
  };

  /// \brief Stream solvers
  SPOT_API std::ostream&
  operator<<(std::ostream& os, game_info::solver s);

  /// \brief Stream benchmarks and options
  SPOT_API std::ostream &
  operator<<(std::ostream &os, const game_info &gi);

  /// \brief Generic interface for game solving
  ///
  /// Calls the most suitable solver, depending on the type of game/
  /// acceptance condition
  ///
  /// \param arena The game arena
  /// \param gi struct ofr options and benchmarking
  /// \return Whether the initial state is won by player or not
  /// \pre Relies on the named properties "state-player"
  /// \post The named properties "strategy" and "state-winner" are set
  SPOT_API bool
  solve_game(twa_graph_ptr arena, game_info& gi);

  /// \brief Generic interface for game solving
  ///
  /// See solve_game(arena, gi)
  SPOT_API bool
  solve_game(twa_graph_ptr arena);


  /// \brief Print a max odd parity game using PG-solver syntax
  SPOT_API
  void pg_print(std::ostream& os, const const_twa_graph_ptr& arena);


  /// \brief Highlight the edges of a strategy on an automaton.
  ///
  /// Pass a negative color to not display the corresponding strategy.
  SPOT_API
  twa_graph_ptr highlight_strategy(twa_graph_ptr& arena,
                                   int player0_color = 5,
                                   int player1_color = 4);

  /// \brief Set the owner for all the states.
  SPOT_API
  void set_state_players(twa_graph_ptr arena, const region_t& owners);
  SPOT_API
  void set_state_players(twa_graph_ptr arena, region_t&& owners);

  /// \brief Set the owner of a state.
  SPOT_API
  void set_state_player(twa_graph_ptr arena, unsigned state, bool owner);

  /// \brief Get the owner of a state.
  SPOT_API
  bool get_state_player(const_twa_graph_ptr arena, unsigned state);
  /// \brief Get the owner of all states
  SPOT_API
  const region_t& get_state_players(const_twa_graph_ptr arena);

  /// \brief Get or set the strategy
  SPOT_API
  const strategy_t& get_strategy(const_twa_graph_ptr arena);
  SPOT_API
  void set_strategy(twa_graph_ptr arena, const strategy_t& strat);
  SPOT_API
  void set_strategy(twa_graph_ptr arena, strategy_t&& strat);

  /// \brief Set all synthesis outputs as a conjunction
  SPOT_API
  void set_synthesis_outputs(const twa_graph_ptr& arena, const bdd& outs);
  SPOT_API
  bdd get_synthesis_outputs(const const_twa_graph_ptr& arena);

  /// \brief Get the vector with the names of the output propositions
  SPOT_API
  std::vector<std::string>
  get_synthesis_output_aps(const const_twa_graph_ptr& arena);

  /// \brief Set the winner for all the states.
  SPOT_API
  void set_state_winners(twa_graph_ptr arena, const region_t& winners);
  SPOT_API
  void set_state_winners(twa_graph_ptr arena, region_t&& winners);

  /// \brief Set the winner of a state.
  SPOT_API
  void set_state_winner(twa_graph_ptr arena, unsigned state, bool winner);

  /// \brief Get the winner of a state.
  SPOT_API
  bool get_state_winner(const_twa_graph_ptr arena, unsigned state);
  /// \brief Get the winner of all states
  SPOT_API
  const region_t& get_state_winners(const_twa_graph_ptr arena);
}
