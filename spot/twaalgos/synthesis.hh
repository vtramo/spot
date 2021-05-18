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

#pragma once

#include <bddx.h>
#include <spot/misc/common.hh>
#include <spot/twa/fwd.hh>
#include <vector>
#include <spot/twaalgos/aiger.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/tl/formula.hh>

namespace spot
{
  /// \brief make each transition (conditionally, see do__simpify)
  ///        a 2-step transition
  ///
  /// Given a set of atomic propositions I, split each transition
  ///     p -- cond --> q                cond in 2^2^AP
  /// into a set of transitions of the form
  ///     p -- {a} --> (p,a) -- o --> q
  /// for each a in cond \cap 2^2^I
  /// and where o = (cond & a) \cap 2^2^(O)
  ///
  /// By definition, the states p are deterministic,
  /// only the states of the form
  /// (p,a) may be non-deterministic.
  /// This function is used to transform an automaton into a turn-based game in
  /// the context of LTL reactive synthesis.
  /// \param aut          automaton to be transformed
  /// \param output_bdd   conjunction of all output AP; Note that all aps
  ///                     not appearing here are considered inputs
  /// \param complete_env Whether the automaton should be complete for the
  ///                     environment, i.e. the player of I
  /// \param do_simplify  If a state has a single outgoing transition
  ///                     we do not necessarily have to split it
  ///                     to solve the game
  /// \note: This function also computes the state players
  /// \note: If the automaton is to be completed for both env and player
  ///        then egdes between the sinks will be added
  /// (assuming that the environnement/player of I) plays first
  SPOT_API twa_graph_ptr
  split_2step(const const_twa_graph_ptr& aut,
              const bdd& output_bdd, bool complete_env, bool do_simplify);

  /// \brief the reverse of split_2step
  ///
  /// \note: This function relies on the named property "state-player"
  SPOT_API twa_graph_ptr
  unsplit_2step(const const_twa_graph_ptr& aut);


  /// \brief Takes a solved game and restricts the automaton to the
  ///        winning strategy of the player
  ///
  /// \param arena        twa_graph with named properties "state-player",
  ///                     "strategy" and "state-winner"
  /// \param unsplit      Whether or not to unsplit the automaton
  /// \param keep_acc     Whether or not keep the acceptance condition
  /// \return             the resulting twa_graph
  SPOT_API twa_graph_ptr
  apply_strategy(const twa_graph_ptr& arena,
                 bool unsplit, bool keep_acc);

  enum class solver
  {
    DET_SPLIT=0,
    SPLIT_DET,
    DPA_SPLIT,
    LAR,
    LAR_OLD,
  };

  SPOT_API std::ostream&
  operator<<(std::ostream& os, solver s);

  struct SPOT_API game_info
  {
    struct bench_var
    {
      double total_time = 0.0;
      double trans_time = 0.0;
      double split_time = 0.0;
      double paritize_time = 0.0;
      double solve_time = 0.0;
      double strat2aut_time = 0.0;
      unsigned nb_states_arena = 0;
      unsigned nb_states_parity_game = 0;
      unsigned nb_strat_states = 0;
      unsigned nb_strat_edges = 0;
      unsigned nb_latches = 0;
      unsigned nb_gates = 0;
      bool realizable = false;
    };

    game_info()
      : force_sbacc{false},
        s{solver::SPLIT_DET},
        minimize_opt{0},
        out_choice{0},
        bv{},
        verbose_stream{nullptr},
        dict(make_bdd_dict())
    {
    }

    bool force_sbacc;
    solver s;
    int minimize_opt;
    int out_choice;
    std::optional<bench_var> bv;
    std::ostream* verbose_stream;
    bdd_dict_ptr dict;
  };

  SPOT_API std::ostream &
  operator<<(std::ostream &os, const game_info &gi);

  SPOT_API twa_graph_ptr
  create_game(const formula& f,
              const std::set<std::string>& all_outs,
              option_map& opt,
              game_info& gi);

  SPOT_API twa_graph_ptr
  create_game(const formula& f,
              const std::set<std::string>& all_outs);

  SPOT_API twa_graph_ptr
  create_game(const std::string& f,
              const std::set<std::string>& all_outs);

  SPOT_API twa_graph_ptr
  create_game(const std::string& f,
              const std::set<std::string>& all_outs,
              option_map& opt,
              game_info& gi);

  SPOT_API bool
  solve_game(twa_graph_ptr arena, game_info& gi);

  SPOT_API bool
  solve_game(twa_graph_ptr arena);

  SPOT_API twa_graph_ptr
  create_strategy(twa_graph_ptr arena, option_map& opt, game_info& gi);

  SPOT_API twa_graph_ptr
  create_strategy(twa_graph_ptr arena);

  SPOT_API std::pair<twa_graph_ptr, int>
  try_create_strategy_from_simple(formula f,
                                  const std::set<std::string>& output_aps,
                                  option_map &extra_opt,
                                  game_info &gi);

  SPOT_API std::pair<std::vector<formula>, std::vector<std::set<formula>>>
  split_independant_formulas(formula f, const std::set<std::string> &outs);
}