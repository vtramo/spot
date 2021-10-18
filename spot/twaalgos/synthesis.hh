// -*- coding: utf-8 -*-
// Copyright (C) 2020-2021 Laboratoire de Recherche et
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

#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/game.hh>
#include <bddx.h>

namespace spot
{
  /// \addtogroup synthesis Reactive Synthesis
  /// \ingroup twa_algorithms

  /// \ingroup synthesis
  /// \brief make each transition a 2-step transition, transforming
  ///        the graph into an alternating arena
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
  ///
  /// \param aut          automaton to be transformed
  /// \param output_bdd   conjunction of all output AP, all APs not present
  ///                     are treated as inputs
  /// \param complete_env Whether the automaton should be complete for the
  ///                     environment, i.e. the player of I
  /// \note This function also computes the state players
  /// \note If the automaton is to be completed for both env and player
  ///       then egdes between the sinks will be added
  /// (assuming that the environnement/player of I) plays first
  SPOT_API twa_graph_ptr
  split_2step(const const_twa_graph_ptr& aut,
              const bdd& output_bdd, bool complete_env);


  /// \ingroup synthesis
  /// \brief make each transition a 2-step transition.
  ///
  /// This algorithm is only applicable if all transitions of the
  /// graph have the form p -- ins & outs --> q.
  /// That is they are a conjunction of a condition over the input
  /// propositions ins and a condition over the output propositions outs
  ///
  /// \param aut          automaton to be transformed
  /// \param output_bdd   conjunction of all output AP, all APs not present
  ///                     are treated as inputs
  /// @{
  SPOT_API void
  split_2step_fast_here(const twa_graph_ptr& aut, const bdd& output_bdd);

  SPOT_API twa_graph_ptr
  split_2step_fast(const const_twa_graph_ptr& aut, const bdd& output_bdd);
  /// @}

  /// \ingroup synthesis
  /// \brief the reverse of split_2step
  ///
  /// \note This function relies on the named property "state-player"
  SPOT_API twa_graph_ptr
  unsplit_2step(const const_twa_graph_ptr& aut);

  /// \ingroup synthesis
  /// \brief Benchmarking data and options for synthesis
  struct SPOT_API synthesis_info
  {
    enum class algo
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

    synthesis_info()
    : force_sbacc{false},
      s{algo::LAR},
      minimize_lvl{2},
      bv{},
      verbose_stream{nullptr},
      dict(make_bdd_dict())
    {
    }

    bool force_sbacc;
    algo s;
    int minimize_lvl;
    std::optional<bench_var> bv;
    std::ostream* verbose_stream;
    option_map opt;
    bdd_dict_ptr dict;
  };

  /// \ingroup synthesis
  /// \brief Stream algo
  SPOT_API std::ostream&
  operator<<(std::ostream& os, synthesis_info::algo s);

  /// \ingroup synthesis
  /// \brief Stream benchmarks and options
  SPOT_API std::ostream &
  operator<<(std::ostream &os, const synthesis_info &gi);


  /// \ingroup synthesis
  /// \brief Creates a game from a specification and a set of
  /// output propositions
  ///
  /// \param f The specification given as an LTL/PSL formula, or
  ///          as a string.
  /// \param all_outs The names of all output propositions
  /// \param gi synthesis_info structure
  /// \note All propositions in the formula that do not appear in all_outs
  /// are treated as input variables.
  /// @{
  SPOT_API twa_graph_ptr
  ltl_to_game(const formula& f,
              const std::vector<std::string>& all_outs,
              synthesis_info& gi);
  SPOT_API twa_graph_ptr
  ltl_to_game(const formula& f,
              const std::vector<std::string>& all_outs);
  SPOT_API twa_graph_ptr
  ltl_to_game(const std::string& f,
              const std::vector<std::string>& all_outs,
              synthesis_info& gi);
  SPOT_API twa_graph_ptr
  ltl_to_game(const std::string& f,
              const std::vector<std::string>& all_outs);
  /// @}

  /// \ingroup synthesis
  /// \brief Takes a solved game and restricts the automaton to the
  ///        winning strategy of the player
  ///
  /// \param arena        twa_graph with named properties "state-player",
  ///                     "strategy" and "state-winner"
  /// \param unsplit      Whether or not to unsplit the automaton
  /// \param keep_acc     Whether or not keep the acceptance condition
  /// \return             the resulting twa_graph
  SPOT_API spot::twa_graph_ptr
  apply_strategy(const spot::twa_graph_ptr& arena,
                 bool unsplit, bool keep_acc);

  /// \ingroup synthesis
  /// \brief Minimizes a strategy. Strategies are infact
  /// Mealy machines. So we can use techniques designed for them
  ///
  /// \param strat The machine to minimize
  /// \param min_lvl How to minimize the machine:
  ///                0: No minimization, 1: Minimizing it like an DFA,
  ///                means the language is preserved, 2: Inclusion with
  ///                output assignement, 3: Exact minimization using
  ///                SAT solving, 4: SAT solving with DFA minimization as
  ///                preprocessing, 5: SAT solving using inclusion based
  ///                 minimization with output assignment as preprocessing
  /// \note min_lvl 1 and 2 work more efficiently on UNSPLIT strategies,
  ///       whereas min_lvl 3, 4 and 5 mandate a SPLIT strategy
  /// @{
  SPOT_API void
  minimize_strategy_here(twa_graph_ptr& strat, int min_lvl);

  SPOT_API twa_graph_ptr
  minimize_strategy(const_twa_graph_ptr& strat, int min_lvl);
  /// @}

  /// \ingroup synthesis
  /// \brief creates a strategy from a solved game taking into account the
  ///        options given in \a gi
  /// @{
  SPOT_API twa_graph_ptr
  create_strategy(twa_graph_ptr arena, synthesis_info& gi);
  SPOT_API twa_graph_ptr
  create_strategy(twa_graph_ptr arena);
  /// @}

  /// \ingroup synthesis
  /// \brief A struct that represents different types of strategy like
  ///        objects
  struct SPOT_API
  strategy_like_t
  {
    //  -1 : Unrealizable
    //  0 : Unknown
    //  1 : Realizable -> regular strat
    //  2 : Realizable -> strat is DTGBA and a glob_cond // todo
    int success;
    twa_graph_ptr strat_like;
    bdd glob_cond;
  };

  /// \ingroup synthesis
  /// \brief Seeks to decompose a formula into independently synthesizable
  /// sub-parts. The conjunction of all sub-parts then
  /// satisfies the specification
  ///
  /// The algorithm is based on work by Finkbeiner et al.
  /// \cite finkbeiner.21.nfm, \cite finkbeiner.21.arxiv.
  ///
  /// \param f the formula to split
  /// \param outs vector with the names of all output propositions
  /// \return A vector of pairs holding a subformula and the used output
  ///  propositions each.
  /// @{
  SPOT_API std::pair<std::vector<formula>, std::vector<std::set<formula>>>
  split_independant_formulas(formula f, const std::vector<std::string>& outs);

  SPOT_API std::pair<std::vector<formula>, std::vector<std::set<formula>>>
  split_independant_formulas(const std::string& f,
                             const std::vector<std::string>& outs);
  /// @}

  /// \ingroup synthesis
  /// \brief Creates a strategy for the formula given by calling all
  ///        intermediate steps
  ///
  /// For certain formulas, we can ''bypass'' the traditional way
  /// and find directly a strategy or some other representation of a
  /// winning condition without translating the formula as such.
  /// If no such simplifications can be made, it executes the usual way.
  ///
  /// \param f The formula to synthesize a strategy for
  /// \param output_aps A vector with the name of all output properties.
  ///                   All APs not named in this vector are treated as inputs
  SPOT_API strategy_like_t
  try_create_direct_strategy(formula f,
                             const std::vector<std::string>& output_aps,
                             synthesis_info& gi);

  /// \ingroup synthesis
  /// \brief Solve a game, and update synthesis_info
  ///
  /// This is just a wrapper around the solve_game() function with a
  /// single argument.  This one measure the runtime and update \a gi.
  SPOT_API bool
  solve_game(twa_graph_ptr arena, synthesis_info& gi);

}
