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

#include <spot/twa/twagraph.hh>
#include <bddx.h>

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
  /// \param input_bdd    conjunction of all input AP
  /// \param output_bdd   conjunction of all output AP
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
  split_2step(const const_twa_graph_ptr& aut, const bdd& input_bdd,
              const bdd& output_bdd, bool complete_env, bool do_simplify);

  /// \brief the reverse of split_2step
  ///
  /// \note: This function relies on the named property "state-player"
  SPOT_API twa_graph_ptr
  unsplit_2step(const const_twa_graph_ptr& aut);


  /// \brief Takes a solved game and restricts the automat to the
  ///        winning strategy of the player
  ///
  /// \param arena        twa_graph with named properties "state-player",
  ///                     "strategy" and "state-winner"
  /// \param all_outputs  bdd of all output signals
  /// \param unsplit      Whether or not to unsplit the automaton
  /// \param keep_acc     Whether or not keep the acceptance condition
  /// \param out_mode     Option on how to treat output aps
  ///                     0: Keep the original out bdd
  ///                     1: Use the minterm with minimal high in out
  ///                     2: Use an heuristic reusing outs
  /// \param sep_out      Whether to store the outcond in the named property
  ///                     or to and it with the incond on the edge
  /// \return             the resulting twa_graph
  /// \pre Solved two player game
  /// \post Strategy automaton. Every edge condition has the form
  ///       (incond)&(outcond) as needed to transform to an aiger circuit
  SPOT_API spot::twa_graph_ptr
  apply_strategy(const spot::twa_graph_ptr& arena,
                 bdd all_outputs, bool unsplit, bool keep_acc,
                 int out_mode, bool sep_out);

}