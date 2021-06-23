// -*- coding: utf-8 -*-
// Copyright (C) 2021 Laboratoire de Recherche et Développement
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

#include <spot/twa/twagraph.hh>

namespace spot
{
  /// \brief Minimizes an (in)completely specified mealy machine
  ///        Based on signature inclusion or equality. This is not guaranteed
  ///        to find the minimal number of states but is usually faster.
  ///        This also comes at another drawback:
  ///        All applicable sequences have to be infinite. Finite
  ///        traces are disregarded
  /// \Note The graph does not have to be split into env and player
  ///        states as for minimize_mealy
  SPOT_API
  void minimize_mealy_fast_here(twa_graph_ptr& mm,
                              bool use_inclusion = false);

  /// \brief Like minimize_mealy_fast_here
  SPOT_API
  twa_graph_ptr minimize_mealy_fast(const const_twa_graph_ptr& mm,
                                    bool use_inclusion = false);

  /// \brief Minimizes an (in)completely specified mealy machine
  ///        The approach is basically described in \cite abel2015memin
  /// \param premin Use minimize_mealy_fast before applying the
  ///               main algorithm if demanded AND
  ///               the original machine has no finite trace.
  ///               -1 : Do not use;
  ///                0 : Use without inclusion;
  ///                1 : Use with inclusion
  /// \param keep_split Whether or not to keep the automaton states
  ///                   partitioned into player and env states
  /// \pre Graph must be split into env states and player states,
  ///      such that they alternate. Edges leaving env states must be labeled
  ///      with input proposition and edges leaving player states must be
  ///      labeled with output propositions.
  SPOT_API
  twa_graph_ptr minimize_mealy(const const_twa_graph_ptr& mm,
                               int premin = -1,
                               bool keep_split = true);


  /// \brief Test if the mealy machine \a right is a specialization of
  /// the mealy machine \a left. That is all input sequences valid for left
  /// must be applicable for right and the induced sequence of output signals
  /// of right must imply the ones of left
  SPOT_API bool is_mealy_specialization(const_twa_graph_ptr left,
                                        const_twa_graph_ptr right,
                                        bool verbose = false);
}