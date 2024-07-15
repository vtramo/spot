// -*- coding: utf-8 -*-
// Copyright (C) by the Spot authors, see the AUTHORS file for details.
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
  /// \brief restrict labels from "dead-end edges"
  ///
  /// A dead-end edge is an edge between two states S₁ and S₂ such
  /// that S₂ has only itself as successor.  I.e., once a run goes
  /// through this "dead-end" edge, it gets stuck in S₂.
  ///
  /// Let Lab(S,D) denote the disjunction of all labels between S and
  /// D.  Let UsefulLab(D,D) be the disjunction of labels of any
  /// subset of self-loops of D that will intersect all accepting
  /// cycles around D (one way to compute this subset is to simplify
  /// the acceptance condition with keep_one_inf_per_branch(), and
  /// then keep each edge that satisfy it).
  ///
  /// Now, if the following implications are satisfied
  ///
  /// ⎧ UsefulLab(D,D) ⇒ Lab(S,D) ⇒ Lab(S,S),<br/>
  /// ⎨ <br/>
  /// ⎩ Lab(D,D) ⇒ Lab(S,S).<br/>
  ///
  /// then any edge between S and D, labeled by ℓ⊆Lab(S,D)
  /// can be replaced by ℓ∩UsefulLab(D,D).
  ///
  /// This algorithm has no effect on deterministic automata (where
  /// it is not possible that Lab(S,D) ⇒ Lab(S,S)).
  SPOT_API twa_graph_ptr
  restrict_dead_end_edges_here(twa_graph_ptr& aut);
}
