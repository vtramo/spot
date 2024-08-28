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

#include <spot/misc/common.hh>
#include <spot/twa/fwd.hh>
#include <vector>

namespace spot
{
  /// \ingroup twa_algorithms
  /// \brief match the state of \a aut1 with the states of \a aut2.
  ///
  /// Return a vector `V` such that for each state `x` of
  /// \a aut1, `V[x]` contains the set of states `y` such that
  /// `(x,y)` is a useful state of `product(aut1,aut2)`.
  ///
  /// In particular, if the language of \a aut2 includes the language
  /// of \a aut1, then any word accepted from state `x` in \a aut1
  /// is also accepted from one of the states in `V[x]`.
  SPOT_API std::vector<std::vector<unsigned>>
  match_states(const const_twa_graph_ptr& aut1,
               const const_twa_graph_ptr& aut2);
}
