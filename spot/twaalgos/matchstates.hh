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
#include <spot/tl/formula.hh>
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

  /// \ingroup twa_algorithms
  /// \brief match the states of \a aut with formulas "reachable" from
  /// \a f.
  ///
  /// The returned vector V assigns each state `x` of \a aut to a
  /// formula `V[x]`.
  ///
  /// This translates \a f as an automaton B in which states are labeled
  /// by formulas, match the states of \a aut with the states of B, and
  /// use that to find formulas associated to each state of \a aut.
  ///
  /// In particular, if the language of \a f is a superset of the
  /// language of \a aut, then every word accepted in \a aut from
  /// state `x` will satisfy formula `V[x]`.  However `V[x]` may
  /// accept more than the words accepted from `a` in \a aut.
  SPOT_API std::vector<formula>
  match_states(const const_twa_graph_ptr& aut, formula f);


  /// \ingroup twa_algorithms
  ///
  /// \brief label the state of \a aut with the result of
  /// `match_states(aut,f)`.
  SPOT_API void
  match_states_decorate(twa_graph_ptr& aut, formula f);
}
