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
  enum given_strategy
    {
      GIVEN_RESTRICT = 1,
      GIVEN_RELAX = 2,
      GIVEN_ALL = GIVEN_RESTRICT | GIVEN_RELAX,
    };

  /// \ingroup twa_algorithms
  /// \brief simplify an automaton given some a priori knowledge
  ///
  /// If \a aut represent the negation of a property that one want
  /// to check on some system S, and we know (by any mean) that the
  /// behaviors of S always satisfies \a fact, we can use that
  /// to modify \a aut in such a way that \a aut intersects S
  /// if an only if `given(aut,fact)` intersects S.
  ///
  /// The GIVEN_RESTRICT strategy uses \a fact to restrict the labels
  /// of the \a aut to the subset of assignments that will actually
  /// matter.  The GIVEN_RELAX strategy is almost the opposite: it use
  /// assignments that will never be synchronized with an edge to
  /// enlarge the set of assignments supported by this edge. The
  /// latter enlargment is only done if it reduces the support of the
  /// edge label.
  /// @{
  SPOT_API twa_graph_ptr
  given_here(twa_graph_ptr& aut, const_twa_graph_ptr& fact,
             given_strategy = GIVEN_ALL);
  SPOT_API twa_graph_ptr
  given_here(twa_graph_ptr& aut, formula fact,
             given_strategy = GIVEN_ALL);
  SPOT_API twa_graph_ptr
  given(const_twa_graph_ptr& aut, const_twa_graph_ptr& fact,
        given_strategy = GIVEN_ALL);
  SPOT_API twa_graph_ptr
  given(const_twa_graph_ptr& aut, formula fact,
        given_strategy = GIVEN_ALL);
  /// @}
}
