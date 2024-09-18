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
  enum mcs_tie_break
    {
      ///\brief Break ties by picking the first possible state.
      MCS_TIE_ANY = 0,
      /// \brief Break ties by picking states from the "highest" SCCs
      ///
      /// This is based on the topological ordering of SCCs computed
      /// by scc_info.  The initial state is always in the highest
      /// SCC, and the smallest SCC has no exit.
      MCS_TIE_SCC,
    };


  /// \brief Return an ordering of the vertices computed by
  /// a maximum cardinality search.
  ///
  /// Unlike Tarjan's paper \cite tarjan.84.sicomp , where states are
  /// numbered from N to 1, this numbers the states from 0 to N-1,
  /// starting from the initial state.  The next number is assigned to
  /// a state that maximizes the number of already-numbered neighbors.
  ///
  /// This version returns a vector such that RESULTS[I] is the rank
  /// of state I in the computed order.
  ///
  /// \param tie specify how to break ties.
  SPOT_API std::vector<unsigned>
  maximum_cardinality_search(const const_twa_graph_ptr& a,
                             mcs_tie_break tie = MCS_TIE_ANY);

  /// \brief Reorder the state of \a a according to the order
  /// computed by maximum_cardinality_search().
  ///
  /// This works in place and return the same automaton.
  SPOT_API twa_graph_ptr
  maximum_cardinality_search_reorder_here(twa_graph_ptr a,
                                          mcs_tie_break tie = MCS_TIE_ANY);
}
