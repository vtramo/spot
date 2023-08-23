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

#include <spot/tl/relabel.hh>
#include <spot/twa/twagraph.hh>
#include <spot/misc/bddlt.hh>

#include <optional>
#include <functional>

namespace spot
{
  /// \brief replace atomic propositions in an automaton
  ///
  /// The relabeling map \a relmap should have keys that are atomic
  /// propositions, and values that are Boolean formulas.
  ///
  /// This function is typically used with maps produced by relabel()
  /// or relabel_bse().
  SPOT_API void
  relabel_here(const twa_graph_ptr& aut, relabeling_map* relmap);

  /// \defgroup Partitioned relabel here
  /// @{
  /// \brief Replace conditions in \a aut with non-overlapping conditions
  /// over fresh variables.
  ///
  /// Partitions the conditions in the automaton, then (binary) encodes
  /// them using fresh propositions.
  /// This can lead to an exponential explosion in the number of
  /// conditions. The operations is aborted if either
  /// the number of new letters (subsets of the partition) exceeds
  /// \a max_letter OR \a max_letter_mult times the number of conditions
  ///  in the original automaton.
  /// The argument \a concerned_ap can be used to filter out transitions.
  /// If given, only the transitions whose support intersects the
  /// concerned_ap (or whose condition is T) are taken into account.
  /// The fresh aps will be enumerated and prefixed by \a var_prefix.
  /// These variables need to be fresh, i.e. may not exist yet (not checked)
  /// If \a split and \a sort is true, then the new labels
  /// will appear in sorted order. That is the edge conditions
  /// will be increasing with respect bdd_stable_less.
  /// \param aut The automaton to relabel
  /// \param split Determines whether to use leaves of the partition, i.e.
  /// conditions that behave like letters
  /// \param max_letter Maximal number of letters before aborting
  /// -1u to deactivate
  /// \param max_letter_mult Abort when the number of letters exceeds
  /// max_letter_mult times the number of different conditions in the
  /// original automaton
  /// \param concerned_ap Which APs to relabel. bddtrue for all. If different
  /// from bddtrue this needs to be a conjunction of APs, all conditions whose
  /// support is covered by this are relabeled.
  /// \param var_prefix Prefix used to generate fresh APs
  /// \param sort Whether the edges in the relabeled automaton appear in a
  /// sorted manner.
  /// \note To ensure reproducibility, \a sort needs to be true.
  /// \note If concerned_ap is given, then there may not be an edge
  /// whose condition uses ap inside AND outside of concerned_ap.
  /// Mostly used in a game setting to distinguish between
  /// env and player transitions.
  SPOT_API relabeling_map
  partitioned_relabel_here(const twa_graph_ptr& aut, bool split,
                           unsigned max_letter,
                           unsigned max_letter_mult,
                           const bdd& concerned_ap,
                           std::string var_prefix,
                           bool sort);
  /// \brief Treats all APs with no stop condition
  SPOT_API relabeling_map
  partitioned_relabel_here(const twa_graph_ptr& aut, bool split = false,
                           bool sort = true,
                           std::string var_prefix = "__nv");
  /// @}
}
