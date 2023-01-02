// -*- coding: utf-8 -*-
// Copyright (C) 2015, 2017 Laboratoire de Recherche et Développement de
// l'Epita (LRDE).
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
  relabel_here(twa_graph_ptr& aut, relabeling_map* relmap);

  /// \brief Helper structure for partitioned relabeling result
  ///
  /// Relabeling but may succeed, but the actual relabeling map
  /// might not be needed.
  class SPOT_API ext_relabeling_map
  {
  public:
    ext_relabeling_map(bool succ = false)
      : rel_map_{}
      , success_(succ)
    {
    }

    ext_relabeling_map(const relabeling_map& rl)
      : rel_map_{rl}
      , success_(rl.size())
    {
    }

    ext_relabeling_map(relabeling_map&& rl)
      : rel_map_{std::move(rl)}
      , success_(rel_map_.size())
    {
    }

    operator const relabeling_map&() const
    {
      return rel_map_;
    }

    operator relabeling_map&()
    {
      return rel_map_;
    }

    operator const relabeling_map*() const
    {
      return &rel_map_;
    }

    operator relabeling_map*()
    {
      return &rel_map_;
    }

    const relabeling_map& get_map() const
    {
      return rel_map_;
    }

    relabeling_map& get_map()
    {
      return rel_map_;
    }

    size_t size() const
    {
      return rel_map_.size();
    }

    bool empty() const
    {
      return rel_map_.empty();
    }
    
    bool success() const
    {
      return success_;
    }

  private:
    relabeling_map rel_map_;
    bool success_;
  };

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
  ///
  /// \note If concerned_ap is given, then there may not be an edge
  /// whose condition uses ap inside AND outside of concerned_ap.
  /// Mostly used in a game setting to distinguish between
  /// env and player transitions.
  SPOT_API ext_relabeling_map
  partitioned_relabel_here(twa_graph_ptr& aut, bool split = false,
                           unsigned max_letter = -1u,
                           unsigned max_letter_mult = -1u,
                           const bdd& concerned_ap = bddtrue,
                           std::string var_prefix = "__nv",
                           bool need_map = true);

}
