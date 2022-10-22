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

  class partition_relabel_dict;

  /// \brief Replace conditions in \a aut with non-overlapping conditions
  /// over fresh variables.
  ///
  /// Partitions the conditions in the automaton, then (binary) encodes
  /// them using fresh propositions.
  /// This can lead to an exponential explosion in the number of
  /// conditions. The operations is aborted if either
  /// the number of new letters exceeds \a max_letter
  /// OR \a max_letter_mult times the number of conditions in the
  /// original automaton
  /// The argument \a select_states can be used to filter out states.
  /// If given, only the transitions leaving states verifying
  /// select_states are taken into account.
  /// All transitions leaving states for whichselect_states
  /// returns false are simply copied over
  /// \note Select states should be used with care, and mostly makes
  /// sense for synthesis to distinguish player and env states
  SPOT_API partition_relabel_dict
  try_partitioned_relabel_here(twa_graph_ptr& aut,
                               bool split = false,
                               unsigned max_letter = -1u,
                               unsigned max_letter_mult = -1u,
                               std::function<bool(unsigned)> select_states
                                 = std::function<bool(unsigned)>(),
                               std::string var_prefix = "__nv");

  class SPOT_API partition_relabel_dict
  {
    friend partition_relabel_dict
              try_partitioned_relabel_here(twa_graph_ptr& aut,
                                           bool split,
                                           unsigned max_letter,
                                           unsigned max_letter_mult,
                                           std::function<bool(unsigned)>
                                               select_states,
                                           std::string car_prefix);
  public:
    // Data structure used to map letters
    using l_map = std::unordered_map<bdd, bdd, bdd_hash>;
  private:
    // The original letters used to relabel the automaton
    l_map orig_letters_;
    // Disjunction of original letters whose images have already been
    // computed
    l_map computed_conditions_;
    // If true, computed results will be stored and can be reused
    // can speed up computation but needs more memory
    // True by default
    bool store_results_ = true;

    // Whether or not relabeling took place
    bool relabel_succ_ = false;

    // The new variables
    std::vector<formula> new_aps_;

    bdd compute_(const bdd& new_cond);
  public:
    partition_relabel_dict() = default;

    partition_relabel_dict(const std::vector<formula>& new_aps,
                           l_map&& orig_letters,
                           l_map&& computed_conditions)
      : orig_letters_{orig_letters}
      , computed_conditions_{computed_conditions}
      , relabel_succ_{true}
      , new_aps_{new_aps}
    {
    }

    void store_results(bool do_store)
    {
      store_results_ = do_store;
    }

    bool succ() const
    {
      return relabel_succ_;
    }

    const std::vector<formula>&
    new_aps() const
    {
      return new_aps_;
    }

    /// \brief Takes a condition over the new variables
    /// \a new_cond and return the corresponding condition
    /// over the old variables
    bdd translate(const bdd& new_cond)
    {
      SPOT_ASSERT(relabel_succ_);
      // First search in orig, then precomputed
      for (const auto& map : {orig_letters_, computed_conditions_})
        {
          auto it = map.find(new_cond);
          if (it != map.end())
            return it->second;
        }

      // Compute
      return compute_(new_cond);
    }
    // todo Do we need/want the other direction
  };

}
