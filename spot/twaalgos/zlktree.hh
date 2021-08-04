// -*- coding: utf-8 -*-
// Copyright (C) 2021 Laboratoire de Recherche et Developpement de
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

#include <iosfwd>
#include <spot/twa/twagraph.hh>

namespace spot
{
  /// \ingroup twa_acc_transform
  /// \brief Zielonka Tree implementation
  ///
  /// This class implements a Zielonka Tree, using
  /// conventions similar to those in \cite casares.21.icalp
  ///
  /// The differences is that this tree is built from Emerson-Lei
  /// acceptance conditions, and can be "walked through" with multiple
  /// colors at once.
  class SPOT_API zielonka_tree
  {
  public:
    /// \brief Build a Zielonka tree from the acceptance condition.
    zielonka_tree(const acc_cond& cond);

    /// \brief The number of branches in the Zielonka tree.
    ///
    /// Branch are designated by the node number of their
    /// leaves.
    unsigned num_branches() const
    {
      return num_branches_;
    }

    /// \brief The number of one branch in the tree.
    ///
    /// This returns the branch whose leave is the smallest one.
    unsigned first_branch() const
    {
      return one_branch_;
    }

    /// \brief Walk through the Zielonka tree.
    ///
    /// Given a \a branch number, and a set of \a colors, this returns
    /// a pair (new branch, level), as needed in definition 3.7 of
    /// \cite casares.21.icalp
    ///
    /// The level correspond to the priority of a minimum parity acceptance
    /// condition, with the parity odd/even as specified by is_even().
    ///
    /// This implementation is slightly different from the original
    /// definition since it allows a set of colors to be processed,
    /// and not exactly one color.  When multiple colors are given,
    /// the minimum corresponding level is returned.  When no color is
    /// given, the branch is not changed and the level returned is one
    /// more than the depth of that branch (this is as if the tree add
    /// another layer of leaves labeled by the empty sets, that do not
    /// store for simplicity).
    std::pair<unsigned, unsigned>
    step(unsigned branch, acc_cond::mark_t colors) const;

    /// \brief Whether the tree corresponds to a min even or min odd
    /// parity acceptance.
    bool is_even() const
    {
      return is_even_;
    }

    /// \brief Whether the Zielonka tree has Rabin shape.
    ///
    /// The tree has Rabin shape of all accepting (round) nodes have
    /// at most one child.
    bool has_rabin_shape() const
    {
      return has_rabin_shape_;
    }

    /// \brief Whether the Zielonka tree has Streett shape.
    ///
    /// The tree has Streett shape of all rejecting (square) nodes have
    /// at most one child.
    bool has_streett_shape() const
    {
      return has_streett_shape_;
    }

    /// \brief Whether the Zielonka tree has parity shape.
    ///
    /// The tree has parity shape of all nodes have at most one child.
    bool has_parity_shape() const
    {
      return has_streett_shape_ && has_rabin_shape_;
    }

    /// \brief Render the tree as in GraphViz format.
    void dot(std::ostream&) const;

  private:
    struct zielonka_node
    {
      unsigned parent;
      unsigned next_sibling = 0;
      unsigned first_child = 0;
      unsigned level;
      acc_cond::mark_t colors;
    };
    std::vector<zielonka_node> nodes_;
    unsigned one_branch_ = 0;
    unsigned num_branches_ = 0;
    bool is_even_;
    bool has_rabin_shape_ = true;
    bool has_streett_shape_ = true;
  };

  /// \ingroup twa_acc_transform
  /// \brief Paritize an automaton using Zielonka tree.
  ///
  /// This corresponds to the application of Section 3 of
  /// \cite casares.21.icalp
  ///
  /// The resulting automaton has a parity acceptance that is either
  /// "min odd" or "min even", depending on the original acceptance.
  /// It may uses up to n+1 colors if the input automaton has n
  /// colors.  Finally, it is colored, i.e., each output transition
  /// has exactly one color.
  SPOT_API
  twa_graph_ptr zielonka_tree_transform(const const_twa_graph_ptr& aut);
}
