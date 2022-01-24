// -*- coding: utf-8 -*-
// Copyright (C) 2015, 2016, 2018 Laboratoire de Recherche et Developpement de
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

#include <spot/misc/common.hh>
#include <vector>
#include <string>
#include <climits>
#include <sstream>

namespace spot
{
  /// \brief A cube is only a set of bits in memory.
  ///
  /// This set can be seen as two bitsets
  ///   - true_var  : a bitset representing variables that
  ///                 are set to true
  ///   - false_var : a bitset representing variables that
  ///                 are set to false
  ///
  /// In the  two vectors a bit set to 1 represent a variable set to
  /// true (resp. false) for the true_var (resp. false_var)
  ///
  /// Warning : a variable cannot be set in both bitset at the
  ///           same time (consistency! cannot be true and false)
  ///
  /// The cube for (a & !b) will be repensented by :
  ///     - true_var  = 1 0
  ///     - false_var = 0 1
  ///
  /// To represent free variables such as in (a & !b) | (a & b)
  /// (wich is equivalent to (a) with b free)
  ///     - true_var  : 1 0
  ///     - false_var : 0 0
  /// This exemple shows that the representation of free variables
  /// is done by unsetting variable in both vector
  ///
  /// To be memory efficient, these two bitsets are contigous in memory
  /// i.e. if we want to represent 35 variables, a cube will be
  /// represented by 4 unsigned int contiguous in memory. The 35
  /// first bits represent truth values. The 29 bits following are
  /// useless. Then, the 35 bits represents false value and the
  /// rest is useless.
  ///
  /// \note Useless bits are only to perform some action efficiently,
  /// i.e. only by ignoring them. The manipulation of cubes must be done
  /// using the cubeset class
  /// \note True is naturally represented by all bits (true and false)
  /// being unset. False has no natural unique representation.
  /// As soon as true and false are set for the same var, the cube is false.
  /// To avoid this ambiguity, we consider a cube to be false when the first
  /// bit is set for true and false
  using cube = unsigned*;

  class SPOT_API cubeset final
  {
    // \brief The total number of variables stored
    const unsigned size_;

    /// \brief The number of unsigned needed by the cube (for each part)
    const unsigned uint_size_;

    /// \brief The number of bits for an unsigned int
    const unsigned nb_bits_;

    template<unsigned UI>
    void set_true_var_(cube c, unsigned int x) const
    {
      static_assert((UI == 1) || (UI == -1u),
                    "set_true_var_ needs template to be 1 or -1u");
      assert(is_valid(c)
             && "cubeset::set_true_var(): Received invalid cube.\n");
      if constexpr (UI == -1u)
        {
          unsigned i = x/nb_bits_;
          unsigned r = x-i*nb_bits_;
          unsigned b = 1 << r;
          *(c+i) |= b;
          *(c+uint_size_+i) &= ~b;
        }
      else
        {
          unsigned b = 1 << x;
          *(c) |= b;
          *(c+uint_size_) &= ~b;
        }
    }

  public:
    // Some default/deleted constructor/destructors
    cubeset() = delete;
    ~cubeset() = default;

    /// \brief Build the cubeset manager for \a aps variables
    cubeset(int aps);

    /// \brief Allocate a new cube
    cube alloc() const;

    /// \brief Set the variable at position \a x to true.
    /// \pre cube is valid (asserted)
    /// \post cube is valid (asserted)
    void set_true_var(cube c, unsigned int x) const
    {
      assert(x < size_
             && "cubeset::set_true_var(): index out of bounds");
      switch (uint_size_)
      {
      case 1:
        return set_true_var_<1>(c, x);
      default:
        return set_true_var_<-1u>(c, x);
      }
    }

    /// \brief Set the variable at position \a x to false.
    /// \pre cube is valid (asserted)
    /// \post cube is valid (asserted)
    void set_false_var(cube c, unsigned int x) const;

    /// \brief Check if the variable at position \a x is true.
    /// \pre cube is valid (asserted)
    bool is_true_var(cube c, unsigned int x) const;

    /// \brief Check if the variable at position \a x is false.
    /// \pre cube is valid (asserted)
    bool is_false_var(cube c, unsigned int x) const;

    /// \brief Checks if a cube corresponds to False
    bool is_false(cube c) const;

    /// \brief return true if two cubes intersect, i.e synchronisables.
    bool intersect(const cube lhs, const cube rhs) const;

    /// \brief return a cube resulting from the intersection of the two cubes
    cube intersection(const cube lhs, const cube rhs) const;

    /// \brief from the intersection is two cubes.
    /// Return the new cube and whether or not the intersection is non-empty
    std::pair<cube, bool>
    intersection_check(const cube lhs, const cube rhs) const;

    /// \brief Check whether \a lhs is valid, is there is not variable
    /// that is true and false at the same time.
    bool is_valid(const cube lhs) const;

    /// \brief Return the size of each cube.
    size_t size() const;

    /// \brief Release a cube.
    void release(cube lhs) const;

    /// \brief Raw display cube
    void display(const cube c) const;

    /// \brief Return the cube binded with atomic proposition names
    std::string dump(cube c, const std::vector<std::string>& aps) const;
  };
}
