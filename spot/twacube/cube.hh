// -*- coding: utf-8 -*-
// Copyright (C) 2015, 2016, 2018, 2022 Laboratoire de
// Recherche et Developpement de l'Epita (LRDE).
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
#include <iostream>
#include <type_traits>

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
  /// Warning : True is representing by a cube with all bits being zero
  ///           however there is no cannonical representation for False.
  ///           By convention we say a cube is False if it is either null
  ///           or it has at least one variable that is true and false.
  ///           If an invalid state is detected, the first variable
  ///           will be set to true and false.
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
  /// Note that useless bits are only to perform some action efficiently,
  /// i.e. only by ignoring them. The manipulation of cubes must be done
  /// using the cubeset class
  using cube = unsigned*;

  class SPOT_API cubeset final
  {
    // \brief The total number of variables stored
    size_t size_;

    /// \brief The number of unsigned needed by the cube (for each part)
    size_t uint_size_;

    /// \brief The number of bits for an unsigned int
    size_t nb_bits_;

  public:
    // Some default/deleted constructor/destructors
    cubeset() = delete;
    ~cubeset() = default;

    /// \brief Build the cubeset manager for \a aps variables
    explicit cubeset(int aps);

    /// \brief Allocate a new cube
    cube alloc() const;

    /// \brief Set the variable at position \a x to true.
    void set_true_var(cube c, unsigned int x) const;

    /// \brief Set the variable at position \a x to false.
    void set_false_var(cube c, unsigned int x) const;

    /// \brief Check if the variable at position \a x is true.
    bool is_true_var(cube c, unsigned int x) const;

    /// \brief Check if the variable at position \a x is false.
    bool is_false_var(cube c, unsigned int x) const;

    /// \brief return true if two cube intersect, i.e synchronisables.
    bool intersect(const cube lhs, const cube rhs) const;

    /// \brief return a cube resulting from the intersection of the  two cubes
    cube intersection(const cube lhs, const cube rhs) const;

    /// \brief Check wether \a lhs is valid, is there is not variable
    /// that is true and false at the same time.
    bool is_valid(cube& lhs) const;

    /// \brief Return the size of each cube.
    size_t size() const;

    /// \brief Release a cube.
    void release(cube& lhs) const;

    /// \brief Raw display cube
    void display(const cube c) const;

    /// \brief Return the cube binded with atomic proposition names
    std::string dump(cube c, const std::vector<std::string>& aps) const;
  };
}

// Implementations
namespace spot
{
  inline cubeset::cubeset(int aps)
    : size_(aps)
    , uint_size_(size_/(sizeof(unsigned int) * CHAR_BIT)
                 + 1*((size_%(sizeof(unsigned int) * CHAR_BIT)) != 0))
    , nb_bits_(sizeof(unsigned int) * CHAR_BIT)
  {
  }

  inline cube cubeset::alloc() const
  {
    return new unsigned int[2*uint_size_]();
  }

  inline void cubeset::set_true_var(cube c, unsigned int x) const
  {
    auto i = x/nb_bits_;
    auto shift = x - i*nb_bits_;
    *(c+i) |= 1 << shift;
    *(c+uint_size_+i) &= ~(1 << shift);
  }

  inline void cubeset::set_false_var(cube c, unsigned int x) const
  {
    auto i = x/nb_bits_;
    auto shift = x - i*nb_bits_;
    *(c+uint_size_+i) |= 1 << shift;
    *(c+i) &= ~(1 << shift);
  }

  inline bool cubeset::is_true_var(cube c, unsigned int x) const
  {
    unsigned int i = x/nb_bits_;
    auto shift = x - i*nb_bits_;
    // before: (*(c+i) >> x)
    // technically UB, but ok for most compilers
    bool true_var = (*(c+i) >> shift) & 1;
    SPOT_ASSERT((!true_var
                 || !((*(c+i+uint_size_) >> shift) & 1))
                 && "Cube is not valid!");
    return true_var;
  }

  inline bool cubeset::is_false_var(cube c, unsigned int x) const
  {
    unsigned int i = x/nb_bits_;
    auto shift = x - i*nb_bits_;
    bool false_var = (*(c+i+uint_size_) >> shift) & 1;
    SPOT_ASSERT((!false_var
                 || !((*(c+i) >> shift) & 1))
                 && "Cube is not valid!");
    return false_var;
  }

  inline bool cubeset::intersect(const cube lhs, const cube rhs) const
  {
    std::remove_pointer_t<cube> true_elt;
    std::remove_pointer_t<cube> false_elt;
    for (auto i = 0u; i < uint_size_; ++i)
      {
        true_elt = *(lhs+i) | *(rhs+i);
        false_elt = *(lhs+i+uint_size_) | *(rhs+i+uint_size_);
        if (true_elt & false_elt)
          return false;
      }
    return true;
  }

  inline cube cubeset::intersection(const cube lhs, const cube rhs) const
  {
    auto res = alloc();
    for (auto i = 0u; i < uint_size_; ++i)
      {
        res[i] = *(lhs+i) | *(rhs+i);
        res[i+uint_size_] = *(lhs+i+uint_size_) | *(rhs+i+uint_size_);
        if (res[i] & res[i+uint_size_])
          {
            // true and false -> False
            release(res);
            return nullptr;
          }
      }
    return res;
  }

  inline bool cubeset::is_valid(cube& lhs) const
  {
    for (auto i = 0u; i < uint_size_; ++i)
      if (*(lhs+i) & *(lhs+i+uint_size_))
        {
           *lhs &= 1u;
           *(lhs + uint_size_) &= 1u;
           return false;
        }
    return true;
  }

  inline size_t cubeset::size() const
  {
    return size_;
  }

  inline void cubeset::release(cube& c) const
  {
    delete[] c;
    c = nullptr;
  }
}