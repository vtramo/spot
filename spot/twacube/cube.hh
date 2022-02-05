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
#include <array>
#include <string>
#include <climits>
#include <sstream>

constexpr size_t MAXSMALLCUBE = 2;

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
//  using cube = unsigned*;

  using cubeptr = unsigned*;
  using c_cubeptr = const unsigned*;
  union cube_int{
    cube_int():ptr{nullptr} {};
    cube_int(cubeptr c):ptr{c} {};
    cube_int(std::array<unsigned, 2*MAXSMALLCUBE> c):a{c} {};

    cubeptr ptr;
    std::array<unsigned, 2*MAXSMALLCUBE> a;
  };
  // For small cubes, false is equiv to nullptr
  struct cube{
    cube_int ci;
    char state; //0 -> invalid, 1 -> small / array, 2 -> large / ptr

    cube():ci(), state{0}{}
    cube(const cube& o):ci{o.ci}, state{o.state}{}
    cube(cubeptr c):ci{c}, state{2} {};
    cube(std::array<unsigned, 2*MAXSMALLCUBE> c):ci{c}, state{1} {};
    cube& operator=(const cube& other) = default;

    operator bool() const{
      return state;
    }
  };




  class SPOT_API cubeset final
  {
    // \brief The total number of variables stored
    const unsigned size_;

    /// \brief The number of unsigned needed by the cube (for each part)
    const unsigned uint_size_;

    /// \brief The number of bits for an unsigned int
    const unsigned nb_bits_;

    template<unsigned UI>
    void set_true_var_(cubeptr c, unsigned int x) const
    {
      static_assert((UI == 1) || (UI == -1u),
                    "set_true_var_ needs template to be 1 or -1u");
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
          *c |= b;
          *(c+uint_size_) &= ~b;
        }
    }

    template<unsigned UI>
    void set_false_var_(cubeptr c, unsigned int x) const
    {
      static_assert((UI == 1) || (UI == -1u),
                    "set_false_var_ needs template to be 1 or -1u");
      if constexpr (UI == -1u)
        {
          unsigned i = x/nb_bits_;
          unsigned r = x-i*nb_bits_;
          *(c+uint_size_+i) |= 1 << r;
          *(c+i) &= ~(1 << r);
        }
      else
        {
          *(c+uint_size_) |= 1 << x;
          *c &= ~(1 << x);
        }
    }

  template<unsigned UI>
  bool is_true_var_(c_cubeptr c, unsigned int x) const
    {
      static_assert((UI == 1) || (UI == -1u),
                    "is_true_var_ needs template to be 1 or -1u");
      if constexpr (UI == -1u)
        {
          unsigned i = x/nb_bits_;
          unsigned r = x-i*nb_bits_;
          bool true_var = (*(c+i) >> r) & 1;
          return true_var;
        }
      else
        return (*c >> x) & 1;
    }
  template<unsigned UI>
  bool is_false_var_(c_cubeptr c, unsigned int x) const
  {
    static_assert((UI == 1) || (UI == -1u),
                  "is_false_var_ needs template to be 1 or -1u");
    if constexpr (UI == -1u)
      {
        unsigned i = x/nb_bits_;
        unsigned r = x-i*nb_bits_;
        bool false_var = (*(c+uint_size_+i) >> r) & 1;
        return false_var;
      }
    else
      return (*(c+uint_size_) >> x) & 1;
  }

  // todo: make it a function in a private header?
  template<unsigned UI, bool dummy = false>
  bool intersect_(c_cubeptr lhs, c_cubeptr rhs) const
  {
    unsigned true_elt;
    unsigned false_elt;
    for (unsigned int i = 0; i < UI; ++i)
      {
        true_elt = *(lhs+i) | *(rhs+i);
        false_elt = *(lhs+i+uint_size_) | *(rhs+i+uint_size_);
        if (true_elt & false_elt)
          return false;
      }

    return true;
  }

  bool intersect_dyn_(c_cubeptr lhs, c_cubeptr rhs) const
  {
    unsigned true_elt;
    unsigned false_elt;
    for (unsigned int i = 0; i < uint_size_; ++i)
    {
      true_elt = *(lhs+i) | *(rhs+i);
      false_elt = *(lhs+i+uint_size_) | *(rhs+i+uint_size_);
      if (true_elt & false_elt)
        return false;
    }

    return true;
  }

  template<unsigned UI>
  std::pair<cube, bool>
  intersection_check_(c_cubeptr lhs, c_cubeptr rhs) const
  {
    // todo this needs to be constexpr
    auto res = alloc();
    auto rawptr = (uint_size_ <= MAXSMALLCUBE) ? res.ci.a.data() : res.ci.ptr;

    for (unsigned i = 0; i < UI; ++i)
      {
        rawptr[i] = *(lhs+i) | *(rhs+i);
        rawptr[i+uint_size_] = *(lhs+i+uint_size_) | *(rhs+i+uint_size_);
        if (rawptr[i] & rawptr[i+uint_size_])
          {
            // If incompatible, the actual values are no longer of interest
            // but make sure to be false
            release(res);
            return std::make_pair(null(), false);
          }
      }
    return std::make_pair(res, true);
  }

  std::pair<cube, bool>
  intersection_check_dyn_(const cubeptr lhs, const cubeptr rhs) const
  {
    auto res = alloc();
    auto rawptr = (uint_size_ <= MAXSMALLCUBE) ? res.ci.a.data() : res.ci.ptr;

    for (unsigned i = 0; i < uint_size_; ++i)
    {
      rawptr[i] = *(lhs+i) | *(rhs+i);
      rawptr[i+uint_size_] = *(lhs+i+uint_size_) | *(rhs+i+uint_size_);
      if (rawptr[i] & rawptr[i+uint_size_])
      {
        // If incompatible, the actual values are no longer of interest
        // but make sure to be false
        release(res);
        return std::make_pair(null(), false);
      }
    }
    return std::make_pair(res, true);
  }

  template<unsigned UI>
  bool is_valid_(c_cubeptr lhs) const
  {
    for (unsigned i = 0; i < UI; ++i)
      if (*(lhs+i) & *(lhs+i+uint_size_))
        return false;
    return true;
  }

  bool is_valid_dyn_(c_cubeptr lhs) const
  {
    for (unsigned i = 0; i < uint_size_; ++i)
      if (*(lhs+i) & *(lhs+i+uint_size_))
        return false;
    return true;
  }

  public:
    size_t uint_size() const {return uint_size_; }
    size_t nb_bits() const {return nb_bits_; }

    // Some default/deleted constructor/destructors
    cubeset() = delete;
    ~cubeset() = default;

    /// \brief Build the cubeset manager for \a aps variables
    cubeset(int aps);

    /// \brief Allocate a new cube
    cube alloc() const;

    /// \brief Return a "nullptr"
    cube null() const{
      return cube();
    }

    /// \brief Set the variable at position \a x to true.
    /// \pre cube is valid (asserted)
    /// \post cube is valid (asserted)
    void set_true_var(cube& c, unsigned int x) const
    {
      SPOT_ASSERT(x < size_
                  && "cubeset::set_true_var(): index out of bounds");
      SPOT_ASSERT(c && is_valid(c)
                  && "cubeset::set_true_var(): Received invalid cube.\n");
      switch (uint_size_)
      {
      case 1:
        return set_true_var_<1>(c.ci.a.data(), x);
      case 2:
        return set_true_var_<-1u>(c.ci.a.data(), x);
      default:
      {
        assert(uint_size_ > MAXSMALLCUBE);
        return set_true_var_<-1u>(c.ci.ptr, x);
      }

      }
    }

    /// \brief Set the variable at position \a x to false.
    /// \pre cube is valid (asserted)
    /// \post cube is valid (asserted)
    void set_false_var(cube& c, unsigned int x) const
    {
      SPOT_ASSERT(x < size_
                  && "cubeset::set_false_var(): index out of bounds");
      SPOT_ASSERT(c && is_valid(c)
                  && "cubeset::set_false_var(): Received invalid cube.\n");
      switch (uint_size_)
      {
      case 1:
        return set_false_var_<1>(c.ci.a.data(), x);
      case 2:
        return set_false_var_<-1u>(c.ci.a.data(), x);
      default:
      {
        assert(uint_size_ > MAXSMALLCUBE);
        return set_false_var_<-1u>(c.ci.ptr, x);
      }
      }
    }

    /// \brief Check if the variable at position \a x is true.
    /// \pre cube is valid (asserted)
    bool is_true_var(const cube& c, unsigned int x) const
    {
      SPOT_ASSERT(x < size_
                  && "cubeset::is_true_var(): index out of bounds");
      SPOT_ASSERT(c && is_valid(c)
                  && "cubeset::is_true_var(): Received invalid cube.\n");
      switch (uint_size_)
      {
      case 1:
        return is_true_var_<1>(c.ci.a.data(), x);
      case 2:
        return is_true_var_<-1u>(c.ci.a.data(), x);
      default:
      {
        assert(uint_size_ > MAXSMALLCUBE);
        return is_true_var_<-1u>(c.ci.ptr, x);
      }
      }
    }

    /// \brief Check if the variable at position \a x is false.
    /// \pre cube is valid (asserted)
    bool is_false_var(const cube& c, unsigned int x) const
    {
      SPOT_ASSERT(x < size_
                  && "cubeset::is_false_var(): index out of bounds");
      SPOT_ASSERT(c && is_valid(c)
                  && "cubeset::is_false_var(): Received invalid cube.\n");
      switch (uint_size_)
      {
      case 1:
        return is_false_var_<1>(c.ci.a.data(), x);
      case 2:
        return is_false_var_<-1u>(c.ci.a.data(), x);
      default:
      {
        assert(uint_size_ > MAXSMALLCUBE);
        return is_false_var_<-1u>(c.ci.ptr, x);
      }
      }
    }

    /// \brief Checks if a cube corresponds to False
    bool is_false(const cube& c) const
    {
      switch (uint_size_)
      {
      case 1:
        return (c.ci.a[0] & 1) & (c.ci.a[1] & 1);
      case 2:
        return (c.ci.a[0] & 1) & (c.ci.a[2] & 1);
      default:
      {
        // Use state?
        auto rawptr = (uint_size_ <= MAXSMALLCUBE) ? c.ci.a.data() : c.ci.ptr;
        return *rawptr & *(rawptr + uint_size_) & 1;;
      }
      }
    }

    /// \brief return true if two cubes intersect, i.e synchronisables.
    bool intersect(const cube& lhs, const cube& rhs) const
    {
      switch(uint_size_)
      {
      case 1:
        return intersect_<1>(lhs.ci.a.data(), rhs.ci.a.data());
      case 2:
        return intersect_<2>(lhs.ci.a.data(), rhs.ci.a.data());
      case 3:
        return intersect_<3>(lhs.ci.ptr, rhs.ci.ptr);
      case 4:
        return intersect_<4>(lhs.ci.ptr, rhs.ci.ptr);
      default:
        return intersect_dyn_(lhs.ci.ptr, rhs.ci.ptr);
      }
    }

    /// \brief return a cube resulting from the intersection of the two cubes
    cube intersection(const cube& lhs, const cube& rhs) const
    {
      return intersection_check(lhs, rhs).first;
    }

    /// \brief from the intersection is two cubes.
    /// Return the new cube and whether or not the intersection is non-empty
    std::pair<cube, bool>
    intersection_check(const cube& lhs, const cube& rhs) const
    {
      switch(uint_size_)
      {
      case 1:
        return intersection_check_<1>(lhs.ci.a.data(), rhs.ci.a.data());
      case 2:
        return intersection_check_<2>(lhs.ci.a.data(), rhs.ci.a.data());
      case 3:
        return intersection_check_<3>(lhs.ci.ptr, rhs.ci.ptr);
      case 4:
        return intersection_check_<4>(lhs.ci.ptr, rhs.ci.ptr);
      default:
        return intersection_check_dyn_(lhs.ci.ptr, rhs.ci.ptr);
      }
    }

    /// \brief Check whether \a lhs is valid, is there is not variable
    /// that is true and false at the same time.
    bool is_valid(const cube& lhs) const
    {
      switch (uint_size_)
      {
      case 1:
        return is_valid_<1>(lhs.ci.a.data());
      case 2:
        return is_valid_<2>(lhs.ci.a.data());
      case 3:
        return is_valid_<3>(lhs.ci.ptr);
      case 4:
        return is_valid_<4>(lhs.ci.ptr);
      default:
        return is_valid_dyn_(lhs.ci.ptr);
      }
    }

    /// \brief Verify that a cube does not correspond to False.
    /// If it is false, put in cannoncical form
    bool make_valid(cube& lhs) const
    {
      if (!is_valid(lhs))
        {
          auto rawptr = (uint_size_ <= MAXSMALLCUBE) ? lhs.ci.a.data() : lhs.ci.ptr;
          *(rawptr) = 1;
          *(rawptr+uint_size_) = 1;
          return false;
        }
      return true;
    }

    /// \brief Return the size of each cube.
    size_t size() const
    {
      return size_;
    }

    /// \brief Release a cube.
    void release(cube& lhs) const;

    /// \brief Raw display cube
    void display(const cube& c) const;

    /// \brief Return the cube binded with atomic proposition names
    std::string dump(const cube& c, const std::vector<std::string>& aps) const;
  };
}
