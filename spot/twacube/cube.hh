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
#include <atomic>
#include <array>
#include <cstring>

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

  constexpr unsigned MAX_SMALL_CUBE = 2;

  class cubeset;

  using cube_data = unsigned;
  using cube_ptr = cube_data*;
  using const_cube_ptr = const cube_data*;
  using small_cube_array = std::array<cube_data, 2*MAX_SMALL_CUBE>;
  constexpr auto small_true_cube = []()
    {
      auto arr = small_cube_array();
      // fill is not constexpr
      for (auto& x : arr)
        x = static_cast<cube_data>(0);
      return arr;
    }();

  struct large_cube
  {
    cube_ptr raw_ptr;
    const cubeset*  cs;
    large_cube() = default;
    large_cube(cube_ptr raw_ptr_in, const cubeset* const cs_in);
    large_cube(const large_cube&) = delete;
    large_cube& operator=(const large_cube& other);
    ~large_cube() = default; // Raii is assured by cube
  };

  // cube with value semantics
  class cube
  {
    friend cubeset;
    int8_t is_small_; // -1 -> uninitialized, 0 -> large, 1 -> small
    union
    {
      small_cube_array arr_;
      large_cube lc_;
    };
    // Constructor only used to create true and
    // false cubes in cubeset
    cube(bool is_small);
  public:
    cube();
    cube(bool is_small, const small_cube_array& arr);
    cube(bool is_small, cube_ptr raw_ptr, const cubeset* const cs);
    cube(const cube& other);
    cube(cube&& other);

    // Performs a deep copy
    cube& operator=(const cube& other);

    ~cube() noexcept;

    // Do we need them?
    cube& operator=(cube&&) = delete;

    cube_ptr data();
    const_cube_ptr data() const;

  };

  class SPOT_API cubeset final
  {
    friend large_cube;
    friend cube;
    // \brief The total number of variables stored
    size_t size_;

    /// \brief The number of unsigned needed by the cube (for each part)
    size_t uint_size_;

    /// \brief The number of bits for an unsigned int
    size_t nb_bits_;

    /// \brief Whether the cube is small or not
    bool is_small_;

    /// \brief cubes representing true or false
    cube true_cube_;
    cube false_cube_;

    /// \brief Release a cube.
    void release(cube& lhs) const;

  public:
    // Some default/deleted constructor/destructors
    cubeset() = delete;
    ~cubeset() = default;

    /// \brief Build the cubeset manager for \a aps variables
    explicit cubeset(int aps);

    /// \brief Allocate the storage for a large cube
    cube_ptr alloc_raw() const;
    /// \brief Allocate a new cube
    cube alloc() const;

    /// \brief Set the variable at position \a x to true.
    void set_true_var(cube& c, unsigned int x) const;

    /// \brief Set the variable at position \a x to false.
    void set_false_var(cube& c, unsigned int x) const;

    /// \brief Check if the variable at position \a x is true.
    bool is_true_var(const cube& c, unsigned int x) const;

    /// \brief Check if the variable at position \a x is false.
    bool is_false_var(const cube& c, unsigned int x) const;

    /// \brief return true if two cube intersect, i.e synchronisables.
    bool intersect(const cube& lhs, const cube& rhs) const;

    /// \brief return a cube resulting from the intersection of the  two cubes
    cube intersection(const cube& lhs, const cube& rhs) const;

    /// \brief Check wether \a lhs is valid, is there is not variable
    /// that is true and false at the same time.
    bool is_valid(cube& lhs) const;

    /// \brief Return the size of each cube.
    size_t size() const;

    /// \brief Raw display cube
    void display(const cube& c) const;

    /// \brief Return the cube binded with atomic proposition names
    std::string dump(const cube& c,
                     const std::vector<std::string>& aps) const;
  };
}

// Implementations cube
namespace spot
{
  inline large_cube::large_cube(cube_ptr raw_ptr_in, const cubeset* const cs_in)
      : raw_ptr{raw_ptr_in}
      , cs{cs_in}
    {
      SPOT_ASSERT(cs && "large_cube needs cubeset");
    }

  inline large_cube& large_cube::operator=(const large_cube& other)
    {
      SPOT_ASSERT((cs->size() == other.cs->size())
                   && "Can not assign between different sizes.");
      std::memcpy(raw_ptr, other.raw_ptr,
                  2*cs->size()*sizeof(cube_data));
      return *this;
    }

  inline cube::cube()
      : is_small_{-1}
    {
    }

  inline cube::cube(bool is_small)
      : is_small_{is_small}
    {
    }

  inline cube::cube(bool is_small, const small_cube_array& arr)
      : is_small_{is_small}
      , arr_{arr}
    {
      SPOT_ASSERT(is_small
                  && "cube: Calling small constructor for large cube");
    }

  inline cube::cube(bool is_small, cube_ptr raw_ptr,
                    const cubeset* const cs)
      : is_small_{is_small}
      , lc_(raw_ptr, cs)
    {
      SPOT_ASSERT(!is_small
                  && "cube: Calling large constructor for small cube");
    }

  inline cube::cube(const cube& other)
      : cube(other.is_small_)
    {
      if (is_small_ == 1)
        arr_ = other.arr_;
      else if (is_small_ == 0)
        {
          lc_.cs = other.lc_.cs;
          lc_.raw_ptr = lc_.cs->alloc_raw();
          lc_ = other.lc_;
        }
      // Nothing to do for uninitialized
    }

  inline cube::cube(cube&& other)
      : cube(other.is_small_)
    {
      if (other.is_small_ == 1)
        arr_ = other.arr_;
      else if (other.is_small_ == 0)
        {
          lc_.cs = std::exchange(other.lc_.cs,
                                nullptr);
          lc_.raw_ptr = std::exchange(other.lc_.raw_ptr,
                                      nullptr);
          other.is_small_ = -1;
        }
    }

  inline cube& cube::operator=(const cube& other)
    {
      SPOT_ASSERT(((is_small_ == other.is_small_)
                    || (is_small_ == -1)
                    || (other.is_small_ == -1))
                  && "Can not copy between small and large cubes");
      if ((is_small_ == 1) & (other.is_small_ == 1))
        arr_ = other.arr_;
      else if ((is_small_ == 0) & (other.is_small_ == 0))
        {
          // Possibly changes cubeset
          if (lc_.cs != other.lc_.cs)
            {
              lc_.cs->release(*this);
              lc_.cs = other.lc_.cs;
              lc_.raw_ptr = lc_.cs->alloc_raw();
            }
          lc_ = other.lc_;
        }
      else
        {
          if (is_small_ == -1)
            {
              if (other.is_small_ == 1)
                {
                  is_small_ = 1;
                  arr_ = other.arr_;
                }
              else if (other.is_small_ == 0)
                {
                  is_small_ = 0;
                  lc_.cs = other.lc_.cs;
                  lc_.raw_ptr = lc_.cs->alloc_raw();
                  lc_ = other.lc_;
                }
            }
          else if (other.is_small_ == -1)
            {
              // Other is unitialized
              if (is_small_)
                  is_small_ = -1;
              else
                {
                  lc_.cs->release(*this);
                  lc_.cs = nullptr;
                  is_small_ = -1;
                }
            }
        }
      return *this;
    }

  inline cube::~cube() noexcept
    {
      // Nothing to do if small or uninitialized
      if (is_small_ == 0)
        lc_.cs->release(*this);
    }

  inline cube_ptr cube::data()
    {
      SPOT_ASSERT(is_small_ != -1
                  && "Can not access data of uninitialized cube");
      if (is_small_ == 1)
        return arr_.data();
      else
        return lc_.raw_ptr;
    }

  inline const_cube_ptr cube::data() const
    {
      SPOT_ASSERT(is_small_ != -1
                  && "Can not access data of uninitialized cube");
      if (is_small_ == 1)
        return arr_.data();
      else
        return lc_.raw_ptr;
    }

}

// Implementations cubeset
namespace spot
{
  inline cubeset::cubeset(int aps)
      : size_(aps)
      , uint_size_(size_/(sizeof(unsigned int) * CHAR_BIT)
                  + 1*((size_%(sizeof(unsigned int) * CHAR_BIT)) != 0))
      , nb_bits_(sizeof(unsigned int) * CHAR_BIT)
      , is_small_{(unsigned) (size_/(sizeof(unsigned int) * CHAR_BIT)
                  + 1*((size_%(sizeof(unsigned int) * CHAR_BIT)) != 0))
                  <= MAX_SMALL_CUBE}
      , true_cube_()
      , false_cube_()
    {
      //define move assignement just for this?
      auto t = alloc();
      auto f = alloc();
      true_cube_ = t;
      false_cube_ = f;

      *false_cube_.data() &= 1;
      *(false_cube_.data() + uint_size_) &= 1;
    }

  inline cube_ptr cubeset::alloc_raw() const
    {
      SPOT_ASSERT(!is_small_
                  && "Allocating large cube, but cubeset is small");
      return new cube_data[2*uint_size_]();
    }

  inline cube cubeset::alloc() const
    {
      if (is_small_)
        return cube(is_small_, small_true_cube);
      else
        return cube(is_small_,
                    alloc_raw(),
                    this);
    }

  inline void cubeset::set_true_var(cube& c, unsigned int x) const
    {
      auto cd = c.data();
      auto i = x/nb_bits_;
      auto shift = x - i*nb_bits_;
      *(cd+i) |= 1 << shift;
      *(cd+uint_size_+i) &= ~(1 << shift);
    }

  inline void cubeset::set_false_var(cube& c, unsigned int x) const
    {
      auto cd = c.data();
      auto i = x/nb_bits_;
      auto shift = x - i*nb_bits_;
      *(cd+uint_size_+i) |= 1 << shift;
      *(cd+i) &= ~(1 << shift);
    }

  inline bool cubeset::is_true_var(const cube& c, unsigned int x) const
    {
      auto cd = c.data();
      unsigned int i = x/nb_bits_;
      auto shift = x - i*nb_bits_;
      // before: (*(c+i) >> x)
      // technically UB, but ok for most compilers
      bool true_var = (*(cd+i) >> shift) & 1;
      SPOT_ASSERT((!true_var
                  || !((*(cd+i+uint_size_) >> shift) & 1))
                  && "Cube is not valid!");
      return true_var;
    }

  inline bool cubeset::is_false_var(const cube& c, unsigned int x) const
    {
      auto cd = c.data();
      unsigned int i = x/nb_bits_;
      auto shift = x - i*nb_bits_;
      bool false_var = (*(cd+i+uint_size_) >> shift) & 1;
      SPOT_ASSERT((!false_var
                  || !((*(cd+i) >> shift) & 1))
                  && "Cube is not valid!");
      return false_var;
    }

  inline bool cubeset::intersect(const cube& lhs, const cube& rhs) const
    {
      cube_data true_elt;
      cube_data false_elt;
      auto lhsd = lhs.data();
      auto rhsd = rhs.data();
      for (auto i = 0u; i < uint_size_; ++i)
        {
          true_elt = *(lhsd+i) | *(rhsd+i);
          false_elt = *(lhsd+i+uint_size_) | *(rhsd+i+uint_size_);
          if (true_elt & false_elt)
            return false;
        }
      return true;
    }

  inline cube cubeset::intersection(const cube& lhs, const cube& rhs) const
    {
      auto res = alloc();
      auto resd = res.data();
      auto lhsd = lhs.data();
      auto rhsd = rhs.data();
      for (auto i = 0u; i < uint_size_; ++i)
        {
          resd[i] = *(lhsd+i) | *(rhsd+i);
          resd[i+uint_size_] = *(lhsd+i+uint_size_) | *(rhsd+i+uint_size_);
          if (resd[i] & resd[i+uint_size_])
            {
              // true and false -> False
              release(res);
              // Do we want the cctor just for this?
              if (is_small_)
                return cube(is_small_, false_cube_.arr_);
              else
              return false_cube_;
            }
        }
      return res;
    }

  inline bool cubeset::is_valid(cube& lhs) const
    {
      auto lhsd = lhs.data();
      for (auto i = 0u; i < uint_size_; ++i)
        if (*(lhsd+i) & *(lhsd+i+uint_size_))
          {
            *lhsd &= 1u;
            *(lhsd + uint_size_) &= 1u;
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
      if (!is_small_)
        {
          delete[] c.lc_.raw_ptr;
          c.lc_.raw_ptr = nullptr;
        }
    }
}