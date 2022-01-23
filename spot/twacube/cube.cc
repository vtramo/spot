// -*- coding: utf-8 -*-
// Copyright (C) 2015, 2016, 2018, 2020, 2021 Laboratoire de Recherche et
// Developpement de l'Epita (LRDE).
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

#include "config.h"
#include <sstream>
#include <iostream>
#include <spot/twacube/cube.hh>
#include <cassert>

namespace spot
{
  cubeset::cubeset(int aps)
    : size_(aps)
    , uint_size_(size_/(sizeof(unsigned int) * CHAR_BIT)
                 + 1*((size_%(sizeof(unsigned int) * CHAR_BIT)) != 0))
    , nb_bits_(sizeof(unsigned int) * CHAR_BIT)
  {
//    size_ = aps;
//    nb_bits_ = sizeof(unsigned int) * CHAR_BIT;
//    uint_size_ = 1;
//    while ((aps = aps -  nb_bits_)>0)
//      ++uint_size_;
//    assert(uint_size_ == size_/nb_bits_ + 1*((size_%nb_bits_) != 0));
  }

  cube cubeset::alloc() const
  {
    return new unsigned int[2*uint_size_]();
  }

  void cubeset::set_true_var(cube c, unsigned int x) const
  {
    assert(is_valid(c)
           && "cubeset::set_true_var(): Received invalid cube.\n");
    unsigned int i = x/nb_bits_;
    unsigned r = x-i*nb_bits_;
    *(c+i) |= 1 << r;
    *(c+uint_size_+i) &= ~(1 << r);
  }

  void cubeset::set_false_var(cube c, unsigned int x) const
  {
    assert(is_valid(c)
           && "cubeset::set_false_var(): Received invalid cube.\n");
    unsigned int i = x/nb_bits_;
    unsigned r = x-i*nb_bits_;
    *(c+uint_size_+i) |= 1 << r;
    *(c+i) &= ~(1 << r);
  }

  bool cubeset::is_true_var(cube c, unsigned int x) const
  {
    assert(is_valid(c)
           && "cubeset::is_true_var(): Received invalid cube.\n");
    unsigned int i = x/nb_bits_;
    unsigned r = x-i*nb_bits_;
    bool true_var = (*(c+i) >> r) & 1;
    return true_var;
  }

  bool cubeset::is_false_var(cube c, unsigned int x) const
  {
    assert(is_valid(c)
           && "cubeset::is_false_var(): Received invalid cube.\n");
    unsigned i = x/nb_bits_;
    unsigned r = x-i*nb_bits_;
    bool false_var = (*(c+i+uint_size_) >> r) & 1;
    return false_var;
  }

  bool cubeset::is_false(cube c) const
  {
    return *c & *(c + uint_size_) & 1;
  }

  bool cubeset::intersect(const cube lhs, const cube rhs) const
  {
    unsigned int true_elt;
    unsigned int false_elt;
    bool incompatible = false;
    for (unsigned int i = 0; i < uint_size_ && !incompatible; ++i)
      {
        true_elt = *(lhs+i) | *(rhs+i);
        false_elt = *(lhs+i+uint_size_) | *(rhs+i+uint_size_);
        incompatible |=  (true_elt & false_elt);
      }

    return !incompatible;
  }

  std::pair<cube, bool>
  cubeset::intersection_check(const cube lhs, const cube rhs) const
  {
    auto* res = alloc();
    for (unsigned int i = 0; i < uint_size_; ++i)
      {
        res[i] = *(lhs+i) | *(rhs+i);
        res[i+uint_size_] = *(lhs+i+uint_size_) | *(rhs+i+uint_size_);
        if (res[i] & res[i+uint_size_])
          {
            // If incompatible, the actual values are no longer of interest
            // but make sure to be false
            *res = 1;
            *(res + uint_size_) = 1;
          }
      }
    return std::make_pair(res, true);
  }

  cube cubeset::intersection(const cube lhs, const cube rhs) const
  {
    return intersection_check(lhs, rhs).first;
  }

  bool cubeset::is_valid(const cube lhs) const
  {
    bool incompatible = false;
    for (unsigned int i = 0; i < uint_size_ && !incompatible; ++i)
      incompatible |= *(lhs+i) & *(lhs+i+uint_size_);
    return !incompatible;
  }

  size_t cubeset::size() const
  {
    return size_;
  }

  void cubeset::release(cube c) const
  {
    delete[] c;
  }

  void cubeset::display(const cube c) const
  {
    for (unsigned int i = 0; i < 2*uint_size_; ++i)
      {
        if (i == uint_size_)
          std::cout << '\n';

        for (unsigned x = 0; x < nb_bits_; ++x)
          std::cout << ((*(c+i) >> x) & 1);
      }
    std::cout << '\n';
  }

  std::string cubeset::dump(cube c, const std::vector<std::string>& aps) const
  {
    std::ostringstream oss;
    bool all_free = true;
    unsigned int cpt = 0;
    for (unsigned int i = 0; i < uint_size_; ++i)
      {
        for (unsigned x = 0; x < nb_bits_ && cpt != size_; ++x)
          {
            bool true_var = (*(c+i) >> x) & 1;
            bool false_var = (*(c+i+uint_size_) >> x) & 1;
            if (true_var)
              {
                oss << aps[cpt]
                    << (cpt != (size_ - 1) ? "&": "");
                all_free = false;
              }
            else if (false_var)
              {
                oss << '!' << aps[cpt]
                    << (cpt != (size_ - 1) ? "&": "");
                all_free = false;
              }
            ++cpt;
          }
      }
    if (all_free)
      oss << '1';

    std::string res = oss.str();
    if (res.back() == '&')
      res.pop_back();
    if (res.front() == '&')
      res =  res.substr(1);
    return res;
  }
}
