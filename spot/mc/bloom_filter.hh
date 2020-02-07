// -*- coding: utf-8 -*-
// Copyright (C) 2020 Laboratoire de Recherche et Developpement de
// l'Epita
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

#include <functional>

namespace spot
{
  class bloom_filter
  {
    using hash_t = uint32_t;
    using hash_function_t = std::function<hash_t(hash_t)>;

    // https://burtleburtle.net/bob/c/lookup3.c
    #define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))
    static hash_t jenkins_hash_function(hash_t k)
    {
      hash_t s1, s2;
      s1 = s2 = 0xdeadbeef;

      s2 ^= s1; s2 -= rot(s1, 14);
      k  ^= s2; k  -= rot(s2, 11);
      s1 ^= k;  s1 -= rot(k, 25);
      s2 ^= s1; s2 -= rot(s1, 16);
      k  ^= s2; k  -= rot(s2, 4);
      s1 ^= k;  s1 -= rot(k, 14);
      s2 ^= s1; s2 -= rot(s1, 24);

      return s2;
    }

  public:
    bloom_filter(uint32_t mem_size)
      : mem_size_(mem_size)
    {
      bitset_.assign(mem_size, false);

      // Internal hash functions
      hash_functions_.push_back(jenkins_hash_function);
    }

    void insert(hash_t elem)
    {
      for (const auto& f : hash_functions_)
      {
        hash_t hash = f(elem) % mem_size_;
        bitset_[hash] = true;
      }
    }

    bool contains(hash_t elem)
    {
      for (const auto& f : hash_functions_)
      {
        hash_t hash = f(elem) % mem_size_;
        if (bitset_[hash] == false)
          return false;
      }

      return true;
    }

  private:
    std::vector<hash_function_t> hash_functions_;
    std::vector<bool> bitset_;
    uint32_t mem_size_;
  };
}
