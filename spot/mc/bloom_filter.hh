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

#include <spot/misc/hashfunc.hh>

#include <atomic>
#include <functional>

/* Lock-free concurrent Bloom Filter implementation */

namespace spot
{
  class concurrent_bloom_filter
  {
  private:
    /* Internal concurrent bitset */
    static const size_t BITS_PER_ELEMENT = sizeof(uint32_t) * CHAR_BIT;

    std::atomic<uint32_t> *bits_;

    size_t get_index(size_t bit) const
    {
      return bit / BITS_PER_ELEMENT;
    }

    size_t get_mask(size_t bit) const
    {
      return 1L << (bit % BITS_PER_ELEMENT);
    }

    void set(size_t bit)
    {
      bits_[get_index(bit)] |= get_mask(bit);
    }

    bool test(size_t bit) const
    {
      return bits_[get_index(bit)] & get_mask(bit);
    }

  public:
    using hash_t = size_t;
    using hash_function_t = std::function<hash_t(hash_t)>;
    using hash_functions_t = std::vector<hash_function_t>;

    concurrent_bloom_filter(size_t mem_size, hash_functions_t hash_functions)
      : mem_size_(mem_size), hash_functions_(hash_functions)
    {
      bits_ = new std::atomic<uint32_t>[mem_size]();
      if (hash_functions.empty())
        throw std::invalid_argument("Bloom filter has no hash functions");
    }

    // Default internal hash function
    concurrent_bloom_filter(size_t mem_size)
      : concurrent_bloom_filter(mem_size, {lookup3_hash}) { }

    ~concurrent_bloom_filter()
    {
      delete[] bits_;
    }

    void insert(hash_t elem)
    {
      for (const auto& f : hash_functions_)
      {
        hash_t hash = f(elem) % mem_size_;
        set(hash);
      }
    }

    bool contains(hash_t elem)
    {
      for (const auto& f : hash_functions_)
      {
        hash_t hash = f(elem) % mem_size_;
        if (test(hash) == false)
          return false;
      }

      return true;
    }

  private:
    size_t mem_size_;
    hash_functions_t hash_functions_;
  };
}
