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

#include <bitset>

#include <spot/kripke/kripke.hh>

namespace spot
{
  template<typename State, typename SuccIterator,
           typename StateHash, typename StateEqual>
  class bitstate
  {
  public:
    bitstate(kripkecube<State, SuccIterator>& sys, unsigned tid):
      sys_(sys), tid_(tid)
    {
      static_assert(spot::is_a_kripkecube_ptr<decltype(&sys),
          State, SuccIterator>::value,
          "error: does not match the kripkecube requirements");

      seen_.reserve(2000000);
      todo_.reserve(100000);
    }

    ~bitstate()
    {
      // States will be destroyed by the system, so just clear map
      seen_.clear();
    }

    unsigned int dfs()
    {
      unsigned int state_number = 1;
      State initial = sys_.initial(tid_);
      todo_.push_back(initial);

      while (!todo_.empty())
      {
        State current = todo_.back();
        todo_.pop_back();
        seen_.insert(current);

        for (auto it = sys_.succ(current, tid_); !it->done(); it->next())
        {
          auto neighbor = it->state();
          if (seen_.count(neighbor) == 0)
          {
            todo_.push_back(neighbor);
            seen_.insert(neighbor);
            state_number++;
          }
        }
      }

      return state_number;
    }

    // Must be a power of two minus 1 (it will be used as a bit mask)
    static const unsigned MEM_SIZE = (1 << 30) - 1;

    // https://burtleburtle.net/bob/c/lookup3.c
    #define rot(x,k) (((x)<<(k)) | ((x)>>(32-(k))))
    uint32_t jenkins_hash(uint32_t k)
    {
      // Internal states
      uint32_t s1, s2;
      s1 = s2 = 0xdeadbeef;

      s2 ^= s1; s2 -= rot(s1, 14);
      k  ^= s2; k  -= rot(s2, 11);
      s1 ^= k;  s1 -= rot(k, 25);
      s2 ^= s1; s2 -= rot(s1, 16);
      k  ^= s2; k  -= rot(s2, 4);
      s1 ^= k;  s1 -= rot(k, 14);
      s2 ^= s1; s2 -= rot(s1, 24);

      return s2 & MEM_SIZE;
    }

    unsigned int dfs_bitstate_hashing()
    {
      unsigned int state_number = 1;
      State initial = sys_.initial(tid_);
      StateHash state_hash;
      todo_.push_back(initial);

      while (!todo_.empty())
      {
        State current = todo_.back();
        todo_.pop_back();
        bs_[jenkins_hash(state_hash(current))] = 1;

        for (auto it = sys_.succ(current, tid_); !it->done(); it->next())
        {
          auto neighbor = it->state();
          auto neighbor_hash = jenkins_hash(state_hash(neighbor));
          if (bs_[neighbor_hash] == 0)
          {
            todo_.push_back(neighbor);
            bs_[neighbor_hash] = 1;
            state_number++;
          }
        }
      }

      return state_number;
    }

  protected:
    kripkecube<State, SuccIterator>& sys_;
    unsigned int tid_;

    std::unordered_set<State, StateHash, StateEqual> seen_;
    std::vector<State> todo_;
    std::bitset<MEM_SIZE> bs_;
  };
}
