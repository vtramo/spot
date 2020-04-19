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

#include <atomic>
#include <chrono>
#include <stdlib.h>
#include <thread>
#include <vector>

#include <spot/bricks/brick-hashset>
#include <spot/kripke/kripke.hh>
#include <spot/mc/bloom_filter.hh>
#include <spot/mc/deadlock.hh>
#include <spot/misc/common.hh>
#include <spot/misc/timer.hh>

namespace spot
{
  /// \brief This class aims to explore a model to detect wether it contains a
  /// deadlock. However, unlike the classical swarmed_deadlock class, it is
  /// using bitstate hashing and a Bloom filter to store persistent information.
  template<typename State, typename SuccIterator,
           typename StateHash, typename StateEqual>
  class swarmed_deadlock_bitstate
  {
    struct deadlock_state
    {
      State st;

      deadlock_state(const State& initial)
        : st(initial)
      { }

      deadlock_state() = default;

      bool operator==(const deadlock_state& other) const
      {
        StateEqual equal;
        return equal(st, other.st);
      }
    };

    /// \brief Internal state hasher for the Brick interface
    struct brick_state_hasher : brq::hash_adaptor<deadlock_state>
    {
      brick_state_hasher(const deadlock_state&)
      { }

      brick_state_hasher() = default;

      auto hash(const deadlock_state& lhs) const
      {
        StateHash hash;
        // Not modulo 31 according to brick::hashset specifications.
        unsigned u = hash(lhs.st) % (1<<30);
        return u;
      }
    };

  public:

    ///< \brief Shortcut to ease shared map manipulation
    using shared_map = brq::concurrent_hash_set<deadlock_state>;

    swarmed_deadlock_bitstate(kripkecube<State, SuccIterator>& sys,
                              shared_map& map, size_t mem_size, unsigned tid,
                              std::atomic<bool>& stop):
      sys_(sys), tid_(tid), map_(map),
      nb_th_(std::thread::hardware_concurrency()),
      stop_(stop),
      bloom_filter_(mem_size)
    {
      static_assert(spot::is_a_kripkecube_ptr<decltype(&sys),
                                              State, SuccIterator>::value,
                    "error: does not match the kripkecube requirements");
    }

    virtual ~swarmed_deadlock_bitstate()
    {
      while (!todo_.empty())
      {
        sys_.recycle(todo_.back().it, tid_);
        todo_.pop_back();
      }
    }

    void setup()
    {
      tm_.start("DFS thread " + std::to_string(tid_));
    }

    bool push(deadlock_state s)
    {
      auto it = map_.insert(s.st, brick_state_hasher());
      if (!it.isnew())
        return false;
      if (bloom_filter_.contains(state_hash_(s.st)))
        return false;
      ++states_;
      return true;
    }

    void pop()
    {
      // Track maximum dfs size
      dfs_ = todo_.size()  > dfs_ ? todo_.size() : dfs_;

      auto elem = todo_.back();

      deadlock_ = elem.current_tr == transitions_;
      if (SPOT_UNLIKELY(deadlock_))
        return;

      todo_.pop_back();
      sys_.recycle(elem.it, tid_);
      map_.erase(elem.st, brick_state_hasher());
      bloom_filter_.insert(state_hash_(elem.st.st));
    }

    void finalize()
    {
      stop_ = true;
      tm_.stop("DFS thread " + std::to_string(tid_));
    }

    unsigned states()
    {
      return states_;
    }

    unsigned transitions()
    {
      return transitions_;
    }

    void run()
    {
      setup();
      deadlock_state initial{sys_.initial(tid_)};
      if (SPOT_LIKELY(push(initial)))
      {
        todo_.push_back({initial, sys_.succ(initial.st, tid_), transitions_});
      }
      while (!todo_.empty() && !stop_.load(std::memory_order_relaxed))
      {
        if (todo_.back().it->done())
        {
          pop();
          if (deadlock_)
            break;
        }
        else
        {
          ++transitions_;
          State dst = todo_.back().it->state();
          deadlock_state next{dst};

          if (SPOT_LIKELY(push(next)))
          {
            todo_.back().it->next();
            todo_.push_back({next, sys_.succ(dst, tid_), transitions_});
          }
          else
          {
            todo_.back().it->next();
          }
        }
      }
      finalize();
    }

    bool has_deadlock()
    {
      return deadlock_;
    }

    unsigned walltime()
    {
      return tm_.timer("DFS thread " + std::to_string(tid_)).walltime();
    }

    deadlock_stats stats()
    {
      return {states(), transitions(), dfs_, has_deadlock(), walltime()};
    }

  private:
    struct todo__element
    {
      deadlock_state st;
      SuccIterator* it;
      unsigned current_tr;
    };

    kripkecube<State, SuccIterator>& sys_; ///< \brief The system to check
    std::vector<todo__element> todo_;      ///< \brief The DFS stack
    unsigned transitions_ = 0;             ///< \brief Number of transitions
    unsigned tid_;                         ///< \brief Thread's current ID
    shared_map map_;                       ///< \brief Map shared by threads
    StateHash state_hash_;                 ///< \brief Spot state hasher
    concurrent_bloom_filter bloom_filter_; ///< \brief Spot Bloom filter
    spot::timer_map tm_;                   ///< \brief Time execution
    unsigned states_ = 0;                  ///< \brief Number of states
    unsigned dfs_ = 0;                     ///< \brief Maximum DFS stack size
    /// \brief Maximum number of threads that can be handled by this algorithm
    unsigned nb_th_ = 0;
    bool deadlock_ = false;                ///< \brief Deadlock detected?
    std::atomic<bool>& stop_;              ///< \brief Stop-the-world boolean
  };
}
