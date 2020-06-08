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
    /// \brief Describes the status of a state
    enum st_status
      {
        UNKNOWN = 1,    // First time this state is discoverd by this thread
        OPEN = 2,       // The state is currently processed by this thread
        CLOSED = 4,     // All the successors of this state have been visited
      };

    /// \brief Describes the structure of a shared state
    struct deadlock_pair
    {
      State st;                 ///< \brief the effective state
      int* colors;              ///< \brief the colors (one per thread)
    };

    /// \brief The hasher for the previous state.
    struct pair_hasher : brq::hash_adaptor<deadlock_pair*>
    {
      pair_hasher(const deadlock_pair*)
      { }

      pair_hasher() = default;

      auto hash(const deadlock_pair* lhs) const
      {
        StateHash hash;
        // Not modulo 31 according to brick::hashset specifications.
        unsigned u = hash(lhs->st) % (1<<30);
        return u;
      }

      bool equal(const deadlock_pair* lhs,
                 const deadlock_pair* rhs) const
      {
        StateEqual equal;
        return equal(lhs->st, rhs->st);
      }

      // WARNING: temporary technical fix to have pointers in brick hash table
      using hash64_t = uint64_t;
      template<typename cell>
      typename cell::pointer match(cell &c, const deadlock_pair* t,
                                   hash64_t h) const
      {
        // NOT very sure that dereferencing will not kill some brick property
        return c.match(h) && equal(c.fetch() , t) ? c.value() : nullptr;
      }
    };

  public:

    ///< \brief Shortcut to ease shared map manipulation
    using shared_map = brq::concurrent_hash_set<deadlock_pair*>;

    swarmed_deadlock_bitstate(kripkecube<State, SuccIterator>& sys,
                              shared_map& map, size_t mem_size,
                              unsigned tid, std::atomic<bool>& stop):
      sys_(sys), tid_(tid), map_(map),
      bloom_filter_(mem_size),
      nb_th_(std::thread::hardware_concurrency()),
      p_(sizeof(int)*std::thread::hardware_concurrency()),
      p_pair_(sizeof(deadlock_pair)),
      stop_(stop)
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

    bool push(State s)
    {
      // Prepare data for a newer allocation
      int* ref = (int*) p_.allocate();
      for (unsigned i = 0; i < nb_th_; ++i)
        ref[i] = UNKNOWN;

      // Try to insert the new state in the shared map.
      deadlock_pair* v = (deadlock_pair*) p_pair_.allocate();
      v->st = s;
      v->colors = ref;
      auto it = map_.insert(v, pair_hasher());
      bool b = it.isnew();

      // Insertion failed, delete element
      // FIXME Should we add a local cache to avoid useless allocations?
      if (!b)
        p_.deallocate(ref);

      // The state has been mark dead by another thread
      for (unsigned i = 0; !b && i < nb_th_; ++i)
        if ((*it)->colors[i] == static_cast<int>(CLOSED))
          return false;

      // The state has already been visited by the current thread
      if ((*it)->colors[tid_] == static_cast<int>(OPEN))
        return false;

      // Set bitstate metadata
      int* unbox_s = sys_.unbox_bitstate_metadata((*it)->st);
      int tmp = unbox_s[0];
      while (!(tmp & (1 << tid_)))
      {
        tmp = __atomic_fetch_or(unbox_s, (1 << tid_), __ATOMIC_RELAXED);
      }

      // Keep a ptr over the array of colors
      refs_.push_back((*it)->colors);

      // Mark state as visited.
      (*it)->colors[tid_] = OPEN;
      ++states_;
      return true;
    }

    bool pop()
    {
      // Track maximum dfs size
      dfs_ = todo_.size()  > dfs_ ? todo_.size() : dfs_;

      // Clear bitstate metadata
      State st = todo_.back().s;
      int* unbox_s = sys_.unbox_bitstate_metadata(st);
      int tmp = unbox_s[0];
      while (tmp & (1 << tid_))
      {
        tmp = __atomic_fetch_and(unbox_s, ~(1 << tid_), __ATOMIC_RELAXED);
      }

      // Don't avoid pop but modify the status of the state
      // during backtrack
      refs_.back()[tid_] = CLOSED;
      refs_.pop_back();
      return true;
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
      State initial = sys_.initial(tid_);
      if (SPOT_LIKELY(push(initial)))
        {
          todo_.push_back({initial, sys_.succ(initial, tid_), transitions_});
        }
      while (!todo_.empty() && !stop_.load(std::memory_order_relaxed))
        {
          if (todo_.back().it->done())
            {
              if (SPOT_LIKELY(pop()))
                {
                  deadlock_ = todo_.back().current_tr == transitions_;
                  if (deadlock_)
                    break;
                  sys_.recycle(todo_.back().it, tid_);
                  todo_.pop_back();
                }
            }
          else
            {
              ++transitions_;
              State dst = todo_.back().it->state();

              if (SPOT_LIKELY(push(dst)))
                {
                  todo_.back().it->next();
                  todo_.push_back({dst, sys_.succ(dst, tid_), transitions_});
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
      State s;
      SuccIterator* it;
      unsigned current_tr;
    };
    kripkecube<State, SuccIterator>& sys_;  ///< \brief The system to check
    std::vector<todo__element> todo_;       ///< \brief The DFS stack
    unsigned transitions_ = 0;              ///< \brief Number of transitions
    unsigned tid_;                          ///< \brief Thread's current ID
    shared_map map_;                        ///< \brief Map shared by threads
    StateHash state_hash_;                  ///< \brief Spot state hasher
    concurrent_bloom_filter bloom_filter_;  ///< \brief Spot Bloom filter
    spot::timer_map tm_;                    ///< \brief Time execution
    unsigned states_ = 0;                   ///< \brief Number of states
    unsigned dfs_ = 0;                      ///< \brief Maximum DFS stack size
    /// \brief Maximum number of threads that can be handled by this algorithm
    unsigned nb_th_ = 0;
    fixed_size_pool<pool_type::Unsafe> p_;  ///< \brief Color Allocator
    fixed_size_pool<pool_type::Unsafe> p_pair_;  ///< \brief State Allocator
    bool deadlock_ = false;                 ///< \brief Deadlock detected?
    std::atomic<bool>& stop_;               ///< \brief Stop-the-world boolean
    /// \brief Stack that grows according to the todo stack. It avoid multiple
    /// concurent access to the shared map.
    std::vector<int*> refs_;
  };
}
