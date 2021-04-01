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
  /// If Deadlock equals std::true_type performs dealock algorithm,
  /// otherwise perform a simple reachability.
  template<typename State, typename SuccIterator,
           typename StateHash, typename StateEqual,
           typename Deadlock>
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

      bool operator==(const deadlock_pair& other) const
      {
        StateEqual equal;
        return equal(st, other.st);
      }
    };

    /// \brief The hasher for the previous state.
    struct pair_hasher : brq::hash_adaptor<deadlock_pair>
    {
      pair_hasher(const deadlock_pair&)
      { }

      pair_hasher() = default;

      auto hash(const deadlock_pair& lhs) const
      {
        StateHash hash;
        // Not modulo 31 according to brick::hashset specifications.
        unsigned u = hash(lhs.st) % (1<<30);
        return u;
      }

      bool equal(const deadlock_pair& lhs,
                 const deadlock_pair& rhs) const
      {
        StateEqual equal;
        return equal(lhs.st, rhs.st);
      }
    };

    static constexpr bool compute_deadlock =
       std::is_same<std::true_type, Deadlock>::value;

  public:

    ///< \brief Shortcut to ease shared map manipulation
    using shared_map = brq::concurrent_hash_set<deadlock_pair>;
    using shared_struct = shared_map;

    static shared_struct* make_shared_structure(shared_map, unsigned)
    {
      return nullptr; // Useless
    }

    swarmed_deadlock_bitstate(kripkecube<State, SuccIterator>& sys,
                              twacube_ptr, /* useless here */
                              shared_map& map,
                              shared_struct* /* useless here */,
                              unsigned tid, std::atomic<bool>& stop):
      sys_(sys), tid_(tid), map_(map),
      bloom_filter_(100000),
      nb_th_(std::thread::hardware_concurrency()),
      p_(sizeof(int)*std::thread::hardware_concurrency()),
      stop_(stop)
    {
      static_assert(spot::is_a_kripkecube_ptr<decltype(&sys),
                                             State, SuccIterator>::value,
                    "error: does not match the kripkecube requirements");
      SPOT_ASSERT(nb_th_ > tid);
    }

    virtual ~swarmed_deadlock_bitstate()
    {
      while (!todo_.empty())
      {
        sys_.recycle_iterator(todo_.back().it, tid_);
        todo_.pop_back();
      }
    }

    void setup()
    {
      tm_.start("DFS thread " + std::to_string(tid_));
    }

    // Returns nullptr if no push
    State push(State s)
    {
      // Prepare data for a newer allocation
      int* ref = (int*) p_.allocate();
      for (unsigned i = 0; i < nb_th_; ++i)
        ref[i] = UNKNOWN;

      // Try to insert the new state in the shared map.
      deadlock_pair v { s, ref };

      auto it = map_.find(v, pair_hasher());
      // State is not in table
      // FIXME is there a method like end() in brick-hashset?
      if (!it.isnew() && !it.valid())
        {
          // But is in bloom ..
          if (bloom_filter_.contains(state_hash_(s)))
            return nullptr;

          // otherwise we have to insert it in table
          it = map_.insert(v, pair_hasher());
        }

      bool b = it.isnew();
      // Insertion or lookup failed, delete element
      // FIXME Should we add a local cache to avoid useless allocations?
      if (!b)
        p_.deallocate(ref);

      // The state has been mark dead by another thread
      for (unsigned i = 0; !b && i < nb_th_; ++i)
        if (it->colors[i] == static_cast<int>(CLOSED))
          return nullptr;

      // The state has already been visited by the current thread
      if (it->colors[tid_] == static_cast<int>(OPEN))
        return nullptr;

      // Rare case: no more threads is using the state
      int* unbox_s = sys_.unbox_bitstate_metadata(it->st);
      int cnt = __atomic_load_n(&unbox_s[0], __ATOMIC_RELAXED);
      if (SPOT_UNLIKELY(cnt == 0))
        return nullptr;

      // Set bitstate metadata
      while (!(cnt & (1 << tid_)))
      {
        cnt = __atomic_fetch_or(unbox_s, (1 << tid_), __ATOMIC_RELAXED);
      }

      // Keep a ptr over the array of colors
      refs_.push_back(it->colors);

      // Mark state as visited.
      it->colors[tid_] = OPEN;
      ++states_;

      return it->st;
    }

    bool pop()
    {
      // Insert the state into the filter
      State st = todo_.back().s;
      bloom_filter_.insert(state_hash_(st));

      // Don't avoid pop but modify the status of the state
      // during backtrack
      refs_.back()[tid_] = CLOSED;
      refs_.pop_back();

      // Clear bitstate metadata
      int* unbox_s = sys_.unbox_bitstate_metadata(st);
      int cnt = __atomic_load_n(&unbox_s[0], __ATOMIC_RELAXED);
      while (cnt & (1 << tid_))
      {
        cnt = __atomic_fetch_and(unbox_s, ~(1 << tid_), __ATOMIC_RELAXED);
      }

      // Release memory if no thread is using the state
      if (cnt == 0)
      {
        deadlock_pair p { st, nullptr };
        map_.erase(p, pair_hasher());
        sys_.recycle_state(st);
      }

      // Track maximum dfs size
      dfs_ = todo_.size()  > dfs_ ? todo_.size() : dfs_;

      return true;
    }

    void finalize()
    {
      bool tst_val = false;
      bool new_val = true;
      bool exchanged = stop_.compare_exchange_strong(tst_val, new_val);
      if (exchanged)
        finisher_ = true;
      tm_.stop("DFS thread " + std::to_string(tid_));
    }

    bool finisher()
    {
      return finisher_;
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
      State tmp = sys_.initial(tid_);
      State initial = push(tmp);
      if (SPOT_LIKELY(initial != nullptr))
        {
          todo_.push_back({initial, sys_.succ(initial, tid_), transitions_});
          if (tmp != initial)
            sys_.recycle_state(tmp);
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
                  sys_.recycle_iterator(todo_.back().it, tid_);
                  todo_.pop_back();
                }
            }
          else
            {
              ++transitions_;
              tmp = todo_.back().it->state();
              State dst = push(tmp);

              if (SPOT_LIKELY(dst != nullptr))
                {
                  todo_.back().it->next();
                  todo_.push_back({dst, sys_.succ(dst, tid_), transitions_});
                  if (tmp != dst)
                    sys_.recycle_state(tmp);
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

    std::string name()
    {
      if (compute_deadlock)
        return "deadlock_bitstate";
      return "reachability";
    }

    int sccs()
    {
      return -1;
    }

    mc_rvalue result()
    {
      if (compute_deadlock)
        return deadlock_ ? mc_rvalue::DEADLOCK : mc_rvalue::NO_DEADLOCK;
      return mc_rvalue::SUCCESS;
    }

    std::string trace()
    {
      std::string result;
      for (auto& e: todo_)
        result += sys_.to_string(e.s, tid_);
      return result;
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
    bool deadlock_ = false;                 ///< \brief Deadlock detected?
    std::atomic<bool>& stop_;               ///< \brief Stop-the-world boolean
    /// \brief Stack that grows according to the todo stack. It avoid multiple
    /// concurent access to the shared map.
    std::vector<int*> refs_;
    bool finisher_ = false;
  };
}
