// -*- coding: utf-8 -*-
// Copyright (C) 2015, 2016, 2017, 2018, 2019, 2020 Laboratoire de Recherche et
// Developpement de l'Epita
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
#include <spot/misc/common.hh>
#include <spot/kripke/kripke.hh>
#include <spot/misc/fixpool.hh>
#include <spot/misc/timer.hh>
#include <spot/twacube/twacube.hh>
#include <spot/twacube/fwd.hh>
#include <spot/mc/mc.hh>
#include <spot/mc/bloom_filter.hh>

namespace spot
{
  template<typename State,
           typename StateHash,
           typename StateEqual>
  class concurrent_hash_set;

  /// \brief Describes the structure of a shared state
  template<typename State,
           typename StateHash,
           typename StateEqual>
  struct deadlock_pair
  {
    State st;                 ///< \brief the effective state
    int* colors;              ///< \brief the colors (one per thread)

    bool operator==(const deadlock_pair& other) const
    {
      StateEqual equal;
      return equal(st, other.st);
    }

    auto hash() const
    {
      StateHash hash;
      return hash(st);
    }

    bool equal(const deadlock_pair& other) const
    {
      StateEqual equal;
      return equal(st, other.st);
    }
  };

  /// \brief This class aims to explore a model to detect wether it
  /// contains a deadlock. This deadlock detection performs a DFS traversal
  /// sharing information shared among multiple threads.
  /// If Deadlock equals std::true_type performs dealock algorithm,
  /// otherwise perform a simple reachability.
  template<typename State, typename SuccIterator,
           typename StateHash, typename StateEqual,
           typename Deadlock>
  class SPOT_API swarmed_deadlock_bitstate
  {
    /// \brief Describes the status of a state
    enum st_status
      {
        UNKNOWN = 1,    // First time this state is discoverd by this thread
        OPEN = 2,       // The state is currently processed by this thread
        CLOSED = 4,     // All the successors of this state have been visited
      };


    static constexpr bool compute_deadlock =
       std::is_same<std::true_type, Deadlock>::value;

  public:

    struct hs_mtx_wrapper
    {
      std::mutex *mtx;
      concurrent_hash_set<State, StateHash, StateEqual> *hs;
    };

    ///< \brief Shortcut to ease shared map manipulation
    using shared_map = concurrent_hash_set<State, StateHash, StateEqual>*;
    using shared_struct = hs_mtx_wrapper;

    static shared_struct* make_shared_structure(shared_map, unsigned)
    {
      auto mtx_ptr = new std::mutex();
      auto hs_ptr = new concurrent_hash_set<State, StateHash, StateEqual>(mtx_ptr);
      return new hs_mtx_wrapper{ mtx_ptr, hs_ptr };
    }

    swarmed_deadlock_bitstate(kripkecube<State, SuccIterator>& sys,
                      twacube_ptr, /* useless here */
                      shared_map& map, shared_struct* ss,
                      unsigned tid,
                      std::atomic<bool>& stop,
                      size_t filter_size):
      sys_(sys), tid_(tid), map_(ss->hs),
      bloom_filter_(filter_size), mtx_(ss->mtx),
      nb_th_(std::thread::hardware_concurrency()),
      p_(sizeof(int)*std::thread::hardware_concurrency()),
      stop_(stop), filter_size_(filter_size)
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

    void setup()
    {
      tm_.start("DFS thread " + std::to_string(tid_));
    }

    // Returns nullptr if no push
    State push(State s)
    {
      std::scoped_lock<std::mutex> lock(*mtx_);

      // Prepare data for a newer allocation
      int* ref = (int*) p_.allocate();
      for (unsigned i = 0; i < nb_th_; ++i)
        ref[i] = UNKNOWN;

      // Try to insert the new state in the shared map.
      deadlock_pair<State, StateHash, StateEqual> v { s, ref };
      auto r = map_->find(v);
      if (!r.first && r.second)
      {
        if (filter_size_ != 0 && bloom_filter_.contains(state_hash_(s)))
          return nullptr;
        r = map_->insert(v);
      }

      auto it = r.first;
      auto b = r.second;
      if (!b)
        // FIXME Should we add a local cache to avoid useless allocations?
        p_.deallocate(ref);
      if (!it)
        return nullptr;

      // The state has been mark dead by another thread
      for (unsigned i = 0; !b && i < nb_th_; ++i)
        if (it->colors[i] == static_cast<int>(CLOSED))
          return nullptr;

      // The state has already been visited by the current thread
      if (it->colors[tid_] == static_cast<int>(OPEN))
        return nullptr;

      if (it->equal({s,nullptr}))
      {
        if (filter_size_ != 0)
        {
          // Rare case: no more threads is using the state
          int* unbox_s = sys_.unbox_bitstate_metadata(it->st);
          int cnt = __atomic_load_n(&unbox_s[0], __ATOMIC_RELAXED);
          if (SPOT_UNLIKELY(cnt == 0))
            return nullptr;

          // Set bitstate metadata
          while (!(cnt & (1 << tid_)))
            cnt = __atomic_fetch_or(unbox_s, (1 << tid_), __ATOMIC_RELAXED);
        }

        // Keep a ptr over the array of colors
        refs_.push_back(it->colors);

        // Mark state as visited.
        it->colors[tid_] = OPEN;
        ++states_;

        return it->st;
      }
      else
        return nullptr;
    }

    bool pop()
    {
      std::scoped_lock<std::mutex> lock(*mtx_);

      // Insert the state into the filter
      State st = todo_.back().s;
      if (filter_size_ != 0)
        bloom_filter_.insert(state_hash_(st));

      // Don't avoid pop but modify the status of the state
      // during backtrack
      refs_.back()[tid_] = CLOSED;
      refs_.pop_back();

      if (filter_size_ != 0)
      {
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
          deadlock_pair<State, StateHash, StateEqual> p { st, nullptr };
          map_->erase(p);
          sys_.recycle_state(st);
        }
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

    unsigned walltime()
    {
      return tm_.timer("DFS thread " + std::to_string(tid_)).walltime();
    }

    std::string name()
    {
      if (compute_deadlock)
        return "deadlock";
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
    struct todo_element
    {
      State s;
      SuccIterator* it;
      unsigned current_tr;
    };
    kripkecube<State, SuccIterator>& sys_; ///< \brief The system to check
    std::vector<todo_element> todo_;       ///< \brief The DFS stack
    unsigned transitions_ = 0;             ///< \brief Number of transitions
    unsigned tid_;                         ///< \brief Thread's current ID
    shared_map map_;                       ///< \brief Map shared by threads
    StateHash state_hash_;
    concurrent_bloom_filter bloom_filter_;
    std::mutex *mtx_;
    spot::timer_map tm_;                   ///< \brief Time execution
    unsigned states_ = 0;                  ///< \brief Number of states
    unsigned dfs_ = 0;                     ///< \brief Maximum DFS stack size
    /// \brief Maximum number of threads that can be handled by this algorithm
    unsigned nb_th_ = 0;
    fixed_size_pool<pool_type::Unsafe> p_;  ///< \brief Color Allocator
    bool deadlock_ = false;                ///< \brief Deadlock detected?
    std::atomic<bool>& stop_;              ///< \brief Stop-the-world boolean
    /// \brief Stack that grows according to the todo stack. It avoid multiple
    /// concurent access to the shared map.
    std::vector<int*> refs_;
    bool finisher_ = false;
    size_t filter_size_;
  };

  template<typename State,
           typename StateHash,
           typename StateEqual>
  class concurrent_hash_set
  {
    using T = deadlock_pair<State, StateHash, StateEqual>;

  public:
    concurrent_hash_set(std::mutex *mtx, std::size_t hs_size)
      : mtx_(mtx), hs_size_(hs_size)
    {
      hs_ = new std::atomic<T*>[hs_size]{nullptr};
    }

    concurrent_hash_set(std::mutex *mtx)
      : concurrent_hash_set(mtx, 5000000) {}

    ~concurrent_hash_set()
    {
      for (std::size_t i = 0; i < hs_size_; i++)
        delete hs_[i];
      delete[] hs_;
    }

    std::optional<std::size_t> search(T element) const
    {
      if (SPOT_UNLIKELY(nb_elements_ == hs_size_))
        return std::nullopt;

      // Linear probing
      std::size_t idx = element.hash() % hs_size_;
      // TODO: check number of loop iterations
      while (hs_[idx] != nullptr && !(element.equal(*hs_[idx])))
        idx = (idx + 1) % hs_size_;
      return std::optional<std::size_t>(idx);
    }

    std::pair<T*, bool> find(T element)
    {
      //std::scoped_lock<std::mutex> lock(*mtx_);

      if (auto idx = search(element))
      {
        if (hs_[*idx] != nullptr)
          return {hs_[*idx], false};
        else
          return {nullptr, true};
      }
      else
        return {nullptr, false};
    }

    std::pair<T*, bool> insert(T element)
    {
      //std::scoped_lock<std::mutex> lock(*mtx_);
      if (auto idx = search(element))
      {
        if (hs_[*idx] != nullptr)
          return {hs_[*idx], false};
        else
        {
          hs_[*idx] = new deadlock_pair<State, StateHash, StateEqual>{element};
          ++nb_elements_;
          return {hs_[*idx], true};
        }
      }
      else
        return {nullptr, false};
    }

    bool erase(T element)
    {
      //std::scoped_lock<std::mutex> lock(*mtx_);
      if (auto idx = search(element))
      {
        if (hs_[*idx] == nullptr)
          return false;

        delete hs_[*idx];
        --nb_elements_;

        // Only deleting the element will break the linear probing
        // mechanism, thus we need to either move the cells to keep the
        // continuous probing block, or use a tombstone. Here we mostly care
        // about memory and not speed performance so we chose the first
        // option.
        std::size_t cur = *idx;
        while (hs_[(cur + 1) % hs_size_] != nullptr)
        {
          T* next = hs_[(cur + 1) % hs_size_];
          // Special case: when an element is already at its original hashing
          // position, stop moving the block otherwise we would move the element
          // to a wrong position.
          if ((next->hash() % hs_size_) == ((cur + 1) % hs_size_))
            break;
          hs_[cur] = next;
          cur = (cur + 1) % hs_size_;
        }
        hs_[cur] = nullptr;

        return true;
      }
      else
        return false;
    }

  private:
    std::atomic<T*> *hs_;
    std::atomic<std::size_t> nb_elements_;
    std::mutex *mtx_;
    std::size_t hs_size_;
  };
}
