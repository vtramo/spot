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
#include <utility>
#include <spot/kripke/kripke.hh>
#include <spot/misc/common.hh>
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
  class concurrent_hash_set_uf;

  template<typename State,
           typename StateHash,
           typename StateEqual>
  class iterable_uf_bitstate
  {

  public:
    enum class uf_status  { LIVE, LOCK, DEAD };
    enum class list_status  { BUSY, LOCK, DONE };
    enum class claim_status  { CLAIM_FOUND, CLAIM_NEW, CLAIM_DEAD };

    /// \brief Represents a Union-Find element
    struct uf_element
    {
      /// \brief the state handled by the element
      State st_;
      /// \brief reference to the pointer
      std::atomic<uf_element*> parent;
      /// The set of worker for a given state
      std::atomic<unsigned> worker_;
      /// \brief next element for work stealing
      std::atomic<uf_element*> next_;
      /// \brief current status for the element
      std::atomic<uf_status> uf_status_;
      ///< \brief current status for the list
      std::atomic<list_status> list_status_;

      auto hash() const
      {
        StateHash hash;
        return hash(st_);
      }

      bool equal(const uf_element& other) const
      {
        StateEqual equal;
        return equal(st_, other.st_);
      }
    };

    ///< \brief Shortcut to ease shared map manipulation
    using shared_map = concurrent_hash_set_uf<State, StateHash, StateEqual>*;

    iterable_uf_bitstate(const iterable_uf_bitstate<State, StateHash,
                         StateEqual>& uf):
      map_(uf.map_), tid_(uf.tid_), size_(std::thread::hardware_concurrency()),
      nb_th_(std::thread::hardware_concurrency()), inserted_(0),
      p_(sizeof(uf_element)),
      filter_size_(uf.filter_size_),
      bloom_filter_(uf.bloom_filter_)
    {  }


    iterable_uf_bitstate(shared_map& map, unsigned tid, size_t filter_size):
      map_(map), tid_(tid), size_(std::thread::hardware_concurrency()),
      nb_th_(std::thread::hardware_concurrency()), inserted_(0),
      p_(sizeof(uf_element)),
      filter_size_(filter_size),
      bloom_filter_(new concurrent_bloom_filter(filter_size))
    {
    }

    ~iterable_uf_bitstate() {}

    std::pair<claim_status, uf_element*>
    make_claim(State a)
    {
      unsigned w_id = (1U << tid_);

      // Setup and try to insert the new state in the shared map.
      uf_element* v = (uf_element*) p_.allocate();
      v->st_ = a;
      v->parent = v;
      v->next_ = v;
      v->worker_ = 0;
      v->uf_status_ = uf_status::LIVE;
      v->list_status_ = list_status::BUSY;

      auto r = map_->find(v);
      if (!r.first && r.second)
      {
        // XXX(thibault): casse le compteur de SCC
        if (filter_size_ != 0 && bloom_filter_->contains(state_hash_(v->st_)))
          return {claim_status::CLAIM_FOUND, nullptr};
        r = map_->insert(v);
      }
      auto it = r.first;
      auto b = r.second;

      // Insertion failed, delete element
      // FIXME Should we add a local cache to avoid useless allocations?
      if (!b)
        p_.deallocate(v);
      else
        ++inserted_;
      if (!it)
        return {claim_status::CLAIM_FOUND, nullptr};

      uf_element* a_root = find(it);
      if (a_root->uf_status_.load() == uf_status::DEAD)
        return {claim_status::CLAIM_DEAD, it};
      // XXX(thibault): est-ce qu'en parallèle on doit faire ce même
      // test pour le cas de DONE ?

      if ((a_root->worker_.load() & w_id) != 0)
        return {claim_status::CLAIM_FOUND, it};

      atomic_fetch_or(&(a_root->worker_), w_id);
      while (a_root->parent.load() != a_root)
        {
          a_root = find(a_root);
          atomic_fetch_or(&(a_root->worker_), w_id);
        }

      return {claim_status::CLAIM_NEW, it};
    }

    uf_element* find(uf_element* a)
    {
      uf_element* parent = a->parent.load();
      uf_element* x = a;
      uf_element* y;

      while (x != parent)
        {
          y = parent;
          parent = y->parent.load();
          if (parent == y)
            return y;
          x->parent.store(parent);
          x = parent;
          parent = x->parent.load();
        }
      return x;
    }

    bool sameset(uf_element* a, uf_element* b)
    {
      while (true)
        {
          uf_element* a_root = find(a);
          uf_element* b_root = find(b);
          if (a_root == b_root)
            return true;

          if (a_root->parent.load() == a_root)
            return false;
        }
    }

    bool lock_root(uf_element* a)
    {
      uf_status expected = uf_status::LIVE;
      if (a->uf_status_.load() == expected)
        {
          if (std::atomic_compare_exchange_strong
              (&(a->uf_status_), &expected, uf_status::LOCK))
            {
              if (a->parent.load() == a)
                return true;
              unlock_root(a);
            }
        }
      return false;
    }

    inline void unlock_root(uf_element* a)
    {
      a->uf_status_.store(uf_status::LIVE);
    }

    uf_element* lock_list(uf_element* a)
    {
      uf_element* a_list = a;
      while (true)
        {
          bool dontcare = false;
          a_list = pick_from_list(a_list, &dontcare);
          if (a_list == nullptr)
            {
              return nullptr;
            }

          auto expected = list_status::BUSY;
          bool b = std::atomic_compare_exchange_strong
            (&(a_list->list_status_), &expected, list_status::LOCK);

          if (b)
            return a_list;

          a_list = a_list->next_.load();
        }
    }

    void unlock_list(uf_element* a)
    {
      a->list_status_.store(list_status::BUSY);
    }

    void unite(uf_element* a, uf_element* b)
    {
      uf_element* a_root;
      uf_element* b_root;
      uf_element* q;
      uf_element* r;

      while (true)
        {
          a_root = find(a);
          b_root = find(b);

          if (a_root == b_root)
            return;

          r = std::max(a_root, b_root);
          q = std::min(a_root, b_root);

          if (!lock_root(q))
            continue;

          break;
        }

      uf_element* a_list = lock_list(a);
      if (a_list == nullptr)
        {
          unlock_root(q);
          return;
        }

      uf_element* b_list = lock_list(b);
      if (b_list == nullptr)
        {
          unlock_list(a_list);
          unlock_root(q);
          return;
        }

      SPOT_ASSERT(a_list->list_status_.load() == list_status::LOCK);
      SPOT_ASSERT(b_list->list_status_.load() == list_status::LOCK);

      //  Swapping
      uf_element* a_next =  a_list->next_.load();
      uf_element* b_next =  b_list->next_.load();
      SPOT_ASSERT(a_next != nullptr);
      SPOT_ASSERT(b_next != nullptr);

      a_list->next_.store(b_next);
      b_list->next_.store(a_next);
      q->parent.store(r);

      // Update workers
      unsigned q_worker = q->worker_.load();
      unsigned r_worker = r->worker_.load();
      if ((q_worker|r_worker) != r_worker)
        {
          atomic_fetch_or(&(r->worker_), q_worker);
          while (r->parent.load() != r)
            {
              r = find(r);
              atomic_fetch_or(&(r->worker_), q_worker);
            }
        }

      unlock_list(a_list);
      unlock_list(b_list);
      unlock_root(q);
    }

    uf_element* pick_from_list(uf_element* u, bool* sccfound)
    {
      uf_element* a = u;
      while (true)
        {
          list_status a_status;
          while (true)
            {
              a_status = a->list_status_.load();

              if (a_status == list_status::BUSY)
                {
                  return a;
                }

              if (a_status == list_status::DONE)
                break;
            }

          uf_element* b = a->next_.load();

          // ------------------------------ NO LAZY : start
          // if (b == u)
          //   {
          //     uf_element* a_root = find(a);
          //     uf_status status = a_root->uf_status_.load();
          //     while (status != uf_status::DEAD)
          //       {
          //         if (status == uf_status::LIVE)
          //           *sccfound = std::atomic_compare_exchange_strong
          //             (&(a_root->uf_status_), &status, uf_status::DEAD);
          //         status = a_root->uf_status_.load();
          //       }
          //     return nullptr;
          //   }
          // a = b;
          // ------------------------------ NO LAZY : end

          if (a == b)
            {
              uf_element* a_root = find(u);
              uf_status status = a_root->uf_status_.load();
              while (status != uf_status::DEAD)
                {
                  if (status == uf_status::LIVE)
                    *sccfound = std::atomic_compare_exchange_strong
                      (&(a_root->uf_status_), &status, uf_status::DEAD);
                  status = a_root->uf_status_.load();
                }
              return nullptr;
            }

          list_status b_status;
          while (true)
            {
              b_status = b->list_status_.load();

              if (b_status == list_status::BUSY)
                {
                  return b;
                }

              if (b_status == list_status::DONE)
                break;
            }

          SPOT_ASSERT(b_status == list_status::DONE);
          SPOT_ASSERT(a_status == list_status::DONE);

          uf_element* c = b->next_.load();
          a->next_.store(c);
          a = c;
        }
    }

    void remove_from_list(uf_element* a)
    {
      if (filter_size_ != 0)
        bloom_filter_->insert(state_hash_(a->st_));

      while (true)
        {
          list_status a_status = a->list_status_.load();

          if (a_status == list_status::DONE)
            break;

          if (a_status == list_status::BUSY)
              std::atomic_compare_exchange_strong
                (&(a->list_status_), &a_status, list_status::DONE);
        }

      // XXX(thibault): casse le compteur de SCC
      if (filter_size_ != 0)
        map_->erase(a);
    }

    unsigned inserted()
    {
      return inserted_;
    }

  private:
    iterable_uf_bitstate() = default;

    shared_map map_;      ///< \brief Map shared by threads copy!
    unsigned tid_;        ///< \brief The Id of the current thread
    unsigned size_;       ///< \brief Maximum number of thread
    unsigned nb_th_;      ///< \brief Current number of threads
    unsigned inserted_;   ///< \brief The number of insert succes
    fixed_size_pool<pool_type::Unsafe> p_; ///< \brief The allocator
    size_t filter_size_;  ///< \brief Bloom filter size
    concurrent_bloom_filter* bloom_filter_; ///< \brief BF shared by threads
    StateHash state_hash_;
  };

  /// \brief This class implements the SCC decomposition algorithm of bloemen
  /// as described in PPOPP'16. It uses a shared union-find augmented to manage
  /// work stealing between threads.
  template<typename State, typename SuccIterator,
           typename StateHash, typename StateEqual>
  class swarmed_bloemen_bitstate
  {
  private:
    swarmed_bloemen_bitstate() = delete;

  public:

    using uf = iterable_uf_bitstate<State, StateHash, StateEqual>;
    using uf_element = typename uf::uf_element;

    using shared_struct = uf;
    using shared_map = typename uf::shared_map;

    static shared_struct* make_shared_structure(shared_map, unsigned i,
        size_t hs_size, size_t filter_size)
    {
      auto mtx_ptr = new std::mutex();
      auto hs_ptr =
        new concurrent_hash_set_uf<State, StateHash, StateEqual>(mtx_ptr,
                                                                 hs_size);
      return new uf(hs_ptr, i, filter_size);
    }

   swarmed_bloemen_bitstate(kripkecube<State, SuccIterator>& sys,
                            twacube_ptr, /* useless here */
                            shared_map& map, /* useless here */
                            iterable_uf_bitstate<State, StateHash,
                                                 StateEqual>* uf,
                            unsigned tid,
                            std::atomic<bool>& stop,
                            size_t hs_size, /* useless here */
                            size_t filter_size /* useless here */):
      sys_(sys),  uf_(*uf), tid_(tid),
      nb_th_(std::thread::hardware_concurrency()),
      stop_(stop)
    {
      static_assert(spot::is_a_kripkecube_ptr<decltype(&sys),
                                             State, SuccIterator>::value,
                    "error: does not match the kripkecube requirements");
    }

    void run()
    {
      setup();
      State init = sys_.initial(tid_);
      auto pair = uf_.make_claim(init);
      todo_.push_back(pair.second);
      Rp_.push_back(pair.second);
      ++states_;

      while (!todo_.empty())
        {
        bloemen_recursive_start:
          while (!stop_.load(std::memory_order_relaxed))
            {
              bool sccfound = false;
              uf_element* v_prime = uf_.pick_from_list(todo_.back(), &sccfound);
              if (v_prime == nullptr)
                {
                  // The SCC has been explored!
                  sccs_ += sccfound;
                  break;
                }

              auto it = sys_.succ(v_prime->st_, tid_);
              while (!it->done())
                {
                  auto w = uf_.make_claim(it->state());
                  it->next();
                  ++transitions_;
                  if (w.first == uf::claim_status::CLAIM_NEW)
                    {
                      todo_.push_back(w.second);
                      Rp_.push_back(w.second);
                      ++states_;
                      sys_.recycle_iterator(it, tid_);
                      goto bloemen_recursive_start;
                    }
                  else if (w.first == uf::claim_status::CLAIM_FOUND)
                    {
                      // XXX(thibault): test/fix using multiple threads
                      if (w.second)
                      {
                        while (!uf_.sameset(todo_.back(), w.second))
                          {
                            uf_element* r = Rp_.back();
                            Rp_.pop_back();
                            uf_.unite(r, Rp_.back());
                          }
                      }
                    }
                }
              uf_.remove_from_list(v_prime);
              sys_.recycle_iterator(it, tid_);
            }

          if (todo_.back() == Rp_.back())
            Rp_.pop_back();
          todo_.pop_back();
        }
      finalize();
    }

    void setup()
    {
      tm_.start("DFS thread " + std::to_string(tid_));
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
      return "bloemen_bitstate_scc";
    }

    int sccs()
    {
      return sccs_;
    }

    mc_rvalue result()
    {
      return mc_rvalue::SUCCESS;
    }

    std::string trace()
    {
      // Returning a trace has no sense in this algorithm
      return "";
    }

  private:
    kripkecube<State, SuccIterator>& sys_;   ///< \brief The system to check
    std::vector<uf_element*> todo_;          ///< \brief The "recursive" stack
    std::vector<uf_element*> Rp_;            ///< \brief The DFS stack
    iterable_uf_bitstate<State, StateHash, StateEqual> uf_; ///< Copy!
    unsigned tid_;
    unsigned nb_th_;
    unsigned inserted_ = 0;           ///< \brief Number of states inserted
    unsigned states_  = 0;            ///< \brief Number of states visited
    unsigned transitions_ = 0;        ///< \brief Number of transitions visited
    unsigned sccs_ = 0;               ///< \brief Number of SCC visited
    spot::timer_map tm_;              ///< \brief Time execution
    std::atomic<bool>& stop_;
    bool finisher_ = false;
  };

  template<typename State,
           typename StateHash,
           typename StateEqual>
  class concurrent_hash_set_uf
  {
    using T = iterable_uf_bitstate<State, StateHash, StateEqual>::uf_element*;

  public:
    concurrent_hash_set_uf(std::mutex *mtx, std::size_t hs_size)
      : mtx_(mtx), hs_size_(hs_size)
    {
      hs_ = new std::atomic<T>[hs_size]{nullptr};
    }

    ~concurrent_hash_set_uf()
    {
      for (std::size_t i = 0; i < hs_size_; i++)
        delete hs_[i];
      delete[] hs_;
    }

    std::optional<std::size_t> search(T element) const
    {
      // Capacity threshold
      if (SPOT_UNLIKELY((100. * (double) nb_elements_ / hs_size_) >= 90.))
        return std::nullopt;

      // Linear probing
      std::size_t idx = element->hash() % hs_size_;
      std::size_t nb_loop = 0;
      while (hs_[idx] != nullptr && !(element->equal(*hs_[idx])))
      {
        if (SPOT_UNLIKELY(nb_loop == hs_size_))
          return std::nullopt;
        idx = (idx + 1) % hs_size_;
        ++nb_loop;
      }
      return std::optional<std::size_t>(idx);
    }

    std::pair<T, bool> find(T element)
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

    std::pair<T, bool> insert(T element)
    {
      //std::scoped_lock<std::mutex> lock(*mtx_);
      if (auto idx = search(element))
      {
        if (hs_[*idx] != nullptr)
          return {hs_[*idx], false};
        else
        {
          hs_[*idx] = element;
          // XXX(thibault): move allocation/deallocation out of HM
          // hs_[*idx] = new iterable_uf_bitstate<State, StateHash,
          // StateEqual>::uf_element{element};
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

        // XXX(thibault): move allocation/deallocation out of HM
        // delete hs_[*idx];
        --nb_elements_;

        // Only deleting the element will break the linear probing
        // mechanism, thus we need to either move the cells to keep the
        // continuous probing block, or use a tombstone. Here we mostly care
        // about memory and not speed performance so we chose the first
        // option.
        std::size_t cur = *idx;
        while (hs_[(cur + 1) % hs_size_] != nullptr)
        {
          T next = hs_[(cur + 1) % hs_size_];
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
    std::atomic<T> *hs_;
    std::atomic<std::size_t> nb_elements_;
    std::mutex *mtx_;
    std::size_t hs_size_;
  };
}
