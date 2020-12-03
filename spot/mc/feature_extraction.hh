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
#include <iostream>
#include <stdlib.h>
#include <thread>
#include <utility>
#include <vector>
#include <spot/bricks/brick-hashset>
#include <spot/kripke/kripke.hh>
#include <spot/mc/intersect.hh>
#include <spot/mc/mc.hh>
#include <spot/misc/common.hh>
#include <spot/misc/fixpool.hh>
#include <spot/misc/timer.hh>
#include <spot/twacube/fwd.hh>
#include <spot/twacube/twacube.hh>
#include <spot/twacube_algos/sccinfocube.hh>

namespace spot
{
  /// \breif Represents a maximal scc of the graph
  struct scc_element
  {
    /// \breif the number of nodes in the scc
    unsigned nb_nodes;
    /// \breif the number of reachable nodes from within the scc
    // always initialised to -1, indicating attribute is not computed
    int nb_reachable;
    /// \brief the in incidence of the scc
    unsigned incidence_in;
    /// \brief the out incidence of the scc
    unsigned incidence_out;
    /// \brief the list of sccs directly reachable from this element
    std::vector<unsigned> children;
  };


  template<typename State,
           typename StateHash,
           typename StateEqual>
  class iterable_uf_fe
  {

  public:
    enum class uf_status  { LIVE, LOCK, DEAD };
    enum class list_status  { BUSY, LOCK, DONE };
    enum class claim_status  { CLAIM_FOUND, CLAIM_NEW, CLAIM_DEAD };

    /// \brief Represents a Union-Find element
    struct uf_element
    {
      /// \brief the kripke state handled by the element
      State st_kripke;
      /// \brief the prop state handled by the element
      unsigned st_prop;
      /// \brief acceptance conditions of the union
      acc_cond::mark_t acc;
      /// \brief index of the node in apparition order
      unsigned index;
      /// \brief index of the scc the node belongs to
      // Set for root sccs at the end of the exploration
      int scc_index;
      /// \brief in incidence of the element
      unsigned incidence_in;
      /// \brief out incidence of the element
      unsigned incidence_out;
      /// \brief mutex for acceptance condition
      std::mutex acc_mutex_;
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
    };

    /// \brief The haser for the previous uf_element.
    struct uf_element_hasher
    {
      uf_element_hasher(const uf_element*)
      { }

      uf_element_hasher() = default;

      brick::hash::hash128_t
      hash(const uf_element* lhs) const
      {
        StateHash hash;
        // Not modulo 31 according to brick::hashset specifications.
        unsigned u = hash(lhs->st_kripke) % (1<<30);
        u = wang32_hash(lhs->st_prop) ^ u;
        u = u % (1<<30);
        return {u, u};
      }

      bool equal(const uf_element* lhs,
                 const uf_element* rhs) const
      {
        StateEqual equal;
        return (lhs->st_prop == rhs->st_prop)
          && equal(lhs->st_kripke, rhs->st_kripke);
      }
    };

    ///< \brief Shortcut to ease shared map manipulation
    using shared_map = brick::hashset::FastConcurrent <uf_element*,
                                                       uf_element_hasher>;

    iterable_uf_fe(const iterable_uf_fe<State, StateHash, StateEqual>& uf):
      map_(uf.map_), tid_(uf.tid_), size_(std::thread::hardware_concurrency()),
      nb_th_(std::thread::hardware_concurrency()), inserted_(0),
      p_(sizeof(uf_element))
    { }

    iterable_uf_fe(shared_map& map, unsigned tid):
      map_(map), tid_(tid), size_(std::thread::hardware_concurrency()),
      nb_th_(std::thread::hardware_concurrency()), inserted_(0),
      p_(sizeof(uf_element))
    { }

    ~iterable_uf_fe() {}

    std::pair<claim_status, uf_element*>
    make_claim(State kripke, unsigned prop)
    {
      unsigned w_id = (1U << tid_);

      // Setup and try to insert the new state in the shared map.
      uf_element* v = (uf_element*) p_.allocate();
      new (v) (uf_element); // required, otherwise the mutex is unitialized
      v->st_kripke = kripke;
      v->st_prop = prop;
      v->acc = {};
      v->parent = v;
      v->next_ = v;
      v->worker_ = 0;
      v->uf_status_ = uf_status::LIVE;
      v->list_status_ = list_status::BUSY;

      auto it = map_.insert({v});
      bool b = it.isnew();

      // Insertion failed, delete element
      // FIXME Should we add a local cache to avoid useless allocations?
      if (!b)
        p_.deallocate(v);
      else
        ++inserted_;

      uf_element* a_root = find(*it);
      if (a_root->uf_status_.load() == uf_status::DEAD)
        return {claim_status::CLAIM_DEAD, *it};

      if ((a_root->worker_.load() & w_id) != 0)
        return {claim_status::CLAIM_FOUND, *it};

      atomic_fetch_or(&(a_root->worker_), w_id);
      while (a_root->parent.load() != a_root)
        {
          a_root = find(a_root);
          atomic_fetch_or(&(a_root->worker_), w_id);
        }

      return {claim_status::CLAIM_NEW, *it};
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

    acc_cond::mark_t
    unite(uf_element* a, uf_element* b, acc_cond::mark_t acc)
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
            {
              // Update acceptance condition
              {
                std::lock_guard<std::mutex> rlock(a_root->acc_mutex_);
                a_root->acc |= acc;
                acc |= a_root->acc;
              }

              while (a_root->parent.load() != a_root)
                {
                  a_root = find(a_root);
                  std::lock_guard<std::mutex> rlock(a_root->acc_mutex_);
                  a_root->acc |= acc;
                  acc |= a_root->acc;
                }
              return acc;
            }

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
          return acc;
        }

      uf_element* b_list = lock_list(b);
      if (b_list == nullptr)
        {
          unlock_list(a_list);
          unlock_root(q);
          return acc;
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

      // Update acceptance condition
      {
        std::lock_guard<std::mutex> rlock(r->acc_mutex_);
        std::lock_guard<std::mutex> qlock(q->acc_mutex_);
        q->acc |= acc;
        r->acc |= q->acc;
        acc |= r->acc;
      }

      while (r->parent.load() != r)
        {
          r = find(r);
          std::lock_guard<std::mutex> rlock(r->acc_mutex_);
          std::lock_guard<std::mutex> qlock(q->acc_mutex_);
          r->acc |= q->acc;
          acc |= r->acc;
        }

      unlock_list(a_list);
      unlock_list(b_list);
      unlock_root(q);
      return acc;
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
      while (true)
        {
          list_status a_status = a->list_status_.load();

          if (a_status == list_status::DONE)
            break;

          if (a_status == list_status::BUSY)
            std::atomic_compare_exchange_strong
              (&(a->list_status_), &a_status, list_status::DONE);
        }
    }

    unsigned inserted()
    {
      return inserted_;
    }

    shared_map map()
    {
      return map_;
    }

  private:
    iterable_uf_fe() = default;

    shared_map map_;      ///< \brief Map shared by threads copy!
    unsigned tid_;        ///< \brief The Id of the current thread
    unsigned size_;       ///< \brief Maximum number of thread
    unsigned nb_th_;      ///< \brief Current number of threads
    unsigned inserted_;   ///< \brief The number of insert succes
    fixed_size_pool<pool_type::Unsafe> p_; ///< \brief The allocator
  };

  /// \brief This class implements the SCC decomposition algorithm of bloemen
  /// as described in PPOPP'16. It uses a shared union-find augmented to manage
  /// work stealing between threads.
  template<typename State, typename SuccIterator,
           typename StateHash, typename StateEqual>
  class swarmed_feature_extraction
  {
  private:
    swarmed_feature_extraction() = delete;
  public:

    using uf = iterable_uf_fe<State, StateHash, StateEqual>;
    using uf_element = typename uf::uf_element;

    using shared_struct = uf;
    using shared_map = typename uf::shared_map;

    static shared_struct* make_shared_structure(shared_map m, unsigned i)
    {
      return new uf(m, i);
    }

    swarmed_feature_extraction(kripkecube<State, SuccIterator>& sys,
                       twacube_ptr twa,
                       shared_map& map, /* useless here */
                       iterable_uf_fe<State, StateHash, StateEqual>* uf,
                       unsigned tid,
                       std::atomic<bool>& stop,
                       scc_infocube_ptr sccinfo):
      sys_(sys),  twa_(twa), uf_(*uf), tid_(tid),
      nb_th_(std::thread::hardware_concurrency()),
      stop_(stop), sccinfo_(sccinfo)
    {
      static_assert(spot::is_a_kripkecube_ptr<decltype(&sys),
                                             State, SuccIterator>::value,
                    "error: does not match the kripkecube requirements");
    }

    ~swarmed_feature_extraction() = default;

    void run()
    {
      setup();
      State init_kripke = sys_.initial(tid_);
      unsigned init_twa = twa_->get_initial();
      auto pair = uf_.make_claim(init_kripke, init_twa);
      todo_.push_back(pair.second);
      Rp_.push_back(pair.second);
      ++states_;
      unsigned index = 0;

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
                  if (sccfound)
                    {
                      // set the index of the scc root, it being the
                      // representative of the scc
                      uf_.find(todo_.back())->scc_index = sccs_;
                      scc_vect_.push_back({0, -1, 0, 0});
                    }
                  sccs_ += sccfound;
                  break;
                }

              auto it_kripke = sys_.succ(v_prime->st_kripke, tid_);
              auto it_prop = twa_->succ(v_prime->st_prop);
              forward_iterators(sys_, twa_, it_kripke, it_prop, true, tid_);
              while (!it_kripke->done())
                {
                  auto w = uf_.make_claim(it_kripke->state(),
                                          twa_->trans_storage(it_prop, tid_)
                                          .dst);

                  auto trans_acc = twa_->trans_storage(it_prop, tid_).acc_;
                  ++transitions_;
                  if (w.first == uf::claim_status::CLAIM_NEW)
                    {
                      w.second->incidence_in = 1;
                      w.second->index = index;
                      ++index;
                      w.second->scc_index = 0;

                      todo_.push_back(w.second);
                      Rp_.push_back(w.second);
                      ++states_;
                      sys_.recycle(it_kripke, tid_);
                      goto bloemen_recursive_start;
                    }
                  else if (w.first == uf::claim_status::CLAIM_FOUND)
                    {
                      ++repeated_;
                      acc_cond::mark_t scc_acc = trans_acc;

                      // This operation is mandatory to update acceptance marks.
                      // Otherwise, when w.second and todo.back() are
                      // already in the same set, the acceptance condition will
                      // not be added.
                      scc_acc |= uf_.unite(w.second, w.second, scc_acc);

                      while (!uf_.sameset(todo_.back(), w.second))
                        {
                          uf_element* r = Rp_.back();
                          Rp_.pop_back();
                          uf_.unite(r, Rp_.back(), scc_acc);
                        }


                      {
                        auto root = uf_.find(w.second);
                        std::lock_guard<std::mutex> lock(w.second->acc_mutex_);
                        scc_acc = w.second->acc;
                      }

                      // cycle found in SCC and it contains acceptance condition
                      if (twa_->acc().accepting(scc_acc))
                        {
                          sys_.recycle(it_kripke, tid_);
                          stop_ = true;
                          is_empty_ = false;
                          tm_.stop("DFS thread " + std::to_string(tid_));
                          log();
                          return;
                        }
                    }
                  forward_iterators(sys_, twa_, it_kripke, it_prop,
                                    false, tid_);
                }
              uf_.remove_from_list(v_prime);
              sys_.recycle(it_kripke, tid_);
            }

          if (todo_.back() == Rp_.back())
            Rp_.pop_back();
          todo_.pop_back();
        }
      log();
      finalize();
    }

    int sccs_get_reachable_at(unsigned index)
    {
      if (scc_vect_[index].nb_reachable == -1)
        {
          scc_vect_[index].nb_reachable = scc_vect_[index].nb_nodes;
          for (auto child_index : scc_vect_[index].children)
            scc_vect_[index].nb_reachable += sccs_get_reachable_at(child_index);
        }
      return scc_vect_[index].nb_reachable;
    }

    int sccs_get_reachable()
    {
      int count = 0;
      for (unsigned i = 0; i < scc_vect_.size(); ++i)
        count += sccs_get_reachable_at(i);
      return count;
    }

    // Number of transition with multiple visits and
    // list of sccs calculated on the fly, needed for unified logging.
    void log()
    {
      log_calculate();
      auto map = uf_.map();
      unsigned total_in = 0;
      unsigned total_out = 0;
      float total_ratio = 0;
      unsigned nb_results = 0;
      for (auto i = 0; i < map.capacity(); i++)
        {
          if (map.valid(i))
          {
            auto element = map.valueAt(i);
            int* state = element->st_kripke;
            if (element->incidence_in)
              {
                float ratio = static_cast<float>(element->incidence_out)
                              / element->incidence_in;
                total_in += element->incidence_in;
                total_out += element->incidence_out;
                total_ratio += ratio;
                ++nb_results;
              }
          }
        }

      float average_scc_incidence = 0;
      float average_reachability = 0;
      for (auto& scc : scc_vect_)
        {
          if (scc.incidence_in)
            average_scc_incidence += static_cast<float>(scc.incidence_out)
                                     / scc.incidence_in;
          average_reachability += scc.nb_reachable;
        }
      average_scc_incidence /= scc_vect_.size();
      average_reachability /= scc_vect_.size();
      average_reachability /= nb_results;

      int nb_weak_scc = 0;
      for (auto b : sccinfo_.weak_sccs())
        {
          if (b)
            ++nb_weak_scc;
        }

      int nb_accepting_scc = 0;
      int nb_trivial_scc = 0;
      for (unsigned i = 0; i < sccinfo_.scc_count(); ++i)
        {
          if (sccinfo_.is_accepting_scc(i))
            ++nb_accepting_scc;
          if (sccinfo_.is_trivial(i))
            ++nb_trivial_scc;
        }

      if (!nb_results)
          nb_results = 1;

      char delimiter = ',';
      std::cout << "feature extraction csv : " << std::endl;
      std::cout << "in_incidence,out_incidence,average_incidence_ratio,"
                << "repeated_transitions,average_scc_incidence_ratio,"
                << "average_node_reachability,nb_weak_scc,"
                << "nb_accepting_scc,nb_trivial_scc" << std::endl;
      std::cout << total_in << delimiter << total_out << delimiter
                << total_ratio / nb_results << delimiter
                << repeated_ << delimiter
                << average_scc_incidence << delimiter
                << average_reachability << delimiter
                << nb_weak_scc << delimiter
                << nb_accepting_scc << delimiter
                << nb_trivial_scc <<std::endl;
    }

    void log_calculate()
    {
      auto map = uf_.map();
      for (auto i = 0; i < map.capacity(); i++)
        {
          if (map.valid(i))
            {
              auto element = map.valueAt(i);

              auto it_kripke = sys_.succ(element->st_kripke, tid_);
              auto it_prop = twa_->succ(element->st_prop);
              unsigned incidence_out = 1;
              forward_iterators(sys_, twa_, it_kripke, it_prop,
                                true, tid_);
              while (!it_kripke->done())
                {
                  ++incidence_out;
                  uf_element v;
                  v.st_kripke = it_kripke->state();
                  v.st_prop = twa_->trans_storage(it_prop, tid_).dst;
                  auto it = map.find(&v);
                  if (*it != *map.end())
                    {
                      ++(*it)->incidence_in;

                      // get scc of the head and tail of the current edge
                      unsigned scc_from = uf_.find(element)->scc_index;
                      unsigned scc_to = uf_.find((*it))->scc_index;
                      ++scc_vect_[scc_from].nb_nodes;
                      if (scc_from != scc_to)
                        {
                          // edge connects two different sccs
                          ++scc_vect_[scc_to].nb_nodes;
                          ++scc_vect_[scc_from].incidence_out;
                          ++scc_vect_[scc_to].incidence_in;
                          auto& from = scc_vect_[scc_from];
                          if (std::find(from.children.begin(),
                                        from.children.end(),
                                        scc_to)
                              == scc_vect_[scc_from].children.end())
                            scc_vect_[scc_from].children.push_back(scc_to);
                        }
                    }

                    forward_iterators(sys_, twa_, it_kripke,
                                    it_prop, false, tid_);
                }
              sys_.recycle(it_kripke, tid_);
              element->incidence_out = incidence_out;
            }
        }
      sccs_get_reachable();
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

    kripkecube<State, SuccIterator>& sys()
    {
        return sys_;
    }

    twacube_ptr twa()
    {
        return twa_;
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
      return "feature_extraction";
    }

    int sccs()
    {
      return sccs_;
    }

    mc_rvalue result()
    {
      return is_empty_ ? mc_rvalue::EMPTY : mc_rvalue::NOT_EMPTY;
    }

    std::string trace()
    {
      return "Not implemented";
    }

  private:
    kripkecube<State, SuccIterator>& sys_;   ///< \brief The system to check
    twacube_ptr twa_;                        ///< \brief The formula to check
    std::vector<uf_element*> todo_;          ///< \brief The "recursive" stack
    std::vector<uf_element*> Rp_;            ///< \brief The DFS stack
    std::vector<scc_element> scc_vect_;      ///< \brief Set of sccs information
    scc_infocube_ptr sccinfo_;                   ///< \brief Scc information
    iterable_uf_fe<State, StateHash, StateEqual> uf_; ///< Copy!
    unsigned tid_;
    unsigned nb_th_;
    unsigned inserted_ = 0;           ///< \brief Number of states inserted
    unsigned states_  = 0;            ///< \brief Number of states visited
    unsigned transitions_ = 0;        ///< \brief Number of transitions visited
    unsigned repeated_ = 0;           ///< \brief Number of repeated visits
    unsigned sccs_ = 0;               ///< \brief Number of SCC visited
    bool is_empty_ = true;
    spot::timer_map tm_;              ///< \brief Time execution
    std::atomic<bool>& stop_;
    bool finisher_ = false;
  };
}
