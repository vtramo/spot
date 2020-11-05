// -*- coding: utf-8 -*-
// Copyright (C) 2017, 2018, 2020 Laboratoire de Recherche et Développement de
// l'Epita (LRDE)
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

#include <algorithm>
#include <spot/bricks/brick-hash>
#include <spot/bricks/brick-hashset>
#include <spot/ltsmin/spins_interface.hh>
#include <spot/misc/fixpool.hh>
#include <spot/misc/mspool.hh>
#include <spot/misc/intvcomp.hh>
#include <spot/misc/intvcmp2.hh>
#include <spot/twacube/cube.hh>


namespace spot
{
  cspins_state_manager::cspins_state_manager(unsigned int state_size,
                                             int compress)
    : p_((state_size+2)*sizeof(int)), compress_(compress),
      /* reserve one integer for the hash value and size */
      state_size_(state_size),
      fn_compress_(compress == 0 ? nullptr
                   : compress == 1 ? int_array_array_compress
                   : int_array_array_compress2),
      fn_decompress_(compress == 0 ? nullptr
                     : compress == 1 ? int_array_array_decompress
                     : int_array_array_decompress2)
  { }

  int* cspins_state_manager::unbox_state(cspins_state s) const
  {
    return s+2;
  }

  // cmp is the area we can use to compute the compressed rep of dst.
  cspins_state
  cspins_state_manager::alloc_setup(int *dst, int* cmp, size_t cmpsize)
  {
    cspins_state out = nullptr;
    size_t size = state_size_;
    int* ref = dst;
    if (compress_)
      {
        size_t csize = cmpsize;
        fn_compress_(dst, state_size_, cmp, csize);
        ref = cmp;
        size = csize;
        out = (cspins_state) msp_.allocate((size+2)*sizeof(int));
      }
    else
      out = (cspins_state) p_.allocate();
    int hash_value = 0;
    memcpy(unbox_state(out), ref, size * sizeof(int));
    for (unsigned int i = 0; i < state_size_; ++i)
      hash_value = wang32_hash(hash_value ^ dst[i]);
    out[0] = hash_value;
    out[1] = size;
    return out;
  }

  void cspins_state_manager::decompress(cspins_state s, int* uncompressed,
                                        unsigned size) const
  {
    fn_decompress_(s+2, s[1], uncompressed, size);
  }

  void cspins_state_manager::dealloc(cspins_state s)
  {
    if (compress_)
      msp_.deallocate(s, (s[1]+2)*sizeof(int));
    else
      p_.deallocate(s);
  }

  unsigned int cspins_state_manager::size() const
  {
    return state_size_;
  }

  cspins_iterator::cspins_iterator(cspins_iterator_param& p)
    :  current_(0), cond_(p.cond), tid_(p.tid)
  {
    successors_.reserve(10);
    setup_iterator(p);
  }

  void cspins_iterator::recycle(cspins_iterator_param& p)
  {
    tid_ = p.tid;
    cond_ = p.cond;
    current_ = 0;
    // Constant time since int* is is_trivially_destructible
    successors_.clear();
    setup_iterator(p);
  }

  void cspins_iterator::setup_iterator(cspins_iterator_param& p)
  {
    str_ = p.str;
    p.inner.manager = &(p.manager);
    p.inner.succ = &successors_;
    p.inner.compress = p.compress;
    p.inner.selfloopize = p.selfloopize;
    int* ref = p.s;

    if (p.compress)
      // already filled by compute_condition
      ref = p.inner.uncompressed;

    int n = p.d->get_successors
      (nullptr, p.manager.unbox_state(ref),
       [](void* arg, transition_info_t*, int *dst){
        inner_callback_parameters* inner =
        static_cast<inner_callback_parameters*>(arg);
        cspins_state s =
        inner->manager->alloc_setup(dst, inner->compressed,
                                    inner->manager->size() * 2);
        inner->succ->push_back(s);
       },
       &(p.inner));
    if (!n && p.selfloopize)
      {
        successors_.push_back(p.s);
        if (p.dead_idx != -1)
          p.cubeset.set_true_var(p.cond, p.dead_idx);
      }

  }

  cspins_iterator::~cspins_iterator()
  {
    // Do not release successors states, the manager
    // will do it on time.
  }

  void cspins_iterator::next()
  {
    ++current_;
  }

  bool cspins_iterator::done() const
  {
    return current_ >= successors_.size();
  }

  cspins_state cspins_iterator::state() const
  {
    if (SPOT_UNLIKELY(!tid_) || str_ == trans_walking_strategy::No_swarming)
      return successors_[current_];
    return   successors_[compute_index()];
  }

  unsigned cspins_iterator::compute_index() const
  {
    unsigned long long c = current_ + 1;
    unsigned long long p = primes[tid_];
    unsigned long long s = successors_.size();
    return (unsigned)  ((c*p) % s);
  }

  cube cspins_iterator::condition() const
  {
    return cond_;
  }


  kripkecube<cspins_state, cspins_iterator>
  ::kripkecube (spins_interface_ptr sip,
                bool compress,
                std::vector<std::string> visible_aps,
                bool selfloopize, std::string dead_prop,
                unsigned int nb_threads,
                trans_walking_strategy str)
    : sip_(sip), d_(sip.get()),
      compress_(compress), cubeset_(visible_aps.size()),
      selfloopize_(selfloopize), aps_(visible_aps),
      nb_threads_(nb_threads), str_(str)
  {
    manager_ = static_cast<cspins_state_manager*>
      (::operator new(sizeof(cspins_state_manager) * nb_threads));
    inner_ = new inner_callback_parameters[nb_threads_];
    for (unsigned i = 0; i < nb_threads_; ++i)
      {
        recycle_.push_back(std::vector<cspins_iterator*>());
        recycle_.back().reserve(2000000);
        new (&manager_[i])
          cspins_state_manager(d_->get_state_size(), compress);
        inner_[i].compressed = new int[d_->get_state_size() * 2];
        inner_[i].uncompressed = new int[d_->get_state_size()+30];
      }
    dead_idx_ = -1;
    for (unsigned  i = 0; i < aps_.size(); ++i)
      {
        if (aps_[i].compare(dead_prop) == 0)
          {
            dead_idx_ = i;
            break;
          }
      }

    const_cast<spot::spins_interface*>(d_)
      ->generate_compute_aps(aps_, dead_prop);
  }

  kripkecube<cspins_state, cspins_iterator>::~kripkecube()
  {
    for (auto& i: recycle_)
      {
        for (auto& j: i)
          {
            cubeset_.release(j->condition());
            delete j;
          }
      }

    for (unsigned i = 0; i < nb_threads_; ++i)
      {
        manager_[i].~cspins_state_manager();
        delete[] inner_[i].compressed;
        delete[] inner_[i].uncompressed;
      }
    ::operator delete(manager_);
    delete[] inner_;
  }

  cspins_state kripkecube<cspins_state, cspins_iterator>::initial(unsigned tid)
  {
    d_->get_initial_state(inner_[tid].uncompressed);
    return manager_[tid].alloc_setup(inner_[tid].uncompressed,
                                     inner_[tid].compressed,
                                     manager_[tid].size() * 2);
  }

  std::string
  kripkecube<cspins_state, cspins_iterator>::to_string(const cspins_state s,
                                                       unsigned tid) const
  {
    std::string res = "";
    cspins_state out = manager_[tid].unbox_state(s);
    cspins_state ref = out;
    if (compress_)
      {
        manager_[tid].decompress(s, inner_[tid].uncompressed,
                                 manager_[tid].size());
        ref = inner_[tid].uncompressed;
      }
    for (int i = 0; i < d_->get_state_size(); ++i)
      res += (d_->get_state_variable_name(i)) +
        ("=" + std::to_string(ref[i])) + ",";
    res.pop_back();
    return res;
  }

  cspins_iterator*
  kripkecube<cspins_state, cspins_iterator>::succ(const cspins_state s,
                                                  unsigned tid)
  {
    cspins_iterator::cspins_iterator_param p =
      {
        s, d_, manager_[tid], inner_[tid],
        nullptr, compress_, selfloopize_,
        cubeset_, dead_idx_, tid, str_,
      };

    if (SPOT_LIKELY(!recycle_[tid].empty()))
      {
        auto tmp  = recycle_[tid].back();
        recycle_[tid].pop_back();
        p.cond = tmp->condition();
        compute_condition(p.cond, s, tid);
        tmp->recycle(p);
        return tmp;
      }
    cube cond = cubeset_.alloc();
    p.cond = cond;
    compute_condition(cond, s, tid);
    return new cspins_iterator(p);
  }

  void
  kripkecube<cspins_state, cspins_iterator>::recycle(cspins_iterator* it,
                                                     unsigned tid)
  {
    recycle_[tid].push_back(it);
  }

  const std::vector<std::string>
  kripkecube<cspins_state, cspins_iterator>::ap()
  {
    return aps_;
  }

  unsigned kripkecube<cspins_state, cspins_iterator>::get_threads()
  {
    return nb_threads_;
  }

  void
  kripkecube<cspins_state, cspins_iterator>::compute_condition
  (cube c, cspins_state s, unsigned tid)
  {
    int *vars = manager_[tid].unbox_state(s);

    // State is compressed, uncompress it
    if (compress_)
      {
        manager_[tid].decompress(s, inner_[tid].uncompressed+2,
                                 manager_[tid].size());
        vars = inner_[tid].uncompressed + 2;
      }
    d_->compute_aps_cube(vars, c);
  }
}
