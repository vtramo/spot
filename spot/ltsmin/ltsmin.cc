// -*- coding: utf-8 -*-
// Copyright (C) 2011, 2012, 2014-2019 Laboratoire de
// Recherche et Développement de l'Epita (LRDE)
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

#include "config.h"
#include <ltdl.h>
#include <cstring>
#include <cstdlib>
#include <vector>
#include <sstream>
#include <sys/stat.h>
#include <unistd.h>

#include <spot/ltsmin/ltsmin.hh>
#include <spot/misc/hashfunc.hh>
#include <spot/misc/fixpool.hh>
#include <spot/misc/mspool.hh>
#include <spot/misc/intvcomp.hh>
#include <spot/misc/intvcmp2.hh>

#include <spot/twaalgos/reachiter.hh>
#include <string.h>
#include <spot/mc/utils.hh>

using namespace std::string_literals;

namespace spot
{
  namespace
  {
    ////////////////////////////////////////////////////////////////////////
    // STATE

    struct spins_state final: public state
    {
      spins_state(int s, fixed_size_pool<pool_type::Safe>* p)
        : pool(p), size(s), count(1)
      {
      }

      void compute_hash()
      {
        hash_value = 0;
        for (int i = 0; i < size; ++i)
          hash_value = wang32_hash(hash_value ^ vars[i]);
      }

      spins_state* clone() const override
      {
        ++count;
        return const_cast<spins_state*>(this);
      }

      void destroy() const override
      {
        if (--count)
          return;
        pool->deallocate(const_cast<spins_state*>(this));
      }

      size_t hash() const override
      {
        return hash_value;
      }

      int compare(const state* other) const override
      {
        if (this == other)
          return 0;
        const spins_state* o = down_cast<const spins_state*>(other);
        if (hash_value < o->hash_value)
          return -1;
        if (hash_value > o->hash_value)
          return 1;
        return memcmp(vars, o->vars, size * sizeof(*vars));
      }

    private:

      ~spins_state()
      {
      }

    public:
      fixed_size_pool<pool_type::Safe>* pool;
      size_t hash_value: 32;
      int size: 16;
      mutable unsigned count: 16;
      int vars[1];
    };

    struct spins_compressed_state final: public state
    {
      spins_compressed_state(int s, multiple_size_pool* p)
        : pool(p), size(s), count(1)
      {
      }

      void compute_hash()
      {
        hash_value = 0;
        for (int i = 0; i < size; ++i)
          hash_value = wang32_hash(hash_value ^ vars[i]);
      }

      spins_compressed_state* clone() const override
      {
        ++count;
        return const_cast<spins_compressed_state*>(this);
      }

      void destroy() const override
      {
        if (--count)
          return;
        pool->deallocate(this, sizeof(*this) - sizeof(vars)
                         + size * sizeof(*vars));
      }

      size_t hash() const override
      {
        return hash_value;
      }

      int compare(const state* other) const override
      {
        if (this == other)
          return 0;
        const spins_compressed_state* o =
          down_cast<const spins_compressed_state*>(other);
        if (hash_value < o->hash_value)
          return -1;
        if (hash_value > o->hash_value)
          return 1;

        if (size < o->size)
          return -1;
        if (size > o->size)
          return 1;

        return memcmp(vars, o->vars, size * sizeof(*vars));
      }

    private:

      ~spins_compressed_state()
      {
      }

    public:
      multiple_size_pool* pool;
      size_t hash_value: 32;
      int size: 16;
      mutable unsigned count: 16;
      int vars[1];
    };

    ////////////////////////////////////////////////////////////////////////
    // CALLBACK FUNCTION for transitions.

    struct callback_context
    {
      typedef std::list<state*> transitions_t;
      transitions_t transitions;
      int state_size;
      void* pool;
      int* compressed;
      void (*compress)(const int*, size_t, int*, size_t&);

      ~callback_context()
      {
        for (auto t: transitions)
          t->destroy();
      }
    };

    void transition_callback(void* arg, transition_info_t*, int *dst)
    {
      callback_context* ctx = static_cast<callback_context*>(arg);
      fixed_size_pool<pool_type::Safe>* p =
        static_cast<fixed_size_pool<pool_type::Safe>*>(ctx->pool);
      spins_state* out =
        new(p->allocate()) spins_state(ctx->state_size, p);
      SPOT_ASSUME(out != nullptr);
      memcpy(out->vars, dst, ctx->state_size * sizeof(int));
      out->compute_hash();
      ctx->transitions.emplace_back(out);
    }

    void transition_callback_compress(void* arg, transition_info_t*, int *dst)
    {
      callback_context* ctx = static_cast<callback_context*>(arg);
      multiple_size_pool* p = static_cast<multiple_size_pool*>(ctx->pool);

      size_t csize = ctx->state_size * 2;
      ctx->compress(dst, ctx->state_size, ctx->compressed, csize);

      void* mem = p->allocate(sizeof(spins_compressed_state)
                              - sizeof(spins_compressed_state::vars)
                              + sizeof(int) * csize);
      spins_compressed_state* out = new(mem) spins_compressed_state(csize, p);
      SPOT_ASSUME(out != nullptr);
      memcpy(out->vars, ctx->compressed, csize * sizeof(int));
      out->compute_hash();
      ctx->transitions.emplace_back(out);
    }

    ////////////////////////////////////////////////////////////////////////
    // SUCC_ITERATOR

    class spins_succ_iterator final: public kripke_succ_iterator
    {
    public:

      spins_succ_iterator(const callback_context* cc,
                         bdd cond)
        : kripke_succ_iterator(cond), cc_(cc)
      {
      }

      void recycle(const callback_context* cc, bdd cond)
      {
        delete cc_;
        cc_ = cc;
        kripke_succ_iterator::recycle(cond);
      }

      ~spins_succ_iterator()
      {
        delete cc_;
      }

      virtual bool first() override
      {
        it_ = cc_->transitions.begin();
        return it_ != cc_->transitions.end();
      }

      virtual bool next() override
      {
        ++it_;
        return it_ != cc_->transitions.end();
      }

      virtual bool done() const override
      {
        return it_ == cc_->transitions.end();
      }

      virtual state* dst() const override
      {
        return (*it_)->clone();
      }

    private:
      const callback_context* cc_;
      callback_context::transitions_t::const_iterator it_;
    };

    ////////////////////////////////////////////////////////////////////////
    // PREDICATE EVALUATION

    typedef enum { OP_EQ, OP_NE, OP_LT, OP_GT, OP_LE, OP_GE } relop;

    struct one_prop
    {
      int var_num;
      relop op;
      int val;
      int bddvar;  // if "var_num op val" is true, output bddvar,
                   // else its negation
    };
    typedef std::vector<one_prop> prop_set;


    struct var_info
    {
      int num;
      int type;
    };


    std::vector<int>
    convert_aps(const atomic_prop_set* aps,
                spins_interface_ptr d,
                bdd_dict_ptr dict,
                formula dead)
    {
      std::vector<std::string> props;
      std::vector<int> bdd_indexes;
      for (atomic_prop_set::const_iterator ap = aps->begin();
           ap != aps->end(); ++ap)
        {
          int v = dict->register_proposition(*ap, d.get());
          bdd_indexes.emplace_back(v);
          props.emplace_back(ap->ap_name());
        }

      const_cast<spot::spins_interface*>(d.get())
        ->generate_compute_aps(props);

      (void) dead; // FIXME
      return bdd_indexes;
    }

    ////////////////////////////////////////////////////////////////////////
    // KRIPKE

    class spins_kripke final: public kripke
    {
    public:

      spins_kripke(spins_interface_ptr d, const bdd_dict_ptr& dict,
                   formula dead, int compress, std::vector<int> bdd_indexes)
        : kripke(dict),
          d_(d),
          state_size_(d_->get_state_size()),
          bdd_indexes_(bdd_indexes),
          compress_(compress == 0 ? nullptr
                    : compress == 1 ? int_array_array_compress
                    : int_array_array_compress2),
          decompress_(compress == 0 ? nullptr
                      : compress == 1 ? int_array_array_decompress
                      : int_array_array_decompress2),
          uncompressed_(compress ? new int[state_size_ + 30] : nullptr),
          compressed_(compress ? new int[state_size_ * 2] : nullptr),
          statepool_(compress ?
                     (sizeof(spins_compressed_state)
                      - sizeof(spins_compressed_state::vars)) :
                     (sizeof(spins_state) - sizeof(spins_state::vars)
                      + (state_size_ * sizeof(int)))),
          state_condition_last_state_(nullptr),
          state_condition_last_cc_(nullptr)
      {
        vname_ = new const char*[state_size_];
        format_filter_ = new bool[state_size_];
        for (int i = 0; i < state_size_; ++i)
          {
            vname_[i] = d_->get_state_variable_name(i);
            // We don't want to print variables that can take a single
            // value (e.g. process with a single state) to shorten the
            // output.
            int type = d->get_state_variable_type(i);
            format_filter_[i] =
              (d->get_type_value_count(type) != 1);
          }

        // Register the "dead" proposition.  There are three cases to
        // consider:
        //  * If DEAD is "false", it means we are not interested in finite
        //    sequences of the system.
        //  * If DEAD is "true", we want to check finite sequences as well
        //    as infinite sequences, but do not need to distinguish them.
        //  * If DEAD is any other string, this is the name a property
        //    that should be true when looping on a dead state, and false
        //    otherwise.
        // We handle these three cases by setting ALIVE_PROP and DEAD_PROP
        // appropriately.  ALIVE_PROP is the bdd that should be ANDed
        // to all transitions leaving a live state, while DEAD_PROP should
        // be ANDed to all transitions leaving a dead state.
        if (dead.is_ff())
          {
            alive_prop = bddtrue;
            dead_prop = bddfalse;
          }
        else if (dead.is_tt())
          {
            alive_prop = bddtrue;
            dead_prop = bddtrue;
          }
        else
          {
            int var = dict->register_proposition(dead, d_);
            dead_prop = bdd_ithvar(var);
            alive_prop = bdd_nithvar(var);
          }
      }

      ~spins_kripke()
      {
        if (iter_cache_)
          {
            delete iter_cache_;
            iter_cache_ = nullptr;
          }
        delete[] format_filter_;
        delete[] vname_;
        if (compress_)
          {
            delete[] uncompressed_;
            delete[] compressed_;
          }
        dict_->unregister_all_my_variables(d_.get());

        if (state_condition_last_state_)
          state_condition_last_state_->destroy();
        delete state_condition_last_cc_; // Might be 0 already.
      }

      virtual state* get_init_state() const override
      {
        if (compress_)
          {
            d_->get_initial_state(uncompressed_);
            size_t csize = state_size_ * 2;
            compress_(uncompressed_, state_size_, compressed_, csize);

            multiple_size_pool* p =
              const_cast<multiple_size_pool*>(&compstatepool_);
            void* mem = p->allocate(sizeof(spins_compressed_state)
                                    - sizeof(spins_compressed_state::vars)
                                    + sizeof(int) * csize);
            spins_compressed_state* res = new(mem)
              spins_compressed_state(csize, p);
            SPOT_ASSUME(res != nullptr);
            memcpy(res->vars, compressed_, csize * sizeof(int));
            res->compute_hash();
            return res;
          }
        else
          {
            fixed_size_pool<pool_type::Safe>* p =
              const_cast<fixed_size_pool<pool_type::Safe>*>(&statepool_);
            spins_state* res = new(p->allocate()) spins_state(state_size_, p);
            SPOT_ASSUME(res != nullptr);
            d_->get_initial_state(res->vars);
            res->compute_hash();
            return res;
          }
      }

      bdd
      compute_state_condition_aux(const int* vars) const
      {
        assert(bdd_indexes_.size() < sizeof(unsigned long long));

        unsigned long long v = d_->compute_aps_bdd(vars);
        bdd res = bddtrue;
        for (unsigned i = 0; i < bdd_indexes_.size(); ++i)
          res &= bdd_cond_ithvar(bdd_indexes_[i], (v >> i) & 1U);
        return res;
      }

      callback_context* build_cc(const int* vars, int& t) const
      {
        callback_context* cc = new callback_context;
        cc->state_size = state_size_;
        cc->pool =
          const_cast<void*>(compress_
                            ? static_cast<const void*>(&compstatepool_)
                            : static_cast<const void*>(&statepool_));
        cc->compress = compress_;
        cc->compressed = compressed_;
        t = d_->get_successors(nullptr, const_cast<int*>(vars),
                               compress_
                               ? transition_callback_compress
                               : transition_callback,
                               cc);
        assert((unsigned)t == cc->transitions.size());
        return cc;
      }

      bdd
      compute_state_condition(const state* st) const
      {
        // If we just computed it, don't do it twice.
        if (st == state_condition_last_state_)
          return state_condition_last_cond_;

        if (state_condition_last_state_)
          {
            state_condition_last_state_->destroy();
            delete state_condition_last_cc_; // Might be 0 already.
            state_condition_last_cc_ = nullptr;
          }

        const int* vars = get_vars(st);

        bdd res = compute_state_condition_aux(vars);
        int t;
        callback_context* cc = build_cc(vars, t);

        if (t)
          {
            res &= alive_prop;
          }
        else
          {
            res &= dead_prop;

            // Add a self-loop to dead-states if we care about these.
            if (res != bddfalse)
              cc->transitions.emplace_back(st->clone());
          }

        state_condition_last_cc_ = cc;
        state_condition_last_cond_ = res;
        state_condition_last_state_ = st->clone();

        return res;
      }

      const int*
      get_vars(const state* st) const
      {
        const int* vars;
        if (compress_)
          {
            const spins_compressed_state* s =
              down_cast<const spins_compressed_state*>(st);

            decompress_(s->vars, s->size, uncompressed_, state_size_);
            vars = uncompressed_;
          }
        else
          {
            const spins_state* s = down_cast<const spins_state*>(st);
            vars = s->vars;
          }
        return vars;
      }


      virtual
      spins_succ_iterator* succ_iter(const state* st) const override
      {
        // This may also compute successors in state_condition_last_cc
        bdd scond = compute_state_condition(st);

        callback_context* cc;
        if (state_condition_last_cc_)
          {
            cc = state_condition_last_cc_;
            state_condition_last_cc_ = nullptr; // Now owned by the iterator.
          }
        else
          {
            int t;
            cc = build_cc(get_vars(st), t);

            // Add a self-loop to dead-states if we care about these.
            if (t == 0 && scond != bddfalse)
              cc->transitions.emplace_back(st->clone());
          }

        if (iter_cache_)
          {
            spins_succ_iterator* it =
              down_cast<spins_succ_iterator*>(iter_cache_);
            it->recycle(cc, scond);
            iter_cache_ = nullptr;
            return it;
          }
        return new spins_succ_iterator(cc, scond);
      }

      virtual
      bdd state_condition(const state* st) const override
      {
        return compute_state_condition(st);
      }

      virtual
      std::string format_state(const state *st) const override
      {
        const int* vars = get_vars(st);

        std::stringstream res;

        if (state_size_ == 0)
          return "empty state";

        int i = 0;
        for (;;)
          {
            if (!format_filter_[i])
              {
                ++i;
                if (i == state_size_)
                  break;
                continue;
              }
            res << vname_[i] << '=' << vars[i];
            ++i;
            if (i == state_size_)
              break;
            res << ", ";
          }
        return res.str();
      }

    private:
      spins_interface_ptr d_;
      int state_size_;
      const char** vname_;
      bool* format_filter_;
      bdd alive_prop;
      bdd dead_prop;
      std::vector<int> bdd_indexes_;
      void (*compress_)(const int*, size_t, int*, size_t&);
      void (*decompress_)(const int*, size_t, int*, size_t);
      int* uncompressed_;
      int* compressed_;
      fixed_size_pool<pool_type::Safe> statepool_;
      multiple_size_pool compstatepool_;

      // This cache is used to speedup repeated calls to state_condition()
      // and get_succ().
      // If state_condition_last_state_ != 0, then state_condition_last_cond_
      // contain its (recently computed) condition.  If additionally
      // state_condition_last_cc_ != 0, then it contains the successors.
      mutable const state* state_condition_last_state_;
      mutable bdd state_condition_last_cond_;
      mutable callback_context* state_condition_last_cc_;
    };
  }

  ltsmin_model
  ltsmin_model::load(const std::string& file_arg)
  {
    return {std::make_shared<spins_interface>(file_arg)};
  }

  ltsmin_kripkecube_ptr
  ltsmin_model::kripkecube(std::vector<std::string> to_observe,
                           const formula dead, int compress,
                           unsigned int nb_threads,
                           trans_walking_strategy str) const
  {
    // Register the "dead" proposition.  There are three cases to
    // consider:
    //  * If DEAD is "false", it means we are not interested in finite
    //    sequences of the system.
    //  * If DEAD is "true", we want to check finite sequences as well
    //    as infinite sequences, but do not need to distinguish them.
    //  * If DEAD is any other string, this is the name a property
    //    that should be true when looping on a dead state, and false
    //    otherwise.
    std::string dead_ap = "";
    bool selfloopize = true;
    if (dead == spot::formula::ff())
      selfloopize = false;
    else if (dead != spot::formula::tt())
      dead_ap = dead.ap_name();

    // Is dead proposition is already in to_observe?
    bool add_dead = true;
    for (auto it: to_observe)
      if (it.compare(dead_ap))
        add_dead = false;

    if (dead_ap.compare("") != 0 && add_dead)
      to_observe.push_back(dead_ap);

    // Finally build the system.
    return std::make_shared<spot::kripkecube<spot::cspins_state,
                                             spot::cspins_iterator>>
      (iface, compress, to_observe, selfloopize, dead_ap, nb_threads,
       str);
  }

  kripke_ptr
  ltsmin_model::kripke(const atomic_prop_set* to_observe,
                       bdd_dict_ptr dict,
                       const formula dead, int compress) const
  {
    std::vector<int> bdd_indexes;
    try
      {
        bdd_indexes = convert_aps(to_observe, iface, dict, dead);
      }
    catch (const std::runtime_error&)
      {
        dict->unregister_all_my_variables(iface.get());
        throw;
      }
    auto res = SPOT_make_shared_enabled__(spins_kripke,
                                          iface, dict, dead, compress,
                                          bdd_indexes);
    // All atomic propositions have been registered to the bdd_dict
    // for iface, but we also need to add them to the automaton so
    // twa::ap() works.
    for (auto ap: *to_observe)
      res->register_ap(ap);
    if (dead.is(op::ap))
      res->register_ap(dead);
    return res;
  }

  ltsmin_model::~ltsmin_model()
  {
  }

  int ltsmin_model::state_size() const
  {
    return iface->get_state_size();
  }

  const char* ltsmin_model::state_variable_name(int var) const
  {
    return iface->get_state_variable_name(var);
  }

  int ltsmin_model::state_variable_type(int var) const
  {
    return iface->get_state_variable_type(var);
  }

  int ltsmin_model::type_count() const
  {
    return iface->get_type_count();
  }

  const char* ltsmin_model::type_name(int type) const
  {
    return iface->get_type_name(type);
  }

  int ltsmin_model::type_value_count(int type)
  {
    return iface->get_type_value_count(type);
  }

  const char* ltsmin_model::type_value_name(int type, int val)
  {
    return iface->get_type_value_name(type, val);
  }
}
