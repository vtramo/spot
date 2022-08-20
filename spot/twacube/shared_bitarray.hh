// -*- coding: utf-8 -*-
// Copyright (C) 2022 Laboratoire de Recherche et Developpement de
// l'Epita (LRDE).
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

#include <spot/misc/common.hh>
#include <spot/misc/fixpool.hh>
#include <spot/misc/hashfunc.hh>
#include <atomic>
#include <array>
#include <deque>
#include <cstring>
#include <climits>
#include <cstdint>
#include <limits>
#include <iostream>
#include <sstream>
#include <map>
#include <unordered_map>
#include <memory>

#ifdef ENABLE_PTHREAD
#include <mutex>
#endif

#ifdef ENABLE_PTHREAD
  #define DO_IF_PTHREAD(ARG) ARG
#else
  #define DO_IF_PTHREAD(ARG)
#endif

namespace spot
{
  namespace internal_bitarr
  {
    constexpr unsigned BITARR_SMALL = 1;

    template<unsigned N>
    class bitdata_varsize;
    template<unsigned N>
    class bitarr_varsize;

    template<unsigned N>
    class bitdata_handler_varsize;
    template<unsigned N>
    class bitarr_handler_varsize;

    using bit_data = std::uintptr_t;
    using bit_data_ptr = std::uintptr_t*;
    using c_bit_data_ptr = const std::uintptr_t*;

    constexpr size_t BIT_DATA_SIZE = sizeof(bit_data);
    constexpr size_t NB_BITS = BIT_DATA_SIZE * CHAR_BIT;

    constexpr bit_data one = 1;

    inline static std::pair<unsigned, unsigned>
    get_pos_(unsigned idx)
    {
      std::pair<unsigned, unsigned> res;
      res.first = idx/NB_BITS;
      res.second = idx - res.first*NB_BITS;
      return res;
    }

    /// \brief Hashes a bitarray made up of \a n
    /// data blocks
    SPOT_API inline size_t
    hash(c_bit_data_ptr ptr, unsigned n)
    {
      return fnv_hash(ptr, ptr+n);
    }

    /// \brief Comparison function for two bitarr
    /// of size \a n
    SPOT_API inline int
    cmp(c_bit_data_ptr lhs, c_bit_data_ptr rhs, unsigned n)
    {
      if (lhs == rhs)
        return 0;
      for (unsigned i = 0; i < n; ++i)
        {
          auto r = lhs[i] - rhs[i];
          if (r)
            return 1 - 2*(r > lhs[i]);
        }
      return 0;
    }

    /// \brief Copy a bitarr of size \a n from \a src to \a dst
    SPOT_API inline void
    cpy(c_bit_data_ptr src, bit_data_ptr dst, unsigned n)
    {
      std::memcpy(dst, src, n*BIT_DATA_SIZE);
    }

    /// \brief Test if the bit at position \a idx is set
    /// in a bitarr of size \a n
    SPOT_API inline bool
    is_set(c_bit_data_ptr ptr, unsigned idx)
    {
      auto [i, b] = get_pos_(idx);
      bool var = (*(ptr+i) >> b) & one;
      return var;
    }

    /// \brief Set the bit at position \a idx in a bitarr of
    /// size \a n
    SPOT_API inline void
    set_to(bit_data_ptr ptr, unsigned idx, bool val)
    {
      auto [i, b] = get_pos_(idx);
      if (val)
        ptr[i] |= (one << b);
      else
        ptr[i] &= ~(one << b);
    }

    /// \brief set all bits to false except the is_small bit
    SPOT_API inline void
    set_false(bit_data_ptr ptr, unsigned n, bool is_small)
    {
      std::memset(ptr, 0, n*BIT_DATA_SIZE);
      ptr[0] |= is_small*one;
    }

    /// \brief Set \a res to the bit-wise or of \a lhs and \a rhs
    /// all bitarr have to be of size \a n
    SPOT_API inline void
    set_union(c_bit_data_ptr lhs, c_bit_data_ptr rhs,
              bit_data_ptr res, unsigned n)
    {
      for (unsigned i = 0; i < n; ++i)
        res[i] = lhs[i] | rhs[i];
    }

    /// \brief Set \a res to the bit-wise and of \a lhs and \a rhs
    /// all bitarr have to be of size \a n
    SPOT_API inline void
    set_intersection(c_bit_data_ptr lhs, c_bit_data_ptr rhs,
                     bit_data_ptr res, unsigned n)
    {
      for (unsigned i = 0; i < n; ++i)
        res[i] = lhs[i] & rhs[i];
    }

    /// \brief Check if two bitarr intersect
    SPOT_API inline bool
    set_intersects(c_bit_data_ptr lhs, c_bit_data_ptr rhs, unsigned n)
    {
      if ((lhs[0]>>1) & (rhs[0]>>1))
        return true;
      else
        {
          for (unsigned i = 1; i < n; ++i)
            if (lhs[i] & rhs[i])
              return true;
        }
      return false;
    }

    /// \brief dump a bitset into a stream
    /// \note The first bit is the small bit
    SPOT_API void
    dump(std::ostream& os, c_bit_data_ptr ptr, unsigned n,
         unsigned stop = -1u, bool full=true);

    // End base algorithms

    // Start classes

    template<unsigned NSMALL>
    class shared_bitdata_varsize
    {
      typedef bitdata_handler_varsize<NSMALL> bitdata_handler_t;
      typedef bitdata_varsize<NSMALL> bitdata_t;

      friend bitdata_handler_t;
      friend bitdata_t;

    protected:

      bitdata_handler_t* bh_;
      std::atomic_uintptr_t use_;

      constexpr shared_bitdata_varsize(bitdata_handler_t* bh) noexcept
        : bh_{bh}
        , use_{0}
      {
      }
      ~shared_bitdata_varsize()
      {
        SPOT_ASSERT(use_ == 0 && "Destroying shared_bitdata which "
                                 "is still used");
      };

      uintptr_t incr() noexcept
      {
        std::cout << use_ << "incr " << this << '\n';
        SPOT_ASSERT(use_ < std::numeric_limits<uintptr_t>::max()
                    && "Use overflow of bitdata");
        return ++use_;
      }

      bool decr() noexcept
      {
        std::cout << ((unsigned) use_) << " decr " << this << '\n';
        SPOT_ASSERT((use_ > 0) && "Use count underflow");
        --use_;
        if (use_ == 0)
          {
            std::cout << "rel " << this << '\n';
            release();
            return false;
          }
        return true;
      }

      void release();

      bit_data_ptr get_data()
      {
        return reinterpret_cast<bit_data_ptr>(this + 1);
      }

      c_bit_data_ptr get_data() const
      {
        return reinterpret_cast<c_bit_data_ptr>(this + 1);
      }




    };

    template<unsigned NSMALL>
    class SPOT_API bitdata_varsize{

    protected:

      typedef shared_bitdata_varsize<NSMALL> shared_bitdata_t;
      typedef bitdata_handler_varsize<NSMALL> bitdata_handler_t;

      friend shared_bitdata_t;
      friend bitdata_handler_t;

      union arr_union{
        std::array<bit_data, NSMALL> s_;
        shared_bitdata_t* l_;
      } u_;


      /// \brief Always allocates a small bitdata array
      /// with all bits set to false
      explicit bitdata_varsize();
      /// \brief Create a small bitdata_varsize from
      /// bit_data_ptr
      explicit bitdata_varsize(bit_data_ptr ptr);
      // Large bitarr from shared data ptr
      explicit bitdata_varsize(shared_bitdata_t* s_data);

      /// \brief Mutator for data
      bit_data_ptr get_data() noexcept
      {
        if (is_small())
          return u_.s_.data();
        else
          return u_.l_->get_data();
      }

      /// \brief Access to handler
      bitdata_handler_t*
      get_handler() const
      {
        SPOT_ASSERT(!is_small());
        return u_.l_->bh_;
      }

      /// \brief Conditional ref count increase
      /// depending on small property
      void c_incr_()
      {
        if (!is_small() && u_.l_)
          u_.l_->incr();
      }

      /// \brief Conditional ref count decrease
      /// depending on small property
      void c_decr_()
      {
        if (!is_small() && u_.l_)
          if (!u_.l_->decr())
            u_.l_ = nullptr;
      }

    public:

      /// \brief copy constructor, trivial if small
      bitdata_varsize(const bitdata_varsize& other)
      {
        u_ = other.u_;
        c_incr_();
      }

      /// \brief move constructor, trivial if small
      bitdata_varsize(bitdata_varsize&& other)
      {
        u_ = other.u_;
        other.u_.l_ = nullptr; // Other becomes large and null
      }

      /// \brief Assignment
      bitdata_varsize& operator=(const bitdata_varsize& other)
      {
        std::cout << "copyassign bitdata" << '\n';
        if (this == &other
            || (!is_small() && (u_.l_ == other.u_.l_)))
          return *this;

        c_decr_();
        u_ = other.u_;
        c_incr_();
        return *this;
      }

      /// \brief Move assignement
      bitdata_varsize& operator=(bitdata_varsize&& other)
      {
        SPOT_ASSERT(this != &other);
        // Unuse this.
        // If usage drops to zero -> destroy
        c_decr_();
        // Take the other
        u_ = other.u_;
        other.u_.l_ = nullptr;
        return *this;
      }

      /// \brief No need for virtual destructor,
      /// we will not use inheritance in a polymorphic way
      ~bitdata_varsize()
      {
        c_decr_();
        u_.l_ = nullptr;
      }

      /// \brief Whether or not the underlying bitarr is small
      bool is_small() const noexcept{
        return *reinterpret_cast<c_bit_data_ptr>(this) & one;
      }

      /// \brief Use count for this bitarr.
      /// \note Zero inndicates small bitarr
      std::uintptr_t
      use_count() const
      {
        if (is_small())
          return 0;
        else
          {
            SPOT_ASSERT(u_.l_);
            return u_.l_->use_;
          }
      }

      /// \brief How many data parts are used to represent the bitarr
      unsigned n_parts() const
      {
        if (is_small())
          return NSMALL;
        else
          return u_.l_->bh_->n_parts();
      }

      /// \brief Accessor for data
      c_bit_data_ptr get_data() const noexcept
      {
        if (is_small())
          return u_.s_.data();
        else
          return u_.l_->get_data();
      }

      /// \brief Dump into a stream, mainly for debug purposes
      void dump(std::ostream& os,
                unsigned stop = -1u, bool full = true) const
      {
        if (full)
          {
            if (is_small())
              os << nullptr << ' ' << nullptr << " 0 ";
            else
              os << u_.l_ << ' ' << u_.l_->bh_ << ' ' << u_.l_->use_ << ' ';
          }
        internal_bitarr::dump(os, get_data(), n_parts(), stop, full);
        os << '\n';
      }

    }; // bitdata_varsize

    template<unsigned NSMALL>
    class SPOT_API bitdata_handler_varsize
    {
    public:
      typedef bitdata_varsize<NSMALL> bitdata_t;
      typedef shared_bitdata_varsize<NSMALL> shared_bitdata_t;

      friend bitdata_t;
      friend shared_bitdata_t;
    private:
      /// \brief Total bit size
      const size_t size_;

      /// \brief Total number of bit_data needed to represent one bitarr
      const size_t n_;

      /// \brief Whether or not the associated bitarr are small
      const bool is_small_;

      typedef fixed_size_pool<pool_type::Unsafe> pool_type_;
      /// \brief allocator for large bitarr, unused if small
      std::unique_ptr<pool_type_> mem_pool_;

      typedef std::unordered_multimap<size_t, shared_bitdata_t*> map_type_;
      /// \brief Map to share large bitarr
      std::unique_ptr<map_type_> map_;

      // We want to avoid temporary allocations for operations.
      // Therefore a special member exists.
      // In the case of multithreading, several such temporaries are
      // created and one may not use more threads than indicated beforehand

      /// \brief Temporary bitarr
      bit_data_ptr temp_;

#ifdef ENABLE_PTHREAD
      /// \brief A lock for the pool
      std::mutex mem_lock_;

      /// \brief Multiple temporaries when threaded
      std::deque<std::pair<std::atomic_flag, bit_data_ptr>> temps_;

      /// \brief A lock for the hash map
      std::mutex map_lock_;
#endif // ENABLE_PTHREAD

    public:

      bitdata_handler_varsize() = delete;

      /// \brief Build a bitdata allocator for at least \a nbits
      /// per bitdata and temporary objects for at most \a nthreads
      /// threads.
      /// \note nthreads is ignored if not configured
      /// with --enable-pthreads
      bitdata_handler_varsize(size_t nbits, size_t nthreads);

      virtual ~bitdata_handler_varsize();

      /// \brief Return the number of bits
      /// \note The bits are enumerated from [1 ... size()]
      size_t size() const
      {
        return size_;
      }

      /// \brief Whether or not the cubes are small
      bool is_small() const noexcept
      {
        return is_small_;
      }

      /// \brief Return the number of data parts per bitarray
      unsigned n_parts() const noexcept
      {
        return n_;
      }

      bool is_set(const bitdata_t& b, unsigned idx)
      {
        check_bounds_(idx);
        return internal_bitarr::is_set(b.get_data(), idx);
      }

      int cmp(const bitdata_t& lhs, const bitdata_t& rhs)
      {
        return internal_bitarr::cmp(lhs.get_data(), rhs.get_data(), n_parts());
      }

      void dump(std::ostream& os, const bitdata_t& b, bool full)
      {
        b.dump(os, full ? -1u : size(), full);
      }

    private:

#ifdef ENABLE_PTHREAD
      std::lock_guard<std::mutex>
      lock_mem_()
      {
        return std::lock_guard(mem_lock_);
      }
#endif

#ifdef ENABLE_PTHREAD
      std::lock_guard<std::mutex>
      lock_map_()
      {
        return std::lock_guard(map_lock_);
      }
#endif
      /// \brief Implementation of the generator functions
      template<class GEN, class SET>
      void gen_like_(GEN& gen,
                     SET set,
                     bit_data_ptr ptr)
      {
        for (; !gen.done(); gen.next())
          {
            const auto& [idx, val] = gen.get();
            set(ptr, idx, val);
          }
      }

      /// \brief Set all bits to false, account for small index
      void set_false_(bit_data_ptr ptr)
      {
        set_false(ptr, n_parts(), is_small());
      }

    protected:

      /// \brief Assert bounds
      void check_bounds_(unsigned idx)
      {
        SPOT_ASSERT(0 < idx && idx <= size()
                    && "Index out of bounds");
      }

      /// \brief provides a bit_data_ptr with appropriate size
      /// \note this is threadsafe if "enough" threads have been given
      /// at construction, throws an error otherwise
      bit_data_ptr get_temp_()
      {
#ifdef ENABLE_PTHREAD
        for (auto& [flag, ptr] : temps_)
          if (!flag.test_and_set()) // todo check memory order
            {
              return ptr;
            }
        throw std::runtime_error("More Threads active than expected!");
#else
        return temp_;
#endif
      }

      /// \brief Release a temporary cube so that another thread can use it
      void rel_temp_(bit_data_ptr ptr)
      {
        SPOT_ASSERT(ptr && "Temporary ptr can not be null!");
        // In no threading case, nothing to do
#ifdef ENABLE_PTHREAD
        auto idx = std::distance(temp_, ptr)/n_;
        SPOT_ASSERT(temps_.at(idx).second == ptr);
        temps_.at(idx).first.clear();
#endif
      }

      void release_(shared_bitdata_t* ptr)
      {
        // If we got here the very last usage was deleted
        // The only way for use_ to be != 0 is
        // if a new cube with the same "value" has been constructed
        // in the mean time
        // No copy constructor can be called in the inbetween time
        auto h = internal_bitarr::hash(ptr->get_data(), n_parts());

        DO_IF_PTHREAD(auto g_h = lock_map_();)
        // Delete from map if still zero
        if (ptr->use_ != 0)
          return;
        std::cout << "Release " << ptr  << ' ' << h << '\n';
        auto [it_b, it_e] = map_->equal_range(h);
        for (; it_b != it_e; ++it_b)
          {
            if (ptr == it_b->second)
              {
                auto ptr = it_b->second;
                map_->erase(it_b);
                dealloc_(ptr);
                return;
              }
          }
        throw std::runtime_error("Deleting a ptr not allocated by "
                                "this cubeset.");
      }

      shared_bitdata_t* alloc_()
      {
        DO_IF_PTHREAD(auto g_m = lock_mem_();)
        void* ptr = mem_pool_->allocate();
        std::cout << "alloc " << ptr << '\n';
        return new (ptr) shared_bitdata_t(this);
      }

      void dealloc_(shared_bitdata_t* ptr)
      {
        ptr->~shared_bitdata_t();
        DO_IF_PTHREAD(auto g_m = lock_mem_();)
        mem_pool_->deallocate((void*) ptr);
      }

      /// \brief takes a bit_data_ptr and searches/inserts it into the map
      /// Only needs to be called for large bit_arr
      /// trivial for small
      /// Constructs the given type from it
      /// using the optional arguments
      template<class T, class... ARGS>
      T lock_as_(bit_data_ptr ptr,
                 ARGS... args)
      {
        if (is_small())
          {
            SPOT_ASSERT(!(ptr[0] & one)
                        && "Does not point to small");
            return T(ptr, std::forward<ARGS>(args)...);
          }

        auto h = hash(ptr, n_parts());
        DO_IF_PTHREAD(auto g_h = lock_map_();)
        auto [it_b, it_e] = map_->equal_range(h);
        for (; it_b != it_e; ++it_b)
          {
            auto& value = it_b->second;
            if (internal_bitarr::cmp(ptr, value->get_data(), n_parts()) == 0)
              {
                // Found it
                rel_temp_(ptr);
                std::cout << "Reuse " << value << ' ' << h << '\n';
                return T(value, std::forward<ARGS>(args)...);
              }
          }
        // We could not find one -> create it
        shared_bitdata_t* sb = alloc_();
        cpy(ptr, sb->get_data(), n_parts());
        map_->emplace(h, sb);
        rel_temp_(ptr);
        std::cout << "New " << sb << ' ' << h << '\n';
        return T(sb, std::forward<ARGS>(args)...);
      }

      template<class T, class GEN, class SET, class... ARGS>
      T generate_as_(GEN gen, SET set, ARGS... args)
      {
        if (is_small())
          {
            auto res = T(std::forward<ARGS>(args)...);
            gen_like_(gen, set,
                      res.get_data());
            return res;
          }
        else
          {
            auto ptr = get_temp_();
            set_false_(ptr);
            gen_like_(gen, set, ptr);
            return lock_as_<T>(ptr, std::forward<ARGS>(args)...);
          }
      }

      template<class T, class BINOP, class... ARGS>
      T binop_as_(BINOP binop, const T& lhs,
                  const T& rhs, ARGS... args)
      {
        if (is_small())
          {
            auto res = T(std::forward<ARGS>(args)...);
            binop(lhs.get_data(), rhs.get_data(),
                  res.get_data(), n_parts());
            return res;
          }
        else
          {
            auto ptr = get_temp_();
            set_false_(ptr);
            binop(lhs.get_data(), rhs.get_data(),
                  ptr, n_parts());
            return lock_as_<T>(ptr, std::forward<ARGS>(args)...);
          }
      }

    }; // bitdata_handler_varsize

    template<unsigned NSMALL>
    class SPOT_API bitarr_varsize
      : public bitdata_varsize<NSMALL>
    {
    public:
      //typedef typename bitdata_varsize<NSMALL>::bitdata_t bitdata_t;
      typedef typename bitdata_varsize<NSMALL>::shared_bitdata_t
              shared_bitdata_t;
      typedef bitdata_handler_varsize<NSMALL> bitdata_handler_t;
      typedef bitarr_handler_varsize<NSMALL> bitarr_handler_t;

      friend shared_bitdata_t;
      friend bitdata_handler_t;
      friend bitarr_handler_t;

    protected:
      /// \brief Always allocates a small bitarr
      /// with all bits set to false
      explicit bitarr_varsize() = default;
      explicit bitarr_varsize(bit_data_ptr ptr)
        : bitdata_varsize<NSMALL>(ptr)
      {
      }
      // Large bitarr from shared data ptr
      explicit bitarr_varsize(shared_bitdata_t* s_data)
        : bitdata_varsize<NSMALL>(s_data)
      {
      }

    public:

      bitarr_varsize(const bitarr_varsize& other) = default;
      bitarr_varsize(bitarr_varsize&& other) = default;
      bitarr_varsize& operator=(const bitarr_varsize& other) = default;
      //{
      //  bitdata_varsize<NSMALL>::operator=(other);
      //  return *this;
      //}
      bitarr_varsize& operator=(bitarr_varsize&& other) = default;
      //{
      //  bitdata_varsize<NSMALL>::operator=(std::move(other));
      //  return *this;
      //}

      // Wrappers to interface
      bool is_set(unsigned idx) const noexcept;
      bool set_intersects(const bitarr_varsize& rhs) const;
      int cmp(const bitarr_varsize& rhs) const;
      bitarr_varsize set_union(const bitarr_varsize& rhs) const;
      bitarr_varsize operator|| (const bitarr_varsize& rhs) const;
      bitarr_varsize& operator|= (const bitarr_varsize& rhs);
      bitarr_varsize set_intersection(const bitarr_varsize& rhs) const;
      bitarr_varsize operator&& (const bitarr_varsize& rhs) const;
      bitarr_varsize& operator&= (const bitarr_varsize& rhs);
    };



    template<unsigned NSMALL>
    class SPOT_API bitarr_handler_varsize
      : public bitdata_handler_varsize<NSMALL>
    {
    public:
      typedef bitdata_handler_varsize<NSMALL> bitdata_handler_t;

      typedef bitarr_varsize<NSMALL> bitarr_t;
      typedef shared_bitdata_varsize<NSMALL> shared_bitarr_t;

      friend bitarr_t;
      friend shared_bitarr_t;

    public:

      bitarr_handler_varsize() = delete;

      /// \brief Build a bitarr allocator for at least \a nbits
      /// per bitarr and temporary objects for at most \a nthreads
      /// threads.
      /// \note nthreads is ignored if not configured
      /// with --enable-pthreads
      bitarr_handler_varsize(size_t nbits, size_t nthreads)
        : bitdata_handler_varsize<NSMALL>(nbits, nthreads)
      {
      }

      ~bitarr_handler_varsize() = default;

      /// \brief Generate a bitarr from a generate object \a gen
      /// This object need to provide a member function void next()
      /// and unsigned get() and bool done();
      /// Must be copy constructible
      /// All indexes returned will be set to true, all other bits are false
      /// It will be used as for (; !gen.done(); gen.next());
      /// unsigned idx = gen.get();
      // todo make lock_ optional to chain construction/operations?
      template<class GEN>
      bitarr_t generate(GEN gen)
      {
        return bitdata_handler_t::template generate_as_<bitarr_t>(
            gen, internal_bitarr::set_to);
      }

      bool set_intersects(const bitarr_t& lhs, const bitarr_t& rhs)
      {
        return set_intersects(lhs.get_data(), rhs.get_data(), this->n_parts());
      }

      bitarr_t set_intersection(const bitarr_t& lhs, const bitarr_t& rhs)
      {
        return this->template binop_as_<bitarr_t>(
            internal_bitarr::set_intersection, lhs, rhs);
      }

      bitarr_t set_union(const bitarr_t& lhs, const bitarr_t& rhs)
      {
        return this->template binop_as_<bitarr_t>(
            internal_bitarr::set_union, lhs, rhs);
      }

      void dump(std::ostream& os, const bitarr_t& b, bool full)
      {
        b.dump(os, full ? -1u : this->size(), full);
      }

    }; // bitarr_handler_varsize

  } // Internal

  typedef internal_bitarr::bitarr_handler_varsize<internal_bitarr::BITARR_SMALL>
          bitarr_handler;
  typedef typename bitarr_handler::bitarr_t bitarr;

  typedef std::shared_ptr<bitarr_handler> bitarr_handler_ptr;
  typedef std::shared_ptr<const bitarr_handler> const_bitarr_handler_ptr;

}


// Out of line definitions
namespace spot
{
  namespace internal_bitarr
  {
    // share_bitarr dependent impl
    template<unsigned NSMALL>
    inline void shared_bitdata_varsize<NSMALL>::release()
    {
      bh_->release_(this);
    }

    // bitarr dependent impl
    template<unsigned NSMALL>
    inline bitdata_varsize<NSMALL>::bitdata_varsize()
    {
      set_false(u_.s_.data(), NSMALL, true);
      assert(is_small());
    }

    template<unsigned NSMALL>
    inline bitdata_varsize<NSMALL>::bitdata_varsize(bit_data_ptr ptr)
    {
      cpy(ptr, u_.s_.data(), NSMALL);
      SPOT_ASSERT(is_small());
    }

    template<unsigned NSMALL>
    inline bitdata_varsize<NSMALL>::bitdata_varsize(shared_bitdata_t* s_data)
    {
      SPOT_ASSERT(s_data && "bitarr can not be created from null data ptr");
      u_.l_ = s_data;
      u_.l_->incr();
    }

    // bitarr_handler impl
    template<unsigned NSMALL>
    bitdata_handler_varsize<NSMALL>::bitdata_handler_varsize(size_t nbits,
                                                             size_t nthreads)
      : size_(nbits)
      , n_((nbits+1)/NB_BITS + (((nbits+1)%NB_BITS) != 0))
      , is_small_{n_ <= NSMALL}
      , mem_pool_(nullptr)
      , map_(nullptr)
      , temp_{new bit_data[nthreads*n_]}
    {
      // Too long for init-list
      if (n_ > NSMALL)
        {
          mem_pool_ = std::make_unique<pool_type_>(
            sizeof(shared_bitdata_varsize<NSMALL>) + n_*BIT_DATA_SIZE);
          map_ = std::make_unique<map_type_>(1000);
        }
      // There is only one dynamic alloc stored in temp_
      // if there are multiple needed in the threaded case
      // they point to somewhere within this alloc
      SPOT_ASSERT(nthreads > 0);
#ifdef ENABLE_PTHREAD
      auto ptr = temp_;
      for (unsigned i = 0; i < nthreads; ++i)
        {
          temps_.emplace_back();
          temps_.back().second = ptr;
          ptr += n_;
        }
#endif // ENABLE_PTHREAD
    }

    template<unsigned NSMALL>
    bitdata_handler_varsize<NSMALL>::~bitdata_handler_varsize()
    {
      delete[] temp_;
    }

    template<unsigned NSMALL>
    inline bool bitarr_varsize<NSMALL>::is_set(unsigned idx) const noexcept
    {
      if (this->is_small())
        {
          SPOT_ASSERT(0 < idx && idx < NSMALL*NB_BITS);
          return internal_bitarr::is_set(this->get_data(), idx);
        }
      else
        {
          SPOT_ASSERT(this->u_.l_);
          return this->get_handler()->is_set(*this, idx);
        }
    }

    template<unsigned NSMALL>
    inline bool
    bitarr_varsize<NSMALL>::set_intersects(const bitarr_varsize<NSMALL>& rhs)
        const
    {
      return set_intersects(this->get_data(), rhs.get_data(),
                            this->n_parts());
    }

    template<unsigned NSMALL>
    inline int
    bitarr_varsize<NSMALL>::cmp(const bitarr_varsize<NSMALL>& rhs) const
    {
      return cmp(this->get_data(), rhs.get_data(), this->n_parts());
    }

    template<unsigned NSMALL>
    inline bitarr_varsize<NSMALL>
    bitarr_varsize<NSMALL>::set_intersection(const bitarr_varsize<NSMALL>& rhs)
        const
    {
        if (this->is_small())
          {
            bitarr_varsize<NSMALL> res; //small array is "free"
            internal_bitarr::set_intersection(this->get_data(), rhs.get_data(),
                                              res.get_data(), NSMALL);
            return res;
          }
        else
          {
            auto dh = static_cast<bitarr_handler_t*>(this->get_handler());
            return dh->set_intersection(*this, rhs);
          }
    }

    template<unsigned NSMALL>
    inline bitarr_varsize<NSMALL>
    bitarr_varsize<NSMALL>::operator&&(const bitarr_varsize<NSMALL>& rhs)
        const
    {
      return this->set_intersection(rhs);
    }

    template<unsigned NSMALL>
    inline bitarr_varsize<NSMALL>&
    bitarr_varsize<NSMALL>::operator&=(const bitarr_varsize<NSMALL>& rhs)
    {
      *this = this->set_intersection(rhs);
      return *this;
    }

    template<unsigned NSMALL>
    inline bitarr_varsize<NSMALL>
    bitarr_varsize<NSMALL>::set_union(const bitarr_varsize<NSMALL>& rhs)
        const
    {
      SPOT_ASSERT(this->is_small() == rhs.is_small());
      if (this->is_small())
        {
          bitarr_varsize<NSMALL> res; //small array re "free"
          internal_bitarr::set_union(this->get_data(), rhs.get_data(),
                                     res.get_data(), NSMALL);
          return res;
        }
      else
        {

            auto dh = static_cast<bitarr_handler_t*>(this->get_handler());
            return dh->set_union(*this, rhs);
        }
    }

    template<unsigned NSMALL>
    inline bitarr_varsize<NSMALL>
    bitarr_varsize<NSMALL>::operator||(const bitarr_varsize<NSMALL>& rhs)
        const
    {
      return this->set_union(rhs);
    }

    template<unsigned NSMALL>
    inline bitarr_varsize<NSMALL>&
    bitarr_varsize<NSMALL>::operator|=(const bitarr_varsize<NSMALL>& rhs)
    {
      *this = this->set_union(rhs);
      return *this;
    }

  } // internal_bitarr

} // SPOT