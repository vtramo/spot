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

#include <spot/twacube/shared_bitarray.hh>
#include <spot/misc/trival.hh>

namespace spot
{
  namespace internal_cube
  {
    // Must be a multiple of 2
    constexpr unsigned CUBE_SMALL = 2;

    template<unsigned N>
    class cube_varsize;

    template<unsigned N>
    class cube_handler_varsize;

    using cube_data = internal_bitarr::bit_data;
    using cube_data_ptr = bit_data_ptr;
    using c_cube_data_ptr = c_bit_data_ptr;

    constexpr cube_data one = 1;

    /// \brief Check if a cube is equivalent to false
    SPOT_API inline bool
    is_false(c_cube_data_ptr ptr)
    {
      return ptr[1] & one;
    }

    /// \brief Returns the value of the proposition with
    /// index \a idx. trival::maybe is interpreted as "do not care"
    SPOT_API inline trival
    val_of(c_cube_data_ptr ptr, unsigned idx)
    {
      auto [i, b] = get_pos_(idx);
      bool t_val = (ptr[i] >> b) & one;
      bool f_val = (ptr[i+1] >> b) & one;
      SPOT_ASSERT(!((t_val & f_val) || is_false(ptr)) && "Cube is false");
      if (t_val)
        return trival(true);
      else if (f_val)
        return trival(false);
      else
        return trival(); // Maybe serves as do not care
    }

    /// \brief Sets the value of the proposition
    /// with index \a idx to \a val with maybe interpreted
    /// as do not care
    SPOT_API inline bool
    set_to(cube_data_ptr ptr, unsigned idx, trival val)
    {
      auto [i, b] = get_pos_(idx);
      if (val.is_known)
        {
          bool off = val.is_true();
          ptr[i + !off] |= (one << b);
          ptr[i + off] &= ~(one << b);
        }
      else
        {
          // Unset both
          ptr[i] &= ~(one << b);
          ptr[i + 1] &= ~(one << b);
        }
    }

    /// \brief Set the cube to logical true, that is all bits
    /// are set to false, except maybe for the small bit
    /// \note The parameter \a n corresponds to the number
    /// of data parts needed to represent the true
    /// AND false values
    SPOT_API inline void
    set_true(cube_data_ptr ptr, unsigned n, bool is_small)
    {
      internal_bitarr::set_false(ptr, n, is_small);
    }

    /// \brief Set the cube to logical false, that is all bits
    /// are set to false, except maybe for the small bit
    /// and the false bit
    /// \note The parameter \a n corresponds to the number
    /// of data parts needed to represent the true
    /// AND false values
    SPOT_API inline void
    set_false(cube_data_ptr ptr, unsigned n, bool is_small)
    {
      set_true(ptr, n, is_small);
      ptr[1] = one;
    }

    // todo union and difference is tricky,
    // as the result of such operations is not a cube

    /// \brief Computes the intersection of two cubes
    /// \returns false iff the result is false.
    /// \a n is the number of data parts needed to represent the true
    /// AND false values
    SPOT_API inline bool
    cube_intersection(c_cube_data_ptr lhs, c_cube_data_ptr rhs,
                      cube_data_ptr res, unsigned n)
    {
      if (is_false(lhs) | is_false(rhs))
        {
          set_false(res);
          return false;
        }

      for (unsigned i = 0; i < n; i += 2)
        {
          res[i] = lhs[i] | rhs[i];
          res[i + 1] = lhs[i + 1] | rhs[i + 1];
          if (res[i] & res[i+1])
            {
              set_false(res);
              return false;
            }
        }
      return true;
    }

    /// \brief Computes if the intersection of two cubes is non-empty
    SPOT_API inline bool
    cube_intersects(c_cube_data_ptr lhs, c_cube_data_ptr rhs,
                    unsigned n)
    {
      if (is_false(lhs) | is_false(rhs))
        return false;

      for (unsigned i = 0; i < n; i += 2)
        if ((lhs[i] | rhs[i]) & (lhs[i+1] | rhs[i+1]))
          return false;
      return true;
    }

    /// \brief dump a cube into a stream
    /// \note The first bit of the true variables is the small bit
    /// The first bit of the false variables is the false bit
    SPOT_API void
    dump(std::ostream& os, c_bit_data_ptr ptr, unsigned n,
         unsigned stop = -1u, bool full=true);


    // Done base algorithms

    // Start classes

    template<unsigned N>
    class cube_varsize;

    template<unsigned N>
    class cube_handler_varsize;


    template<unsigned NSMALL>
    class SPOT_API cube_varsize
      : protected internal_bitarr::bitarr_varsize<NSMALL>
    {
      static_assert((NSMALL >= 2) && (NSMALL%2 == 0));

    protected:
      typedef internal_bitarr::shared_bitarr_varsize<NSMALL>
              shared_cube_t;
      typedef cube_handler_varsize<NSMALL> cube_handler_t;

      friend cube_handler_t;

      /// \brief Always allocates a small cube
      /// with logical value true
      explicit cube_varsize()
        : internal_bitarr::bitarr_varsize()
      {
      }
      // Large bitarr from shared data ptr
      explicit cube_varsize(shared_cube_t* c_data)
        : internal_bitarr::bitarr_varsize<NSMALL>(c_data)
      {
      }
      // Conversion constructor to facilitate creation
      explicit
      cube_varsize(internal_bitarr::bitarr_varsize<NSMALL>&& other)
        : internal_bitarr::bitarr_varsize<NSMALL>(std::forward(other))
      {
      }

    public:

      /// \brief copy constructor, trivial if small
      cube_varsize(const cube_varsize& other) = default;

      /// \brief move constructor, trivial if small
      cube_varsize(cube_varsize&& other) = default;

      /// \brief Assignment
      cube_varsize& operator=(const cube_varsize& other) = default;

      /// \brief Move assignement
      cube_varsize& operator=(cube_varsize&& other) = default;

      /// \brief No need for virtual destructor,
      /// we will not use inheritance in a polymorphic way
      ~cube_varsize() = default;

      /// \brief Whether or not the cube is equivalent to false
      bool is_false() const noexcept{
        return *reinterpret_cast<c_cube_data_ptr>(this) & one;
      }

      // Wrappers to interface
      trival val_of(unsigned idx) const noexcept;
      bool intersects(const cube_varsize& rhs) const;
      int cmp(const cube_varsize& rhs) const;
      cube_varsize intersection(const cube_varsize& rhs) const;
      cube_varsize operator&& (const cube_varsize& rhs) const;
      cube_varsize& operator&= (const cube_varsize& rhs);
      cube_varsize neg() const;
      cube_varsize operator!() const;
      operator bool() const;

      // todo: generator for "set_minus"
    };

    template<unsigned NSMALL>
    class SPOT_API cube_handler_varsize
      : protected internal_bitarr::bitarr_handler_varsize<NSMALL>
    {
    public:
      typedef internal_bitarr::bitarr_handler_varsize<NSMALL>
              bitarr_handler_t;

      typedef cube_varsize<NSMALL> cube_t;
      typedef shared_bitarr_varsize<NSMALL> shared_cube_t;

      friend cube_t;
      friend shared_cube_t;

    private:
      /// \brief number of propositions
      /// \note the number of bits will be rounded up
      const size_t n_aps_;

    public:

      cube_handler_varsize() = delete;

      /// \brief Build a cube allocator for at least \a naps
      /// atomic propositions and temporary objects for at most
      /// \a nthreads threads.
      /// \note nthreads is ignored if not configured
      /// with --enable-pthreads
      cube_handler_varsize(size_t naps, size_t nthreads);

      ~cube_handler_varsize() = default;

      /// \brief Number of propositions,
      /// enumerated from [1 ... naps()]

      size_t n_aps() const
      {
        return n_aps_;
      }

      /// \brief Generate a cube from a generate object \a gen
      /// This object need to provide a member function void next()
      /// and std::pair<unsigned, trival> get() and bool done();
      /// Must be copy constructible
      /// All indexes returned will be set to the value val
      /// It will be used as for (; !gen.done(); gen.next());
      /// auto [idx, val] = gen.get();
      // todo make lock_ optional to chain construction/operations?
      template<class GEN>
      cube_t generate(GEN gen)
      {
        if (is_small())
          {
            cube_t res;
            gen_(gen, res.get_data());
            return res;
          }
        else
          {
            auto ptr = get_temp_();
            set_true_(ptr);
            gen_(gen, ptr);
            auto res_ba = lock_(ptr);
            // lock_ returns a unique bitarray
            return cube_t(res_ba);
          }
      }

      trival val_of(const cube_t& c, unsigned idx) const
      {
        SPOT_ASSERT(!c.is_false());
        check_bounds_(idx);
        return internal_cube::val_of(c.get_data(), idx);
      }

      int cmp(const cube_t& lhs, const cube_t& rhs)
      {
        return bitarr_handler_t(lhs, rhs);
      }

      bool intersects(const cube_t& lhs, const cube_t& rhs)
      {
        return internal_cube::cube_intersects(lhs.get_data(), rhs.get_data(),
                                              n_parts());
      }

      cube_t intersection(const cube_t& lhs, const cube_t& rhs)
      {
        return binop_(internal_cube::cube_intersection, lhs, rhs);
      }

    private:

      template<class BINOP>
      cube_t binop_(BINOP binop,
                    const cube_t& lhs, const cube_t& rhs)
      {
        if (is_small())
          {
            cube_t res;
            binop(lhs.get_data(), rhs.get_data(),
                  res.get_data(), n_parts());
            return res;
          }
        else
          {
            cube_data_ptr ptr = get_temp_();
            set_true_(ptr);
            binop(lhs.get_data(), rhs.get_data(),
                  ptr, n_parts());
            return cube_t(lock_(ptr));
          }
      }

    } // cube_handler_varsize



    // Implementations cube_varsize
    template<unsigned NSMALL>
    inline trival
    cube_varsize<NSMALL>::val_of(unsigned idx) const
    {
      if (is_small())
        {

        }
      else
        {
          SPOT_ASSERT(u_.l_);
          u_.l_->
        }
    }




  } // internal
} // spot