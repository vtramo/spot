// -*- coding: utf-8 -*-
// Copyright (C) 2021  Laboratoire de Recherche et Developpement de
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

#include <string>
#include <vector>
#include <tuple>
#include <memory>
#include <iostream>
#include <cassert>
#include <set>
#include <algorithm>


namespace spot
{
namespace minutils
{
  struct xi_t
  {
    size_t hash() const noexcept
    {
      size_t h = x;
      h <<= 32;
      h += i;
      return std::hash<size_t>()(h);
    }
    bool operator<(const xi_t& rhs) const
    {
      return std::tie(x, i) < std::tie(rhs.x, rhs.i);
    }
    bool operator==(const xi_t& rhs) const
    {
      return std::tie(x, i) == std::tie(rhs.x, rhs.i);
    }

    unsigned x, i;
  };
  struct hash_xi
  {
    size_t operator()(const xi_t& xi) const noexcept
      {
        return xi.hash();
      }
  };
  struct less_xi
  {
    bool operator()(const xi_t& lhs, const xi_t& rhs) const
    {
      return lhs < rhs;
    }
  };
  struct equal_to_xi
  {
    bool operator()(const xi_t& lhs, const xi_t& rhs) const
    {
      return lhs == rhs;
    }
  };

  struct iaj_t
  {
    size_t hash() const noexcept
    {
      size_t h = i;
      h <<= 21;
      h += a;
      h <<= 20;
      h += j;
      return std::hash<size_t>()(h);
    }
    bool operator==(const iaj_t& rhs) const
    {
      return std::tie(i, a, j) == std::tie(rhs.i, rhs.a, rhs.j);
    }
    bool operator<(const iaj_t& rhs) const
    {
      return std::tie(i, a, j) < std::tie(rhs.i, rhs.a, rhs.j);
    }

    unsigned i, a, j;
  };
  struct hash_iaj
  {
    size_t operator()(const iaj_t& iaj) const noexcept
      {
        return iaj.hash();
      }
  };
  struct less_iaj
  {
    bool operator()(const iaj_t& lhs, const iaj_t& rhs) const
    {
      return lhs < rhs;
    }
  };
  struct equal_to_iaj
  {
    bool operator()(const iaj_t& lhs, const iaj_t& rhs) const
    {
      return lhs == rhs;
    }
  };

  template<class T>
  class square_matrix: private std::vector<T>
  {
  private:
    size_t dim_;

  public:
    square_matrix()
        : std::vector<T>()
        , dim_(0)
    {}

    square_matrix(size_t dim)
        :  std::vector<T>(dim*dim)
        ,  dim_{dim}
    {}

    square_matrix(size_t dim, const T& t)
        :  std::vector<T>(dim*dim, t)
        ,  dim_{dim}
    {}

    using typename std::vector<T>::value_type;
    using typename std::vector<T>::size_type;
    using typename std::vector<T>::difference_type;
    using typename std::vector<T>::iterator;
    using typename std::vector<T>::const_iterator;

    inline size_t dim() const
    {
      return dim_;
    }
    // i: row number
    // j: column number
    // Stored in row major
    inline size_t idx_(size_t i, size_t j) const
    {
      return i * dim_ + j;
    }
    inline size_t idx(size_t i, size_t j) const
    {
      assert(i<dim_ && j<dim_);
      return idx_(i, j);
    }
    inline T operator()(size_t i, size_t j) const
    {
      return this->at(idx(i, j));
    }
    inline T& operator()(size_t i, size_t j)
    {
      return this->at(idx(i, j));
    }
    std::pair<const_iterator, const_iterator> get_cline(size_t i) const
    {
      assert(i < dim_);
      return {cbegin() + idx(i, 0), cbegin() + idx_(i+1, 0)};
    }
    std::pair<iterator, iterator> get_line(size_t i)
    {
      assert(i < dim_);
      return {begin() + idx(i, 0), begin() + idx_(i+1, 0)};
    }
    using std::vector<T>::begin;
    using std::vector<T>::cbegin;
    using std::vector<T>::end;
    using std::vector<T>::cend;

    void print() const
    {
      for (size_t i = 0; i < dim_; ++i)
      {
        for (size_t j = 0; j < dim_; ++j)
          std::cout << (int)(*this)(i, j) << ' ';
        std::cout << std::endl;
      }
    }
  };

  struct part_sol_t
  {
    std::set<unsigned> psol_s; //Keep two copies for access and look-up
    std::vector<unsigned> psol_v;
    std::vector<unsigned> incompvec;
  };

  template <class MAT>
  part_sol_t get_part_sol(const MAT& incompmat)
  {
    // Use the "most" incompatible states as partial sol
    unsigned n_states = incompmat.dim();
    std::vector<std::pair<unsigned, size_t>> incompvec(n_states);

    // square_matrix is row major!
    for (size_t ns = 0; ns < n_states; ++ns)
      {
        auto line_it = incompmat.get_cline(ns);
        incompvec[ns] = {ns,
                         std::count(line_it.first,
                                    line_it.second,
                                    true)};
      }

    // Sort in reverse order
    std::sort(incompvec.begin(), incompvec.end(),
              [](const auto& p1, const auto& p2)
                { return p1.second > p2.second; });

    part_sol_t part_sol_p;
    auto& part_sol = part_sol_p.psol_v;
    part_sol.reserve(n_states/2);
    // Add states that are incompatible with ALL states in part_sol
    for (auto& p : incompvec)
      {
        auto ns = p.first;
        if (std::all_of(part_sol.begin(), part_sol.end(),
                        [&](auto npart)
                          {
                            return incompmat(ns, npart);
                          }))
          part_sol.push_back(ns);
      }
    std::sort(part_sol.begin(), part_sol.end());
    //Also construct the set
    std::for_each(part_sol.begin(), part_sol.end(),
                  [&psols  = part_sol_p.psol_s](auto s)
                  {
                    psols.emplace_hint(psols.end(), s);
                  });

    // Also store the states in their compatibility order
    auto& part_sol_i = part_sol_p.incompvec;
    part_sol_i.reserve(n_states);
    std::for_each(incompvec.begin(), incompvec.end(),
                  [&part_sol_i](auto& p){ part_sol_i.push_back(p.first); });
    return part_sol_p;
  }
}
}
