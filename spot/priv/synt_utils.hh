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

#include <spot/misc/satsolver.hh>


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

#define USE_OPT_LIT
#ifdef USE_OPT_LIT
  struct lit_mapper
  {
    std::weak_ptr<satsolver> Sw_;
    unsigned n_classes_, n_env_, n_sigma_red_;
    std::shared_ptr<satsolver> S_;
    int next_var_;
    bool frozen_xi_, frozen_iaj_;
    std::unordered_map<xi_t, int, hash_xi, equal_to_xi> sxi_map_; //xi -> lit
    //iaj -> lit
    std::unordered_map<iaj_t, int, hash_iaj, equal_to_iaj> ziaj_map_;

    std::deque<int> all_clauses_;

    lit_mapper(std::weak_ptr<satsolver> S, unsigned n_classes,
               unsigned n_env, unsigned n_sigma_red)
      : Sw_{S}
      , n_classes_{n_classes}
      , n_env_{n_env}
      , n_sigma_red_{n_sigma_red}
      , S_{nullptr}
      , next_var_{1}
      , frozen_xi_{false}
      , frozen_iaj_{false}
    {
      assert(Sw_.lock()->get_nb_vars() == 0);
    }

    int sxi2lit(xi_t xi)
    {
      assert(xi.i < n_classes_);
      assert(xi.x < n_env_);
      auto [it, inserted] = sxi_map_.try_emplace(xi, next_var_);
      assert(!frozen_xi_ || !inserted);
      if (inserted)
        {
//          S_->adjust_nvars(next_var_); // Does this have to be consistent or set once?
          ++next_var_;
        }
      return it->second;
    }

    int sxi2lit(xi_t xi) const
    {
      return sxi_map_.at(xi);
    }

    int get_sxi(xi_t xi) const // Gets the literal or zero of not defined
    {
      auto it = sxi_map_.find(xi);
      if (it == sxi_map_.end())
        return 0;
      else
        return it->second;
    }

    void freeze_xi()
    {
      frozen_xi_ = true;
      S_ = nullptr;
    }
    void unfreeze_xi()
    {
      frozen_xi_ = false;
      S_ = Sw_.lock();
    }

    int ziaj2lit(iaj_t iaj)
    {
      auto [it, inserted] = ziaj_map_.try_emplace(iaj, next_var_);
      assert(!frozen_iaj_ || !inserted);
      if (inserted)
        {
//          S_->adjust_nvars(next_var_); // Does this have to be consistent or set once?
          ++next_var_;
        }
      return it->second;
    }

    int ziaj2lit(iaj_t iaj) const
    {
      assert(iaj.i < n_classes_);
      assert(iaj.a < n_sigma_red_);
      assert(iaj.j < n_classes_);
      return ziaj_map_.at(iaj);
    }
    int get_iaj(iaj_t iai) const // Gets the literal or zero of not defined
    {
      auto it = ziaj_map_.find(iai);
      if (it == ziaj_map_.end())
        return 0;
      else
        return it->second;
    }

    void freeze_iaj()
    {
      frozen_iaj_ = true;
      S_ = nullptr;
    }
    void unfreeze_iaj()
    {
      frozen_iaj_ = false;
      S_ = Sw_.lock();
    }

    void add(int v)
    {
      all_clauses_.push_back(v);
    }

    void add(std::initializer_list<int> l)
    {
      for (auto&& v : l)
        add(v);
    }

    void finalize()
    {
      S_ = Sw_.lock();
      S_->adjust_nvars(next_var_ - 1);
      S_->add(all_clauses_);
      S_ = nullptr;
      all_clauses_.clear();
    }

    std::ostream& print(std::ostream& os = std::cout)
    {
      {
        std::map<xi_t, int, less_xi> xi_tmp(sxi_map_.begin(),
                                                         sxi_map_.end());
        os << "x - i -> lit\n";
        for (auto &it : xi_tmp)
          os << it.first.x << " - " << it.first.i << " -> " << it.second
             << '\n';
      }
      {
        std::map<iaj_t, int, less_iaj> iaj_tmp(ziaj_map_.begin(), ziaj_map_.end());
        os << "i - a - j -> lit\n";
        for (auto &it : iaj_tmp)
            os << it.first.i << " - " << it.first.a << " - " << it.first.j
             << " -> " << it.second << '\n';
      }
      return os;
    }
  };
#else
  struct lit_mapper
  {
    unsigned n_classes_, n_env_, n_sigma_red_;

    lit_mapper(unsigned n_classes, unsigned n_env, unsigned n_sigma_red)
      : n_classes_{n_classes}
      , n_env_{n_env}
      , n_sigma_red_{n_sigma_red}
    {
    }

    int sxi2lit(xi_t xi) const
    {
      assert(xi.i < n_classes_);
      assert(xi.x < n_env_);
      return (int) 1 + xi.x*n_classes_ + xi.i;
    }
    int get_sxi(xi_t xi) const
    {
      return sxi2lit(xi);
    }

    int ziaj2lit(iaj_t iaj) const
    {
      assert(iaj.i < n_classes_);
      assert(iaj.a < n_sigma_red_);
      assert(iaj.j < n_classes_);
      return (int) 1 + n_classes_*n_env_ + iaj.i*n_sigma_red_*n_classes_
                   + iaj.a*n_classes_ + iaj.j;
    }
    int get_iaj(iaj_t iaj) const
    {
      return ziaj2lit(iaj);
    }

  };
#endif


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
