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

#include <spot/priv/synt_utils_struct.hh>
#include <spot/misc/satsolver.hh>


namespace spot
{
namespace minutils
{
#define USE_OPT_LIT
#ifdef USE_OPT_LIT
  struct lit_mapper
  {
    std::weak_ptr<satsolver> Sw_;
    unsigned n_classes_, n_env_, n_sigma_red_;
    std::shared_ptr<satsolver> S_;
    int next_var_;
    bool frozen_xi_, frozen_iaj_, frozen_si_;
    std::unordered_map<xi_t, int, hash_xi, equal_to_xi> sxi_map_;//xi -> lit
    std::unordered_map<iaj_t, int, hash_iaj, equal_to_iaj> ziaj_map_;//iaj -> lit
    std::vector<int> si_map_;//class -> lit, only for multi version

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
      , frozen_si_{false}
      , si_map_(n_classes, 0)
    {
      assert(Sw_.lock()->get_nb_vars() == 0);
    }

    int si2lit(unsigned si)
    {
      assert(si < n_classes_);
      assert(!frozen_si_ || (si_map_[si] != 0));
      if (si_map_[si] == 0)
        si_map_[si] = next_var_++;
      return si_map_[si];
    }

    int si2lit(unsigned si) const
    {
      assert(si_map_[si]);
      return si_map_[si];
    }

    int get_si(unsigned si)
    {
      return si_map_[si];
    }

    void freeze_si()
    {
      frozen_si_ = true;
      S_ = nullptr;
    }
    void unfreeze_si()
    {
      frozen_si_ = false;
      S_ = Sw_.lock();
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
      for(auto&& v : l)
        add(v);
    }

    template<class C>
    void add(const C& c)
    {
      all_clauses_.insert(all_clauses_.end(), c.begin(), c.end());
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
             << "\n";
      }
      {
        std::map<iaj_t, int, less_iaj> iaj_tmp(ziaj_map_.begin(), ziaj_map_.end());
        os << "i - a - j -> lit\n";
        for (auto &it : iaj_tmp)
            os << it.first.i << " - " << it.first.a << " - " << it.first.j
             << " -> " << it.second << "\n";
      }
      return os;
    }
  };
#else
  struct lit_mapper
  {
    unsigned n_classes_, n_env_, n_sigma_red_;
    bool is_joint_

    lit_mapper(unsigned n_classes, unsigned n_env, unsigned n_sigma_red,
               bool is_joint = false)
      : n_classes_{n_classes}
      , n_env_{n_env}
      , n_sigma_red_{n_sigma_red}
      , is_joint_(is_joint)
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

    int si2lit(unsigned i) const
    {
      assert(is_joint_);
      assert(i < n_classes_);
      return (int) 1 + n_classes_*n_env_ +  n_classes_*n_sigma_red_*n_classes_
             + n_sigma_red_*n_classes_ + n_classes_ + i;
    }
    int get_si(int i) const
    {
      return si2lit(i);
    }
  };
#endif

}
}
