// -*- coding: utf-8 -*-
// Copyright (C) 2021 Laboratoire de Recherche et Développement de
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

#include "config.h"
#include <spot/misc/minato.hh>
#include <spot/priv/robin_hood.hh>
#include <spot/tl/expansions.hh>
#include <spot/twa/bdddict.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/twaalgos/remprop.hh>

namespace spot
{
  namespace
  {
    class expansion_basic final : expansion_builder
    {
    public:
      using exp_map = expansion_builder::exp_map;

      expansion_basic(bdd_dict_ptr d)
      {}

      expansion_basic(exp_map&& m, bdd_dict_ptr d)
        : bdd2formula_(m)
        , formula2bdd_()
      {}

      void insert(bdd letter, formula suffix) final;

      void finalize() final
      {}

      exp_map& result() final
      {
        return bdd2formula_;
      }

      bool empty() final
      {
        return bdd2formula_.empty();
      }

      void clear() final
      {
        bdd2formula_.clear();
      }

    private:
      exp_map bdd2formula_;
      std::map<formula, exp_map::iterator> formula2bdd_;
    };

    void expansion_basic::insert(bdd letter, formula suffix)
    {
      auto res = bdd2formula_.insert({letter, suffix});
      if (!res.second)
        {
          auto it = res.first;
          it->second = formula::OrRat({it->second, suffix});
        }
    }

    class expansion_merge_formulas final : expansion_builder
    {
    public:
      using exp_map = expansion_builder::exp_map;

      expansion_merge_formulas(bdd_dict_ptr d)
      {}

      expansion_merge_formulas(exp_map&& m, bdd_dict_ptr d)
        : res_()
        , terms_(m.begin(), m.end())
      {}

      void insert(bdd letter, formula suffix) final;

      void finalize() final;

      exp_map& result() final
      {
        return res_;
      }

      bool empty() final
      {
        return terms_.empty();
      }

      void clear() final
      {
        terms_.clear();
        res_.clear();
      }

    private:
      std::vector<std::pair<bdd, formula>> terms_;
      exp_map res_;
    };

    void expansion_merge_formulas::insert(bdd letter, formula suffix)
    {
      terms_.push_back({letter, suffix});
    }

    void expansion_merge_formulas::finalize()
    {
      res_.clear();

      // Given such terms:
      //
      // - a . ϕ1
      // - a . ϕ2
      // - b . ϕ1
      //
      // Merge them by suffix:
      //
      // - (a ∨ b) . ϕ1
      // - a . ϕ2
      std::map<formula, bdd> suffix2letter;
      for (const auto& [letter, suffix]: terms_)
        {
          auto res = suffix2letter.insert({suffix, letter});
          if (!res.second)
            {
              auto it = res.first;
              it->second |= letter;
            }
        }

      // Given such terms:
      //
      // - a . ϕ1
      // - a . ϕ2
      //
      // Merge them by letter:
      //
      // - a . (ϕ1 ∨ ϕ2)
      for (const auto& [suffix, letter]: suffix2letter)
        {
          auto res = res_.insert({letter, suffix});
          if (!res.second)
            {
              auto it = res.first;
              it->second = formula::OrRat({it->second, suffix});
            }
        }
    }

    class expansion_bdd final : expansion_builder
    {
    public:
      using exp_map = expansion_builder::exp_map;

      expansion_bdd(bdd_dict_ptr d)
        : anon_set_(bddtrue)
        , d_(d)
      {}

      expansion_bdd(exp_map&& m, bdd_dict_ptr d)
        : anon_set_(bddtrue)
        , d_(d)
      {
        for (const auto& [letter, suffix] : m)
          {
            insert(letter, suffix);
          }
      }

      expansion_bdd(const expansion_bdd&) = delete;

      expansion_bdd&
      operator=(const expansion_bdd& other) = delete;

      expansion_bdd&
      operator=(const expansion_bdd&& other)
      {
        d_->unregister_all_my_variables(this);

        anon_set_ = std::move(other.anon_set_);
        exp_ = std::move(other.exp_);
        res_ = std::move(other.res_);
        formula2bdd_ = std::move(other.formula2bdd_);
        bdd2formula_ = std::move(other.bdd2formula_);

        d_ = other.d_;
        d_->register_all_variables_of(&other, this);

        return *this;
      }

      ~expansion_bdd()
      {
        d_->unregister_all_my_variables(this);
      }

      void insert(bdd letter, formula suffix) final;

      void finalize() final;

      exp_map& result() final
      {
        return res_;
      }

      bool empty() final
      {
        return formula2bdd_.empty();
      }

      void clear() final
      {
        formula2bdd_.clear();
        bdd2formula_.clear();
        exp_ = bddfalse;
        anon_set_ = bddtrue;
        res_.clear();
      }

    private:
        bdd exp_;
        bdd anon_set_;
        std::map<formula, int> formula2bdd_;
        std::map<int, formula> bdd2formula_;
        exp_map res_;
        bdd_dict_ptr d_;

        formula var_to_formula(int var);
        formula conj_bdd_to_sere(bdd b);
    };

    formula
    expansion_bdd::var_to_formula(int var)
    {
      formula f = bdd2formula_[var];
      assert(f);
      return f;
    }

    formula
    expansion_bdd::conj_bdd_to_sere(bdd b)
    {
      if (b == bddtrue)
        return formula::tt();
      if (b == bddfalse)
        return formula::ff();

      // Unroll the first loop of the next do/while loop so that we
      // do not have to create v when b is not a conjunction.
      formula res = var_to_formula(bdd_var(b));
      bdd high = bdd_high(b);
      if (high == bddfalse)
        {
          res = formula::Not(res);
          b = bdd_low(b);
        }
      else
        {
          assert(bdd_low(b) == bddfalse);
          b = high;
        }
      if (b == bddtrue)
        return res;
      std::vector<formula> v{std::move(res)};
      do
        {
          res = var_to_formula(bdd_var(b));
          high = bdd_high(b);
          if (high == bddfalse)
            {
              res = formula::Not(res);
              b = bdd_low(b);
            }
          else
            {
              assert(bdd_low(b) == bddfalse);
              b = high;
            }
          assert(b != bddfalse);
          v.emplace_back(std::move(res));
        }
      while (b != bddtrue);
      return formula::multop(op::AndRat, std::move(v));
    }

    void expansion_bdd::insert(bdd letter, formula suffix)
    {

      int anon_var_num;
      auto it = formula2bdd_.find(suffix);
      if (it != formula2bdd_.end())
        {
          anon_var_num = it->second;
        }
      else
        {
          anon_var_num = d_->register_anonymous_variables(1, this);
          formula2bdd_.insert({suffix, anon_var_num});
          bdd2formula_.insert({anon_var_num, suffix});
        }

      bdd var = bdd_ithvar(anon_var_num);
      anon_set_ &= var;
      exp_ |= letter & var;
    }

    void expansion_bdd::finalize()
    {
      minato_isop isop(exp_);
      bdd cube;
      while ((cube = isop.next()) != bddfalse)
        {
          bdd letter = bdd_exist(cube, anon_set_);
          bdd suffix = bdd_existcomp(cube, anon_set_);
          formula dest = conj_bdd_to_sere(suffix);

          auto it = res_.insert({letter, dest});
          if (!it.second)
            {
              auto it2 = it.first;
              it2->second = formula::OrRat({it2->second, dest});
            }
        }
    }

    // FIXME: could probably just return a map directly
    static std::vector<std::string>
    formula_aps(formula f)
    {
      auto res = std::unordered_set<std::string>();

      f.traverse([&res](formula f)
      {
        if (f.is(op::ap))
        {
          res.insert(f.ap_name());
          return true;
        }

        return false;
      });

      return std::vector(res.begin(), res.end());
    }

  formula
  rewrite_and_nlm(formula f)
    {
      unsigned s = f.size();
      std::vector<formula> final;
      std::vector<formula> non_final;

      for (auto g: f)
        if (g.accepts_eword())
          final.emplace_back(g);
        else
          non_final.emplace_back(g);

      if (non_final.empty())
        // (a* & b*);c = (a*|b*);c
        return formula::OrRat(std::move(final));
      if (!final.empty())
      {
        // let F_i be final formulae
        //     N_i be non final formula
        // (F_1 & ... & F_n & N_1 & ... & N_m)
        // =   (F_1 | ... | F_n);[*] && (N_1 & ... & N_m)
        //   | (F_1 | ... | F_n) && (N_1 & ... & N_m);[*]
        formula f = formula::OrRat(std::move(final));
        formula n = formula::AndNLM(std::move(non_final));
        formula t = formula::one_star();
        formula ft = formula::Concat({f, t});
        formula nt = formula::Concat({n, t});
        formula ftn = formula::AndRat({ft, n});
        formula fnt = formula::AndRat({f, nt});
        return formula::OrRat({ftn, fnt});
      }
      // No final formula.
      // Translate N_1 & N_2 & ... & N_n into
      //   N_1 && (N_2;[*]) && ... && (N_n;[*])
      // | (N_1;[*]) && N_2 && ... && (N_n;[*])
      // | (N_1;[*]) && (N_2;[*]) && ... && N_n
      formula star = formula::one_star();
      std::vector<formula> disj;
      for (unsigned n = 0; n < s; ++n)
      {
        std::vector<formula> conj;
        for (unsigned m = 0; m < s; ++m)
        {
          formula g = f[m];
          if (n != m)
            g = formula::Concat({g, star});
          conj.emplace_back(g);
        }
        disj.emplace_back(formula::AndRat(std::move(conj)));
      }
      return formula::OrRat(std::move(disj));
    }
  }

  formula
  expansion_to_formula(expansion_t e, bdd_dict_ptr& d)
  {
    std::vector<formula> res;

    for (const auto& [key, val] : e)
      {
        formula prefix = bdd_to_formula(key, d);
        res.push_back(formula::Concat({prefix, val}));
      }

    return formula::OrRat(res);
  }


  template<typename ExpansionBuilder>
  expansion_t
  expansion_impl(formula f, const bdd_dict_ptr& d, void *owner, expansion_builder::expand_opt opts)
  {
    if (f.is_boolean())
      {
        auto f_bdd = formula_to_bdd(f, d, owner);

        if (f_bdd == bddfalse)
          return {};

        return {{f_bdd, formula::eword()}};
      }


    switch (f.kind())
      {
        case op::ff:
        case op::tt:
        case op::ap:
          SPOT_UNREACHABLE();

        case op::eword:
          return {{bddfalse, formula::ff()}};

        case op::Concat:
          {
            auto exps = expansion(f[0], d, owner, opts);

            ExpansionBuilder res(d);
            for (const auto& [bdd_l, form] : exps)
              {
                res.insert(bdd_l, formula::Concat({form, f.all_but(0)}));
              }

            if (f[0].accepts_eword())
              {
                auto exps_rest = expansion(f.all_but(0), d, owner, opts);
                for (const auto& [bdd_l, form] : exps_rest)
                  {
                    res.insert(bdd_l, form);
                  }
              }

            res.finalize();
            return res.result();
          }

        case op::FStar:
          {
            formula E = f[0];

            if (f.min() == 0 && f.max() == 0)
              return {{bddtrue, formula::eword()}};

            auto min = f.min() == 0 ? 0 : (f.min() - 1);
            auto max = f.max() == formula::unbounded()
                         ? formula::unbounded()
                         : (f.max() - 1);

            auto E_i_j_minus = formula::FStar(E, min, max);

            auto exp = expansion(E, d, owner, opts);
            ExpansionBuilder res(d);
            for (const auto& [li, ei] : exp)
              {
                res.insert(li, formula::Fusion({ei, E_i_j_minus}));

                if (ei.accepts_eword() && f.min() != 0)
                  {
                    for (const auto& [ki, fi] : expansion(E_i_j_minus, d, owner, opts))
                      {
                        // FIXME: build bdd once
                        if ((li & ki) != bddfalse)
                          res.insert(li & ki, fi);
                      }
                  }
              }
            if (f.min() == 0)
              res.insert(bddtrue, formula::eword());

            res.finalize();
            return res.result();
          }

        case op::Star:
          {
            auto min = f.min() == 0 ? 0 : (f.min() - 1);
            auto max = f.max() == formula::unbounded()
                         ? formula::unbounded()
                         : (f.max() - 1);

            auto exps = expansion(f[0], d, owner, opts);

            ExpansionBuilder res(d);
            for (const auto& [bdd_l, form] : exps)
              {
                res.insert(bdd_l, formula::Concat({form, formula::Star(f[0], min, max)}));
              }

            res.finalize();
            return res.result();
          }

        case op::AndNLM:
          {
            formula rewrite = rewrite_and_nlm(f);
            return expansion(rewrite, d, owner, opts);
          }

        case op::first_match:
          {
            auto exps = expansion(f[0], d, owner, opts);

            ExpansionBuilder ndet_res(d);
            for (const auto& [bdd_l, form] : exps)
              {
                ndet_res.insert(bdd_l, form);
              }

            bdd or_labels = bddfalse;
            bdd support = bddtrue;
            bool is_det = true;
            ndet_res.finalize();
            for (const auto& [l, _] : ndet_res.result())
              {
                support &= bdd_support(l);
                if (is_det)
                  is_det = !bdd_have_common_assignment(l, or_labels);
                or_labels |= l;
              }

            if (is_det)
              {
                // we don't need to determinize the expansion, it's already
                // deterministic
                for (auto& [_, dest] : ndet_res.result())
                  dest = formula::first_match(dest);
                return ndet_res.result();
              }

            ExpansionBuilder res(d);
            // TODO: extraire en fonction indépendante + lambda choix wrapper
            std::vector<formula> dests;
            for (bdd l: minterms_of(or_labels, support))
              {
                for (const auto& [ndet_label, ndet_dest] : ndet_res.result())
                  {
                    if (bdd_implies(l, ndet_label))
                      dests.push_back(ndet_dest);
                  }
                formula or_dests = formula::OrRat(dests);
                res.insert(l, formula::first_match(or_dests));
                dests.clear();
              }

            res.finalize();
            return res.result();
          }

        case op::Fusion:
          {
            ExpansionBuilder res(d);
            formula E = f[0];
            formula F = f.all_but(0);

            expansion_t Ei = expansion(E, d, owner, opts);
            // TODO: std::option
            expansion_t Fj = expansion(F, d, owner, opts);

            for (const auto& [li, ei] : Ei)
              {
                if (ei.accepts_eword())
                  {
                    for (const auto& [kj, fj] : Fj)
                        if ((li & kj) != bddfalse)
                          res.insert(li & kj, fj);
                  }
                res.insert(li, formula::Fusion({ei, F}));
              }

            res.finalize();
            return res.result();
          }

        case op::AndRat:
          {
            ExpansionBuilder res(d);
            for (const auto& sub_f : f)
              {
                auto exps = expansion(sub_f, d, owner, opts);

                if (exps.empty())
                  {
                    // op::AndRat: one of the expansions was empty (the only
                    //             edge was `false`), so the AndRat is empty as
                    //             well
                    res.clear();
                    break;
                  }

                if (res.empty())
                  {
                    res = ExpansionBuilder(std::move(exps), d);
                    res.finalize();
                    continue;
                  }

                ExpansionBuilder new_res(d);
                for (const auto& [l_key, l_val] : exps)
                  {
                    for (const auto& [r_key, r_val] : res.result())
                      {
                        if ((l_key & r_key) != bddfalse)
                          new_res.insert(l_key & r_key, formula::multop(f.kind(), {l_val, r_val}));
                      }
                  }

                res = std::move(new_res);
                res.finalize();
              }

            res.finalize();
            return res.result();
          }

        case op::OrRat:
          {
            ExpansionBuilder res(d);
            for (const auto& sub_f : f)
              {
                auto exps = expansion(sub_f, d, owner, opts);
                if (exps.empty())
                  continue;

                if (res.empty())
                  {
                    res = ExpansionBuilder(std::move(exps), d);
                    continue;
                  }

                for (const auto& [label, dest] : exps)
                  res.insert(label, dest);
              }

            res.finalize();
            return res.result();
          }

        default:
          std::cerr << "unimplemented kind "
                    << static_cast<int>(f.kind())
                    << std::endl;
          SPOT_UNIMPLEMENTED();
      }

    return {};
  }

  expansion_t
  expansion(formula f, const bdd_dict_ptr& d, void *owner, expansion_builder::expand_opt opts)
  {
    if (opts & expansion_builder::Basic)
      return expansion_impl<expansion_basic>(f, d, owner, opts);
    else if (opts & expansion_builder::MergeSuffix)
      return expansion_impl<expansion_merge_formulas>(f, d, owner, opts);
    else // expansion_builder::Bdd
      return expansion_impl<expansion_bdd>(f, d, owner, opts);
  }

  twa_graph_ptr
  expand_automaton(formula f, bdd_dict_ptr d, expansion_builder::expand_opt opts)
  {
    auto finite = expand_finite_automaton(f, d, opts);
    return from_finite(finite);
  }

  twa_graph_ptr
  expand_finite_automaton(formula f, bdd_dict_ptr d, expansion_builder::expand_opt opts)
  {
    auto aut = make_twa_graph(d);

    aut->prop_state_acc(true);
    const auto acc_mark = aut->set_buchi();

    auto formula2state = robin_hood::unordered_map<formula, unsigned>();

    unsigned init_state = aut->new_state();
    aut->set_init_state(init_state);
    formula2state.insert({ f, init_state });

    auto f_aps = formula_aps(f);
    for (auto& ap : f_aps)
        aut->register_ap(ap);

    auto todo = std::vector<std::pair<formula, unsigned>>();
    todo.push_back({f, init_state});

    auto state_names = new std::vector<std::string>();
    std::ostringstream ss;
    ss << f;
    state_names->push_back(ss.str());

    auto find_dst = [&](formula suffix) -> unsigned
      {
        unsigned dst;
        auto it = formula2state.find(suffix);
        if (it != formula2state.end())
        {
          dst = it->second;
        }
        else
        {
          dst = aut->new_state();
          todo.push_back({suffix, dst});
          formula2state.insert({suffix, dst});
          std::ostringstream ss;
          ss << suffix;
          state_names->push_back(ss.str());
        }

        return dst;
      };

    while (!todo.empty())
      {
        auto [curr_f, curr_state] = todo[todo.size() - 1];
        todo.pop_back();

        auto curr_acc_mark= curr_f.accepts_eword()
          ? acc_mark
          : acc_cond::mark_t();

        auto exp = expansion(curr_f, d, aut.get(), opts);

        for (const auto& [letter, suffix] : exp)
          {
            if (suffix.is(op::ff))
              continue;

            auto dst = find_dst(suffix);
            aut->new_edge(curr_state, dst, letter, curr_acc_mark);
          }

        // if state has no transitions and should be accepting, create
        // artificial transition
        if (aut->get_graph().state_storage(curr_state).succ == 0
            && curr_f.accepts_eword())
          aut->new_edge(curr_state, curr_state, bddfalse, acc_mark);
      }

    aut->set_named_prop("state-names", state_names);
    aut->merge_edges();
    return aut;
  }
}
