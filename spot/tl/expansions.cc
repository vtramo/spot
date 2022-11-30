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
#include <spot/priv/robin_hood.hh>
#include <spot/tl/expansions.hh>
#include <spot/twa/bdddict.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/twaalgos/remprop.hh>

namespace spot
{
  namespace
  {
    static void
    insert_or_merge(expansion_t& exp, bdd letter, formula suffix)
    {
      auto res = exp.insert({letter, suffix});
      if (!res.second)
        {
          auto it = res.first;
          it->second = formula::OrRat({it->second, suffix});
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

  expansion_t
  expansion(formula f, const bdd_dict_ptr& d, void *owner)
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
            auto exps = expansion(f[0], d, owner);

            expansion_t res;
            for (const auto& [bdd_l, form] : exps)
              {
                res.insert({bdd_l, formula::Concat({form, f.all_but(0)})});
              }

            if (f[0].accepts_eword())
              {
                auto exps_rest = expansion(f.all_but(0), d, owner);
                for (const auto& [bdd_l, form] : exps_rest)
                  {
                    insert_or_merge(res, bdd_l, form);
                  }
              }
            return res;
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

            auto exp = expansion(E, d, owner);
            expansion_t res;
            for (const auto& [li, ei] : exp)
              {
                insert_or_merge(res, li, formula::Fusion({ei, E_i_j_minus}));

                if (ei.accepts_eword() && f.min() != 0)
                  {
                    for (const auto& [ki, fi] : expansion(E_i_j_minus, d, owner))
                      {
                        // FIXME: build bdd once
                        if ((li & ki) != bddfalse)
                          insert_or_merge(res, li & ki, fi);
                      }
                  }
              }
            if (f.min() == 0)
              insert_or_merge(res, bddtrue, formula::eword());

            return res;
          }

        case op::Star:
          {
            auto min = f.min() == 0 ? 0 : (f.min() - 1);
            auto max = f.max() == formula::unbounded()
                         ? formula::unbounded()
                         : (f.max() - 1);

            auto exps = expansion(f[0], d, owner);

            expansion_t res;
            for (const auto& [bdd_l, form] : exps)
              {
                res.insert({bdd_l, formula::Concat({form, formula::Star(f[0], min, max)})});
              }

            return res;
          }

        case op::AndNLM:
          {
            formula rewrite = rewrite_and_nlm(f);
            return expansion(rewrite, d, owner);
          }

        case op::first_match:
          {
            auto exps = expansion(f[0], d, owner);

            expansion_t res;
            for (const auto& [bdd_l, form] : exps)
              {
                res.insert({bdd_l, formula::first_match(form)});
              }

            return res;
          }

        case op::Fusion:
          {
            expansion_t res;
            formula E = f[0];
            formula F = f.all_but(0);

            expansion_t Ei = expansion(E, d, owner);
            // TODO: std::option
            expansion_t Fj = expansion(F, d, owner);

            for (const auto& [li, ei] : Ei)
              {
                if (ei.accepts_eword())
                  {
                    for (const auto& [kj, fj] : Fj)
                        if ((li & kj) != bddfalse)
                          insert_or_merge(res, li & kj, fj);
                  }
                insert_or_merge(res, li, formula::Fusion({ei, F}));
              }

            return res;
          }

        case op::AndRat:
        case op::OrRat:
          {
            expansion_t res;
            for (const auto& sub_f : f)
              {
                auto exps = expansion(sub_f, d, owner);

                if (exps.empty())
                  {
                    if (f.kind() == op::OrRat)
                      continue;

                    // op::AndRat: one of the expansions was empty (the only
                    //             edge was `false`), so the AndRat is empty as
                    //             well
                    res.clear();
                    break;
                  }

                if (res.empty())
                  {
                    res = std::move(exps);
                    continue;
                  }

                expansion_t new_res;
                for (const auto& [l_key, l_val] : exps)
                  {
                    for (const auto& [r_key, r_val] : res)
                      {
                        if ((l_key & r_key) != bddfalse)
                          insert_or_merge(new_res, l_key & r_key, formula::multop(f.kind(), {l_val, r_val}));

                        if (f.is(op::OrRat))
                          {
                            if ((l_key & !r_key) != bddfalse)
                              insert_or_merge(new_res, l_key & !r_key, l_val);

                            if ((!l_key & r_key) != bddfalse)
                              insert_or_merge(new_res, !l_key & r_key, r_val);
                          }
                      }
                  }

                res = std::move(new_res);
              }

            return res;
          }

        default:
          std::cerr << "unimplemented kind "
                    << static_cast<int>(f.kind())
                    << std::endl;
          SPOT_UNIMPLEMENTED();
      }

      return {};
    }

  twa_graph_ptr
  expand_automaton(formula f, bdd_dict_ptr d)
  {
    auto finite = expand_finite_automaton(f, d);
    return from_finite(finite);
  }

  twa_graph_ptr
  expand_finite_automaton(formula f, bdd_dict_ptr d)
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

        auto exp = expansion(curr_f, d, aut.get());

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
