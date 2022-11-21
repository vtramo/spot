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
#include <spot/tl/derive.hh>
#include <spot/twa/bdddict.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/twaalgos/remprop.hh>

namespace spot
{
  namespace
  {
    static std::pair<bdd, bdd>
    first(formula f, const bdd_dict_ptr& d, void* owner)
    {
      if (f.is_boolean())
        {
          bdd res = formula_to_bdd(f, d, owner);
          return { res, bdd_support(res) };
        }

      switch (f.kind())
      {
        // handled by is_boolean above
        case op::ff:
        case op::tt:
        case op::ap:
        case op::And:
        case op::Or:
          SPOT_UNREACHABLE();

        case op::eword:
          return { bddfalse, bddtrue };

        case op::OrRat:
          {
            bdd res = bddfalse;
            bdd support = bddtrue;
            for (auto subformula : f)
              {
                auto [r, sup] = first(subformula, d, owner);
                res |= r;
                support &= sup;
              }
            return { res, support };
          }

        case op::AndRat:
          {
            bdd res = bddtrue;
            bdd support = bddtrue;
            for (auto subformula : f)
              {
                auto [r, sup] = first(subformula, d, owner);
                res &= r;
                support &= sup;
              }
            return { res, support };
          }

        case op::AndNLM:
          return first(rewrite_and_nlm(f), d, owner);

        case op::Concat:
          {
            auto [res, support] = first(f[0], d, owner);

            if (f[0].accepts_eword())
              {
                auto [r, sup] = first(f.all_but(0), d, owner);
                res |= r;
                support &= sup;
              }

            return { res, support };
          }

        case op::Fusion:
          {
            auto [res, support] = first(f[0], d, owner);

            // this should be computed only if f[0] recognizes words of size 1
            // or accepts eword ?
            auto p = first(f.all_but(0), d, owner);

            return { res, support & p.second };
          }

        case op::Star:
        case op::first_match:
          return first(f[0], d, owner);

        case op::FStar:
          {
            auto [res, support] = first(f[0], d, owner);

            if (f.min() == 0)
              res = bddtrue;

            return { res, support };
          }

        default:
          std::cerr << "unimplemented kind "
                    << static_cast<int>(f.kind())
                    << std::endl;
          SPOT_UNIMPLEMENTED();
      }

      return { bddfalse, bddtrue };
    }

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

  twa_graph_ptr
  derive_finite_automaton_with_first(formula f, bdd_dict_ptr bdd_dict,
                                     bool deterministic, derive_opts options)
  {
    auto aut = make_twa_graph(bdd_dict);

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

    auto find_dst = [&](formula derivative) -> unsigned
      {
        unsigned dst;
        auto it = formula2state.find(derivative);
        if (it != formula2state.end())
        {
          dst = it->second;
        }
        else
        {
          dst = aut->new_state();
          todo.push_back({derivative, dst});
          formula2state.insert({derivative, dst});
          std::ostringstream ss;
          ss << derivative;
          state_names->push_back(ss.str());
        }

        return dst;
      };

    while (!todo.empty())
      {
        auto [curr_f, curr_state] = todo[todo.size() - 1];
        todo.pop_back();

        auto curr_acc_mark = curr_f.accepts_eword()
          ? acc_mark
          : acc_cond::mark_t();

        auto [firsts, firsts_support] = first(curr_f, bdd_dict, aut.get());
        for (const bdd one : minterms_of(firsts, firsts_support))
          {
            formula derivative =
              partial_derivation(curr_f, one, bdd_dict, aut.get(), options);

            // no transition possible from this letter
            if (derivative.is(op::ff))
              continue;

            // either the formula isn't an OrRat, or if it is we consider it as
            // as a whole to get a deterministic automaton
            if (deterministic || !derivative.is(op::OrRat))
              {
                auto dst = find_dst(derivative);
                aut->new_edge(curr_state, dst, one, curr_acc_mark);
                continue;
              }

            // formula is an OrRat and we want a non deterministic automaton,
            // so consider each child as a destination
            for (const auto& subformula : derivative)
              {
                auto dst = find_dst(subformula);
                aut->new_edge(curr_state, dst, one, curr_acc_mark);
              }
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

  twa_graph_ptr
  derive_finite_automaton(formula f, bool deterministic)
  {
    auto bdd_dict = make_bdd_dict();
    auto aut = make_twa_graph(bdd_dict);

    aut->prop_state_acc(true);
    const auto acc_mark = aut->set_buchi();

    auto formula2state = robin_hood::unordered_map<formula, unsigned>();

    unsigned init_state = aut->new_state();
    aut->set_init_state(init_state);

    formula2state.insert({ f, init_state });

    auto f_aps = formula_aps(f);
    for (auto& ap : f_aps)
        aut->register_ap(ap);
    bdd all_aps = aut->ap_vars();

    auto todo = std::vector<std::pair<formula, unsigned>>();
    todo.push_back({f, init_state});

    auto state_names = new std::vector<std::string>();
    std::ostringstream ss;
    ss << f;
    state_names->push_back(ss.str());

    auto find_dst = [&](formula derivative) -> unsigned
      {
        unsigned dst;
        auto it = formula2state.find(derivative);
        if (it != formula2state.end())
        {
          dst = it->second;
        }
        else
        {
          dst = aut->new_state();
          todo.push_back({derivative, dst});
          formula2state.insert({derivative, dst});
          std::ostringstream ss;
          ss << derivative;
          state_names->push_back(ss.str());
        }

        return dst;
      };

    while (!todo.empty())
      {
        auto [curr_f, curr_state] = todo[todo.size() - 1];
        todo.pop_back();

        auto curr_acc_mark = curr_f.accepts_eword()
          ? acc_mark
          : acc_cond::mark_t();

        for (const bdd one : minterms_of(bddtrue, all_aps))
          {
            formula derivative =
              partial_derivation(curr_f, one, bdd_dict, aut.get());

            // no transition possible from this letter
            if (derivative.is(op::ff))
              continue;

            // either the formula isn't an OrRat, or if it is we consider it as
            // as a whole to get a deterministic automaton
            if (deterministic || !derivative.is(op::OrRat))
              {
                auto dst = find_dst(derivative);
                aut->new_edge(curr_state, dst, one, curr_acc_mark);
                continue;
              }

            // formula is an OrRat and we want a non deterministic automaton,
            // so consider each child as a destination
            for (const auto& subformula : derivative)
              {
                auto dst = find_dst(subformula);
                aut->new_edge(curr_state, dst, one, curr_acc_mark);
              }
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

  twa_graph_ptr
  derive_automaton_with_first(formula f, bdd_dict_ptr bdd_dict,
                              bool deterministic)
  {
    auto finite = derive_finite_automaton_with_first(f, bdd_dict,
                                                     deterministic);

    return from_finite(finite);
  }

  twa_graph_ptr
  derive_automaton(formula f, bool deterministic)
  {
    auto finite = derive_finite_automaton(f, deterministic);

    return from_finite(finite);
  }

  formula
  partial_derivation(formula f, const bdd var, const bdd_dict_ptr& d,
                     void* owner, derive_opts options)
  {
    if (f.is_boolean())
      {
        auto f_bdd = formula_to_bdd(f, d, owner);

        if (bdd_implies(var, f_bdd))
            return formula::eword();

        return formula::ff();
      }

    switch (f.kind())
      {
        // handled by is_boolean above
        case op::ff:
        case op::tt:
        case op::ap:
          SPOT_UNREACHABLE();

        case op::eword:
          return formula::ff();

        // d(E.F) = { d(E).F } U { c(E).d(F) }
        case op::Concat:
          {
            formula E = f[0];
            formula F = f.all_but(0);

            formula d_E = partial_derivation(E, var, d, owner, options);

            formula res;

            if (options.concat_star_distribute && d_E.is(op::OrRat))
              {
                std::vector<formula> distributed;
                for (auto g : d_E)
                  {
                    distributed.push_back(formula::Concat({g, F}));
                  }

                res = formula::OrRat(distributed);
              }
            else
              {
                res =
                  formula::Concat({ partial_derivation(E, var, d, owner, options), F });
              }


            if (E.accepts_eword())
                res = formula::OrRat(
                        { res, partial_derivation(F, var, d, owner, options) });

            return res;
          }

        // d(E*) = d(E).E*
        // d(E[*i..j]) = d(E).E[*(i-1)..(j-1)]
        case op::Star:
          {
            auto min = f.min() == 0 ? 0 : (f.min() - 1);
            auto max = f.max() == formula::unbounded()
                         ? formula::unbounded()
                         : (f.max() - 1);

            formula d_E = partial_derivation(f[0], var, d, owner, options);

            if (options.concat_star_distribute && !f[0].is_finite() && d_E.is(op::OrRat))
              {
                std::vector<formula> distributed;
                for (auto g : d_E)
                  {
                    distributed.push_back(formula::Concat({g, formula::Star(f[0], min, max)}));
                  }

                return formula::OrRat(distributed);
              }

            return formula::Concat({ d_E, formula::Star(f[0], min, max) });
          }

        // d(E[:*i..j]) = E:E[:*(i-1)..(j-1)] + (eword if i == 0 or c(d(E)))
        case op::FStar:
          {
            formula E = f[0];

            if (f.min() == 0 && f.max() == 0)
              return formula::tt();

            auto d_E = partial_derivation(E, var, d, owner, options);

            auto min = f.min() == 0 ? 0 : (f.min() - 1);
            auto max = f.max() == formula::unbounded()
                         ? formula::unbounded()
                         : (f.max() - 1);

            auto results = std::vector<formula>();

            auto E_i_j_minus = formula::FStar(E, min, max);
            results.push_back(formula::Fusion({ d_E, E_i_j_minus }));

            if (d_E.accepts_eword())
              results.push_back(d_E);

            if (f.min() == 0)
              results.push_back(formula::eword());

            return formula::OrRat(std::move(results));
          }

        // d(E && F) = d(E) && d(F)
        // d(E + F) = {d(E)} U {d(F)}
        case op::AndRat:
        case op::OrRat:
          {
            std::vector<formula> subderivations;
            for (auto subformula : f)
              {
                auto subderivation =
                  partial_derivation(subformula, var, d, owner, options);
                subderivations.push_back(subderivation);
              }
            return formula::multop(f.kind(), std::move(subderivations));
          }

        case op::AndNLM:
          {
            formula rewrite = rewrite_and_nlm(f);
            return partial_derivation(rewrite, var, d, owner, options);
          }

        // d(E:F) = {d(E):F} U {c(d(E)).d(F)}
        case op::Fusion:
          {
            formula E = f[0];
            formula F = f.all_but(0);

            auto d_E = partial_derivation(E, var, d, owner, options);
            auto res = formula::Fusion({ d_E, F });

            if (d_E.accepts_eword())
              res =
                formula::OrRat({ res, partial_derivation(F, var, d, owner, options) });

            return res;
          }

        case op::first_match:
          {
            formula E = f[0];
            auto d_E = partial_derivation(E, var, d, owner, options);
            // if d_E.accepts_eword(), first_match(d_E) will return eword
            return formula::first_match(d_E);
          }

        default:
          std::cerr << "unimplemented kind "
                    << static_cast<int>(f.kind())
                    << std::endl;
          SPOT_UNIMPLEMENTED();
      }
    return formula::ff();
  }
}
