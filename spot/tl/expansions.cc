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

    class bdd_finalizer
    {
      public:
        int encode(formula f)
          {
            bool is_anon = false;
            int var_num;
            auto it = formula2bdd_.find(f);
            if (it != formula2bdd_.end())
            {
              var_num = it->second;
            }
            else
            {
              if (opt_sigma_star_ && (f.is(op::Star)
                                      && f[0].is(op::tt)
                                      && f.min() == 0
                                      && f.max() == formula::unbounded()))
                {
                  var_num = bddtrue.id();
                }
              else if (opt_bdd_encode_ && (f.is(op::AndRat) || f.is(op::OrRat)))
                {
                  bdd var = f.is(op::AndRat) ? bdd(bddtrue) : bdd(bddfalse);
                  for (const auto& sub_f : f)
                    {
                      int bddid = encode(sub_f);
                      bdd subvar = bdd_ithvar(bddid);
                      var = f.is(op::AndRat) ? var & subvar : var | subvar;
                    }
                  var_num = var.id();
                }
              else
                {
                  var_num = d_->register_anonymous_variables(1, this);
                  is_anon = true;
                }

              formula2bdd_.insert({f, var_num});
              bdd2formula_.insert({var_num, f});
            }

            bdd var = bdd_ithvar(var_num);

            if (is_anon)
              anon_set_ &= var;

            return var_num;
          }

        bdd_finalizer(std::multimap<bdd, formula, bdd_less_than>& exp, bdd_dict_ptr d, bool opt_sigma_star, bool opt_bdd_encode)
          : anon_set_(bddtrue)
          , d_(d)
          , opt_sigma_star_(opt_sigma_star)
          , opt_bdd_encode_(opt_bdd_encode)
        {
          for (const auto& [prefix, suffix] : exp)
          {
            int var_num = encode(suffix);
            bdd var = bdd_ithvar(var_num);
            exp_ |= prefix & var;
          }
        }

        ~bdd_finalizer()
        {
          d_->unregister_all_my_variables(this);
        }

        expansion_t
        simplify(exp_opts::expand_opt opts);

      private:
        bdd exp_;
        bdd anon_set_;
        std::map<formula, int> formula2bdd_;
        std::map<int, formula> bdd2formula_;
        bdd_dict_ptr d_;
        bool opt_sigma_star_;
        bool opt_bdd_encode_;

        formula var_to_formula(int var);
        formula conj_bdd_to_sere(bdd b);
        formula bdd_to_sere(bdd b);
    };

    formula
    bdd_finalizer::var_to_formula(int var)
    {
      formula f = bdd2formula_[var];
      assert(f);
      return f;
    }

    formula
    bdd_finalizer::bdd_to_sere(bdd f)
    {
      if (f == bddfalse)
        return formula::ff();

      std::vector<formula> v;
      minato_isop isop(f);
      bdd cube;
      while ((cube = isop.next()) != bddfalse)
        v.emplace_back(conj_bdd_to_sere(cube));
      return formula::OrRat(std::move(v));
    }

    formula
    bdd_finalizer::conj_bdd_to_sere(bdd b)
    {
      if (b == bddtrue)
        {
          if (opt_sigma_star_){
            return formula::Star(formula::tt(), 0, formula::unbounded());
          } else {
            return formula::tt();
          }
        }
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

    expansion_t
    bdd_finalizer::simplify(exp_opts::expand_opt opts)
    {
      expansion_t res;

      if (opts & exp_opts::expand_opt::BddMinterm)
      {
        bdd prop_set = bdd_exist(bdd_support(exp_), anon_set_);
        bdd or_labels = bdd_exist(exp_, anon_set_);
        // TODO: check are_equivalent avec or_labels/exp_ en premier argument
        for (bdd letter: minterms_of(or_labels, prop_set))
        {
          bdd dest_bdd = bdd_restrict(exp_, letter);
          formula dest = bdd_to_sere(dest_bdd);

          auto it = res.insert({letter, dest});
          assert(it.second);
          (void) it;
        }
      }
      else // BddIsop
      {
        minato_isop isop(exp_);
        bdd cube;
        while ((cube = isop.next()) != bddfalse)
        {
          bdd letter = bdd_exist(cube, anon_set_);
          bdd suffix = bdd_existcomp(cube, anon_set_);
          formula dest = conj_bdd_to_sere(suffix);

          res.insert({letter, dest});
        }
      }

      return res;
    }

    void
    finalize(expansion_t& exp, exp_opts::expand_opt opts, bdd_dict_ptr d)
    {
      if (opts & (exp_opts::expand_opt::BddIsop
                  | exp_opts::expand_opt::BddMinterm))
      {
        bdd_finalizer bddf(exp, d, opts & exp_opts::expand_opt::BddSigmaStar, opts & exp_opts::expand_opt::BddEncode);
        exp = bddf.simplify(opts);
      }

      if (opts & exp_opts::expand_opt::UniqueSuffix)
      {
        std::map<formula, bdd> unique_map;
        for (const auto& [prefix, suffix] : exp)
        {
          auto res = unique_map.insert({suffix, prefix});
          if (!res.second)
          {
            auto it = res.first;
            it->second |= prefix;
          }
        }

        exp.clear();
        for (const auto [suffix, prefix] : unique_map)
        {
          exp.insert({prefix, suffix});
        }
      }

      if (opts & exp_opts::expand_opt::UniquePrefix)
      {
        std::map<bdd, formula, bdd_less_than> unique_map;
        for (const auto& [prefix, suffix] : exp)
        {
          auto res = unique_map.insert({prefix, suffix});
          if (!res.second)
          {
            auto it = res.first;
            it->second = formula::OrRat({it->second, suffix});
          }
        }

        exp.clear();
        for (const auto [prefix, suffix] : unique_map)
        {
          exp.insert({prefix, suffix});
        }
      }

      if (opts & exp_opts::expand_opt::Determinize)
        {
          std::multimap<bdd, formula, bdd_less_than> exp_new;

          bdd props = bddtrue;
          for (const auto& [prefix, _] : exp)
            props &= bdd_support(prefix);

          std::vector<formula> dests;
          for (bdd letter : minterms_of(bddtrue, props))
            {
              for (const auto& [prefix, suffix] : exp)
                {
                  if (bdd_implies(letter, prefix))
                    dests.push_back(suffix);
                }
              formula or_dests = formula::OrRat(dests);
              exp_new.insert({letter, or_dests});
              dests.clear();
            }
          exp = exp_new;
        }
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

  void print_expansion(const expansion_t& exp, const bdd_dict_ptr& dict)
  {
    for (const auto& [prefix, suffix] : exp)
      {
        std::cout << bdd_to_formula(prefix, dict) << ": " << suffix << std::endl;
      }
  }


  expansion_t
  expansion(formula f, const bdd_dict_ptr& d, void *owner, exp_opts::expand_opt opts)
  {
    using exp_t = std::multimap<bdd, formula, bdd_less_than>;

    if (f.is_boolean())
      {
        auto f_bdd = formula_to_bdd(f, d, owner);

        if (f_bdd == bddfalse)
          return {};

        return {{f_bdd, formula::eword()}};
      }

    auto rec = [&d, owner, opts](formula f){
      return expansion(f, d, owner, exp_opts::None);
    };


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
            auto exps = rec(f[0]);

            exp_t res;
            for (const auto& [bdd_l, form] : exps)
              {
                res.insert({bdd_l, formula::Concat({form, f.all_but(0)})});
              }

            if (f[0].accepts_eword())
              {
                auto exps_rest = rec(f.all_but(0));
                for (const auto& [bdd_l, form] : exps_rest)
                  {
                    res.insert({bdd_l, form});
                  }
              }

            finalize(res, opts, d);
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

            auto exp = rec(E);
            exp_t res;
            for (const auto& [li, ei] : exp)
              {
                res.insert({li, formula::Fusion({ei, E_i_j_minus})});

                if (ei.accepts_eword() && f.min() != 0)
                  {
                    for (const auto& [ki, fi] : rec(E_i_j_minus))
                      {
                        // FIXME: build bdd once
                        if ((li & ki) != bddfalse)
                          res.insert({li & ki, fi});
                      }
                  }
              }
            if (f.min() == 0)
              res.insert({bddtrue, formula::eword()});

            finalize(res, opts, d);
            return res;
          }

        case op::Star:
          {
            auto min = f.min() == 0 ? 0 : (f.min() - 1);
            auto max = f.max() == formula::unbounded()
                         ? formula::unbounded()
                         : (f.max() - 1);

            auto exps = rec(f[0]);

            exp_t res;
            for (const auto& [bdd_l, form] : exps)
              {
                res.insert({bdd_l, formula::Concat({form, formula::Star(f[0], min, max)})});
              }

            finalize(res, opts, d);
            return res;
          }

        case op::AndNLM:
          {
            formula rewrite = rewrite_and_nlm(f);
            auto res = rec(rewrite);
            finalize(res, opts, d);
            return res;
          }

        case op::first_match:
          {
            auto exps = rec(f[0]);

            exp_t res;
            for (const auto& [bdd_l, form] : exps)
              {
                res.insert({bdd_l, form});
              }

            // determinize
            bdd or_labels = bddfalse;
            bdd support = bddtrue;
            bool is_det = true;
            for (const auto& [l, _] : res)
              {
                support &= bdd_support(l);
                if (is_det)
                  is_det = !bdd_have_common_assignment(l, or_labels);
                or_labels |= l;
              }

            if (is_det)
              {
                for (auto& [_, dest] : res)
                  dest = formula::first_match(dest);
                finalize(res, opts, d);
                return res;
              }

            exp_t res_det;
            std::vector<formula> dests;
            for (bdd l: minterms_of(or_labels, support))
              {
                for (const auto& [ndet_label, ndet_dest] : res)
                  {
                    if (bdd_implies(l, ndet_label))
                      dests.push_back(ndet_dest);
                  }
                formula or_dests = formula::OrRat(dests);
                res_det.insert({l, or_dests});
                dests.clear();
              }

            for (auto& [_, dest] : res_det)
              dest = formula::first_match(dest);
            finalize(res_det, opts, d);
            return res_det;
          }

        case op::Fusion:
          {
            exp_t res;
            formula E = f[0];
            formula F = f.all_but(0);

            exp_t Ei = rec(E);
            // TODO: std::option
            exp_t Fj = rec(F);

            for (const auto& [li, ei] : Ei)
              {
                if (ei.accepts_eword())
                  {
                    for (const auto& [kj, fj] : Fj)
                        if ((li & kj) != bddfalse)
                          res.insert({li & kj, fj});
                  }
                res.insert({li, formula::Fusion({ei, F})});
              }

            finalize(res, opts, d);
            return res;
          }

        case op::AndRat:
          {
            exp_t res;
            for (const auto& sub_f : f)
              {
                auto exps = rec(sub_f);

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
                    res = std::move(exps);
                    continue;
                  }

                exp_t new_res;
                bool inserted = false;
                for (const auto& [l_key, l_val] : exps)
                  {
                    for (const auto& [r_key, r_val] : res)
                      {
                        if ((l_key & r_key) != bddfalse)
                          {
                            new_res.insert({l_key & r_key, formula::multop(f.kind(), {l_val, r_val})});
                            inserted = true;
                          }
                      }
                  }

                if (!inserted)
                  {
                    // all prefix conjuctions led to bddfalse, And is empty
                    res.clear();
                    break;
                  }

                res = std::move(new_res);
              }

            finalize(res, opts, d);
            return res;
          }

        case op::OrRat:
          {
            exp_t res;
            for (const auto& sub_f : f)
              {
                auto exps = rec(sub_f);
                if (exps.empty())
                  continue;

                if (res.empty())
                  {
                    res = std::move(exps);
                    continue;
                  }

                for (const auto& [label, dest] : exps)
                  res.insert({label, dest});
              }

            finalize(res, opts, d);
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
  expand_automaton(formula f, bdd_dict_ptr d, exp_opts::expand_opt opts)
  {
    auto finite = expand_finite_automaton(f, d, opts);
    return from_finite(finite);
  }

  struct signature_hash
  {
    std::size_t
    operator() (const std::pair<bool, std::multimap<bdd, formula, bdd_less_than>>& sig) const
    {
      size_t hash = std::hash<bool>()(sig.first);

      for (const auto& keyvalue : sig.second)
        {
          hash ^= (bdd_hash()(keyvalue.first) ^ std::hash<formula>()(keyvalue.second))
            + 0x9e3779b9 + (hash << 6) + (hash >> 2);
        }

      return hash;
    }
  };

  twa_graph_ptr
  expand_finite_automaton(formula f, bdd_dict_ptr d, exp_opts::expand_opt opts)
  {
    bool signature_merge = opts & exp_opts::expand_opt::SignatureMerge;

    auto aut = make_twa_graph(d);

    aut->prop_state_acc(true);
    const auto acc_mark = aut->set_buchi();

    auto formula2state = robin_hood::unordered_map<formula, unsigned>();
    auto signature2state = std::unordered_map<std::pair<bool, expansion_t>, unsigned, signature_hash>();

    unsigned init_state = aut->new_state();
    aut->set_init_state(init_state);
    formula2state.insert({ f, init_state });


    auto f_aps = formula_aps(f);
    for (auto& ap : f_aps)
        aut->register_ap(ap);

    if (signature_merge)
      signature2state.insert({ {f.accepts_eword(), expansion(f, d, aut.get(), opts)}, init_state});


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
          if (signature_merge)
            {
              auto exp = expansion(suffix, d, aut.get(), opts);
              bool accepting = suffix.accepts_eword();
              auto it2 = signature2state.find({accepting, exp});
              if (it2 != signature2state.end())
                {
                  formula2state.insert({suffix, it2->second});
                  return it2->second;
                }
            }

          dst = aut->new_state();
          todo.push_back({suffix, dst});

          formula2state.insert({suffix, dst});
          if (signature_merge)
            signature2state.insert({{suffix.accepts_eword(), expansion(suffix, d, aut.get(), opts)}, dst});

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

    if ((opts & exp_opts::MergeEdges)
        && !(opts & exp_opts::UniqueSuffix))
      aut->merge_edges();

    return aut;
  }
}
