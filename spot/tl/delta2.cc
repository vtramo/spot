// -*- coding: utf-8 -*-
// Copyright (C) by the Spot authors, see the AUTHORS file for details.
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
#include <spot/tl/delta2.hh>
#include <iostream>

namespace spot
{
  namespace
  {
    static formula
    is_F(formula f)
    {
      if (f.is(op::F))
        return f[0];
      if (f.is(op::U) && f[0].is_tt())
        return f[1];
      if (f.is(op::M) && f[1].is_tt())
        return f[0];
      return nullptr;
    }

    static formula
    is_G(formula f)
    {
      if (f.is(op::G))
        return f[0];
      if (f.is(op::R) && f[0].is_ff())
        return f[1];
      if (f.is(op::W) && f[1].is_ff())
        return f[0];
      return nullptr;
    }

    static formula
    is_FG(formula x)
    {
      if (formula f = is_F(x); f)
        return is_G(f);
      return nullptr;
    }

    static formula
    is_GF(formula x)
    {
      if (formula f = is_G(x); f)
        return is_F(f);
      return nullptr;
    }


    static formula
    rewrite_strong_under_weak(formula f)
    {
      // FIXME: Can we replace is_FG/is_GF by is_suspendable?  This
      // isn't straightforward, because stage3 is only looking for
      // FG/GF.
      if (f.is_delta1() || is_FG(f) || is_GF(f))
        return f;
      if (f.is(op::W) || f.is(op::G))
        {
          formula f0 = f[0];
          formula f1 = f.is(op::W) ? f[1] : formula::ff();
          // If φ₁ contains a strong operator (i.e., is not a safety)
          // we have   φ₀ W φ₁ = (φ₀ U φ₁) | G(φ₀)
          if (!f1.is_syntactic_safety())
            {
              formula left = formula::U(f0, f1);
              formula right = formula::G(f0);
              return rewrite_strong_under_weak(formula::Or({left, right}));
            }
          // x[φ₀Uφ₁] W φ₂ =
          //    (GFφ₁ & (x[φ₀Wφ₁] W φ₂)) | x[φ₀Uφ₁] U (φ₂|G(x[false]))
          // x[Fφ₀] W φ₂=  (GFφ₀ & (x[true] W φ₂)) | x[Fφ₀] U (φ₂ | G(x[false]))
          // x[φ₀Mφ₁] W φ₂ =
          //    (GFφ₀ & (x[φ₀Rφ₁] R φ₂)) | x[φ₀Mφ₁] U (φ₂|G(x[false]))
          formula match = nullptr; // (φ₀ U φ₁) once matched
          formula prefix = nullptr; // GF(φ₁)
          auto find_u = [&](formula node, auto&& self) {
            if (!match || match == node)
              {
                if (is_FG(node) || is_GF(node))
                  return node;
                if (node.is(op::U))
                  {
                    if (!match)
                      {
                        match = node;
                        prefix = formula::G(formula::F(match[1]));
                      }
                    return formula::W(node[0], node[1]);
                  }
                else if (node.is(op::M))
                  {
                    if (!match)
                      {
                        match = node;
                        prefix = formula::G(formula::F(match[0]));
                      }
                    return formula::R(node[0], node[1]);
                  }
                else if (node.is(op::F)) // like tt U φ₀
                  {
                    if (!match)
                      {
                        match = node;
                        prefix = formula::G(formula::F(match[0]));
                      }
                    return formula::tt();
                  }
              }
            return node.map(self, self);
          };
          formula g = find_u(f0, find_u);
          if (!match)
            return f;
          assert(!match.is_syntactic_safety());
          auto match_to_false = [&](formula node, auto&& self) {
            if (node == match)
              return formula::ff();
            if (node.is_syntactic_safety())
              return node;
            return node.map(self, self);
          };
          formula ww = rewrite_strong_under_weak(formula::W(g, f1));
          prefix = formula::And({prefix, ww});
          formula gx_false = formula::G(match_to_false(f0, match_to_false));
          formula u_right = formula::U(f0, formula::Or({f1, gx_false}));
          return formula::Or({prefix, rewrite_strong_under_weak(u_right)});
        }
      if (f.is(op::R))
        {
          formula f0 = f[0];
          formula f1 = f[1];
          // If φ₀ contains a strong operator (i.e., is not a safety)
          // we have   φ₀ R φ₁ = (φ₀ M φ₁) | G(φ₁)
          if (!f0.is_syntactic_safety())
            {
              formula left = formula::M(f0, f1);
              formula right = formula::G(f1);
              return rewrite_strong_under_weak(formula::Or({left, right}));
            }
          // φ₀ R x[φ₁Uφ₂]  =
          //    (GFφ₂ & (φ₀ R x[φ₁Wφ₂])) | ((φ₀|G(x[false])) M x[φ₁Uφ₂])
          // φ₀ R x[Fφ₁] = (GFφ₁ & (φ₀ R x[true])) | ((φ₀|G(x[false])) M x[Fφ₁])
          // φ₀ R x[φ₁Mφ₂] =
          //    (GFφ₀ & (φ₀ R x[φ₁Rφ₂])) | ((φ₀|G(x[false])) M x[φ₁Mφ₂])
          formula match = nullptr; // (φ₀ U φ₁) once matched
          formula prefix = nullptr; // GF(φ₁)
          auto find_u = [&](formula node, auto&& self) {
            if (!match || match == node)
              {
                if (is_FG(node) || is_GF(node))
                  return node;
                if (node.is(op::U))
                  {
                    if (!match)
                      {
                        match = node;
                        prefix = formula::G(formula::F(match[1]));
                      }
                    return formula::W(node[0], node[1]);
                  }
                else if (node.is(op::M))
                  {
                    if (!match)
                      {
                        match = node;
                        prefix = formula::G(formula::F(match[0]));
                      }
                    return formula::R(node[0], node[1]);
                  }
                else if (node.is(op::F)) // like tt U φ₀
                  {
                    if (!match)
                      {
                        match = node;
                        prefix = formula::G(formula::F(match[0]));
                      }
                    return formula::tt();
                  }
              }
            return node.map(self, self);
          };
          formula g = find_u(f1, find_u);
          if (!match)
            return f;
          // φ₀ R x[φ₁Uφ₂]  =
          //    (GFφ₂ & (φ₀ R x[φ₁Wφ₂])) | ((φ₀|G(x[false])) M x[φ₁Uφ₂])
          // φ₀ R x[Fφ₁] = (GFφ₁ & (φ₀ R x[true])) | ((φ₀|G(x[false])) M x[Fφ₁])
          // φ₀ R x[φ₁Mφ₂] =
          //    (GFφ₀ & (φ₀ R x[φ₁Rφ₂])) | ((φ₀|G(x[false])) M x[φ₁Mφ₂])
          assert(!match.is_syntactic_safety());
          auto match_to_false = [&](formula node, auto&& self) {
            if (node == match)
              return formula::ff();
            if (node.is_syntactic_safety())
              return node;
            return node.map(self, self);
          };
          formula rw = rewrite_strong_under_weak(formula::R(f0, g));
          prefix = formula::And({prefix, rw});
          formula gx_false = formula::G(match_to_false(f1, match_to_false));
          formula m_right = formula::M(formula::Or({f0, gx_false}), f1);
          return formula::Or({prefix, rewrite_strong_under_weak(m_right)});
        }
      return f.map(rewrite_strong_under_weak);
    }

    // c[susp] = (susp & c[true]) || c[false]
    formula
    fish_inner_suspendable(formula f)
    {
      if (f.is_delta1() || is_FG(f) || is_GF(f))
        return f;
      formula match = nullptr;
      // return c[true], and set match to susp.
      auto find_inner_susp = [&](formula node, auto self)
      {
        if (node.is_delta1())
          {
            return node;
          }
        else if (node.is_eventual() && node.is_universal())
          {
            if (!match)
              {
                // Try to find a deeper suspendable node if it
                // exist, we want to start from the bottom.
                node = node.map(self, self);
                if (!match)
                  match = node;
              }
            if (node == match)
              return formula::tt();
          }
        return node.map(self, self);
      };
      formula c_true = f.map(find_inner_susp, find_inner_susp);
      if (!match)
        return c_true; // == f.

      auto match_to_false = [&](formula node, auto&& self) {
        if (node.is_delta1())
          return node;
        if (node == match)
          return formula::ff();
        return node.map(self, self);
      };
      formula c_false = f.map(match_to_false, match_to_false);
      match = fish_inner_suspendable(match);
      c_true = fish_inner_suspendable(c_true);
      c_false = fish_inner_suspendable(c_false);
      return formula::Or({formula::And({match, c_true}), c_false});
    }

    static formula
    normalize_inside_suspendable(formula f)
    {
      if (f.is_delta1())
        return f;
      if (formula inner = is_GF(f))
        {
          // GF(x[φ₀ W φ₁]) = GF(x[φ₀ U φ₁]) | (FG(φ₀) & GF(x[true])
          // GF(x[φ₀ R φ₁]) = GF(x[φ₀ M φ₁]) | (FG(φ₁) & GF(x[true])
          // GF(x[Gφ₀]) =     GF(x[false]) |   (FG(φ₀) & GF(x[true])
          formula match = nullptr; // (φ₀ W φ₁) once matched
          formula suffix = nullptr; // FG(φ₀)
          auto find_w = [&](formula node, auto&& self) {
            if (!match || match == node)
              {
                if (node.is(op::W))
                  {
                    if (!match)
                      {
                        match = node;
                        suffix = formula::F(formula::G(match[0]));
                      }
                    return formula::U(node[0], node[1]);
                  }
                else if (node.is(op::R))
                  {
                    if (!match)
                      {
                        match = node;
                        suffix = formula::F(formula::G(match[1]));
                      }
                    return formula::M(node[0], node[1]);
                  }
                else if (node.is(op::G)) // like 0 R φ₀
                  {
                    if (!match)
                      {
                        match = node;
                        suffix = formula::F(formula::G(match[0]));
                      }
                    return formula::ff();
                  }
              }
            return node.map(self, self);
          };
          formula res = find_w(inner, find_w);
          if (!match)
            return f;
          // append GF(x[true]) to suffix
          assert(!match.is_syntactic_guarantee());
          auto match_to_true = [&](formula node, auto&& self) {
            if (node == match)
              return formula::tt();
            if (node.is_syntactic_guarantee())
              return node;
            return node.map(self, self);
          };
          suffix = formula::And({suffix,
              f.map(match_to_true, match_to_true)});
          res = formula::Or({formula::G(formula::F(res)), suffix});
          return normalize_inside_suspendable(res);
        }
      else if (formula inner = is_FG(f))
        {
          // FG(x[φ₀ U φ₁]) = (GF(φ₁) & FG(x[φ₀ W φ₁])) | FG(x[false])
          // FG(x[φ₀ M φ₁]) = (GF(φ₀) & FG(x[φ₀ R φ₁])) | FG(x[false])
          // FG(x[Fφ₀]) =     (GF(φ₀) & FG(x[true]))    | FG(x[false])
          formula match = nullptr; // (φ₀ U φ₁) once matched
          formula prefix = nullptr; // GF(φ₁)
          auto find_u = [&](formula node, auto&& self) {
            if (!match || match == node)
              {
                if (node.is(op::U))
                  {
                    if (!match)
                      {
                        match = node;
                        prefix = formula::G(formula::F(match[1]));
                      }
                    return formula::W(node[0], node[1]);
                  }
                else if (node.is(op::M))
                  {
                    if (!match)
                      {
                        match = node;
                        prefix = formula::G(formula::F(match[0]));
                      }
                    return formula::R(node[0], node[1]);
                  }
                else if (node.is(op::F)) // like tt U φ₀
                  {
                    if (!match)
                      {
                        match = node;
                        prefix = formula::G(formula::F(match[0]));
                      }
                    return formula::tt();
                  }
              }
            return node.map(self, self);
          };
          formula res = find_u(inner, find_u);
          if (!match)
            return f;
          res = formula::And({formula::F(formula::G(res)), prefix});
          // append FG(x[false])
          assert(!match.is_syntactic_safety());
          auto match_to_false = [&](formula node, auto&& self) {
            if (node == match)
              return formula::ff();
            if (node.is_syntactic_safety())
              return node;
            return node.map(self, self);
          };
          res = formula::Or({res, f.map(match_to_false, match_to_false)});
          return normalize_inside_suspendable(res);
        }
      return f.map(normalize_inside_suspendable);
    }


    // Dispatch Fun on top-level temporal operators that aren't
    // already in Δ₂ form.
    template<typename Fun>
    static formula
    dispatch(formula f, Fun&& fun)
    {
      if (f.is_delta2())
        return f;
      switch (auto k = f.kind())
        {
        case op::F:
        case op::G:
        case op::U:
        case op::R:
        case op::W:
        case op::M:
          return fun(f);
        case op::EConcat:
        case op::EConcatMarked:
        case op::UConcat:
          // not yet supported
          return formula::binop(k, f[0], dispatch(f[1], fun));
        default:
          break;
        }
      return f.map(dispatch<Fun>, fun);
    }
 }

  formula to_delta2(formula f, tl_simplifier* tls)
  {
    if (f.is_delta2())
      return f;
    bool own_tls = !tls;
    if (own_tls)
      {
        tl_simplifier_options opt(false, false, false,
                                  false, false, false,
                                  false, false, false,
                                  true);
        tls = new tl_simplifier(opt);
      }
    // This will ensure the formula is in NNF, except
    // maybe for the top level operator.
    f = tls->simplify(f);
    // stage 1
    f = dispatch(f, rewrite_strong_under_weak);
    // stage 2
    f = dispatch(f, fish_inner_suspendable);
    // stage 3
    f = dispatch(f, normalize_inside_suspendable);
    // f = tls->simplify(f);
    if (own_tls)
      delete tls;
    return f;
  }
}
