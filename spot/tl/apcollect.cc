// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2014, 2015, 2018, 2023 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
// Copyright (C) 2004, 2005  Laboratoire d'Informatique de Paris 6 (LIP6),
// département Systèmes Répartis Coopératifs (SRC), Université Pierre
// et Marie Curie.
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
#include <spot/tl/apcollect.hh>
#include <spot/twa/twa.hh>
#include <spot/twa/bdddict.hh>

namespace spot
{
  atomic_prop_set create_atomic_prop_set(unsigned n)
  {
    atomic_prop_set res;
    for (unsigned i = 0; i < n; ++i)
      {
        std::ostringstream p;
        p << 'p' << i;
        res.insert(formula::ap(p.str()));
      }
    return res;
  }

  atomic_prop_set*
  atomic_prop_collect(formula f, atomic_prop_set* s)
  {
    if (!s)
      s = new atomic_prop_set;
    f.traverse([&](const formula& f)
               {
                 if (f.is(op::ap))
                   s->insert(f);
                 return false;
               });
    return s;
  }

  bdd
  atomic_prop_collect_as_bdd(formula f, const twa_ptr& a)
  {
    spot::atomic_prop_set aps;
    atomic_prop_collect(f, &aps);
    bdd res = bddtrue;
    for (auto f: aps)
      res &= bdd_ithvar(a->register_ap(f));
    return res;
  }

  atomic_prop_set collect_litterals(formula f)
  {
    atomic_prop_set res;

    // polirity: 0 = negative, 1 = positive, 2 or more = both.
    auto rec = [&res](formula f, unsigned polarity, auto self)
    {
      switch (f.kind())
        {
        case op::ff:
        case op::tt:
        case op::eword:
          return;
        case op::ap:
          if (polarity != 0)
            res.insert(f);
          if (polarity != 1)
            res.insert(formula::Not(f));
          return;
        case op::Not:
        case op::NegClosure:
        case op::NegClosureMarked:
          self(f[0], polarity ^ 1, self);
          return;
        case op::Xor:
        case op::Equiv:
          self(f[0], 2, self);
          self(f[1], 2, self);
          return;
        case op::Implies:
        case op::UConcat:
          self(f[0], polarity ^ 1, self);
          self(f[1], polarity, self);
          return;
        case op::U:
        case op::R:
        case op::W:
        case op::M:
        case op::EConcat:
        case op::EConcatMarked:
          self(f[0], polarity, self);
          self(f[1], polarity, self);
          return;
        case op::X:
        case op::F:
        case op::G:
        case op::Closure:
        case op::Or:
        case op::OrRat:
        case op::And:
        case op::AndRat:
        case op::AndNLM:
        case op::Concat:
        case op::Fusion:
        case op::Star:
        case op::FStar:
        case op::first_match:
        case op::strong_X:
          for (formula c: f)
            self(c, polarity, self);
          return;
        }
    };
    rec(f, 1, rec);
    return res;
  }

}
