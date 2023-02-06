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

#pragma once

#include <map>

#include <bddx.h>

#include <spot/misc/bddlt.hh>
#include <spot/tl/formula.hh>
#include <spot/twa/bdddict.hh>
#include <spot/twa/twagraph.hh>

namespace spot
{
  using expansion_t = std::map<bdd, formula, bdd_less_than>;

  struct exp_opts
  {
    enum expand_opt {
      None = 0,
      Deterministic = 1,
      Basic = 2,
      MergeSuffix = 4,
      Bdd = 8,
    };
  };

  SPOT_API expansion_t
  expansion(formula f, const bdd_dict_ptr& d, void *owner, exp_opts::expand_opt opts);

  SPOT_API formula
  expansion_to_formula(expansion_t e, bdd_dict_ptr& d);

  SPOT_API twa_graph_ptr
  expand_automaton(formula f, bdd_dict_ptr d, exp_opts::expand_opt opts);

  SPOT_API twa_graph_ptr
  expand_finite_automaton(formula f, bdd_dict_ptr d, exp_opts::expand_opt opts);
}
