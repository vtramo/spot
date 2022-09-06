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

#include <vector>

#include <bddx.h>

#include <spot/tl/formula.hh>
#include <spot/twa/bdddict.hh>
#include <spot/twa/twagraph.hh>

namespace spot
{
  /// \ingroup tl_misc
  /// \brief Produce a SERE formula's partial derivative
  SPOT_API formula
  partial_derivation(formula f, const bdd var, const bdd_dict_ptr& d,
                     void* owner);

  SPOT_API twa_graph_ptr
  derive_automaton(formula f, bool deterministic = true);

  SPOT_API twa_graph_ptr
  derive_automaton_with_first(formula f, bdd_dict_ptr bdd_dict,
                              bool deterministic = true);

  SPOT_API twa_graph_ptr
  derive_finite_automaton(formula f, bool deterministic = true);

  SPOT_API twa_graph_ptr
  derive_finite_automaton_with_first(formula f, bdd_dict_ptr bdd_dict,
                                     bool deterministic = true);

  SPOT_API formula
  rewrite_and_nlm(formula f);
}
