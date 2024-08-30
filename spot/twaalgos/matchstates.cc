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
#include <spot/twaalgos/matchstates.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/ltl2tgba_fm.hh>
#include <spot/tl/parse.hh>
#include <spot/tl/print.hh>
#include <spot/tl/simplify.hh>

namespace spot
{
  std::vector<std::vector<unsigned>>
  match_states(const const_twa_graph_ptr& aut1,
               const const_twa_graph_ptr& aut2)
  {
    twa_graph_ptr prod = product(aut1, aut2);
    product_states* ps = prod->get_named_prop<product_states>("product-states");
    if (!ps)
      return {};
    scc_info si(prod, scc_info_options::TRACK_SUCCS);

    std::vector<std::vector<unsigned>> v(aut1->num_states());
    unsigned sz = ps->size();
    assert(sz == prod->num_states());
    for (unsigned sp = 0; sp < sz; ++sp)
      if (si.is_useful_state(sp))
        {
          auto [sl, sr] = (*ps)[sp];
          v[sl].push_back(sr);
        }
    return v;
  }

  std::vector<formula>
  match_states(const const_twa_graph_ptr& aut1, formula f)
  {
    twa_graph_ptr aut2 = ltl_to_tgba_fm(f, aut1->get_dict(),
                                        false /* exprop */,
                                        true /* symbolic merge */,
                                        false /* branching postponement */,
                                        false /* fair loop approx. */,
                                        nullptr /* unobs event */,
                                        nullptr /* simplifier */,
                                        false /* unambiguous */,
                                        nullptr /* aborter */,
                                        true /* label with LTL */);
    auto state_names =
      aut2->get_named_prop<std::vector<std::string>>("state-names");
    auto v = match_states(aut1, aut2);
    unsigned sz1 = aut1->num_states();
    unsigned sz2 = aut2->num_states();

    // State are labeled with strings, but we know those strings to
    // represent LTL formulas, so convert those.
    std::vector<formula> state_formulas;
    state_formulas.reserve(sz2);
    for (unsigned i = 0; i < sz2; ++i)
      state_formulas.push_back(parse_formula((*state_names)[i]));

    tl_simplifier tls(tl_simplifier_options(2));

    std::vector<formula> res;
    res.reserve(sz1);

    std::vector<formula> disjuncts;
    for (unsigned i = 0; i < sz1; ++i)
      {
        disjuncts.clear();
        for (unsigned j: v[i])
          disjuncts.push_back(state_formulas[j]);
        res.push_back(tls.simplify(formula::Or(disjuncts)));
      }
    return res;
  }

  void
  match_states_decorate(twa_graph_ptr& aut, formula f)
  {
    std::vector<formula> v = spot::match_states(aut, f);
    auto* n = new std::vector<std::string>;
    n->reserve(v.size());
    for (spot::formula f: v)
      n->push_back(str_psl(f));
    aut->set_named_prop("state-names", n);
  }

}
