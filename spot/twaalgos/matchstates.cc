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



}
