// -*- coding: utf-8 -*-
// Copyright (C) 2017-2020 Laboratoire de Recherche et Développement
// de l'Epita.
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
#include <spot/twaalgos/split.hh>
#include <spot/misc/minato.hh>
#include <spot/twaalgos/totgba.hh>
#include <spot/misc/bddlt.hh>

#include <algorithm>
#include <map>

namespace spot
{
  twa_graph_ptr split_edges(const const_twa_graph_ptr& aut)
  {
    twa_graph_ptr out = make_twa_graph(aut->get_dict());
    out->copy_acceptance_of(aut);
    out->copy_ap_of(aut);
    out->prop_copy(aut, twa::prop_set::all());
    out->new_states(aut->num_states());
    out->set_init_state(aut->get_init_state_number());

    internal::univ_dest_mapper<twa_graph::graph_t> uniq(out->get_graph());

    bdd all = aut->ap_vars();
    std::map<unsigned, std::pair<unsigned, unsigned>> split_cond;

    for (auto& e: aut->edges())
      {
        bdd cond = e.cond;
        if (cond == bddfalse)
          continue;
        unsigned dst = e.dst;
        if (aut->is_univ_dest(dst))
          {
            auto d = aut->univ_dests(dst);
            dst = uniq.new_univ_dests(d.begin(), d.end());
          }

        auto& [begin, end] = split_cond[cond.id()];
        if (begin == end)
          {
            begin = aut->num_edges();

            while (cond != bddfalse)
              {
                bdd cube = bdd_satoneset(cond, all, bddfalse);
                cond -= cube;
                out->new_edge(e.src, dst, cube, e.acc);
              }

            end = aut->num_edges();
          }
        else
          {
            auto& g = aut->get_graph();
            for (unsigned i = begin; i < end; ++i)
              out->new_edge(e.src, dst, g.edge_storage(i).cond, e.acc);
          }
      }
    return out;
  }
}
