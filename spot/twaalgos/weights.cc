// -*- coding: utf-8 -*-
// Copyright (C) 2017-2018, 2020-2021 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
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

#include <spot/twa/twa.hh>
#include <spot/twaalgos/weights.hh>

namespace spot
{
  void set_weight(twa_graph_ptr twa, unsigned edge, int wt)
  {
    auto weights =
      twa->get_named_prop<std::vector<int>>("weights");
    if (!weights && wt)
    {
      weights = new std::vector<int>;
      twa->set_named_prop("weights", weights);
    }
    if (wt)
    {
      if (weights->size() <= edge)
        weights->resize(edge+1, weights::one);
      (*weights)[edge] = wt;
    }
  }

  int get_weight(const_twa_graph_ptr twa, unsigned edge)
  {
    auto weights =
      twa->get_named_prop<std::vector<int>>("weights");
    if (!weights || weights->size() <= edge)
      return weights::one;
    return (*weights)[edge];
  }

  int get_weight(const_twa_graph_ptr twa, const twa_graph::edge_storage_t& edge)
  {
    auto weights =
      twa->get_named_prop<std::vector<int>>("weights");
     auto idx = twa->get_graph().index_of_edge(edge);
    if (!weights || weights->size() <= idx)
      return weights::one;
    return (*weights)[idx];
  }

}
