// -*- coding: utf-8 -*-
// Copyright (C) 2021 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#include <spot/twa/twagraph.hh>
#include <spot/twacube/twacube.hh>
#include <spot/misc/bddlt.hh>

namespace spot
{
  inline twa_graph_ptr create_twa_from(const const_twa_graph_ptr& a)
  {
    twa_graph_ptr res = make_twa_graph(a->get_dict());
    res->copy_ap_of(a);
    res->copy_acceptance_of(a);
    return res;
  }
  inline twacube_ptr create_twa_from(const const_twacube_ptr& a)
  {
    twacube_ptr res = make_twacube(a->ap());
    res->acc() = a->acc();
    return res;
  }
}
