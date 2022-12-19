// -*- coding: utf-8 -*-
// Copyright (C) 2022 Laboratoire de Recherche de l'Epita.
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
#include <iostream>
#include "spot/priv/partitioned_relabel.hh"

using namespace spot;

void
test_partitioned()
{
  auto g = make_twa_graph(make_bdd_dict());

  bdd a = bdd_ithvar(g->register_ap("a"));
  bdd na = bdd_nithvar(g->register_ap("a"));
  bdd b = bdd_ithvar(g->register_ap("b"));
  bdd nb = bdd_nithvar(g->register_ap("b"));

  std::vector<bdd> all_cond;

  all_cond.push_back(a&b);
  all_cond.push_back(na&nb);

  auto part = try_partition_me(all_cond, g->ap(), -1u);

  part.verify(true);
  part.dump(std::cout);
  std::cout << '\n';
}

void
test_simple1()
{
  auto g = make_twa_graph(make_bdd_dict());

  bdd a = bdd_ithvar(g->register_ap("a"));
  bdd b = bdd_ithvar(g->register_ap("b"));

  std::vector<bdd> all_cond;

  all_cond.push_back(a);
  all_cond.push_back(a&b);

  auto part = try_partition_me(all_cond, g->ap(), -1u);

  part.verify(true);
  part.dump(std::cout);
  std::cout << '\n';

}

void
test_simple2()
{
  auto g = make_twa_graph(make_bdd_dict());

  bdd a = bdd_ithvar(g->register_ap("a"));
  bdd b = bdd_ithvar(g->register_ap("b"));

  std::vector<bdd> all_cond;

  all_cond.push_back(a&b);
  all_cond.push_back(a);

  auto part = try_partition_me(all_cond, g->ap(), -1u);

  part.verify(true);
  part.dump(std::cout);
  std::cout << '\n';
}

void
test_simple3()
{
  auto g = make_twa_graph(make_bdd_dict());

  bdd a = bdd_ithvar(g->register_ap("a"));
  bdd b = bdd_ithvar(g->register_ap("b"));

  std::vector<bdd> all_cond;

  all_cond.push_back(a);
  all_cond.push_back(b);

  auto part = try_partition_me(all_cond, g->ap(), -1u);

  part.verify(true);
  part.dump(std::cout);
  std::cout << '\n';
}


void
test_cascade()
{
  auto g = make_twa_graph(make_bdd_dict());

  std::vector<bdd> all_cond;

  bdd thiscond = bddtrue;
  for (unsigned i = 0; i < 6; ++i)
    {
      bdd a = bdd_ithvar(g->register_ap("i" + std::to_string(i)));
      thiscond &= a;
      all_cond.push_back(thiscond);
    }

  {
    auto part = try_partition_me(all_cond, g->ap(), -1u);

    part.verify(true);
    part.dump(std::cout);
    std::cout << '\n';
  }

  std::reverse(all_cond.begin(), all_cond.end());

  {
    auto part = try_partition_me(all_cond, g->ap(), -1u);

    part.verify(true);
    part.dump(std::cout);
    std::cout << '\n';
  }
}

int main()
{
  test_partitioned();
  test_simple1();
  test_simple2();
  test_simple3();
  test_cascade();
}
