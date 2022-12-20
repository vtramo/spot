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
#include <spot/misc/partitioned_relabel.hh>

using namespace spot;

static void
show(const std::vector<bdd>& all_cond,
     const std::vector<formula>& ap)
{
  auto part = try_partition_me(all_cond, ap, -1u);

  for (const auto& p : part.treated)
    part.ig->state_storage(p.second).new_label = p.first;

  part.dump(std::cout);
  part.verify(true);
}

static void
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

  show(all_cond, g->ap());
}

static void
test_simple1()
{
  auto g = make_twa_graph(make_bdd_dict());

  bdd a = bdd_ithvar(g->register_ap("a"));
  bdd b = bdd_ithvar(g->register_ap("b"));

  std::vector<bdd> all_cond;

  all_cond.push_back(a);
  all_cond.push_back(a&b);

  show(all_cond, g->ap());
}

static void
test_simple2()
{
  auto g = make_twa_graph(make_bdd_dict());

  bdd a = bdd_ithvar(g->register_ap("a"));
  bdd b = bdd_ithvar(g->register_ap("b"));

  std::vector<bdd> all_cond;

  all_cond.push_back(a&b);
  all_cond.push_back(a);

  show(all_cond, g->ap());
}

static void
test_simple3()
{
  auto g = make_twa_graph(make_bdd_dict());

  bdd a = bdd_ithvar(g->register_ap("a"));
  bdd b = bdd_ithvar(g->register_ap("b"));

  std::vector<bdd> all_cond;

  all_cond.push_back(a);
  all_cond.push_back(b);

  auto part = try_partition_me(all_cond, g->ap(), -1u);

  show(all_cond, g->ap());
}


static void
test_cascade(unsigned nap)
{
  auto g = make_twa_graph(make_bdd_dict());

  std::vector<bdd> all_cond;

  bdd thiscond = bddtrue;
  for (unsigned i = 0; i < nap; ++i)
    {
      bdd a = bdd_ithvar(g->register_ap("i" + std::to_string(i)));
      thiscond &= a;
      all_cond.push_back(thiscond);
    }


  show(all_cond, g->ap());

  std::reverse(all_cond.begin(), all_cond.end());

  show(all_cond, g->ap());
}

static void
test_double_cascade(unsigned nap)
{
  auto g = make_twa_graph(make_bdd_dict());

  std::vector<bdd> all_cond;

  bdd thiscond1 = bddtrue;
  bdd thiscond2 = bddtrue;
  for (unsigned i = 0; i < nap; ++i)
    {
      bdd a = bdd_ithvar(g->register_ap("i" + std::to_string(i)));
      bdd na = bdd_nithvar(g->register_ap("i" + std::to_string(i)));

      thiscond1 &= a;
      thiscond2 &= i&1 ? na : a;

      all_cond.push_back(thiscond1);
      all_cond.push_back(thiscond2);
    }


  show(all_cond, g->ap());

  std::reverse(all_cond.begin(), all_cond.end());

  show(all_cond, g->ap());
}

static void
test_bytwo(unsigned nap)
{
  auto g = make_twa_graph(make_bdd_dict());

  std::vector<bdd> all_ap;
  std::vector<bdd> all_nap;

  for (unsigned i = 0; i < nap; ++i)
    {
      all_ap.push_back(bdd_ithvar(g->register_ap("i" + std::to_string(i))));
      all_nap.push_back(bdd_nithvar(g->register_ap("i" + std::to_string(i))));
    }

  bdd thiscond1 = bddfalse;
  bdd thiscond2 = bddfalse;

  std::vector<bdd> all_cond;

  for (unsigned i = 0; i < nap-1; ++i)
    {
      thiscond1 = bdd_or(thiscond1, all_ap[i]&all_ap[i+1]);
      thiscond2
        = bdd_or(thiscond2,
                 (i&1 ? all_ap[i]&all_nap[i+1] : all_ap[i]&all_ap[i+1]));
      all_cond.push_back(thiscond1);
      all_cond.push_back(thiscond2);
    }

  show(all_cond, g->ap());

  std::reverse(all_cond.begin(), all_cond.end());

  show(all_cond, g->ap());
}



int main()
{
  std::cout << "/* Partitioned */\n";
  test_partitioned();
  std::cout << "/* Simple 1 */\n";
  test_simple1();
  std::cout << "/* Simple 2 */\n";
  test_simple2();
  std::cout << "/* Simple 3 */\n";
  test_simple3();
  std::cout << "/* Cascade 3 */\n";
  test_cascade(3);
  std::cout << "/* Cascade 6 */\n";
  test_cascade(6);
  std::cout << "/* Cascade 12 */\n";
  test_cascade(12);
  std::cout << "/* Double Cascade 3 */\n";
  test_double_cascade(3);
  std::cout << "/* Double Cascade 6 */\n";
  test_double_cascade(6);
  std::cout << "/* Double Cascade 11 */\n";
  test_double_cascade(11);
  std::cout << "/* By Two 4 */\n";
  test_bytwo(4);
  std::cout << "/* By Two 6 */\n";
  test_bytwo(6);
  std::cout << "/* By Two 11 */\n";
  test_bytwo(11);
}
