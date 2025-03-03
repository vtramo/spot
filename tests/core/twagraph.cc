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
#include <iostream>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/dot.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/tl/defaultenv.hh>

static void f1()
{
  auto d = spot::make_bdd_dict();
  auto tg = make_twa_graph(d);
  bdd p1 = bdd_ithvar(tg->register_ap("p1"));
  bdd p2 = bdd_ithvar(tg->register_ap("p2"));
  tg->acc().add_sets(2);

  for (auto f: tg->ap())
    std::cout << f.ap_name() << '\n';

  auto s1 = tg->new_state();
  auto s2 = tg->new_state();
  auto s3 = tg->new_state();
  tg->new_edge(s1, s1, bddfalse, {});
  tg->new_edge(s1, s2, p1, {});
  tg->new_edge(s1, s3, p2, tg->acc().mark(1));
  tg->new_edge(s2, s3, p1 & p2, tg->acc().mark(0));
  tg->new_edge(s3, s1, p1 | p2, spot::acc_cond::mark_t({0, 1}));
  tg->new_edge(s3, s2, p1 >> p2, {});
  tg->new_edge(s3, s3, bddtrue, spot::acc_cond::mark_t({0, 1}));

  spot::print_dot(std::cout, tg);

  {
    auto i = tg->get_graph().out_iteraser(s3);
    ++i;
    i.erase();
    i.erase();
    assert(!i);
    spot::print_dot(std::cout, tg);
  }

  {
    auto i = tg->get_graph().out_iteraser(s3);
    i.erase();
    assert(!i);
    spot::print_dot(std::cout, tg);
  }

  spot::acc_cond::mark_t all({0, 1});
  tg->new_edge(s3, s1, p1 | p2, all);
  tg->new_edge(s3, s2, p1 >> p2, {});
  tg->new_edge(s3, s1, bddtrue, all);

  std::cerr << tg->num_edges() << '\n';
  assert(tg->num_edges() == 7);

  spot::print_dot(std::cout, tg);
  tg->merge_edges();
  spot::print_dot(std::cout, tg);

  std::cerr << tg->num_edges() << '\n';
  assert(tg->num_edges() == 5);

  // Add enough states so that the state vector is reallocated.
  for (unsigned i = 0; i < 100; ++i)
    tg->new_state();
  spot::print_dot(std::cout, tg);
}

// Test purge with named and highlighted states.
static void f2()
{
  auto

  d = spot::make_bdd_dict();
  auto tg = make_twa_graph(d);

  auto s1 = tg->new_state();
  auto s2 = tg->new_state();
  auto s3 = tg->new_state();
  (void) s2;
  tg->set_named_prop("state-names",
                     new std::vector<std::string>({"s1", "s2", "s3"}));
  {
    auto hs = new std::map<unsigned, unsigned>;
    hs->emplace(s1, 5);
    hs->emplace(s3, 7);
    tg->set_named_prop("highlight-states", hs);
  }
  tg->set_init_state(s3);
  spot::print_dot(std::cout, tg);
  void (*action)(const std::vector<unsigned>&, void*) =
    [](const std::vector<unsigned>& newst, void*)
    {
      for (unsigned i = 0; i != newst.size(); ++i)
        {
          std::cout << i << " -> ";
          if (newst[i] == -1U)
            std::cout << "deleted" << std::endl;
          else
            std::cout << newst[i] << std::endl;
        }
    };
  tg->purge_unreachable_states(&action);
  spot::print_dot(std::cout, tg);
}

// Make sure the HOA printer adjusts the highlighted edges numbers
static void f3()
{
  auto d = spot::make_bdd_dict();
  auto tg = make_twa_graph(d);

  auto hs = new std::map<unsigned, unsigned>;
  tg->set_named_prop("highlight-edges", hs);

  auto s1 = tg->new_state();
  auto s2 = tg->new_state();
  auto s3 = tg->new_state();
  tg->set_init_state(s3);
  hs->emplace(tg->new_edge(s3, s2, bddtrue), 1);
  hs->emplace(tg->new_edge(s2, s1, bddtrue), 2);
  hs->emplace(tg->new_edge(s1, s1, bddtrue), 3);

  spot::print_hoa(std::cout, tg, "1.1") << '\n';
}

// Test creation of universal edges via initializer-list
static void f4()
{
  auto d = spot::make_bdd_dict();
  auto tg = make_twa_graph(d);

  auto s1 = tg->new_state();
  auto s2 = tg->new_state();
  auto s3 = tg->new_state();
  tg->set_univ_init_state({s3, s1});
  tg->new_univ_edge(s3, {s1, s2}, bddtrue);
  tg->new_univ_edge(s2, {s1}, bddtrue);
  tg->new_edge(s1, s1, bddtrue);

  spot::print_hoa(std::cout, tg, "1.1") << '\n';
}

// Test merge_states()
static void f5()
{
  auto d = spot::make_bdd_dict();
  auto tg = make_twa_graph(d);

  auto s1 = tg->new_state();
  auto s2 = tg->new_state();
  auto s3 = tg->new_state();
  auto s4 = tg->new_state();
  auto s5 = tg->new_state();

  tg->set_init_state(s5);
  tg->new_edge(s1, s2, bddtrue);
  tg->new_edge(s2, s2, bddtrue);
  tg->new_edge(s3, s2, bddtrue);
  tg->new_edge(s4, s4, bddtrue);
  tg->new_edge(s5, s1, bddtrue);
  tg->new_edge(s5, s2, bddtrue);
  tg->new_edge(s5, s3, bddtrue);
  tg->new_edge(s5, s4, bddtrue);

  unsigned out = tg->merge_states();
  std::cerr << out << '\n';
  assert(out == 3);
  spot::print_hoa(std::cout, tg) << '\n';
}

// Test merge_states_of()
static void f6()
{
  auto d = spot::make_bdd_dict();
  auto tg = make_twa_graph(d);

  auto s1 = tg->new_state();
  auto s2 = tg->new_state();
  auto s3 = tg->new_state();
  auto s4 = tg->new_state();
  auto s5 = tg->new_state();

  tg->set_init_state(s5);
  tg->new_edge(s1, s2, bddtrue);
  tg->new_edge(s2, s2, bddtrue);
  tg->new_edge(s3, s2, bddtrue);
  tg->new_edge(s4, s4, bddtrue);
  tg->new_edge(s5, s1, bddtrue);
  tg->new_edge(s5, s2, bddtrue);
  tg->new_edge(s5, s3, bddtrue);
  tg->new_edge(s5, s4, bddtrue);

  unsigned out = tg->merge_states_of();
  assert(out == 3);
  (void) out;
}

// Compare merge_states() and merge_states_of()
// when faced with a more involved problem
static void f7()
{
  // The current merge_states implementation of "next"
  // needs two successive calls to obtain an automaton with only 3 states
  // This is especially annoying as this depends on the numbering.
  // By renumbering 2->1 3->2 1->3 the current version only needs one call too
  auto get_aut = []()
    {
      auto d = spot::make_bdd_dict();
      auto aut = make_twa_graph(d);

      aut->new_states(5);

      aut->new_edge(0, 1, bddtrue);
      aut->new_edge(0, 2, bddtrue);

      aut->new_edge(1, 1, bddtrue);
      aut->new_edge(1, 4, bddtrue);

      aut->new_edge(2, 3, bddtrue);
      aut->new_edge(2, 4, bddtrue);

      aut->new_edge(3, 3, bddtrue);
      aut->new_edge(3, 4, bddtrue);

      return aut;
    };

  auto aut = get_aut();
  // Basic merge_states needs 2 iterations
  // Merging only one step each
  assert(aut->merge_states() == 1u);
  assert(aut->merge_states() == 1u);
  assert(aut->num_states() == 3u);

  // merge_states_of can do it in one iteration
  // when used on all states
  aut = get_aut();
  assert(aut->merge_states_of() == 2u);
  assert(aut->num_states() == 3u);
}

int main()
{
  f1();
  f2();
  f3();
  f4();
  f5();
  f6();
  f7();
}
