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
#include "spot/twaalgos/given.hh"
#include "spot/twaalgos/translate.hh"
#include "spot/twaalgos/product.hh"
#include "spot/twaalgos/sccinfo.hh"
#include "spot/twaalgos/mask.hh"
#include "spot/twaalgos/stutter.hh"
#include "spot/twaalgos/complement.hh"
#include "spot/misc/minato.hh"

namespace spot
{
  twa_graph_ptr given_here(twa_graph_ptr& aut,
                           const_twa_graph_ptr& fact,
                           given_strategy strat,
                           bool* changed)
  {
    bdd aut_ap = aut->ap_vars();
    auto prod = product(aut, fact);
    product_states& ps_pair =
      *prod->get_named_prop<product_states>("product-states");

    // For each input edge, gather the union of the conditions of all
    // edges of the useful part of the product that used this edge.
    scc_info si(prod, scc_info_options::TRACK_SUCCS);
    unsigned prod_ns = prod->num_states();

    // if aut is incompatible with knowledge, simply return
    // the false automaton.
    if (!si.is_useful_state(prod->get_init_state_number()))
      {
        if (changed)
          *changed = aut->num_edges() != 0;
        aut->set_init_state(aut->new_state());
        aut->purge_dead_states();
        aut->remove_unused_ap();
        aut->prop_state_acc(true);
        aut->prop_terminal(true);
        aut->prop_universal(true);
        aut->prop_complete(false);
        aut->prop_stutter_invariant(true);
        return aut;
      }

    bool changed_ = false; // did we modify the automaton

    if (strat & GIVEN_RESTRICT)
      {
        std::vector<bdd> edge_constraint(aut->edge_vector().size(),
                                         bddfalse);
        for (unsigned ps = 0; ps < prod_ns; ++ps)
          if (si.is_useful_state(ps))
            {
              unsigned aut_src = ps_pair[ps].first;
              for (auto& prod_edge: prod->out(ps))
                if (si.is_useful_state(prod_edge.dst))
                  {
                    unsigned aut_dst = ps_pair[prod_edge.dst].first;
                    for (auto& aut_edge: aut->out(aut_src))
                      if (aut_edge.dst == aut_dst
                          && bdd_implies(prod_edge.cond, aut_edge.cond))
                        edge_constraint[aut->edge_number(aut_edge)]
                          |= bdd_existcomp(prod_edge.cond, aut_ap);
                  }
            }
        for (auto& e: aut->edges())
          {
            bdd nb = e.cond & edge_constraint[aut->edge_number(e)];
            if (e.cond != nb)
              {
                e.cond = nb;
                changed_ = true;
              }
          }
      }
    if (strat & GIVEN_RELAX)
      {
        // Keep track of conditions that an edge is never synchronized
        // with.
        std::vector<bdd> edge_freedom(aut->edge_vector().size(),
                                      bddtrue);
        for (unsigned ps = 0; ps < prod_ns; ++ps)
          {
            auto [aut_src, fact_src] = ps_pair[ps];
            for (auto& aut_edge: aut->out(aut_src))
              {
                unsigned aut_edge_num = aut->edge_number(aut_edge);
                bdd c = edge_freedom[aut_edge_num];
                for (auto& fact_edge: fact->out(fact_src))
                  {
                    if (c == bddfalse)
                      break;
                    c -= bdd_existcomp(fact_edge.cond, aut_ap);
                  }
                edge_freedom[aut_edge_num] = c;
              }
          }
        // replace each e.cond by an irredundant sum-of-products that
        // is between e.cond and e.cond|edge_freedom(e)
        for (auto& e: aut->edges())
          {
            if (e.cond == bddfalse)
              continue;
            bdd freedom = edge_freedom[aut->edge_number(e)];
            bdd max_cond = e.cond | freedom;
            if (max_cond == e.cond)
              continue;
            minato_isop isop(e.cond, max_cond, true);
            bdd res = bddfalse;
            bdd cube = bddfalse;
            while ((cube = isop.next()) != bddfalse)
              res |= cube;
            if (e.cond == res)
              continue;
#ifndef NDEBUG
            bdd sup_orig = bdd_support(e.cond);
            bdd sup_new = bdd_support(max_cond);
            assert(bdd_implies(sup_orig, sup_new));
#endif
            e.cond = res;
            changed_ = true;
          }
      }

    aut->prop_keep({
        true,  // sbacc
        false, // inweak/weak/terminal
        false, // det/semidet/unambig
        !(strat & GIVEN_RELAX), // improve det/semidet/unambig
        false, // complete
        !(strat & (GIVEN_RELAX | GIVEN_RESTRICT)), // stutter
      });
    aut->purge_dead_states();

    if (strat & GIVEN_STUTTER)
      if (!aut->prop_stutter_invariant().is_true())
        {
          auto stut = sl2(closure(aut));
          if (aut->num_states() != stut->num_states()
              || aut->num_edges() != stut->num_edges())
            if (!product(stut, complement(aut))->intersects(fact))
              {
                if (changed)
                  *changed = true;
                stut->prop_stutter_invariant(true);
                return stut;
              }
        }
    if (changed)
      *changed = changed_;
    return aut;
  }

  twa_graph_ptr given(const_twa_graph_ptr& aut,
                      const_twa_graph_ptr& fact,
                      given_strategy strat)
  {
    auto res = make_twa_graph(aut, twa::prop_set::all());
    return given_here(res, fact, strat);
  }

  twa_graph_ptr given_here(twa_graph_ptr& aut,
                           formula fact,
                           given_strategy strat,
                           bool* changed)
  {
    translator trans(aut->get_dict());
    const_twa_graph_ptr aut_fact = trans.run(fact);
    return given_here(aut, aut_fact, strat, changed);
  }

  twa_graph_ptr given(const_twa_graph_ptr& aut,
                       formula fact,
                       given_strategy strat)
  {
    auto res = make_twa_graph(aut, twa::prop_set::all());
    return given_here(res, fact, strat);
  }

}
