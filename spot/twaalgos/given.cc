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
  twa_graph_ptr update_bounds_given_here(twa_graph_ptr& aut,
                                         const_twa_graph_ptr& fact,
                                         bool* changed)
  {
    // If there is no upper bound set, default it to the current
    // condition of each edge (assumed to represent the lower bound).
    std::vector<bdd>* upper =
      aut->get_or_set_named_prop<std::vector<bdd>>("upper-cond");
    unsigned es = aut->edge_vector().size();
    if (upper->empty())
      {
        upper->resize(es);
        for (unsigned e = 1; e < es; ++e)
          (*upper)[e] = aut->edge_storage(e).cond;
      }
    else
      {
        if (es != upper->size())
          throw std::runtime_error("update_bounds_given_here(): upper-cond"
                                   " property does not match the size of "
                                   "the edge vector");
      }

    bdd aut_ap = aut->ap_vars();
    auto prod = product(aut, fact);
    scc_info si(prod, scc_info_options::TRACK_SUCCS);
    unsigned prod_ns = prod->num_states();

    bool changed_ = false; // did we modify the automaton?

    // If aut is incompatible with the knowledge, simply set all
    // lowerbounds to false.
    if (!si.is_useful_state(prod->get_init_state_number()))
      {
        for (auto& e: aut->edges())
          if (e.cond != bddfalse)
            {
              e.cond = bddfalse;
              changed_ = true;
            }
        if (changed)
          *changed = changed_;
        return aut;
      }

    product_states& ps_pair =
      *prod->get_named_prop<product_states>("product-states");

    scc_info sif(fact, scc_info_options::TRACK_SUCCS);

    std::vector<bdd> edge_uses(es, bddfalse);
    std::vector<bdd> edge_nonuses(es, bddtrue);
    for (unsigned ps = 0; ps < prod_ns; ++ps)
      if (si.is_useful_state(ps))
        {
          auto [aut_src, fact_src] = ps_pair[ps];
          for (auto& prod_edge: prod->out(ps))
            if (si.is_useful_state(prod_edge.dst))
              {
                unsigned aut_dst = ps_pair[prod_edge.dst].first;
                for (auto& aut_edge: aut->out(aut_src))
                  if (aut_edge.dst == aut_dst
                      && bdd_implies(prod_edge.cond, aut_edge.cond))
                    edge_uses[aut->edge_number(aut_edge)]
                      |= bdd_existcomp(prod_edge.cond, aut_ap);
              }
          // FIXME: Skip this if fact is complete
          for (auto& aut_edge: aut->out(aut_src))
            {
              unsigned en = aut->edge_number(aut_edge);
              bdd c = edge_nonuses[en];
              // FIXME: cache the following computation for each fact_src.
              for (auto& fact_edge: fact->out(fact_src))
                {
                  if (c == bddfalse)
                    break;
                  if (sif.is_useful_state(fact_edge.dst))
                    c -= bdd_existcomp(fact_edge.cond, aut_ap);
                }
              edge_nonuses[en] = c;
            }
        }

    for (auto& e: aut->edges())
      {
        unsigned en = aut->edge_number(e);
        bdd low = e.cond & edge_uses[en];
        bdd up = (*upper)[en];
        bdd high = up | edge_nonuses[en];
        if (e.cond != low)
          {
            e.cond = low;
            changed_ = true;
          }
        if (up != high)
          {
            (*upper)[en] = high;
            changed_ = true;
          }
      }
    aut->prop_keep({
        true,  // sbacc
        false, // inweak/weak/terminal
        false, // det/semidet/unambig
        true,  // det (of lowerbound) is improved
        false, // complete
        false, // stutter
      });
    return aut;
  }


  twa_graph_ptr bounds_simplify_here(twa_graph_ptr& aut)
  {
    std::vector<bdd>* upper =
      aut->get_named_prop<std::vector<bdd>>("upper-cond");
    if (upper == nullptr)
      throw std::runtime_error
        ("bounds_simplify_here(): property upper-cond not set");

    for (auto& e: aut->edges())
      {
        if (e.cond == bddfalse)
          continue;
        unsigned en = aut->edge_number(e);
        bdd max_cond = (*upper)[en];
        if (e.cond == max_cond)
          continue;
        minato_isop isop(e.cond, max_cond, true);
        bdd res = bddfalse;
        bdd cube = bddfalse;
        while ((cube = isop.next()) != bddfalse)
          res |= cube;
        e.cond = res;
      }
    aut->set_named_prop("upper-cond", nullptr);
    aut->purge_dead_states();
    aut->prop_keep({
        true,  // sbacc
        false, // inweak/weak/terminal
        false, // det/semidet/unambig
        false,
        false, // complete
        false, // stutter
      });
    return aut;
  }

  twa_graph_ptr stutterize_given(twa_graph_ptr& aut,
                                 std::vector<const_twa_graph_ptr>& facts,
                                 bool relax)
  {
    if (aut->prop_stutter_invariant().is_true())
      return aut;
    twa_graph_ptr stut = sl2_inplace(closure(aut));
    stut->prop_stutter_invariant(true);
    // FIXME: detect whether sl2(closure(aut)) modified the automaton.
    // If not, return stut.
    if (aut->num_states() != stut->num_states()
        || aut->num_edges() != stut->num_edges())
      {
        if (relax)
          {
            // If the part added to aut to make it stuttering is
            // outside of some fact, then it's ok to keep it.
            twa_graph_ptr added = product(stut, complement(aut));
            for (const_twa_graph_ptr& fact: facts)
              if (!added->intersects(fact))
                return stut;
            // TODO: It would be nice to have a n-ary intersection test here.
            // add->intersects(fact1*fact2*...*factn) is a stronger
            // test than the above loop.
          }
        else
          {
            twa_graph_ptr neg = complement(aut);
            // ss is the stutter-sensitive part of aut.
            twa_graph_ptr ss =
              product(aut, sl2_inplace(closure(product(stut, neg))));
            for (const_twa_graph_ptr& fact: facts)
              if (!ss->intersects(fact))
                {
                  twa_graph_ptr p = product(aut, complement(ss));
                  p->prop_stutter_invariant(true);
                  return p;
                }
          }
      }
    return aut;
  }

  twa_graph_ptr update_bounds_given(const_twa_graph_ptr& aut,
                                    const_twa_graph_ptr& fact)
  {
    auto res = make_twa_graph(aut, twa::prop_set::all());
    res->copy_named_properties_of(aut);
    return update_bounds_given_here(res, fact);
  }

  twa_graph_ptr update_bounds_given_here(twa_graph_ptr& aut,
                                         formula fact,
                                         bool* changed)
  {
    translator trans(aut->get_dict());
    const_twa_graph_ptr aut_fact = trans.run(fact);
    return update_bounds_given_here(aut, aut_fact, changed);
  }

  twa_graph_ptr update_bounds_given(const_twa_graph_ptr& aut,
                                    formula fact)
  {
    auto res = make_twa_graph(aut, twa::prop_set::all());
    res->copy_named_properties_of(aut);
    return update_bounds_given_here(res, fact);
  }

  twa_graph_ptr bounds_simplify(const_twa_graph_ptr& aut)
  {
    auto res = make_twa_graph(aut, twa::prop_set::all());
    res->copy_named_properties_of(aut);
    return bounds_simplify_here(res);
  }
}
