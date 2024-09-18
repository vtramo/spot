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
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/mcs.hh>
#include <spot/twaalgos/sccinfo.hh>

namespace spot
{
  namespace
  {
    struct mcs_vertex
    {
      // Each vertex is part of a circular doubly-linked list.
      mcs_vertex* prev = nullptr;
      mcs_vertex* next = nullptr;
      // The weight of a vertex, initially 0, is the number of
      // neighbors that already have an MCS-number.  The weight is -1
      // if the vertex itself has an MCS-number.
      int weight = 0;
    };

    struct mcs_data
    {
      std::vector<mcs_vertex> vertex;
      // set is an array of doubly-linked list built using vertex elements
      std::vector<mcs_vertex*> set;

      // Initialy, all n vertices are in set[0]
      mcs_data(unsigned n)
        : vertex(n), set(n, nullptr)
      {
        // make a circular list of everything in vertex
        vertex[0].prev = &vertex[n - 1];
        for (unsigned i = 0; i < n - 1; i++)
          {
            vertex[i].next = &vertex[i + 1];
            vertex[i + 1].prev = &vertex[i];
          }
        vertex[n - 1].next = &vertex[0];
        set[0] = &vertex[0];
      }

      void remove_vertex(unsigned vertex_i, unsigned from_set)
      {
        mcs_vertex* v = &vertex[vertex_i];
        mcs_vertex* prev = v->prev;
        mcs_vertex* next = v->next;
        prev->next = next;
        next->prev = prev;
        if (v == set[from_set])
          set[from_set] = (v == next) ? nullptr : next;
      }

      void insert_vertex(unsigned vertex_i, unsigned to_set)
      {
        mcs_vertex* v = &vertex[vertex_i];
        mcs_vertex* next = set[to_set];
        if (next == nullptr)
          {
            v->prev = v;
            v->next = v;
            set[to_set] = v;
          }
        else
          {
            mcs_vertex* prev = next->prev;
            v->prev = prev;
            v->next = next;
            prev->next = v;
            next->prev = v;
          }
      }

      void increase_vertex_weight(unsigned vertex_i)
      {
        mcs_vertex* v = &vertex[vertex_i];
        if (v->weight >= 0)
          {
            remove_vertex(vertex_i, v->weight);
            ++v->weight;
            insert_vertex(vertex_i, v->weight);
          }
      }

      unsigned select_any_vertex(unsigned from_set)
      {
        mcs_vertex* start = set[from_set];
        assert(start);
        return start - &vertex[0];
      }

      scc_info* si;
      unsigned select_best_vertex_scc(unsigned from_set)
      {
        mcs_vertex* start = set[from_set];
        assert(start);
        assert(si);
        unsigned best = start - &vertex[0];
        unsigned best_scc = si->scc_of(best);
        mcs_vertex* v = start->next;
        while (v != start)
          {
            unsigned i = v - &vertex[0];
            if (si->scc_of(i) > best_scc)
              {
                best = i;
                best_scc = si->scc_of(i);
              }
            v = v->next;
          }
        return best;
      }
    };
  }

  /// \brief Return an ordering of the vertices computed by
  /// a maximum cardinality search.
  ///
  /// Unlike Tarjan's paper \cite tarjan.84.sicomp , where states are
  /// numbered from N to 1, this number the states from 0 to N-1,
  /// starting from the initial state.  The next number is assigned to
  /// a state that maximizes the number of already-numbered neighbors.
  std::vector<unsigned>
  maximum_cardinality_search(const const_twa_graph_ptr& a, mcs_tie_break tie)
  {
    unsigned n = a->num_states();
    mcs_data data(n);

    // We need to compute the neighbors of each state independently of
    // the orientation of the edges.
    std::vector<std::set<unsigned>> neighbors(n);
    for (auto& e: a->edges())
      {
        neighbors[e.src].insert(e.dst);
        neighbors[e.dst].insert(e.src);
      }

    // How to break ties when selecting the next vertex?
    unsigned (mcs_data::* pick_state)(unsigned) = &mcs_data::select_any_vertex;
    if (tie == MCS_TIE_SCC)
      {
        data.si = new scc_info(a, scc_info_options::NONE);
        pick_state = &mcs_data::select_best_vertex_scc;
      }

    std::vector<unsigned> order(n, 0U); // order is α in Tarjan's paper
    unsigned index = 0;              // index is n-i in Tarjan's paper
    int max_weight = 0;         // max_weight is j in Tarjan's paper
    auto number_state = [&](unsigned i)
    {
      order[i] = index++;
      int& w = data.vertex[i].weight;
      data.remove_vertex(i, w);
      w = -1;
      for (unsigned j: neighbors[i])
        data.increase_vertex_weight(j);
      ++max_weight;
    };

    unsigned init = a->get_init_state_number();
    number_state(init);

    while (index < n)
      {
        while (max_weight > 0 && data.set[max_weight] == nullptr)
          --max_weight;
        number_state((data.*pick_state)(max_weight));
      }
    return order;
  }

  twa_graph_ptr
  maximum_cardinality_search_reorder_here(twa_graph_ptr a, mcs_tie_break tie)
  {
    std::vector<unsigned> order = maximum_cardinality_search(a, tie);
    a->defrag_states(order, order.size());
    return a;
  }
}
