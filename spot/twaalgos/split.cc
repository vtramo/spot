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
#include <unordered_map>
#include <spot/priv/robin_hood.hh>

#include <chrono>

namespace spot
{
//  twa_graph_ptr split_edges(const const_twa_graph_ptr& aut)
//  {
//    twa_graph_ptr out = make_twa_graph(aut->get_dict());
//    out->copy_acceptance_of(aut);
//    out->copy_ap_of(aut);
//    out->prop_copy(aut, twa::prop_set::all());
//    out->new_states(aut->num_states());
//    out->set_init_state(aut->get_init_state_number());
//
//    internal::univ_dest_mapper<twa_graph::graph_t> uniq(out->get_graph());
//
//    bdd all = aut->ap_vars();
//    std::map<unsigned, std::pair<unsigned, unsigned>> split_cond;
//
//    unsigned nfound=0, nmiss=0;
//    auto start = std::chrono::high_resolution_clock::now();
//
//    for (auto& e: aut->edges())
//      {
//        bdd cond = e.cond;
//        if (cond == bddfalse)
//          continue;
//        unsigned dst = e.dst;
//        if (aut->is_univ_dest(dst))
//          {
//            auto d = aut->univ_dests(dst);
//            dst = uniq.new_univ_dests(d.begin(), d.end());
//          }
//
//        auto& [begin, end] = split_cond[cond.id()];
//        if (begin == end)
//          {
//            ++nmiss;
//            begin = aut->num_edges();
//
//            while (cond != bddfalse)
//              {
//                bdd cube = bdd_satoneset(cond, all, bddfalse);
//                cond -= cube;
//                out->new_edge(e.src, dst, cube, e.acc);
//              }
//
//            end = aut->num_edges();
//          }
//        else
//          {
//            ++nfound;
//            auto& g = aut->get_graph();
//            for (unsigned i = begin; i < end; ++i)
//              out->new_edge(e.src, dst, g.edge_storage(i).cond, e.acc);
//          }
//      }
//
//    auto stop = std::chrono::high_resolution_clock::now();
//    std::cerr << nmiss << " " << nfound << "\n"
//              << std::chrono::duration_cast<std::chrono::nanoseconds>(stop-start).count() << "\n";
//    return out;
//  }
//
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
    std::unordered_map<bdd, std::pair<std::pair<unsigned, unsigned>, bdd>,
                       spot::bdd_hash> split_cond;
    split_cond.reserve(aut->num_edges());
//    robin_hood::unordered_map<bdd, std::pair<std::pair<unsigned, unsigned>, bdd>,
//        spot::bdd_hash> split_cond;
//    split_cond.reserve(aut->num_edges());
//    std::map<bdd, std::pair<std::pair<unsigned, unsigned>, bdd>,
//             bdd_less_than> split_cond;

    const unsigned n_inter_safe = 10*bdd_nodecount(all) + 1;
    unsigned nmiss=0, nfound=0, nis=0;
    auto start = std::chrono::high_resolution_clock::now();

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

        do
          {
            auto& [edgelim, nextbdd] = split_cond[cond];

            if (edgelim.first != edgelim.second)
              {
                // Found one!
                ++nfound;
                for (unsigned i = edgelim.first; i < edgelim.second; ++i)
                  out->new_edge(e.src, dst, out->edge_storage(i).cond, e.acc);
                // Update
                cond = nextbdd;
              }
            else
              {
                // Not found -> decompose
                ++nmiss;
                bdd base = cond;
                unsigned n2restart = n_inter_safe;
                edgelim.first = out->num_edges();
                do
                  {
                    bdd cube = bdd_satoneset(cond, all, bddfalse);
                    cond -= cube;
                    out->new_edge(e.src, dst, cube, e.acc);
                    --n2restart;
                  } while( n2restart
                           && (cond != bddfalse)
                           && (split_cond.count(cond) == 0));
                nis += (n2restart == 0);//Artificial restart?
                // Insert this partial sol
                // and continue
                edgelim.second = out->num_edges();
                nextbdd = cond;
              }
          }while(cond != bddfalse);
      }

    auto stop = std::chrono::high_resolution_clock::now();
    std::cerr << nmiss << " " << nfound  << " " << nis << "\n"
              << std::chrono::duration_cast<std::chrono::nanoseconds>(stop-start).count() << "\n";
    return out;
  }
}
