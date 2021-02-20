// -*- coding: utf-8 -*-
// Copyright (C) 2019 Laboratoire de Recherche et Développement
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

#include <spot/twacube/twacube.hh>
#include <spot/twa/twagraph.hh>
#include <spot/misc/bddlt.hh>

namespace spot
{
  class twacube;

  template <typename Aut>
  bool twa_merge_edges(Aut& aut)
  {
    auto& g = aut.get_graph();
    g.remove_dead_edges_();

    auto& trans = g.edge_vector();
    unsigned orig_size = trans.size();
    unsigned tend = orig_size;

    // When two transitions have the same (src,colors,dst),
    // we can marge their conds.
    auto merge_conds_and_remove_false = [&]()
    {
      // FIXME twacube: we can merge some case, for exemple:
      // !a&b and !a but not a and c.
    if constexpr(std::is_same<Aut, twacube>::value)
      return;
    else
    {
      g.sort_edges_([](const auto& lhs, const auto& rhs)
      {
        if (lhs.src < rhs.src)
          return true;
        if (lhs.src > rhs.src)
          return false;
        if (lhs.dst < rhs.dst)
          return true;
        if (lhs.dst > rhs.dst)
          return false;
        return lhs.acc < rhs.acc;
        // Do not sort on conditions, we'll merge
        // them.
      });

      unsigned out = 0;
      unsigned in = 1;

      // Skip any leading false edge.
      while (in < tend && trans[in].cond == bddfalse)
        ++in;
      if (in < tend)
        {
          ++out;
          if (out != in)
            trans[out] = trans[in];
          for (++in; in < tend; ++in)
            {
              if (trans[in].cond == bddfalse) // Unusable edge
                continue;
              // Merge edges with the same source, destination, and
              // colors.  (We test the source last, because this is the
              // most likely test to be true as edges are ordered by
              // sources and then destinations.)
              if (trans[out].dst == trans[in].dst
                  && trans[out].acc == trans[in].acc
                  && trans[out].src == trans[in].src)
                {
                  trans[out].cond |= trans[in].cond;
                }
              else
                {
                  ++out;
                  if (in != out)
                    trans[out] = trans[in];
                }
            }
        }
      if (++out != tend)
        {
          tend = out;
            trans.resize(tend);
          }
   }
    };

    // When two transitions have the same (src,cond,dst), we can marge
    // their colors.  This only works for Fin-less acceptance.
    //
    // FIXME: We could should also merge edges when using
    // fin_acceptance, but the rule for Fin sets are different than
    // those for Inf sets, (and we need to be careful if a set is used
    // both as Inf and Fin)
    auto merge_colors = [&]()
    {
      if (tend < 2 || aut.acc().uses_fin_acceptance())
        return;
      g.sort_edges_([&](const auto& lhs, const auto& rhs)
      {
        if (lhs.src < rhs.src)
          return true;
        if (lhs.src > rhs.src)
          return false;
        if (lhs.dst < rhs.dst)
          return true;
        if (lhs.dst > rhs.dst)
          return false;
        if constexpr(std::is_same<Aut, twa_graph>::value)
          {
            bdd_less_than_stable lt;
            return lt(lhs.cond, rhs.cond);
          }
        else
          {
            return aut.get_cubeset().lt(lhs.cube_, rhs.cube_);
          }
          // Do not sort on acceptance, we'll merge them.
    });

      const auto has_same_cond = [&](const auto& e1, const auto& e2)
      {
        if constexpr(std::is_same<Aut, twa_graph>::value)
          return e1.cond.id() == e2.cond.id();
        else
          return aut.get_cubeset().eq(e1.cube_, e2.cube_);
      };

      // Start on the second position and try to merge it into the
      // first one
      unsigned out = 1;
      unsigned in = 2;

      for (; in < tend; ++in)
        {
          // Merge edges with the same source, destination,
          // and conditions.  (We test the source last, for the
          // same reason as above.)
          if (trans[out].dst == trans[in].dst
              && has_same_cond(trans[out], trans[in])
              && trans[out].src == trans[in].src)
            {
              trans[out].acc |= trans[in].acc;
            }
          else
            {
              ++out;
              if (in != out)
                trans[out] = std::move(trans[in]);
            }
        }
      if (++out != tend)
        {
          tend = out;
          trans.resize(tend);
        }
    };

    // These next two lines used to be done in the opposite order in
    // 2.9.x and before.
    //
    // However merging colors first is more likely to
    // make parallel non-deterministic transition disappear.
    //
    // Consider:
    //           (1)--a-{1}--->(2)
    //           (1)--a-{2}--->(2)
    //           (1)--!a-{1}-->(2)
    // If colors are merged first, the first two transitions become one,
    // and the result is more deterministic:
    //           (1)--a-{1,2}->(2)
    //           (1)--!a-{1}-->(2)
    // If conditions were merged first, we would get the following
    // non-deterministic transitions instead:
    //           (1)--1-{1}--->(2)
    //           (1)--a-{2}--->(2)
    merge_colors();
    merge_conds_and_remove_false();

    g.chain_edges_();

    return tend != orig_size;
  }
}
