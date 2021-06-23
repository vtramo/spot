// -*- coding: utf-8 -*-
// Copyright (C) 2018, 2019 Laboratoire de Recherche et Développement de
// l'Epita.
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
#include <deque>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/complement.hh>
#include <spot/twaalgos/ltl2tgba_fm.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/game.hh>
#include <spot/misc/hash.hh>

namespace spot
{
  namespace
  {
    static spot::const_twa_graph_ptr
    translate(formula f, const bdd_dict_ptr& dict)
    {
      return ltl_to_tgba_fm(f, dict);
    }
  }

  bool contains(const_twa_graph_ptr left, const_twa_graph_ptr right)
  {
    return !complement(left)->intersects(right);
  }

  bool contains(const_twa_graph_ptr left, formula right)
  {
    return contains(left, translate(right, left->get_dict()));
  }

  bool contains(formula left, const_twa_graph_ptr right)
  {
    return !translate(formula::Not(left), right->get_dict())->intersects(right);
  }

  bool contains(formula left, formula right)
  {
    return contains(left, translate(right, make_bdd_dict()));
  }

  bool is_mealy_specialization(const_twa_graph_ptr left,
                               const_twa_graph_ptr right,
                               bool verbose)
  {
    auto& spl = get_state_players(left);
    auto& spr = get_state_players(right);

    const unsigned initl = left->get_init_state_number();
    const unsigned initr = right->get_init_state_number();

    if (spl[initl])
      throw std::runtime_error("left: Mealy machine must have an "
                               "environment controlled initial state.");
    if (spr[initr])
      throw std::runtime_error("right: Mealy machine must have an "
                               "environment controlled initial state.");

    auto check_out = [](const const_twa_graph_ptr& aut,
                        const auto& sp)
      {
        for (unsigned s = 0; s < aut->num_states(); ++s)
          if (sp.at(s))
            if (((++aut->out(s).begin()) != aut->out(s).end())
                || (aut->out(s).begin() == aut->out(s).end()))
              {
                std::cerr << "Failed for " << s << '\n';
                return false;
              }

        return true;
      };
    assert(check_out(left, spl) &&
           "Left mealy machine has multiple or no player edges for a state");
    assert(check_out(right, spr) &&
           "Right mealy machine has multiple or no player edges for a state");

    // Get for each env state of right the uncovered input letters
    std::vector<bdd> ucr(right->num_states(), bddtrue);
    const unsigned nsr = right->num_states();
    for (unsigned s = 0; s < nsr; ++s)
      {
        if (spr[s])
          continue;
        for (const auto& e : right->out(s))
          ucr[s] -= e.cond;
      }

    using prod_state = std::pair<unsigned, unsigned>;

    std::unordered_set<prod_state, pair_hash> seen;
    std::deque<prod_state> todo;
    todo.emplace_back(initl, initr);
    seen.emplace(todo.back());

    auto get_p_edge_l = [&](const auto& e_env)
      {return *(left->out(e_env.dst).begin()); };
    auto get_p_edge_r = [&](const auto& e_env)
      {return *(right->out(e_env.dst).begin()); };

    while (!todo.empty())
      {
        const auto [sl, sr] = todo.front();
        todo.pop_front();
        for (const auto& el_env : left->out(sl))
          {
            // check if el_env.cond intersects with the unspecified of
            // sr. If so the sequence is not applicable -> false
            if (bdd_has_common_assignement(ucr[sr], el_env.cond))
              {
                if (verbose)
                  std::cerr << "State " << sl << " of left is not completely"
                            << " covered by " << sr << " of right.\n";
                return false;
              }


            const auto& el_p = get_p_edge_l(el_env);

            for (const auto& er_env : right->out(sr))
              {
                // if they can be taken at the same time, the output
                // of r must implies the one of left
                if (bdd_has_common_assignement(el_env.cond, er_env.cond))
                  {
                    const auto& er_p = get_p_edge_r(er_env);
                    if (!bdd_implies(er_p.cond, el_p.cond))
                      {
                        if (verbose)
                          std::cerr << "left " << el_env.src << " to "
                                    << el_env.dst << " and right "
                                    << er_env.src << " to " << er_env.dst
                                    << " have common letter "
                                    << (el_env.cond & er_env.cond) << " but "
                                    << er_p.cond << " does not imply "
                                    << el_p.cond << std::endl;
                        return false;
                      }


                    // Check if the new dst pair was already visited
                    assert(spl[el_p.src] && !spl[el_p.dst]);
                    assert(spr[er_p.src] && !spr[er_p.dst]);
                    auto [itdst, inserted] = seen.emplace(el_p.dst,
                                                          er_p.dst);
                    if (inserted)
                      todo.push_back(*itdst);
                  }
              }
          }
      }
    return true;
  }

  bool are_equivalent(const_twa_graph_ptr left, const_twa_graph_ptr right)
  {
    // Start with a deterministic automaton at right if possible to
    // avoid a determinization (in case the first containment check
    // fails).
    if (!is_deterministic(right))
      std::swap(left, right);
    return contains(left, right) && contains(right, left);
  }

  bool are_equivalent(const_twa_graph_ptr left, formula right)
  {
    // The first containement check does not involve a
    // complementation, the second might.
    return contains(left, right) && contains(right, left);
  }

  bool are_equivalent(formula left, const_twa_graph_ptr right)
  {
    // The first containement check does not involve a
    // complementation, the second might.
    return contains(right, left) && contains(left, right);
  }

  bool are_equivalent(formula left, formula right)
  {
    return contains(right, left) && contains(left, right);
  }
}
