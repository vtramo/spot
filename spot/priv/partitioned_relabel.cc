// -*- coding: utf-8 -*-
// Copyright (C) 2022 Laboratoire de Recherche
// de l'Epita (LRE).
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

#include <spot/priv/partitioned_relabel.hh>
#include <spot/twaalgos/hoa.hh>

#include <sstream>

void bdd_partition::dump(std::ostream& os) const
{
  if (!ig)
    throw std::runtime_error("bdd_partition::dump(): "
                             "No implication graph available!\n");

  auto& igr = *ig;

  auto m = make_twa_graph(make_bdd_dict());
  auto& mr = *m;

  auto rm = to_relabeling_map(*m);

  mr.new_states(igr.num_states());

  unsigned init = mr.new_state();

  // Edge to all initial states
  for (unsigned s = 0; s < init; ++s)
    mr.new_edge(init, s, bddtrue);

  mr.set_init_state(init);

  // copy transitions
  for (const auto& e : igr.edges())
    mr.new_edge(e.src, e.dst, bddtrue);

  auto* nvec = new std::vector<std::string>(mr.num_states());

  mr.set_named_prop<std::vector<std::string>>("state-names", nvec);

  // Original conditions
  for (unsigned i = 0; i < all_cond_.size(); ++i)
    {
      std::stringstream ss;
      ss << all_cond_[i];
      (*nvec)[i] = ss.str();
    }

  // "letters" of the partition
  for (const auto& p : treated)
    {
      std::stringstream ss;
      ss << p.first;
      (*nvec)[p.second] = ss.str();
    }

  // Letters over new labels
  for (unsigned s = 0; s < igr.num_states(); ++s)
    {
      const auto& sd = igr.state_storage(s);
      if (sd.new_label == bddfalse)
        continue;

      mr.new_edge(s, s, sd.new_label);
    }

  // Print it
  print_hoa(os, m);
}

relabeling_map
bdd_partition::to_relabeling_map(const twa_graph_ptr& for_me) const
{
  assert(for_me && "to_relabeling_map(): Graph is null.\n");
  return to_relabeling_map(*for_me);
}

relabeling_map
bdd_partition::to_relabeling_map(twa_graph& for_me) const
{
  // Change to unordered_map?
  relabeling_map res;

  bdd_dict_ptr bdddict = for_me.get_dict();

  for (const auto& ap : all_orig_ap_)
    for_me.register_ap(ap);

  for (const auto& ap : new_aps)
    for_me.register_ap(ap);

  bool use_inner = ig->state_storage(0).new_label != bddfalse;
  std::vector<bool> doskip
      = use_inner ? std::vector<bool>(ig->num_states(), false)
                  : std::vector<bool>();

  auto bdd2form = [&bdddict](const bdd& cond)
    {
      return bdd_to_formula(cond, bdddict);
    };

  for (const auto& [old_letter, s] : treated)
    {
      std::cout << ig->state_storage(s).new_label << std::endl;
      formula new_letter_form = bdd2form(ig->state_storage(s).new_label);
      assert(res.count(new_letter_form) == 0);
      if (use_inner)
          doskip[s] = true;
      res[new_letter_form] = bdd2form(old_letter);
    }

  if (use_inner)
    {
      // This implies that the split option was false,
      // so we can store further info
      const unsigned Norig = all_cond_.size();

      for (unsigned i = 0; i < Norig; ++i)
        {
          // Internal node -> new ?
          if (doskip[i])
              continue;
          // Leave node -> already exists
          if (ig->state_storage(i).succ == 0)
              continue;
          doskip[i] = true;
          formula new_letter_form
              = bdd2form(ig->state_storage(i).new_label);
#ifdef NDEBUG
          res[new_letter_form] = bdd2form(all_cond_[i]);
#else
          // Check if they are the same
          formula old_form = bdd2form(all_cond_[i]);
          if (res.count(new_letter_form) == 0)
              res[new_letter_form] = old_form;
          else
              assert(res[new_letter_form] == old_form);
#endif
        }
      }
  return res;
}

/// \brief Tries to partition the given condition vector \a all_cond
/// abandons at \a max_letter.
/// \return The corresponding bdd_partition
/// \note A pointer to all_cond is captured internally, it needs
/// to outlive the returned bdd_partition
bdd_partition
try_partition_me(const std::vector<bdd>& all_cond,
                 const std::vector<formula>& ap, unsigned max_letter)
{
  // We create vector that will be succesively filled.
  // Each entry corresponds to a "letter", of the partition
  const size_t Norig = all_cond.size();

  bdd_partition result(all_cond, ap);

  auto& treated = result.treated;
  auto& ig = *result.ig;

  for (unsigned io = 0; io < Norig; ++io)
    {
      bdd cond = all_cond[io];
      const auto Nt = treated.size();
      for (size_t in = 0; in < Nt; ++in)
        {
          if (cond == bddfalse)
            break;
          if (treated[in].first == cond)
            {
              // Found this very condition -> make transition
              ig.new_edge(io, treated[in].second);
              cond = bddfalse;
              break;
            }
          if (bdd_have_common_assignment(treated[in].first, cond))
            {
              bdd inter = treated[in].first & cond;
              // Create two new states
              unsigned ssplit = ig.new_states(2);
              // ssplit becomes the state without the intersection
              // ssplit + 1 becomes the intersection
              // Both of them are implied by the original node,
              // Only inter is implied by the current letter
              ig.new_edge(treated[in].second, ssplit);
              ig.new_edge(treated[in].second, ssplit+1);
              ig.new_edge(io, ssplit+1);
              treated.emplace_back(inter, ssplit+1);
              // Update
              cond -= inter;
              treated[in].first -= inter;
              treated[in].second = ssplit;
              if (treated.size() > max_letter)
                return bdd_partition{};
            }
        }
        if (cond != bddfalse)
          {
            unsigned sc = ig.new_state();
            treated.emplace_back(cond, sc);
            ig.new_edge(io, sc);
          }
    }

  result.relabel_succ = true;
  return result;
}