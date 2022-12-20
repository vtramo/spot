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

#include <spot/misc/partitioned_relabel.hh>

#include <spot/twaalgos/hoa.hh>
#include <sstream>

void
bdd_partition::dump(std::ostream& os) const
{
  if (!ig)
    throw std::runtime_error("bdd_partition::dump(): "
                             "No implication graph available!\n");

  auto& igr = *ig;

  auto m = make_twa_graph(make_bdd_dict());
  auto& mr = *m;

  for (const auto& ap : all_orig_ap_)
    mr.register_ap(ap);

  for (const auto& ap : new_aps)
    mr.register_ap(ap);

  mr.new_states(igr.num_states());

  unsigned init = mr.new_state();

  // Edge to all initial states
  const unsigned Norig = all_cond_.size();
  for (unsigned s = 0; s < Norig; ++s)
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
  os.put('\n');
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

bool
bdd_partition::verify(bool verbose)
{
  const unsigned Nl = treated.size();

  // Check if no intersection
  for (unsigned l1 = 0; l1 < Nl; ++l1)
    {
      for (unsigned l2 = l1 + 1; l2 < Nl; ++l2)
        {
          if (bdd_have_common_assignment(treated[l1].first, treated[l2].first))
            {
              if (verbose)
                std::cerr << "letter " << l1 << ": " << treated[l1].first
                          << "and letter " << l2 << ": " << treated[l2].first
                          << " intersect.\n";
              return false;
            }
        }
    }

  // Check for completeness
  const unsigned No = all_cond_.size();
  std::unordered_map<unsigned, bdd> node2oldcond;
  node2oldcond.reserve(treated.size());
  std::for_each(treated.cbegin(), treated.cend(),
                [&node2oldcond](const auto& p)
                  {
                    assert(node2oldcond.find(p.second)
                           == node2oldcond.cend());
                    node2oldcond[p.second] = p.first;
                  });

  auto search_leaves
        = [&](unsigned s, auto&& search_leaves_) -> bdd
    {
      if (ig->state_storage(s).succ == 0)
        {
          // Leaf
          return node2oldcond.at(s);
        }
      else
        {
          // Traverse
          bdd full_cond = bddfalse;
          for (const auto& e : ig->out(s))
            full_cond |= search_leaves_(e.dst, search_leaves_);
          return full_cond;
        }
    };

  for (unsigned so = 0; so < No; ++so)
    {
      bdd full_cond = search_leaves(so, search_leaves);
      if (all_cond_[so] != full_cond)
        {
          if (verbose)
            {
              std::cerr << "Orig cond of " << so << " was " << all_cond_[so]
                        << " but obtained " << full_cond << '\n';
              return false;
            }
        }
    }

  // Test all intermediate as well
  for (const auto& p : all_inter_)
    {
      bdd full_cond = search_leaves(p.second, search_leaves);
      if (p.first != full_cond)
        {
          if (verbose)
            {
              std::cerr << "Intermediate cond of " << p.second << " was "
                        << p.first << " but obtained " << full_cond << '\n';
              return false;
            }
        }
    }

  return true;

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
  auto& all_inter = result.all_inter_;

  for (unsigned io = 0; io < Norig; ++io)
    {
      bdd cond = all_cond[io];
      if (cond == bddfalse)
        throw std::runtime_error("try_partition_me(): bddfalse can not "
                                 "be part of the original letters!\n");

      const auto Nt = treated.size();
      for (size_t in = 0; in < Nt; ++in)
        {
          assert(treated[in].first != bddfalse);
          if (cond == bddfalse)
            break;

          // Check if exists
          if (auto cond_it = all_inter.find(cond);
              cond_it != all_inter.end())
            {
              ig.new_edge(io, cond_it->second);
              cond = bddfalse;
              break; // Done
            }

          if (bdd_have_common_assignment(treated[in].first, cond))
            {
              bdd propwocond = treated[in].first - cond;
              bdd inter = treated[in].first & cond;
              bdd condwoprop =  cond - treated[in].first;

              assert(inter != bddfalse);

              if (propwocond == bddfalse)
                {
                  // prop = treated[in].first is a subset of cond
                  // and therefore implies the original letter
                  ig.new_edge(io, treated[in].second);
                  assert(inter == treated[in].first);
                  cond = condwoprop;
                }
              else
                {
                  // They truly intersect and we need to search
                  // if they alreay exist
                  // subsets of current letter should never exist
                  // or the partition precond is violated
                  assert(all_inter.find(propwocond) == all_inter.end());

                  auto inter_it = all_inter.find(inter);

                  // Only implies prop
                  unsigned dst_pwoc = ig.new_state();
                  ig.new_edge(treated[in].second, dst_pwoc);

                  // Implies prop and cond
                  unsigned dst_inter
                    = inter_it == all_inter.cend() ? ig.new_state()
                                                   : inter_it->second;
                  ig.new_edge(treated[in].second, dst_inter);
                  ig.new_edge(io, dst_inter);
                  if (inter_it == all_inter.cend())
                    {
                      all_inter[inter] = dst_inter;
                      treated.emplace_back(inter, dst_inter);
                    }

                  // Update
                  treated[in].first = propwocond;
                  treated[in].second = dst_pwoc;
                  cond = condwoprop;
                }

              if (treated.size() > max_letter)
                return bdd_partition{};
            }
        }
      if (cond != bddfalse)
        {
          unsigned sc = ig.new_state();
          treated.emplace_back(cond, sc);
          ig.new_edge(io, sc);
          all_inter[cond] = sc;
        }
    }

  result.relabel_succ = true;
  //assert(result.verify(true));
  return result;
}