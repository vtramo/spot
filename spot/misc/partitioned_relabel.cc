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
#include <string>
#include <cmath>
#include <cassert>

namespace spot
{
  constexpr bool VERBOSEDBG = true;

  // Private bdd_partition functions
  void
  bdd_partition::comp_new_letters_(const std::string& prefix_new)
  {
    auto& ig = *ig_;
    // Get the new variables and their negations
    const unsigned Nnl = leaves_.size();
    const unsigned Nnv = std::ceil(std::log2(Nnl));
    std::vector<std::array<bdd, 2>> Nv_vec(Nnv);

    new_ap_.reserve(Nnv);
    for (unsigned i = 0; i < Nnv; ++i)
      {
        new_ap_.push_back(formula::ap(prefix_new + std::to_string(i)));
        int v = dict_new_->register_proposition(new_ap_.back(), this);
        Nv_vec[i] = {bdd_nithvar(v), bdd_ithvar(v)};
      }

    // Binary encode an idx using the fresh aps
    auto leaveidx2label = [&](unsigned idx)
      {
        unsigned c = 0;
        unsigned rem = idx;
        bdd thisbdd = bddtrue;
        while (rem)
          {
            thisbdd &= Nv_vec[c][rem & 1];
            ++c;
            rem >>= 1;
          }
        for (; c < Nnv; ++c)
          thisbdd &= Nv_vec[c][0];
        return thisbdd;
      };

    // Compute only labels of leaves
    for (unsigned idx = 0; idx < Nnl; ++idx)
      ig.state_storage(leaves_[idx].second).new_label = leaveidx2label(idx);

    // We will label the implication graph with the new letters
    auto relabel_impl = [&](unsigned s, auto&& relabel_impl_rec)
      {
        auto& ss = ig.state_storage(s);
        if (ss.new_label != bddfalse)
          return ss.new_label;
        else
          {
            assert((ss.succ != 0) && "Should not be a leave");
            bdd thisbdd = bddfalse;
            for (const auto& e : ig.out(s))
              thisbdd |= relabel_impl_rec(e.dst, relabel_impl_rec);
            ss.new_label = thisbdd;
            return thisbdd;
          }
      };

    // We need to call relabel_impl on every root
    for (const auto& r : orig_)
      relabel_impl(r.second, relabel_impl);

  } // comp_new_letters

  // Check if it is still a valid partition
  bool
  bdd_partition::verify_(bool verbose)
  {
    auto& ig = *ig_;
    const unsigned Nl = leaves_.size();

    // All leaves are actual leaves
    auto fake_leaf = std::vector<std::pair<bdd, unsigned>>();
    std::copy_if(leaves_.begin(), leaves_.end(),
                 std::back_inserter(fake_leaf),
                 [&](const auto& p)
                  {
                    return ig.state_storage(p.second).succ != 0;
                  });
    if (!fake_leaf.empty())
      {
        if (verbose)
          {
            std::cerr << "Nodes\n";
            std::for_each(fake_leaf.begin(), fake_leaf.end(),
                          [](const auto& p)
                            {
                              std::cerr << p.first << " : " << p.second
                                        << "; ";
                            });
            std::cerr << "\nhave children despite being marked as leaf.\n";
          }
        return false;
      }

    // Check for leaves not marked as such
    fake_leaf.clear();
    for (unsigned s = 0; s < ig.num_states(); ++s)
      {
        if (std::find_if(leaves_.begin(), leaves_.end(),
              [s](const auto& p){ return p.second == s; })
            != leaves_.end())
          continue; // Already marked as leaf
        auto sd = ig.state_storage(s);
        if (sd.succ == 0)
          fake_leaf.emplace_back(sd.orig_label, s);
      }
    if (!fake_leaf.empty())
      {
        if (verbose)
          {
            std::cerr << "Nodes\n";
            std::for_each(fake_leaf.begin(), fake_leaf.end(),
                          [](const auto& p)
                            {
                              std::cerr << p.first << " : " << p.second
                                        << "; ";
                            });
            std::cerr << "\nhave NO children despite "
                      << "NOT being marked as leaf.\n";
          }
        return false;
      }

    // Check if no intersection
    for (unsigned l1 = 0; l1 < Nl; ++l1)
      {
        const auto& [l1c, l1n] = leaves_[l1];
        if (l1c == bddfalse)
          {
            if (verbose)
              std::cerr << "Encountered false on node " << l1n << '\n';
            return false;
          }
        for (unsigned l2 = l1 + 1; l2 < Nl; ++l2)
          {
            const auto& [l2c, l2n] = leaves_[l2];
            if (bdd_have_common_assignment(l1c, l2c))
              {
                if (verbose)
                  std::cerr << "leaf " << l1n << ": " << l1c
                            << " and leaf " << l2n << ": " << l2c
                            << " intersect.\n";
                return false;
              }
          }
      }

    // Check for completeness
    // All original cond are found
    std::all_of(orig_.cbegin(), orig_.cend(),
        [&](const auto& e)
          {
            bool res = e.first == ig.state_storage(e.second).orig_label;
            if (!res && verbose)
              {
                std::cerr << "Orig condition " << e.first
                          << " was not found at "
                          << e.second
                          << ".\nEncountered "
                          << ig.state_storage(e.second).orig_label
                          << " instead.\n";
              }
            return res;
          });
    // The label of a state (no matter if new or orig)
    // is the disjunction over the children
    if (!std::all_of(all_inter_.cbegin(), all_inter_.cend(),
        [&](const auto& p)
          {
            const auto& sdo = ig.state_storage(p.second);
            if (sdo.orig_label != p.first)
              {
                if (verbose)
                  std::cerr << "Orig labels did not coincide for "
                            << p.second << ":\n"
                            << p.first << "\nvs\n"
                            << sdo.orig_label << '\n';
                return false;
              }
            bdd c_orig = bddfalse;
            bdd c_new = bddfalse;
            for (const auto& e : ig.out(p.second))
              {
                const auto& sdp = ig.state_storage(e.dst);
                c_orig |= sdp.orig_label;
                c_new |= sdp.new_label;
              }
            bool ro = c_orig == sdo.orig_label;
            bool rn = c_new == sdo.new_label;
            if ((c_orig != bddfalse) && !ro)
              {
                if (verbose)
                  std::cerr << "Orig label is not the disjunction over"
                            << "children for "
                            << p.second << ":\n"
                            << sdo.orig_label << "\nvs\n"
                            << c_orig << '\n';
                return false;
              }
            if ((c_new != bddfalse) && !rn)
              {
                if (verbose)
                  std::cerr << "New label is not the disjunction over"
                            << "children for "
                            << p.second << ":\n"
                            << sdo.new_label << "\nvs\n"
                            << c_new << '\n';
                return false;
              }
            return true;
          }))
      return false;

    // Verify the number of parents

    return true;
  } // verify

  std::string
  bdd_partition::to_string_hoa_() const
  {

    auto& ig = *ig_;

    auto m = make_twa_graph(dict_orig_);
    auto& mr = *m;

    for (const auto& ap : orig_ap_)
      mr.register_ap(ap);

    for (const auto& ap : new_ap_)
      mr.register_ap(ap);

    mr.new_states(ig.num_states());

    unsigned init = mr.new_state();
    mr.set_init_state(init);

    // Edge to all initial states
    for (const auto& [_, so] : orig_)
      mr.new_edge(init, so, bddtrue);

    // copy transitions
    for (const auto& e : ig.edges())
      mr.new_edge(e.src, e.dst, bddtrue);

    // Use orig_labels as names
    auto* nvec = new std::vector<std::string>(mr.num_states());

    mr.set_named_prop<std::vector<std::string>>("state-names", nvec);

    for (const auto& [orig_label, s] : all_inter_)
      {
        const auto& sd = ig.state_storage(s);
        std::stringstream ss;
        ss << sd.n_parents << " : " << orig_label;
        (*nvec)[s] = ss.str();
        // Create self-loops with new labels
        mr.new_edge(s, s, sd.new_label);
      }

    std::stringstream ss;
    // Print it
    print_hoa(ss, m);
    ss << '\n';
    return ss.str();
  }

  // Public functions

  bdd_partition&
  bdd_partition::operator=(const bdd_partition& other)
  {
    dict_orig_->unregister_all_my_variables(this);
    if (dict_new_)
      dict_new_->unregister_all_my_variables(this);


    ig_ = std::make_unique<implication_graph>(*other.ig_);
    orig_ = other.orig_;
    dict_orig_ = other.dict_orig_;
    orig_ap_ = other.orig_ap_;
    orig_support_ = other.orig_support_;
    dict_new_ = other.dict_new_;
    new_ap_ = other.new_ap_;
    new_support_ = other.new_support_;
    locked_ = other.locked_;
    leaves_ = other.leaves_;
    all_inter_ = other.all_inter_;

    dict_orig_->register_all_variables_of(&other, this);
    if (dict_new_)
      dict_new_->register_all_variables_of(&other, this);
    return *this;
  }

  bdd_partition&
  bdd_partition::operator=(bdd_partition&& other)
  {
    dict_orig_->unregister_all_my_variables(this);
    if (dict_new_)
      dict_new_->unregister_all_my_variables(this);


    ig_ = std::move(other.ig_);
    orig_ = std::move(other.orig_);
    dict_orig_ = std::move(other.dict_orig_);
    orig_ap_ = std::move(other.orig_ap_);
    orig_support_ = std::move(other.orig_support_);
    dict_new_ = std::move(other.dict_new_);
    new_ap_ = std::move(other.new_ap_);
    new_support_ = std::move(other.new_support_);
    locked_ = std::move(other.locked_);
    leaves_ = std::move(other.leaves_);
    all_inter_ = std::move(other.all_inter_);

    dict_orig_->register_all_variables_of(&other, this);
    if (dict_new_)
      dict_new_->register_all_variables_of(&other, this);

    // Ok even after stealing since it only uses the address
    dict_orig_->unregister_all_my_variables(&other);
    if (dict_new_)
      dict_new_->unregister_all_my_variables(&other);

    return *this;
  }

  void
  bdd_partition::unlock()
  {
    if (!locked_)
      throw std::runtime_error("bdd_partition::unlock(): "
                               "Must be locked before");

    // Remove all new labels from ig
    // Might have been stolen
    if (ig_)
      {
        auto& ig = *ig_;
        for (auto& s : ig.states())
          s.new_label = bddfalse;
      }

    // Erase all new aps
    new_support_ = bddtrue;
    new_ap_.clear();
    // Might have been stolen
    if (dict_new_)
      {
        dict_new_->unregister_all_my_variables(this);
        dict_new_.reset();
      }
    locked_ = false;
  }

  void
  bdd_partition::lock(bdd_dict_ptr dict_new,
                      const std::string& prefix_new)
  {
    if (locked_)
      throw std::runtime_error("Trying to reloc a second time!");

    dict_new_ = std::move(dict_new);

    // Ensure that the prefix_new does not appear in existing APs
    if (std::any_of(orig_ap_.cbegin(), orig_ap_.cend(),
                    [&prefix_new](const auto& e)
                    {return e.ap_name().find(prefix_new)
                        != std::string::npos; }))
      throw std::runtime_error("bdd_partition::lock(): prefix "
                               + prefix_new
                               + " is also a prefix of existing AP.");

    comp_new_letters_(prefix_new);
    locked_ = true;
  }

  std::string
  bdd_partition::to_string(const std::string& type) const
  {
    if (!locked_)
      throw std::runtime_error("bdd_partition::to_string():"
                                " Must be locked!");

    if (type == "hoa")
      return to_string_hoa_();
    else
      throw std::runtime_error("bdd_partition::to_string(): "
                               "Unknown type " + type);

  }

  void
  bdd_partition::remove_one_(const bdd& r)
  {
    auto& ig = *ig_;
    auto it = orig_.find(r);
    if (it == orig_.end())
      {
        std::cerr << "Failed for \n" << r << '\n';
        throw std::runtime_error("bdd_partition::remove_one_():"
                                "Condition to remove was not an original!");
      }

    auto sn = it->second;
    --ig.state_storage(sn).n_parents;
    assert(ig.state_storage(sn).n_parents != -1u);

    orig_.erase(it);
  }

  void
  bdd_partition::tidy_up_()
  {
    // This will build a new "flat" implication graph

    // We only need the old graph and the old (cleaned) original conditions
    // To avoid different results, do not loop over unordered_amp
    auto old_orig
      = std::map<bdd, unsigned, bdd_less_than_stable>(orig_.begin(),
                                                      orig_.end());
    auto old_ig_ptr = std::move(ig_);
    auto old_ig = *old_ig_ptr;
    auto old_leaves = leaves_;

    // Reset
    ig_ = std::make_unique<implication_graph>(2*leaves_.size(),
                                              5*leaves_.size());
    orig_.clear();
    leaves_.clear();
    all_inter_.clear();

    // Create a new flat graph
    std::vector<unsigned> stack;
    auto push = [&stack](unsigned s) -> void
      {
        stack.push_back(s);
      };
    auto pop = [&stack]() -> unsigned
      {
        auto s = stack.back();
        stack.pop_back();
        return s;
      };
    auto is_leaf = [&old_ig](unsigned s) -> bool
      {
        return old_ig.state_storage(s).succ == 0;
      };

    // Leave state number to leaf index
    const unsigned nleaves = old_leaves.size();
    const unsigned norig = old_orig.size();
    auto lns2lidx = std::vector<unsigned>(old_ig.num_states(), -1u);
    for (unsigned idx = 0; idx < nleaves; ++idx)
      lns2lidx[old_leaves[idx].second] = idx;
    // Original condition state to index
    auto os2oidx = std::vector<unsigned>(old_ig.num_states(), -1u);
    {
      unsigned idx = 0;
      for (const auto& [ocond, ostate] : old_orig)
        {
          os2oidx[ostate] = idx;
          ++idx;
        }
    }

    // For each leaf a vector of booleans indicating if it
    // is implied by the orig condition
    auto all_parents
      = std::vector<std::vector<bool>>(nleaves,
                                       std::vector<bool>(norig, false));
    // Also keep track which leaves are used
    auto used_leaves = std::vector<bool>(nleaves, false);

    // Mark
    for (const auto& [ocond, ostate] : old_orig)
      {
        auto oidx = os2oidx[ostate];
        push(ostate);
        while (!stack.empty())
          {
            unsigned s = pop();
            if (is_leaf(s))
              {
                unsigned lidx = lns2lidx[s];
                assert(lidx != -1u);
                used_leaves[lidx] = true;
                all_parents[lidx][oidx] = true;
              }
            else
              {
                for (const auto& e : old_ig.out(s))
                  push(e.dst);
              }
          }
      }

    // Now we can form classes for the leaves
    // Implied originals to index
    auto leaves_classes = std::map<std::vector<bool>, unsigned>();
    // unordered not possible
    auto lidx2lcl = std::vector<unsigned>(nleaves, -1u);
    for (unsigned lidx = 0; lidx < nleaves; ++lidx)
      {
        // There might be unused leaves -> not implied
        // by anyone -> throw away
        if (std::none_of(all_parents[lidx].cbegin(), all_parents[lidx].cend(),
                         [](auto p){return p; }))
          {
            lidx2lcl[lidx] = -2u; // Special marker for unused
            continue;
          }
        auto [it, _] = leaves_classes.emplace(all_parents[lidx],
                                              leaves_classes.size());
        lidx2lcl[lidx] = it->second;
      }
    assert(std::count(lidx2lcl.cbegin(), lidx2lcl.cend(), -1u) == 0);

    // Construct the new graph
    // First all original conditions
    for (const auto& [ocond, ostate] : old_orig)
      {
#ifdef NDEBUG
        auto ns = new_state_(ocond, true, false);
        assert(ns == os2oidx[ostate]);
        (void) ns; // debian-unstable-gcc-coverage marks this as unused
#elif
        new_state_(ocond, true, false);
#endif
      }
    // Now a state for each leaf class whose condition is the disjunction
    // overall class members
    // leaf class index to new state number
    auto lcl2ns = std::vector<unsigned>(leaves_classes.size(), -1u);
    for (const auto& [lc, lcidx] : leaves_classes)
      {
        bdd new_cond = bddfalse;
        for (unsigned lidx = 0; lidx < nleaves; ++lidx)
          if (lidx2lcl[lidx] == lcidx) // This leaf is in the class
            new_cond |= old_leaves[lidx].first;
        // Get the corresponding new state
        unsigned lclns = -1u;
        // Check if the condition already exists
        if (auto it = all_inter_.find(new_cond);
            it != all_inter_.end())
          {
            // Found it
            leaves_.emplace_back(it->first, it->second);
            lclns = it->second;
          }
        else
          // We need to create the state
          // Note: can not be original as it would have been found
          lclns = new_state_(new_cond, false, true);
        lcl2ns[lcidx] = lclns;
      }

    // Now we can construct the transitions
    for (const auto& [lc, lcidx] : leaves_classes)
      {
        assert(std::any_of(lc.cbegin(), lc.cend(), [](auto p){return p; }));

        // lc[i] is true if the state #i corresponds to an implied original
        // oidx is also the state number
        unsigned lclns = lcl2ns[lcidx];
        for (unsigned oidx = 0; oidx < norig; ++oidx)
          if (lc[oidx] && (lclns != oidx)) // Second condition avoids selfloops
            new_edge_(oidx, lclns);
      }
    assert(verify_(VERBOSEDBG));
    // Done
  }

  void
  bdd_partition::add_condition(const bdd& cond)
  {
    if (cond == bddfalse)
      throw std::runtime_error("bdd_partition::add_condition(): bddfalse "
                               "can not be part of the original letters!\n");

    auto& ig = *ig_;

    // Adds the condition to the set of
    // original conditions and enlarges the
    // partition if necessary
    if (auto it = orig_.find(cond); it != orig_.end())
      return; // Nothing to do, the condition already exists

    // Check if it exists as intermediate
    if (auto it = all_inter_.find(cond); it != all_inter_.end())
    {
      // Mark the node as initial; add one to parent
      orig_[cond] = it->second;
      ++ig.state_storage(it->second).n_parents;
      assert(verify_(VERBOSEDBG));
      return;
    }

    // We do actually need to do the work
    // We need to check at the end if it is also a leaf
    unsigned sorig = new_state_(cond, true, false);

    // Loop over all current partition members
    // and check if we need to refine them
    bdd rem = cond;

    const unsigned Nleaves = leaves_.size();
    for (unsigned il = 0; il < Nleaves; ++il)
    {
      assert(leaves_[il].first != bddfalse); // Invariant

      const auto [leave_cond, leave_node] = leaves_[il];
      if (bdd_have_common_assignment(leave_cond, rem))
        {
          bdd propworem = leave_cond - rem;
          bdd inter = leave_cond & rem;
          bdd remwoprop =  rem - leave_cond;

          assert(inter != bddfalse);

          if (propworem == bddfalse)
            {
              // leave_cond is a subset of cond / rem
              // and therefore implies the original letter
              new_edge_(sorig, leave_node);
              assert(inter == leave_cond);
            }
          else
            {
              // They truly intersect
              // Two cases can arise:
              // rem is a subset of prop
              // remwoprop is not empty
              // we need to search
              // if this intersection already exists

              // propworem is not allowed to exist,
              // as leave_node would not be a leave in this case
              assert(!all_inter_.count(propworem));

              // Only implies prop
              // This in not a new leave, it "takes" the place of prop
              unsigned dst_pwor = new_state_(propworem, false, false);
              new_edge_(leave_node, dst_pwor);

              // Implies prop and cond
              auto it_inter = all_inter_.find(inter);
              unsigned dst_inter =
                it_inter == all_inter_.end() ? new_state_(inter, false, true)
                                             : it_inter->second;
              // If cond is a subset of leave_cond, then inter
              // already exists
              new_edge_(leave_node, dst_inter);
              if (dst_inter != sorig)
                new_edge_(sorig, dst_inter); // No self-loops

              // Update the leave (Corresponding now to the
              // prop without rem)
              leaves_[il].first = propworem;
              leaves_[il].second = dst_pwor;
            }
          // Update what remains to be treated
          rem = remwoprop;

          // Check if we have finished treating cond
          if (rem == bddfalse)
            break;

          // Check if remaining condition exists
          if (auto rem_it = all_inter_.find(rem);
              rem_it != all_inter_.end())
            {
              new_edge_(sorig, rem_it->second);
              rem = bddfalse;
              break; // Done
            }
        }
    }
    // Check what remains to be done
    if ((rem != bddfalse) && (rem != cond))
      {
        // A part of cond is not covered by the existing
        // partition -> new leave
        unsigned s_rem = new_state_(rem, false, true);
        new_edge_(sorig, s_rem);
      }
    // Check if the original state is a leaf
    const auto& sdorig = ig.state_storage(sorig);
    if (sdorig.succ == 0)
      {
        // It became a leaf, which can only happen if
        // rem was not modified
        assert((rem == cond) || (rem == bddfalse));
        leaves_.emplace_back(cond, sorig);
      }
    assert(verify_(VERBOSEDBG));
    return;
  }

  relabeling_map
  bdd_partition::to_relabeling_map(bool inverse) const
  {
    // Change to unordered_map?
    relabeling_map res;

    // We need a bdd_dict with both the original
    // and new aps
    // We take the original bdd_dict and
    // register the variables for a fake address
    int dummy_addr = 0;
    //auto thisdict = make_bdd_dict();
    auto& thisdict = dict_orig_;

    for (const auto& ap : orig_ap_)
      thisdict->register_proposition(ap, &dummy_addr);
    for (const auto& ap : new_ap_)
      thisdict->register_proposition(ap, &dummy_addr);

    auto bdd2form = [&thisdict](const bdd& cond)
      {
        return bdd_to_formula(cond, thisdict);
      };

    std::for_each(all_inter_.cbegin(), all_inter_.cend(),
      [&bdd2form, &res, &ig = *this->ig_, inverse](const auto& e)
        {
          const auto& sd = ig.state_storage(e.second);
          if (inverse)
            res[bdd2form(sd.new_label)] = bdd2form(sd.orig_label);
          else
            res[bdd2form(sd.orig_label)] = bdd2form(sd.new_label);

      });

    thisdict->unregister_all_my_variables(&dummy_addr);

    return res;
  }

  bdd_partition
  try_partition_me(bdd_dict_ptr bdd_dict,
                   const std::vector<bdd>& all_cond,
                   const std::vector<formula>& aps,
                   unsigned max_letter)
  {

    auto res = bdd_partition(std::move(bdd_dict), aps, bddfalse,
                             std::max(20u,
                                      (unsigned) (2*all_cond.size())));

    // Try adding conditions one by one
    // Abort if too large
    for (const auto& c : all_cond)
      {
        if (res.size() > max_letter)
          return bdd_partition(res.get_orig_dict(), aps, bddfalse);

        res.add_condition(c);
      }
    return res;
  }

  bdd_partition
  try_partition_me(const twa_graph_ptr& aut, unsigned max_letter)
  {
    auto seen = std::unordered_set<bdd, bdd_hash>();
    seen.reserve(std::max((size_t) 10,
                          (size_t)(0.1*aut->num_edges())));
    for (const auto& e : aut->edges())
      seen.insert(e.cond);

    auto cond = std::vector<bdd>(seen.begin(), seen.end());

    return try_partition_me(aut->get_dict(), cond, aut->ap(), max_letter);
  }

  void
  bdd_partition::remove_condition(const bdd& to_remove)
  {
    if (locked_)
      throw std::runtime_error("bdd_partition::remove_condition(): "
                               "Partition may not be locked!");

    remove_one_(to_remove);
    tidy_up_();
  }

  void
  bdd_partition::remove_condition(const std::vector<bdd>& to_remove)
  {
    if (locked_)
      throw std::runtime_error("bdd_partition::remove_condition(): "
                               "Partition may not be locked!");

    std::for_each(to_remove.begin(), to_remove.end(),
                  [&](const bdd& r){this->remove_one_(r); });
    tidy_up_();
  }
}