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

#include <spot/misc/escape.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/tl/print.hh>
#include <sstream>
#include <string>
#include <cmath>
#include <cassert>
#include <deque>

namespace
{
  using namespace spot;
  // Implementation of separating and relabeling

  template<bool USE_NEW>
  void
  relabel_no_split_(twa_graph& aut,
                    const unsigned Nt,
                    const std::unordered_map<bdd,
                        unsigned,
                        bdd_hash>& orig_cond,
                    const bdd_partition::implication_graph& ig)
  {
    for (auto& e : aut.edges())
      {
        unsigned ne = aut.edge_number(e);
        if (ne > Nt)
          break; // New edge -> edges are traversed in order
        if (auto itc = orig_cond.find(e.cond);
            itc != orig_cond.end())
          {
            if constexpr (USE_NEW)
              e.cond = ig.state_storage(itc->second).new_label;
            else
              e.cond = ig.state_storage(itc->second).orig_label;
          }
        // else: skipped condition
      }
  }

  template<bool USE_NEW>
  void
  relabel_split_no_sort_(twa_graph& aut,
                         const unsigned Nt,
                         const bdd_partition& bdd_part)
  {
    auto get_label
      = USE_NEW ? [](const implying_iterator& it){return it->new_label; }
                : [](const implying_iterator& it){return it->orig_label; };
    for (auto& e : aut.edges())
      {
        unsigned ne = aut.edge_number(e);
        if (ne > Nt)
          break; // New edge -> edges are traversed in order
        // Relabel this
        // If econd does not exist, the container will be empty
        // and the iterator corresponds to the end iterator
        if (auto impl_it
              = bdd_part.get_set_of(e.cond).begin();
            impl_it)
          {
            // Set first cond
            e.cond = get_label(impl_it);
            ++impl_it;
            // Continue? If so we need a local copy as new_edge might
            // reallocate
            if (impl_it)
              {
                auto ecopy = e;
                for (; impl_it; ++impl_it)
                  aut.new_edge(ecopy.src, ecopy.dst,
                               get_label(impl_it), ecopy.acc);
              }
          }
        // else: skipped condition
      }
  }

  template<bool USE_NEW>
  void
  relabel_split_sort_(twa_graph& aut,
                      const bdd_partition& bdd_part)
  {

    struct split_e
    {
      implying_iterator it;
      twa_graph::edge_storage_t eorig;
      const bdd& get() const noexcept
        {
          SPOT_ASSERT(!!it);
          if constexpr (USE_NEW)
            return it->new_label;
          else
            return it->orig_label;
        }
    };

    auto edge_it = std::vector<split_e>();

    auto repl_edge = std::deque<unsigned>();
    auto used = std::vector<unsigned>();

    auto cmp = [](const split_e& cl, const split_e& cr)
      {
        return bdd_stable_cmp(cl.get(), cr.get());
      };

    for (unsigned s = 0; s < aut.num_states(); ++s)
      {
        assert(edge_it.empty() && repl_edge.empty());
        // Get all concerned edges of this state
        for (const auto& e: aut.out(s))
          {
            if (auto impl_it = bdd_part.get_set_of(e.cond).begin();
                impl_it)
              {
                repl_edge.push_back(aut.edge_number(e));
                edge_it.push_back({impl_it, e});
              }
          }
        auto new_edge = [&](unsigned dst,
                            const bdd& cond,
                            acc_cond::mark_t acc)
          {
            if (repl_edge.empty())
              // Create the new edge
              aut.new_edge(s, dst, cond, acc);
            else
              {
                unsigned eidx = repl_edge.front();
                repl_edge.pop_front();
                auto& e = aut.edge_storage(eidx);
                e.dst = dst;
                e.cond = cond;
                e.acc = acc;
              }
          };
      // Now replace them
      while (!edge_it.empty())
        {
          // Check that all still present are not empty
          assert(std::all_of(edge_it.cbegin(), edge_it.cend(),
                             [](const auto& er) -> bool {return er.it; }));
          unsigned c_idx = 0;
          unsigned m_idx = edge_it.size();
          unsigned smallest_idx = 0;
          used.clear();
          used.push_back(c_idx);
          ++c_idx;
          for (; c_idx < m_idx; ++c_idx)
            {
              int res = cmp(edge_it[c_idx], edge_it[smallest_idx]);
              if (res > 0)
                continue; // Larger -> ignored
              else if (res == 0)
                used.push_back(c_idx); // Same -> use as well
              else
                {
                  // Smaller -> use this and ignore other
                  smallest_idx = c_idx;
                  used.clear();
                  used.push_back(c_idx);
                }
          }

        // Replace and advance
        // All split_e that are marked as used need to get
        // new edges and advance
        // If an iterator becomes empty -> erase it
        // For this we iterate in reverse order,
        // as not to change smaller idx
        for (auto uit = used.crbegin(); uit != used.crend(); ++uit)
          {
            // Use and advance
            {
              auto& se = edge_it[*uit];
              new_edge(se.eorig.dst, se.get(), se.eorig.acc);
              ++se.it;
            }
            // Delete?
            if (!edge_it[*uit].it)
              {
                if (edge_it.size() >= 2)
                  edge_it[*uit] = edge_it.back();
                edge_it.pop_back();
              }
          }
      }
    }
  }

  template<bool USE_NEW>
  void relabel_or_sep_impl_(const bdd_partition& bdd_part,
                            twa_graph& aut,
                            bool sorted, bool split)
  {
    if (bdd_part.get_dict() != aut.get_dict())
      throw std::runtime_error("During partitioned relabeling: "
                               "bdd_partition and aut need to use the same "
                               "bdd_dict!");
    if (USE_NEW && ((bdd_part.leaves().size() > 1)
                && (bdd_part.new_ap_vars() == bddtrue
                    || bdd_part.new_ap_vars() == bddfalse)))
      throw std::runtime_error("During partitioned relabeling: "
                               "Relabeling not possible, locked with "
                               "empty prefix?");

    // Unregister old aps and register new ones
    {
      bdd oldap = bdd_part.orig_ap_vars();
      while (oldap != bddtrue)
        {
          int v = bdd_var(oldap);
          aut.unregister_ap(v);
          oldap = bdd_high(oldap);
        }
    }
    {
      const auto& bmap = bdd_part.get_dict()->bdd_map;
      bdd newap = bdd_part.new_ap_vars();
      while (newap != bddtrue)
        {
          int v = bdd_var(newap);
          aut.register_ap(bmap[v].f);
          newap = bdd_high(newap);
        }
    }

    // An original condition is represented by either
    // The new label: split == false
    // The disjunction over all leaves implying it
    // In this case a new edge is created for each leave
    const auto& ig = bdd_part.get_graph();
    // Edges are only appended, never reused
    const unsigned Nt = aut.edge_vector().size();

    // Loop over all edges, check if the condition appears
    // in orig_conditions, if so it needs
    // to be replaced, skipped otherwise
    const auto& orig_conditions = bdd_part.orig_conditions();
    if (split)
      {
        if (sorted)
          relabel_split_sort_<USE_NEW>(aut, bdd_part);
        else
          relabel_split_no_sort_<USE_NEW>(aut, Nt, bdd_part);
      }
    else
      {
        assert(USE_NEW && "No split plus old label gives the "
                          "original automaton!");
        relabel_no_split_<USE_NEW>(aut, Nt, orig_conditions, ig);
      }
  }
}

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

    new_support_ = bddtrue;
    for (unsigned i = 0; i < Nnv; ++i)
      {
        auto new_ap = formula::ap(prefix_new + std::to_string(i));
        int v = dict_->register_proposition(new_ap, this);
        Nv_vec[i] = {bdd_nithvar(v), bdd_ithvar(v)};
        new_support_ &= Nv_vec[i][1];
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
    // We need to sort the root in order to keep results consistent
    auto orig_sorted
      = std::vector<std::pair<bdd, unsigned>>(orig_.cbegin(), orig_.cend());

    std::sort(orig_sorted.begin(), orig_sorted.end(),
              [](const auto& l, const auto& r)
                {return bdd_less_than_stable()(l.first, r.first); });

    for (const auto& r : orig_sorted)
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
    if (!std::all_of(orig_.cbegin(), orig_.cend(),
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
           }))
      return false;
    // The label of a state (no matter if new or orig)
    // is the disjunction over the children
    if (!std::all_of(all_cond_.cbegin(), all_cond_.cend(),
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

    auto m = make_twa_graph(dict_);
    auto& mr = *m;

    for (const auto& ap : orig_ap())
      mr.register_ap(ap);

    for (const auto& ap : new_ap())
      mr.register_ap(ap);

    mr.new_states(ig.num_states());

    unsigned init = mr.new_state();
    mr.set_init_state(init);

    // Edge to all initial states
    auto orig_sorted = std::vector<std::pair<bdd, unsigned>>(orig_.cbegin(),
                                                        orig_.cend());
    std::sort(orig_sorted.begin(), orig_sorted.end(),
              [](const auto& l, const auto& r)
                {return l.second < r.second; });
    for (const auto& [_, so] : orig_sorted)
      {
        (void) _;
        mr.new_edge(init, so, bddtrue);
      }
    // copy transitions
    for (const auto& e : ig.edges())
      mr.new_edge(e.src, e.dst, bddtrue);

    // Use orig_labels as names
    auto* nvec = new std::vector<std::string>(mr.num_states());

    mr.set_named_prop<std::vector<std::string>>("state-names", nvec);

    auto bdd2str = [bdddict = get_dict()](const bdd& cond)
      {
        auto f =  bdd_to_formula(cond, bdddict);
        std::string s = str_psl(f);
        if (s.size() > 2048)
          s = "(label too long)";
        return s;
      };

    for (const auto& [orig_label, s] : all_cond_)
      {
        const auto& sd = ig.state_storage(s);
        std::stringstream ss;
        ss << sd.n_parents << " : " << bdd2str(orig_label);
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
    // Release those of this
    if (dict_)
      dict_->unregister_all_my_variables(this);

    // Assign
    ig_ = std::make_unique<implication_graph>(*other.ig_);
    orig_ = other.orig_;
    dict_ = other.dict_;
    orig_support_ = other.orig_support_;
    orig_is_dyn_ = other.orig_is_dyn_;
    new_support_ = other.new_support_;
    locked_ = other.locked_;
    sorted_ = other.sorted_;
    leaves_ = other.leaves_;
    all_cond_ = other.all_cond_;

    // Register those of other
    if (dict_)
      dict_->register_all_variables_of(&other, this);
    return *this;
  }

  bdd_partition&
  bdd_partition::operator=(bdd_partition&& other)
  {
    // Release those of this
    if (dict_)
      dict_->unregister_all_my_variables(this);

    // Assign
    ig_ = std::move(other.ig_);
    orig_ = std::move(other.orig_);
    dict_ = std::move(other.dict_);
    orig_support_ = other.orig_support_;
    orig_is_dyn_ = other.orig_is_dyn_;
    new_support_ = std::move(other.new_support_);
    locked_ = other.locked_;
    sorted_ = other.sorted_;
    leaves_ = std::move(other.leaves_);
    all_cond_ = std::move(other.all_cond_);

    if (dict_)
      {
        dict_->register_all_variables_of(&other, this);
      // Ok even after stealing since it only uses the address
        dict_->unregister_all_my_variables(&other);
      }

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

    // Erase all new aps (and only new aps)
    while (new_support_ != bddtrue)
      {
        int var = bdd_var(new_support_);
        dict_->unregister_variable(var, this);
        new_support_ = bdd_high(new_support_);
      }

    locked_ = false;
  }

  void
  bdd_partition::lock(const std::string& prefix_new,
                      bool sort)
  {
    if (!dict_)
      throw std::runtime_error("bdd_partition::lock() No "
                               "dict found!");
    if (locked_)
      throw std::runtime_error("Trying to lock a second time!");
    sorted_ = sort;

    // Ensure that the prefix_new does not appear in existing original APs
    if (!prefix_new.empty())
      {
        bdd os = orig_support_;
        const auto bmap = dict_->bdd_map;
        while (os != bddtrue)
          {
            int var = bdd_var(os);
            if (bmap[var].f.ap_name().find(prefix_new) == 0)
              throw std::runtime_error("bdd_partition::lock(): given prefix "
                                       "is also a prefix of existing AP.\n"
                                       "Given: " + prefix_new + '\n' +
                                       "Found: "
                                       + bmap[var].f.ap_name() + '\n');
            os = bdd_high(os);
          }
      }

    if (sort)
      flatten_();  // todo check if better to sort tree

    // Compute new letters only if prefix is non-empty
    if (!prefix_new.empty())
      comp_new_letters_(prefix_new);

    locked_ = true;

    if (!sort)
      return;  // Done

    // This only works if flattened
    if (sort && prefix_new.empty())
      {
        ig_->sort_edges_srcfirst_(
          [&ig=*ig_](const auto& e1, const auto& e2){
              assert(&e1 == &e2
                     || ig.state_storage(e1.dst).orig_label
                        != ig.state_storage(e2.dst).orig_label);
              return bdd_less_than_stable()(
                  ig.state_storage(e1.dst).orig_label,
                  ig.state_storage(e2.dst).orig_label); });
        ig_->chain_edges_();
      }
    else if (sort)
      {
        ig_->sort_edges_srcfirst_(
          [&ig=*ig_](const auto& e1, const auto& e2){
              assert(&e1 == &e2
                     || ig.state_storage(e1.dst).new_label
                        != ig.state_storage(e2.dst).new_label);
              return bdd_less_than_stable()(
                  ig.state_storage(e1.dst).new_label,
                  ig.state_storage(e2.dst).new_label); });
        ig_->chain_edges_();
      }

    return;  // Done with sorting
  }

  void
  bdd_partition::lock()
  {
    if (!dict_)
      throw std::runtime_error("bdd_partition::lock() No "
                               "dict found!");
    return lock("__nv", true);
  }

  std::string
  bdd_partition::to_str(const std::string& type) const
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

    // Being an original condition counts as having one parent
    // Delete the orig condition r might cause the state to be
    // superfluous but this is not always the case
    auto sn = it->second;
    --ig.state_storage(sn).n_parents;
    assert(ig.state_storage(sn).n_parents != -1u);

    orig_.erase(it);
  }

  void
  bdd_partition::flatten_()
  {
    // This will build a new "flat" implication graph
    // The difference with tidy_up_ is that this
    // function supposes that the graph is minimal
    // and will not seek to merge nodes -> easier

    // Only works if unlocked
    if (locked_)
      throw std::runtime_error("bdd_partition::flatten_(): "
                               "Can only be called if unlocked.");

    // We only need the old graph and the old (cleaned) original conditions
    // To avoid different results, do not loop over unordered_amp
    auto old_ig_ptr = std::move(ig_);
    auto old_ig = *old_ig_ptr;
    auto old_orig = orig_;

    // Reset
    ig_ = std::make_unique<implication_graph>(2*leaves_.size(),
                                              5*leaves_.size());
    // orig and leaves has the same conditions, only the
    // associated states change
    auto orig_sorted = std::vector<bdd>();
    orig_sorted.reserve(orig_.size());
    std::transform(orig_.cbegin(), orig_.cend(),
                   std::back_inserter(orig_sorted),
                   [](const auto& p){return p.first; });
    std::sort(orig_sorted.begin(), orig_sorted.end(),
              [](const bdd& l, const bdd& r){
                return bdd_less_than_stable()(l, r); });

    all_cond_.clear();
    all_cond_.reserve(orig_.size() + leaves_.size());

    // Create all nodes
    // First original conditions
    // As this does not remove nodes, the support stays the same
    for (const bdd& oc : orig_sorted)
      {
        unsigned s = new_state_(oc, false, false);
        ig_->state_storage(s).n_parents = 1;
        orig_[oc] = s;
      }
    // Now the leaves
    // A root can also be a leave
    for (auto it = leaves_.begin(); it != leaves_.end(); ++it)
      {
        if (auto itc = all_cond_.find(it->first);
            itc != all_cond_.end())
          it->second = itc->second;
        else
          // condition is already in leaves, update state
          it->second = new_state_(it->first, false, false);
      }

    // Loop over all original conditions and set the implications
    auto set_impl_ = [&](unsigned nstate,
                         unsigned ostate, auto&& set_impl_rec_) -> void
      {
        auto& oss = old_ig.state_storage(ostate);
        if (oss.succ == 0)
          new_edge_(nstate, all_cond_.at(oss.orig_label)); // Found a leaf
        else
          {
            for (const auto& e : old_ig.out(ostate))
              set_impl_rec_(nstate, e.dst, set_impl_rec_);
          }
      };

    for (const bdd& oc : orig_sorted)
      {
        unsigned ostate = old_orig[oc];
        // Only necessary if there are children
        if (old_ig.state_storage(ostate).succ != 0u)
          {
            auto nstate = orig_.at(oc);
            set_impl_(nstate, ostate, set_impl_);
          }
      }
    assert(verify_(VERBOSEDBG));
    // Done
  }

  void
  bdd_partition::tidy_up_()
  {
    // This will tidy-up the data structure, that is delete all
    // useless nodes and update the support
    if (locked_)
      throw std::runtime_error("bdd_partition::tidy_up_(): "
                               "Can only be called if unlocked.");

    bdd old_orig_sup = orig_support_;

    // The idea is the following:
    // The only things strictly needed are the original conditions
    // and the leaves.
    // However, it can be that leaves can be merged as they
    // implie the exact same set of original conditions.

    // We only need the old graph and the old (cleaned) original conditions
    // To avoid different results, do not loop over unordered_amp
    auto old_orig
      = std::vector<std::pair<bdd, unsigned>>(orig_.cbegin(),
                                              orig_.cend());
    // We need to sort it for consistent results
    std::sort(old_orig.begin(), old_orig.end(),
              [](const auto& l, const auto& r)
                {return bdd_less_than_stable()(l.first, r.first); });

    auto old_ig_ptr = std::move(ig_);
    auto old_ig = *old_ig_ptr;
    auto old_leaves = leaves_;

    // Reset
    ig_ = std::make_unique<implication_graph>(2*leaves_.size(),
                                              5*leaves_.size());
    // The original conditions persist
    // However leaves_ and all_cond_ can change
    leaves_.clear();
    all_cond_.clear();

    // Create a new flat graph

    // Leave state number to leaf index
    const unsigned nleaves = old_leaves.size();
    const unsigned norig = old_orig.size();
    // Old state number to index of leaf
    // leaf old state 2 leaf index: los2lidx
    auto los2lidx = std::vector<unsigned>(old_ig.num_states(), -1u);
    for (unsigned idx = 0; idx < nleaves; ++idx)
      los2lidx[old_leaves[idx].second] = idx;

    // Original condition state to index
    // original condition old state 2 orignal cond index
    auto oos2oidx = std::vector<unsigned>(old_ig.num_states(), -1u);
    for (unsigned idx = 0; idx < norig; ++idx)
      oos2oidx[old_orig[idx].second] = idx;

    // For each leaf a vector of booleans indicating if it
    // implies the orig condition
    auto all_parents
      = std::vector<std::vector<bool>>(nleaves,
                                       std::vector<bool>(norig, false));
    // Also keep track which leaves are used
    auto used_leaves = std::vector<bool>(nleaves, false);

    // Mark
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
    for (const auto& [ocond, ostate] : old_orig)
      {
        assert(stack.empty());
        (void) ocond;
        auto oidx = oos2oidx[ostate];
        push(ostate);
        while (!stack.empty())
          {
            unsigned s = pop();
            if (is_leaf(s))
              {
                unsigned lidx = los2lidx[s];
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
    // implied by the exact same originals
    // We will construct the corresponding condition as well
    auto leaves_classes
      = std::map<std::vector<bool>, bdd>();
    // unordered not possible due to reordering issues
    for (unsigned lidx = 0; lidx < nleaves; ++lidx)
      {
        // There might be unused leaves -> not implied
        // by anyone -> throw away
        if (std::none_of(all_parents[lidx].cbegin(), all_parents[lidx].cend(),
                         [](auto p){return p; }))
          continue;

        auto p
          = leaves_classes.emplace(all_parents[lidx], bddfalse);
        // Update condition
        p.first->second |= old_leaves[lidx].first;
      }

    // Construct the new graph
    // First all original conditions
    // Also construct the new support if dynamic
    if (orig_is_dyn_)
      orig_support_ = bddtrue;
    for (auto& p : old_orig)
      {
        // We no longer need old_orig and by updating
        // the state we do not need to perform a lookup later
        p.second = new_state_(p.first, false, false);
        ig_->state_storage(p.second).n_parents = 1;
        // Also update orig_ as it still holds the old values
        orig_[p.first] = p.second;
        if (orig_is_dyn_)
          orig_support_ &= bdd_support(p.first);
      }
    // If dynamic, unregister all aps that are no longer in the support
    if (orig_is_dyn_)
      {
        bdd removedap = bdd_exist(old_orig_sup, orig_support_);
        while (removedap != bddtrue)
          {
            int v = bdd_var(removedap);
            dict_->unregister_variable(v, this);
            removedap = bdd_high(removedap);
          }
      }
    // Now create the leaves and connect them
    for (const auto& p : leaves_classes)
      {
        // The only chance that it might already exist is
        // if it is also an orig. condition
        unsigned ns = -1u;
        if (auto it = orig_.find(p.second); it != orig_.end())
          {
            // Add it to leaves, no connections to be made
            leaves_.emplace_back(it->first, it->second);
            ns = it->second;
          }
        else
          ns = new_state_(p.second, false, true);

        // Loop over all orig conditions
        for (unsigned ostate = 0; ostate < norig; ++ostate)
          if (p.first[ostate] && (ostate != ns))
            new_edge_(ostate, ns);
      }

    assert(verify_(VERBOSEDBG));
    // Done
  }

  std::vector<formula>
  bdd_partition::get_vec_(bdd cond) const
  {
    auto new_ap = std::vector<formula>();
    const auto& bmap = dict_->bdd_map;
    while (cond != bddtrue)
      {
        int v = bdd_var(cond);
        new_ap.push_back(bmap[v].f);
        cond = bdd_high(cond);
      }
    return new_ap;
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
    if (auto it = all_cond_.find(cond); it != all_cond_.end())
    {
      // Mark the node as initial; add one to parent
      orig_[cond] = it->second;
      ++ig.state_storage(it->second).n_parents;
      assert(verify_(VERBOSEDBG));
      return;
    }

    // We do actually need to do the work
    if (orig_is_dyn_)
      {
        bdd cond_sup = bdd_support(cond);
        bdd missing_sup = bdd_exist(cond_sup, orig_support_);
        if (missing_sup != bddtrue)
        {
          // There are elements currently not covered
          // Add to support
          orig_support_ &= missing_sup;
          auto& bmap = dict_->bdd_map;
          // Register
          while (missing_sup != bddtrue)
          {
            int var = bdd_var(missing_sup);
            dict_->register_proposition(bmap[var].f, this);
            missing_sup = bdd_high(missing_sup);
          }
        }
      }
    else
    {
      assert(bdd_exist(cond, orig_support_) == bddtrue
                       && "Condition not covered by given support!");
    }
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
              assert(!all_cond_.count(propworem));

              // Only implies prop
              // This in not a new leave, it "takes" the place of prop
              unsigned dst_pwor = new_state_(propworem, false, false);
              new_edge_(leave_node, dst_pwor);

              // Implies prop and cond
              auto it_inter = all_cond_.find(inter);
              unsigned dst_inter =
                it_inter == all_cond_.end() ? new_state_(inter, false, true)
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
          if (auto rem_it = all_cond_.find(rem);
              rem_it != all_cond_.end())
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

  implying_container
  bdd_partition::get_set_of(const bdd& ocond) const
  {
    if (!locked_)
      throw std::runtime_error("bdd_partition::get_set_of(): "
                                "Partition needs to be locked!");
    if (auto it = all_cond_.find(ocond); it != all_cond_.end())
      return implying_container(this, it->second);
    else
      return implying_container(this, -1u);
  }

  relabeling_map
  bdd_partition::to_relabeling_map(bool inverse) const
  {
    // Change to unordered_map?
    relabeling_map res;

    auto bdd2form = [&dict = this->dict_](const bdd& cond)
      {
        return bdd_to_formula(cond, dict);
      };

    std::for_each(all_cond_.cbegin(), all_cond_.cend(),
      [&bdd2form, &res, &ig = *this->ig_, inverse](const auto& e)
        {
          const auto& sd = ig.state_storage(e.second);
          if (inverse)
            res[bdd2form(sd.new_label)] = bdd2form(sd.orig_label);
          else
            res[bdd2form(sd.orig_label)] = bdd2form(sd.new_label);

      });

    return res;
  }

  std::pair<bool, bdd_partition>
  try_partition_me(const bdd_dict_ptr& bdd_dict,
                   const std::vector<bdd>& all_cond,
                   const bdd& aps,
                   unsigned max_letter)
  {

    auto res
      = std::make_pair(true,
                       bdd_partition(bdd_dict, aps,
                         std::max(20u,
                                 (unsigned) (2*all_cond.size()))));

    // Try adding conditions one by one
    // Abort if too large
    for (const auto& c : all_cond)
      {
        if (res.second.size() > max_letter)
        {
          res.first = false;
          break;
        }

        res.second.add_condition(c);
      }

    return res;
  }

  std::pair<bool, bdd_partition>
  try_partition_me(const twa_graph_ptr& aut, unsigned max_letter)
  {
    auto seen = std::unordered_set<bdd, bdd_hash>();
    seen.reserve(std::max((size_t) 10,
                          (size_t)(0.1*aut->num_edges())));
    for (const auto& e : aut->edges())
      seen.insert(e.cond);

    auto cond = std::vector<bdd>(seen.begin(), seen.end());

    return try_partition_me(aut->get_dict(), cond, aut->ap_vars(), max_letter);
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

  void
  bdd_partition::relabel_edges_here(const twa_graph_ptr& aut, bool split) const
  {
    if (!aut)
      throw std::runtime_error("bdd_partition::relabel_edges_here(): "
                               "graph_ptr is empty!");
    relabel_or_sep_impl_<true>(*this, *aut, sorted_, split);
  }

  void
  bdd_partition::separate_edges_here(const twa_graph_ptr& aut) const
  {
    if (!aut)
      throw std::runtime_error("bdd_partition::separate_edges_here(): "
                               "graph_ptr is empty!");
    relabel_or_sep_impl_<false>(*this, *aut, sorted_, true);
  }
}