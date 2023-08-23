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

#pragma once

#include <bddx.h>
#include <spot/graph/graph.hh>
#include <spot/tl/formula.hh>
#include <spot/tl/relabel.hh>
#include <spot/twa/bdddict.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/twa/twagraph.hh>
#include <spot/misc/bddlt.hh>
#include <memory>

#include <algorithm>

namespace spot
{
  // FWD
  class implying_container;

  /// \brief Class to represent the partitioning of a
  /// set of bdds
  class SPOT_API bdd_partition
  {
  public:
    struct impl_state
    {
      bdd orig_label = bddfalse; /// Condition over original
      bdd new_label = bddfalse; /// Condition over new label
      unsigned n_parents = 0; /// Number of parent nodes; 1 is added
      /// if original condition
    };
    using impl_edge = void;
    using implication_graph = digraph<impl_state, impl_edge>;

  private:
    /// The main data structure;
    /// The implication graph is such that parent nodes imply their children
    /// Leave nodes do not intersect
    std::unique_ptr<implication_graph> ig_;

    /// A map from conditions over the original APs
    /// to the corresponding state, might be a leaf/root/internal node
    std::unordered_map<bdd, unsigned, bdd_hash> orig_;

    /// The bdd_dict, contains old and new propositions
    bdd_dict_ptr dict_;

    /// The original APs as bdd support
    /// This may change during the construction
    bdd orig_support_;
    /// Dynamic support
    bool orig_is_dyn_;

    /// The new APs as bdd support
    /// This may not change when locked
    bdd new_support_ = bddtrue;

    /// Whether or not the partition may currently be modified
    bool locked_ = false;
    /// Wether the implication graph is sorted
    /// Either with respect to the original label
    /// if locked without prefix or to the new label
    /// depending on the prefix given when calling lock()
    bool sorted_ = false;

    /// current elements of the partition
    std::vector<std::pair<bdd, unsigned>> leaves_ = {};

    /// A map from any condition encountered so far (given or produced
    /// during the partitioning) to the corresponding node in ig_
    std::unordered_map<bdd, unsigned, bdd_hash> all_cond_;

    /// \brief Computes the new letters used for relabelling
    /// based on fresh propositions
    /// \param prefix_new The prefix used for the new propositions
    /// \post The member new_label of all states in the graph
    /// are computed, orig_ is sorted with respect to the
    /// original label
    void
    comp_new_letters_(const std::string& prefix_new);

    /// \brief Returns a "new" state in the implication graph;
    /// New here means, either a reused or actually new
    /// \param orig_label Original condition (over orig_support_)
    /// \param is_root_cond True iff the condition belongs to the set
    /// of conditions to partition
    /// \param is_leaf True iff the condition is a leaf in the
    /// current partition
    /// \return The associated state number
    inline unsigned
    new_state_(const bdd& orig_label,
               bool is_root_cond, bool is_leaf)
    {
      auto& ig = *ig_;

      unsigned s = ig.new_state();

      auto& sd = ig.state_storage(s);
      sd.orig_label = orig_label;
      sd.new_label = bddfalse;
      sd.n_parents = is_root_cond;

      // Update data structures
      SPOT_ASSERT(!all_cond_.count(orig_label));
      all_cond_[orig_label] = s;
      if (is_root_cond)
        {
          SPOT_ASSERT(!orig_.count(orig_label));
          orig_[orig_label] = s;
        }
      if (is_leaf)
        leaves_.emplace_back(orig_label, s);
      return s;
    }

    /// \brief Add a new edge between \a src and \a dst
    /// Keep track of parent counting
    inline void
    new_edge_(unsigned src, unsigned dst) {
      auto& ig = *ig_;
      SPOT_ASSERT(src != dst && "No loop in implication graph");
      SPOT_ASSERT([&](){
        for (const auto& e : ig.out(src))
          if (e.dst == dst)
            return false;
        return true;
      }() && "Implication graph is not a multigraph");
      ++ig.state_storage(dst).n_parents;
      ig.new_edge(src, dst);
    }

    /// \brief Verify if the partition is in a valid state
    bool verify_(bool verbose = true);

    /// Dumb as hoa
    std::string
    to_string_hoa_() const;

    /// \brief Remove one condition, but do no touch the graph.
    /// Only the number of parents is updated, the original support might
    /// also be incorrect
    void
    remove_one_(const bdd& r);

    /// \brief Brief builds a flattened version, that is a tree with
    /// depth one, of the implication graph.
    /// Does not seek to minimize it, as tidy_up_ does.
    void
    flatten_();

    /// \brief Tidy up everything after conditions have been removed.
    /// That is remove all unnecessary states of the graph and updates
    /// the original suppport
    void
    tidy_up_();

    /// \brief Expects the graph to be tided up. Edges are sorted
    /// with respect to the bdd_less_stable for the new_label of the
    /// destination
    void
    sort_by_new_label_();

    /// \brief Turn a support into a vector of atomic formulas
    std::vector<formula>
    get_vec_(bdd cond) const;

  public:

    /// \brief Initializes an empty bdd_partition
    ///
    /// \param dict The bdd_dict holding the original propositions and in
    /// which the new propositions will be created
    /// \param orig_support If this is a support over some propositions,
    /// i.e. a conjunction of variables, the support is fixed and all
    /// original conditions given subsequently need to have there support
    /// covered by it. If it is set to false, the support will be
    /// automatically updated to cover all given original conditions
    /// \param n_reserve the size of the implication graph to reserve.
    bdd_partition(const bdd_dict_ptr& dict,
                  const bdd& orig_support = bddfalse,
                  unsigned n_reserve = 10)
      : ig_(std::make_unique<implication_graph>(n_reserve, n_reserve*10))
      , orig_(n_reserve)
      , dict_{dict}
      , orig_support_{orig_support}
      , orig_is_dyn_(orig_support == bddfalse)
      , all_cond_(2*n_reserve)
    {
      if (!dict_)
        throw std::runtime_error("bdd_partition::bdd_partition(): "
                                 "Needs dictionary!");
      if (orig_support_ == bddtrue)
        throw std::runtime_error("bdd_partition::bdd_partition(): "
                                 "orig_support can either be bddfalse "
                                 "or a conjunction of variables!");

      leaves_.reserve(n_reserve);

      // Register original ap for this
      if (orig_is_dyn_)
        orig_support_ = bddtrue;
      else
        {
          bdd osup = orig_support_;
          const auto& bmap = dict_->bdd_map;
          while (osup != bddtrue)
            {
              int v = bdd_var(osup);
              dict_->register_proposition(bmap.at(v).f, this);
              osup = bdd_high(osup);
            }
        }
    }

    bdd_partition(const bdd& orig_support,
                  unsigned n_reserve = 10)
      : bdd_partition(make_bdd_dict(), orig_support, n_reserve)
    {
    }

    /// \brief Constructor needs to take care of APs
    bdd_partition(const bdd_partition& other)
      : ig_(std::make_unique<implication_graph>(*other.ig_))
      , orig_{other.orig_}
      , dict_(other.dict_)
      , orig_support_{other.orig_support_}
      , new_support_{other.new_support_}
      , locked_{other.locked_}
      , sorted_{other.sorted_}
      , leaves_{other.leaves_}
      , all_cond_{other.all_cond_}
    {
      dict_->register_all_variables_of(&other, this);
    }

    /// \brief Move constructor
    bdd_partition(bdd_partition&& other)
      : ig_(std::move(other.ig_))
      , orig_{std::move(other.orig_)}
      , dict_(std::move(other.dict_))
      , orig_support_{std::move(other.orig_support_)}
      , orig_is_dyn_{other.orig_is_dyn_}
      , new_support_{other.new_support_}
      , locked_{other.locked_}
      , sorted_{other.sorted_}
      , leaves_{std::move(other.leaves_)}
      , all_cond_{std::move(other.all_cond_)}
    {
      dict_->register_all_variables_of(&other, this);
      dict_->unregister_all_my_variables(&other);
    }

    /// \brief Assignement operator of bdd_partition;
    /// Takes into account the APs to register/unregister
    bdd_partition& operator=(const bdd_partition& other);

    /// \brief Assignement operator of bdd_partition;
    /// Takes into account the APs to register/unregister
    bdd_partition& operator=(bdd_partition&& other);

    /// \brief Destructor needs to clean up the APs
    ~bdd_partition()
    {
      // Might have been stolen
      if (dict_)
        {
          if (locked_)
            unlock();
          dict_->unregister_all_my_variables(this);
        }
    }

    /// \brief Resets the partition to empty
    void
    reset()
    {
      bdd newsup = bddfalse;
      if (!orig_is_dyn_ && (orig_support_ != bddtrue))
        newsup = orig_support_;
      *this = bdd_partition(dict_, newsup);
    }

    /// \brief Access the implication graph directly
    const implication_graph&
    get_graph() const
    {
      return *ig_;
    }

    /// \brief The size of the partition corresponds to the
    /// number of leaves
    size_t
    size() const
    {
      return leaves_.size();
    }

    /// \brief Check if the relabeling has either
    /// not yet started or failed
    /// @return T iff the implication graph
    /// is non-empty
    bool
    is_empty() const
    {
      return !size();
    }

    /// \brief Access the leaves of the implication graph
    /// which also correspond to the new letters of the partition
    /// \note The partition must not necessarily be locked
    /// however if it is not locked, there are no new labels.
    const std::vector<std::pair<bdd, unsigned>>&
    leaves() const
    {
      return leaves_;
    }

    /// \brief Return the map from the original conditions to
    /// the corresponding state in the graph
    /// \note if the partition is not locked,
    /// new labels are not available
    const std::unordered_map<bdd, unsigned, bdd_hash>&
    orig_conditions() const
    {
      return orig_;
    }

    /// \brief Access to all conditions stored in the graph
    const std::unordered_map<bdd, unsigned, bdd_hash>&
    all_conditions() const
    {
      return all_cond_;
    }

    /// \brief Accessor for the new aps as support.
    /// Returns true if locked with empty prefix.
    /// \pre must be locked
    const bdd&
    new_ap_vars() const {
      return new_support_;
    }

    /// \brief Accessor for the new ap
    /// if locked without prefix the list will
    /// be empty
    /// \pre Must be locked
    std::vector<formula>
    new_ap() const
    {
      if (!locked_)
        throw std::runtime_error("bdd_partition::new_ap(): Must be locked!");

      return get_vec_(new_support_);
    }

    /// \brief Accessor for the original ap as support.
    /// Maybe true if dynamic support and no conditions have been reg.
    const bdd&
    orig_ap_vars() const {
      return orig_support_;
    }

    /// \brief Accessor for the original ap.
    /// Maybe true if support is dynamic and no conditions have been reg.
    std::vector<formula>
    orig_ap() const
    {
      return get_vec_(orig_support_);
    }

    /// \brief Get the new label corresponding to \a orig_label
    /// \note Throws if orig_label was not amongst
    /// the conditions to be partitioned
    const bdd&
    relabel(const bdd& orig_label)
    {
      return ig_->state_storage(all_cond_.at(orig_label)).new_label;
    }

    /// \brief Unlocks the partition; This erases the new APs
    /// and all encodings
    /// \pre Needs to be locked
    void
    unlock();

    /// \brief Locks the partition; If \a prefix_new is given, the new
    /// propositions needed to encode are created using
    /// the names pref_XXX; The prefix must not appear as prefix of
    /// any existing ap.
    /// If \a sort is set to true the implied leave nodes will appear in
    /// increasing order with respect to the new labal (if \a prefix_new)
    /// is not empty, other to the old-label.
    /// Currently the graph is flattened, but this is not guaranteed
    /// to always be the case. If it is not flattened, the internal
    /// nodes have a value corresponding to their largest child.
    /// \pre May not be already locked
    void
    lock(const std::string& prefix_new, bool sort = false);

    /// \brief Like above, but defaults to reusing the same
    /// dictionary, the prefix being __nv and sort
    /// being true
    void
    lock();

    /// \brief Add a condition to the partition
    /// \pre The partition needs to be unlocked
    void
    add_condition(const bdd& c);

    /// \brief Remove the given conditions from the partition
    ///
    /// This will possibly cause nodes to fuse and leaves to disappear
    /// \note The conditions to be removed MUST exist as original condition
    /// in the graph
    /// \note This will restructure the graph, all nodes,
    /// iterators etc are invalidated
    /// @{
    void
    remove_condition(const std::vector<bdd>& to_remove);
    void
    remove_condition(const bdd& to_remove);
    /// @}

    /// \brief Converts a bdd_partition into a relabeling map
    ///
    /// If \a inverse is false, returns the map
    /// going from original to new APs. Otherwise
    /// the map is going from new to original AP
    /// \pre Partition must be locked
    /// \note This operation can be expensive due to the
    /// conversion from bdd to formula
    relabeling_map
    to_relabeling_map(bool inverse = true) const;

    /// \brief Converts the partition to a string in
    /// the demanded format, currently \a type only
    /// supports 'hoa'
    ///
    /// Original labels are shown as state names
    /// New labels are shown as conditions on self-loops
    /// \pre Needs to be locked
    /// \note String is not reproducible as it iterates over unordered
    std::string
    to_str(const std::string& type) const;


    /// \brief Access the underlying bdd_dict
    const bdd_dict_ptr&
    get_dict() const
    {
      return dict_;
    }

    /// \brief Return a fake container containing all
    /// implying leaves, that is all disjoint conditions
    /// whose union correspond to the given condition
    /// \note The given condition \a ocond can be a original
    /// condition, or some other condition over the original
    /// ap contained in the implication graph (a so-called
    /// intermediate condition). If \a ocond does not
    /// exist in the partition, the container will be
    /// empty.
    /// \note The container and the iterators may not be
    /// used if the partition was unlocked in the mean time
    implying_container
    get_set_of(const bdd& ocond) const;

    /// \brief Relabels all the edges of the automaton \a aut
    /// whose conditions have been added to the partition beforehand.
    /// The bool \a split decides whether conditions are split
    /// into disjoint unions or not.
    /// \pre Partition needs to be locked with a given prefix
    /// \note The outgoing edges will be sorted if the corresponding
    /// argument was set to true when locking.
    void relabel_edges_here(const twa_graph_ptr& aut, bool split) const;
    /// \brief Separates all edges of the automaton \a aut
    /// into disjoint unions if the condition has been added to the
    /// partitions beforehand.
    /// \pre The partition is locked
    /// \note The outgoing edges will be sorted if the corresponding
    /// argument was set to true when locking
    void separate_edges_here(const twa_graph_ptr& aut) const;
  }; // bdd_partition


  /// \brief Iterator to iterate over leaves that imply a root node
  class SPOT_API implying_iterator
  {
  public:
    using reference = bdd_partition::impl_state&;
    using pointer = bdd_partition::impl_state*;
    using difference_type = std::ptrdiff_t;
    using iterator_category = std::forward_iterator_tag;

  private:
    const bdd_partition* bdd_part_;
    unsigned root_;
    std::vector<std::array<unsigned, 2>> stack_;

  private:
    /// \brief Returns the first outgoing edge of the state \a s
    inline unsigned succ_s(unsigned s)
    {
      auto& g = bdd_part_->get_graph();
      SPOT_ASSERT(s < g.num_states());
      return g.state_storage(s).succ;
    }
    /// \brief Return the next edge of \a e
    inline unsigned succ_e(unsigned e)
    {
      SPOT_ASSERT(e != 0);
      auto& g = bdd_part_->get_graph();
      return g.edge_storage(e).next_succ;
    }

  public:
    implying_iterator(const bdd_partition* bdd_part,
                                       unsigned root,
                                       bool end)
      : bdd_part_{bdd_part}
      , root_{root}
    {
      SPOT_ASSERT(root_ < bdd_part_->get_graph().num_states()
             || root_ == -1u);
      if (end)
        stack_.clear();
      else
        {
          stack_.push_back({root_, succ_s(root)});
          if (stack_.back()[1] != 0)
            ++(*this);
        }
    }
    implying_iterator(const implying_iterator&) = default;
    implying_iterator(implying_iterator&&) = default;
    implying_iterator& operator=(const implying_iterator&) = default;
    implying_iterator& operator=(implying_iterator&&) = default;
    ~implying_iterator() = default;

    /// \brief Equality operator
    inline bool operator==(const implying_iterator& other) const noexcept
    {
      return bdd_part_ == other.bdd_part_
             && root_ == other.root_
             && stack_ == other.stack_;
    }
    /// \brief Inequality operator
    inline bool operator!=(const implying_iterator& other) const noexcept
    {
      return !(*this == other);
    }
    /// \brief Increments the iterator so that it points to
    /// the next leaves implying the root.
    /// \post Last element of the stack is a leaf or stack is empty
    inline implying_iterator& operator++()
    {
      if (stack_.empty())
        return *this;

      // Now iterate until we find the next leaf
      while (!stack_.empty())
        {
          if (stack_.back()[1] == 0)
            // Exhausted or initial leaf
            stack_.pop_back();
          else
            {
              // Successor
              unsigned dst
                = bdd_part_->get_graph().edge_storage(stack_.back()[1]).dst;
              // Advance
              stack_.back()[1] = succ_e(stack_.back()[1]);
              // Put on stack
              stack_.push_back({dst, succ_s(dst)});
              if (stack_.back()[1] == 0)
                break; // Leaf
            }
        }
      SPOT_ASSERT(stack_.empty()
                  || (bdd_part_->get_graph()
                        .state_storage(stack_.back()[0]).succ_tail == 0));
      return *this;
    }
    /// \brief Dereferencing returns the state data of the node in the
    /// implication graph, containing the original and new label
    /// \note If locked with an empty prefix, the new label is set
    /// to bdd_fase
    inline const bdd_partition::impl_state&
    operator*() const
    {
      SPOT_ASSERT(!stack_.empty());
      return bdd_part_->get_graph().state_data(stack_.back()[0]);
    }
    inline const bdd_partition::impl_state*
    operator->() const
    {
      return &(this->operator*());
    }

    /// \brief All leaves have been iterated over once the stack
    /// is empty
    inline operator bool() const noexcept
    {
      return !stack_.empty();
    }
  };

  /// \brief Fake container to easily iterate over all
  /// leaves nodes reachable.
  /// \note If root is set to -1u, the container is considered empty
  class SPOT_API implying_container
  {
  private:
    const bdd_partition* bdd_part_;
    unsigned root_;

  public:
    implying_container(const bdd_partition* bdd_part, unsigned root)
      : bdd_part_{bdd_part}
      , root_{root}
    {
      SPOT_ASSERT(root_ < bdd_part_->get_graph().num_states()
                  || root_ == -1u);
    }
    ~implying_container() = default;
    implying_container(const implying_container&) = default;
    implying_container(implying_container&&) = default;
    implying_container& operator=(const implying_container&) = default;
    implying_container& operator=(implying_container&&) = default;

    /// \brief Begin iterator over implying leaves
    inline implying_iterator begin() const
    {
      return implying_iterator(bdd_part_, root_, root_ == -1u);
    }

    /// \brief End iterator over implying leaves
    inline implying_iterator end() const
    {
      return implying_iterator(bdd_part_, root_, true);
    }
  };



  /// \brief Tries to build a bdd_partition for the given
  /// conditions but aborts once the number of new
  /// letters exceeds the given threshhold \a max_letter
  /// \note The partition will be empty if relabelling failed
  /// \param bdd_dict The bdd_dict holding the ap
  /// \param all_cond All conditions to be partitioned
  /// \param aps support of all the conditions or false to build dynamically
  /// \param max_letter Abort criterion
  /// \return res.first is true iff all conditions have been partitioned.
  /// Second corresponds to the (partial) partition
  SPOT_API std::pair<bool, bdd_partition>
  try_partition_me(const bdd_dict_ptr& bdd_dict,
                   const std::vector<bdd>& all_cond,
                   const bdd& aps = bddfalse,
                   unsigned max_letter = -1u);

  SPOT_API std::pair<bool, bdd_partition>
  try_partition_me(const twa_graph_ptr& aut, unsigned max_letter = -1u);
}
