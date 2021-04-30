// -*- coding: utf-8 -*-
// Copyright (C) 2020 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
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

#include <spot/tl/apcollect.hh>
#include <spot/tl/hierarchy.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/synthesis.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/twa/fwd.hh>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/complete.hh>
#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/game.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/minimize.hh>
#include <spot/twaalgos/strength.hh>
#include <spot/twaalgos/parity.hh>
#include <spot/twaalgos/toparity.hh>
#include <spot/twaalgos/sbacc.hh>
#include <spot/twaalgos/sepsets.hh>
#include <spot/twa/bddprint.hh>
#include <spot/misc/timer.hh>

#include <algorithm>
#include <string>
#include <queue>

namespace spot
{
  static void
  restore_form(const twa_graph_ptr &aut, bdd all_outputs)
  {
    bdd all_inputs = bddtrue;
    for (const auto &ap : aut->ap())
    {
      int bddvar = aut->get_dict()->has_registered_proposition(ap, aut);
      assert(bddvar >= 0);
      bdd b = bdd_ithvar(bddvar);
      if (!bdd_implies(all_outputs, b)) // ap is not an output AP
        all_inputs &= b;
    }

    // Loop over all edges and split those that do not have the form
    // (in)&(out)
    // Note new_edge are always appended at the end
    unsigned n_old_edges = aut->num_edges();
    // Temp storage
    // Output condition to possible input conditions
    std::map<bdd, bdd, bdd_less_than> edge_map_;
    for (unsigned i = 1; i <= n_old_edges; ++i)
    {
      // get the edge
      auto &e = aut->edge_storage(i);
      // Check if cond already has the correct form
      if ((bdd_exist(e.cond, all_inputs) & bdd_existcomp(e.cond, all_inputs)) == e.cond)
        // Nothing to do here
        continue;
      // Do the actual split
      edge_map_.clear();
      bdd old_cond = e.cond;
      while (old_cond != bddfalse)
      {
        bdd minterm = bdd_satone(old_cond);
        bdd minterm_in = bdd_exist(minterm, all_outputs);
        // Get all possible valid outputs
        bdd valid_out = bdd_exist((minterm_in & e.cond), all_inputs);
        // Check if this out already exists
        auto it = edge_map_.find(valid_out);
        if (it == edge_map_.end())
          edge_map_[valid_out] = minterm_in;
        else
          // Reuse the outs for this in
          it->second |= minterm_in;

        // Remove this minterm
        old_cond -= minterm;
      }
      // Computed the splitted edges.
      // Replace the current edge cond with the first pair
      auto it = edge_map_.begin();
      e.cond = (it->first & it->second);
      ++it;
      for (; it != edge_map_.end(); ++it)
        aut->new_edge(e.src, e.dst, it->first & it->second, e.acc);
    }
    // Done
  }

} // namespace spot


namespace spot
{
  namespace
  {
    // Used to get the signature of the state.
    typedef std::vector<bdd> vector_state_bdd;

    // Get the list of state for each class.
    typedef std::map<bdd, std::list<unsigned>,
                     bdd_less_than>
        map_bdd_lstate;

    // This class helps to compare two automata in term of
    // size.
    struct automaton_size final
    {
      automaton_size()
          : edges(0),
            states(0)
      {
      }

      automaton_size(const const_twa_graph_ptr &a)
          : edges(a->num_edges()),
            states(a->num_states())
      {
      }

      void set_size(const const_twa_graph_ptr &a)
      {
        states = a->num_states();
        edges = a->num_edges();
      }

      inline bool operator!=(const automaton_size &r)
      {
        return edges != r.edges || states != r.states;
      }

      inline bool operator<(const automaton_size &r)
      {
        if (states < r.states)
          return true;
        if (states > r.states)
          return false;

        if (edges < r.edges)
          return true;
        if (edges > r.edges)
          return false;

        return false;
      }

      inline bool operator>(const automaton_size &r)
      {
        if (states < r.states)
          return false;
        if (states > r.states)
          return true;

        if (edges < r.edges)
          return false;
        if (edges > r.edges)
          return true;

        return false;
      }

      int edges;
      int states;
    };

    // TODO: This part is just a copy of a part of simulation.cc
    class sig_calculator final
    {
    protected:
      typedef std::map<bdd, bdd, bdd_less_than> map_bdd_bdd;
      int acc_vars;
      acc_cond::mark_t all_inf_;

    public:

      sig_calculator(twa_graph_ptr aut) : a_(aut),
          po_size_(0),
          all_class_var_(bddtrue),
          record_implications_(nullptr)
      {
        unsigned ns = a_->num_states();
        size_a_ = ns;
        // Now, we have to get the bdd which will represent the
        // class. We register one bdd by state, because in the worst
        // case, |Class| == |State|.
        unsigned set_num = a_->get_dict()
                               ->register_anonymous_variables(size_a_ + 1, this);


        bdd_initial = bdd_ithvar(set_num++);
        bdd init = bdd_ithvar(set_num++);

        used_var_.emplace_back(init);

        // Initialize all classes to init.
        previous_class_.resize(size_a_);
        for (unsigned s = 0; s < size_a_; ++s)
          previous_class_[s] = init;

        // Put all the anonymous variable in a queue, and record all
        // of these in a variable all_class_var_ which will be used
        // to understand the destination part in the signature when
        // building the resulting automaton.
        all_class_var_ = init;
        for (unsigned i = set_num; i < set_num + size_a_ - 1; ++i)
        {
          free_var_.push(i);
          all_class_var_ &= bdd_ithvar(i);
        }

        relation_[init] = init;
      }

      // Reverse all the acceptance condition at the destruction of
      // this object, because it occurs after the return of the
      // function simulation.
      virtual ~sig_calculator()
      {
        a_->get_dict()->unregister_all_my_variables(this);
      }

      // Update the name of the classes.
      void update_previous_class()
      {
        std::list<bdd>::iterator it_bdd = used_var_.begin();

        // We run through the map bdd/list<state>, and we update
        // the previous_class_ with the new data.
        for (auto &p : sorted_classes_)
        {
          // If the signature of a state is bddfalse (no
          // edges) the class of this state is bddfalse
          // instead of an anonymous variable. It allows
          // simplifications in the signature by removing a
          // edge which has as a destination a state with
          // no outgoing edge.
          if (p->first == bddfalse)
            for (unsigned s : p->second)
              previous_class_[s] = bddfalse;
          else
            for (unsigned s : p->second)
              previous_class_[s] = *it_bdd;
          ++it_bdd;
        }
      }

      void main_loop()
      {
        unsigned int nb_partition_before = 0;
        unsigned int nb_po_before = po_size_ - 1;

        while (nb_partition_before != bdd_lstate_.size() || nb_po_before != po_size_)
        {
          update_previous_class();
          nb_partition_before = bdd_lstate_.size();
          nb_po_before = po_size_;
          po_size_ = 0;
          update_sig();
          go_to_next_it();
          // print_partition();
        }
        update_previous_class();
      }

      // Take a state and compute its signature.
      bdd compute_sig(unsigned src)
      {
        bdd res = bddfalse;

        for (auto &t : a_->out(src))
        {
          // to_add is a conjunction of the acceptance condition,
          // the label of the edge and the class of the
          // destination and all the class it implies.
          bdd to_add = t.cond & relation_[previous_class_[t.dst]];

          res |= to_add;
        }
        return res;
      }

      void update_sig()
      {
        bdd_lstate_.clear();
        sorted_classes_.clear();
        for (unsigned s = 0; s < size_a_; ++s)
        {
          bdd sig = compute_sig(s);
          auto p = bdd_lstate_.emplace(std::piecewise_construct,
                                       std::make_tuple(sig),
                                       std::make_tuple());
          p.first->second.emplace_back(s);
          if (p.second)
            sorted_classes_.emplace_back(p.first);
        }
      }

      // This method renames the color set, updates the partial order.
      void go_to_next_it()
      {
        int nb_new_color = bdd_lstate_.size() - used_var_.size();

        // If we have created more partitions, we need to use more
        // variables.
        for (int i = 0; i < nb_new_color; ++i)
        {
          assert(!free_var_.empty());
          used_var_.emplace_back(bdd_ithvar(free_var_.front()));
          free_var_.pop();
        }

        // If we have reduced the number of partition, we 'free' them
        // in the free_var_ list.
        for (int i = 0; i > nb_new_color; --i)
        {
          assert(!used_var_.empty());
          free_var_.push(bdd_var(used_var_.front()));
          used_var_.pop_front();
        }

        assert((bdd_lstate_.size() == used_var_.size()) || (bdd_lstate_.find(bddfalse) != bdd_lstate_.end() && bdd_lstate_.size() == used_var_.size() + 1));

        // This vector links the tuple "C^(i-1), N^(i-1)" to the
        // new class coloring for the next iteration.
        std::vector<std::pair<bdd, bdd>> now_to_next;
        unsigned sz = bdd_lstate_.size();
        now_to_next.reserve(sz);

        std::list<bdd>::iterator it_bdd = used_var_.begin();

        for (auto &p : sorted_classes_)
        {
          // If the signature of a state is bddfalse (no edges) the
          // class of this state is bddfalse instead of an anonymous
          // variable. It allows simplifications in the signature by
          // removing an edge which has as a destination a state
          // with no outgoing edge.
          bdd acc = bddfalse;
          if (p->first != bddfalse)
            acc = *it_bdd;
          now_to_next.emplace_back(p->first, acc);
          ++it_bdd;
        }

        // Update the partial order.

        // This loop follows the pattern given by the paper.
        // foreach class do
        // |  foreach class do
        // |  | update po if needed
        // |  od
        // od

        for (unsigned n = 0; n < sz; ++n)
        {
          bdd n_sig = now_to_next[n].first;
          bdd n_class = now_to_next[n].second;
          if (want_implications_)
            for (unsigned m = 0; m < sz; ++m)
            {
              if (n == m)
                continue;
              if (bdd_implies(n_sig, now_to_next[m].first))
              {
                n_class &= now_to_next[m].second;
                ++po_size_;
              }
            }
          relation_[now_to_next[n].second] = n_class;
        }
      }

    protected:
      // The automaton which is reduced.
      twa_graph_ptr a_;

      // Implications between classes.
      map_bdd_bdd relation_;

      // Represent the class of each state at the previous iteration.
      vector_state_bdd previous_class_;

      // The list of states for each class at the current_iteration.
      // Computed in `update_sig'.
      map_bdd_lstate bdd_lstate_;
      // The above map, sorted by states number instead of BDD
      // identifier to avoid non-determinism while iterating over all
      // states.
      std::vector<map_bdd_lstate::const_iterator> sorted_classes_;

      // The queue of free bdd. They will be used as the identifier
      // for the class.
      std::queue<int> free_var_;

      // The list of used bdd. They are in used as identifier for class.
      std::list<bdd> used_var_;

      // Size of the automaton.
      unsigned int size_a_;

      // Used to know when there is no evolution in the partial order.
      unsigned int po_size_;

      // Whether to compute implications between classes.  This is costly
      // and useless for deterministic automata.
      bool want_implications_;

      // All the class variable:
      bdd all_class_var_;

      // The flag to say if the outgoing state is initial or not
      bdd bdd_initial;

      bdd all_proms_;

      automaton_size stat;

      // const const_twa_graph_ptr original_;

      std::vector<bdd> *record_implications_;
    };

  } // End namespace anonymous.

} // namespace spot

namespace spot
{
  namespace
  {
    // This class is a tree where the node is ⊤ and a node implies its parent
    class bdd_tree
    {
      bdd label;
      unsigned state_;
      std::vector<bdd_tree> children;

      public:

      bdd_tree() : label(bddtrue), state_(-1U) {}

      bdd_tree(bdd value, unsigned state) : label(value), state_(state) {}

      void add_child(bdd value, unsigned state, bool rec)
      {
        if (value == bddtrue)
        {
          assert(label == bddtrue);
          state_ = state;
        }
        if (rec)
        {
          const unsigned nb_children = children.size();
          for (unsigned i = 0; i < nb_children; ++i)
          {
            // If a child contains a BDD that implies the value, we need a
            // recursive call
            if (bdd_implies(value, children[i].label))
            {
              children[i].add_child(value, state, rec);
              return;
            }
            else if (bdd_implies(children[i].label, value))
            {
              bdd_tree new_node(value, state);
              // If a child contains a BDD that implies the value, we create a
              // new bdd_tree. It must contains all the children that imply
              // value
              std::vector<bdd_tree> removed;
              auto impl_filter = [value, &new_node](bdd_tree tree)
              {
                if (bdd_implies(tree.label, value) == 1)
                {
                  new_node.children.push_back(tree);
                  return true;
                }
                return false;
              };
              auto new_end = std::remove_if(children.begin() + i,
                                            children.end(),
                                            impl_filter);
              children.erase(new_end, children.end());
              children.push_back(new_node);
              return;
            }
          }
        }
        children.push_back(bdd_tree(value, state));
      }

      bdd
      get_lowest_bdd()
      {
        if (children.size() == 0)
          return label;
        return children[0].get_lowest_bdd();
      }

      unsigned
      flatten_aux(std::map<bdd, unsigned, bdd_less_than> &res)
      {
        if (children.size() == 0)
        {
          res.insert({label, state_});
          return state_;
        }
        unsigned rep = children[0].flatten_aux(res);
        res.insert({label, rep});
        for (unsigned i = 1; i < children.size(); ++i)
          children[i].flatten_aux(res);
        return rep;
      }

      // Every node is associated to the state of a leaf
      std::map<bdd, unsigned, bdd_less_than>
      flatten()
      {
        std::map<bdd, unsigned, bdd_less_than> res;
        flatten_aux(res);
        return res;
      }

      void
      print()
      {
        std::cout << "(" << this->label << ", " << this->state_ << ") : " << std::endl;
        for (auto c : children)
          std::cout << c.state_ << std::endl;
        for (auto c : children)
          c.print();
      }
    };

    // Associate to a state a representative
    std::vector<unsigned>
    get_repres(twa_graph_ptr& a, bool rec)
    {
      std::vector<unsigned> repr;
      auto a_num_states = a->num_states();
      repr.reserve(a_num_states);
      bdd_tree tree;
      std::unordered_set<bdd, spot::bdd_hash> bdd_done;
      bdd_done.insert(bddtrue);
      std::vector<bdd> signatures;
      sig_calculator red(a);
      red.main_loop();
      for (unsigned i = 0; i < a_num_states; ++i)
      {
        bdd sig = red.compute_sig(i);
        signatures.push_back(sig);
        if (bdd_done.find(sig) == bdd_done.end())
        {
          tree.add_child(sig, i, rec);
          bdd_done.insert(sig);
        }
      }
      // tree.print();
      auto repr_map = tree.flatten();
      for (unsigned i = 0; i < a_num_states; ++i)
        repr[i] = repr_map[signatures[i]];
      return repr;
    }

    void
    reduce_graph_here(twa_graph_ptr& a, int level)
    {
      // TODO: Si le nombre de classes est égal au nombre d'états de l'automate,
      // pas besoin de faire tout ça.
      // We cannot have a dead state.
      assert(
          [&]()  {
          auto n1 = a->num_states();
          a->purge_dead_states();
          return n1 == a->num_states();
      }() );
      //
      // auto repr = get_repres(a);
      // for (auto&e : a->edges())
      // {
      //   e.dst = repr[e.dst];
      // }
      // a->set_init_state(repr[a->get_init_state_number()]);
      //

      auto repr = get_repres(a, level == 2);
      auto init = repr[a->get_init_state_number()];
      a->set_init_state(init);
      std::stack<unsigned> todo;
      std::vector<bool> done(a->num_states(), false);
      todo.emplace(init);
      while (!todo.empty())
      {
        auto current = todo.top();
        todo.pop();
        done[current] = true;
        for (auto& e : a->out(current))
        {
          if (e.dst == current)
            continue;
          auto repr_dst = repr[e.dst];
          e.dst = repr_dst;
          if (!done[repr_dst])
            todo.emplace(repr_dst);
        }
      }
      a->purge_unreachable_states();
      // a->merge_edges();
    }
  }
}


// Helper function/structures for split_2step
namespace{
  using namespace spot;
  // Computes and stores the restriction
  // of each cond to the input domain and the support
  // This is useful as it avoids recomputation
  // and often many conditions are mapped to the same
  // restriction
  struct small_cacher_t
  {
    //e to e_in and support
    std::unordered_map<bdd, std::pair<bdd, bdd>, bdd_hash> cond_hash_;

    void fill(const const_twa_graph_ptr& aut, bdd output_bdd)
    {
      cond_hash_.reserve(aut->num_edges()/5+1);
      // 20% is about lowest number of different edge conditions
      // for benchmarks taken from syntcomp

      for (const auto& e : aut->edges())
        {
          // Check if stored
          if (cond_hash_.find(e.cond) != cond_hash_.end())
            continue;

          cond_hash_[e.cond] =
              std::pair<bdd, bdd>(
                  bdd_exist(e.cond, output_bdd),
                  bdd_exist(bdd_support(e.cond), output_bdd));
        }
    }

    // Get the condition restricted to input and support of a condition
    const std::pair<bdd, bdd>& operator[](const bdd& econd) const
    {
      return cond_hash_.at(econd);
    }
  };

  // Struct to locally store the information of all outgoing edges
  // of the state.
  struct e_info_t
  {
    e_info_t(const twa_graph::edge_storage_t& e,
             const small_cacher_t& sm)
        : dst(e.dst),
          econd(e.cond),
          einsup(sm[e.cond]),
          acc(e.acc)
    {
      pre_hash = (wang32_hash(dst)
                 ^ std::hash<acc_cond::mark_t>()(acc))
                 * fnv<size_t>::prime;
    }

    inline size_t hash() const
    {
      return wang32_hash(bdd_hash()(econdout)) ^ pre_hash;
    }

    unsigned dst;
    bdd econd;
    mutable bdd econdout;
    std::pair<bdd, bdd> einsup;
    acc_cond::mark_t acc;
    size_t pre_hash;
  };
  // We define a order between the edges to avoid creating multiple
  // states that in fact correspond to permutations of the order of the
  // outgoing edges
  struct less_info_t
  {
    // Note: orders via !econd!
    inline bool operator()(const e_info_t &lhs, const e_info_t &rhs) const
    {
      const int l_id = lhs.econd.id();
      const int r_id = rhs.econd.id();
      return std::tie(lhs.dst, lhs.acc, l_id)
             < std::tie(rhs.dst, rhs.acc, r_id);
    }
  }less_info;

  struct less_info_ptr_t
  {
    // Note: orders via !econdout!
    inline bool operator()(const e_info_t* lhs, const e_info_t* rhs)const
    {
      const int l_id = lhs->econdout.id();
      const int r_id = rhs->econdout.id();
      return std::tie(lhs->dst, lhs->acc, l_id)
             < std::tie(rhs->dst, rhs->acc, r_id);
    }
  }less_info_ptr;

  static twa_graph_ptr
  ntgba2dpa(const twa_graph_ptr &split, bool force_sbacc)
  {
    // if the input automaton is deterministic, degeneralize it to be sure to
    // end up with a parity automaton
    auto dpa = tgba_determinize(degeneralize_tba(split),
                                      false, true, true, false);
    dpa->merge_edges();
    if (force_sbacc)
      dpa = sbacc(dpa);
    reduce_parity_here(dpa, true);
    change_parity_here(dpa, parity_kind_max,
                             parity_style_odd);
    assert((
               [&dpa]() -> bool {
                 bool max, odd;
                 dpa->acc().is_parity(max, odd);
                 return max && odd;
               }()));
    assert(is_deterministic(dpa));
    return dpa;
  }

  static twa_graph_ptr
  change_init_to_0(twa_graph_ptr& a)
  {
    auto res = make_twa_graph(a->get_dict());
    res->copy_ap_of(a);
    res->new_states(a->num_states());
    res->set_init_state(0);
    auto change = [&a](const unsigned state) {
      if (state == 0) return a->get_init_state_number();
      if (state == a->get_init_state_number()) return 0U;
      return state;
    };
    for (auto& e : a->edges())
    {
      res->new_edge(change(e.src), change(e.dst), e.cond, e.acc);
    }
    a->set_acceptance(acc_cond::acc_code::t());
    return res;
  }

  static void
  minimize_strategy_here(twa_graph_ptr& strat, option_map& opt)
  {
    strat->set_acceptance(acc_cond::acc_code::t());
    unsigned simplification_level = opt.get("minimization-level", 1);
    opt.report_unused_options();
    bdd *obdd = strat->get_named_prop<bdd>("synthesis-outputs");
    assert(obdd);
    auto new_bdd = new bdd(*obdd);
    if (simplification_level != 0)
      reduce_graph_here(strat, simplification_level);
    // auto copy = make_twa_graph(strat, twa::prop_set::all());
    strat = change_init_to_0(strat);
    // (void) change_init_to_0;
    // assert(are_equivalent(strat, copy));
    // std::cout << *new_bdd << std::endl;
    strat->set_named_prop("synthesis-outputs", new_bdd);
    (void) restore_form;
    // restore_form(strat, *new_bdd);
    // print_hoa(std::cout, strat) << '\n';
    // print_hoa(std::cout, copy) << '\n';
  }
}

namespace spot
{
  std::ostream& operator<<(std::ostream& os, solver s)
  {
    switch (s)
    {
    case (solver::DET_SPLIT):
      os << "ds";
      break;
    case (solver::SPLIT_DET):
      os << "sd";
      break;
    case (solver::DPA_SPLIT):
      os << "ps";
      break;
    case (solver::LAR):
      os << "lar";
      break;
    case (solver::LAR_OLD):
      os << "lar.old";
      break;
    }
    return os;
  }

  std::ostream&
  operator<<(std::ostream& os, const game_info& gi)
  {
    os << "force sbacc: " << gi.force_sbacc << '\n'
      << "solver: " << gi.s << '\n'
      << (gi.verbose_stream ? "Is verbose\n" : "Is not verbose\n");
    return os;
  }


  twa_graph_ptr
  split_2step(const const_twa_graph_ptr& aut,
              const bdd& output_bdd, bool complete_env,
              bool do_simplify)
  {
    auto split = make_twa_graph(aut->get_dict());
    split->copy_ap_of(aut);
    split->copy_acceptance_of(aut);
    split->new_states(aut->num_states());
    split->set_init_state(aut->get_init_state_number());
    split->set_named_prop<bdd>("synthesis-output", new bdd(output_bdd));

    bdd input_bdd = bddtrue;
    {
      bdd allbdd = aut->ap_vars();
      while (allbdd != bddtrue)
        {
          bdd l = bdd_ithvar(bdd_var(allbdd));
          if (not bdd_implies(output_bdd, l))
            // Input
            input_bdd &= l;
          allbdd = bdd_high(allbdd);
          assert(allbdd != bddfalse);
        }
    }

    // The environment has all states
    // with num <= aut->num_states();
    // So we can first loop over the aut
    // and then deduce the owner

    // a sort of hash-map for all new intermediate states
    std::unordered_multimap<size_t, unsigned> env_hash;
    env_hash.reserve((int) 1.5 * aut->num_states());
    // a local map for edges leaving the current src
    // this avoids creating and then combining edges for each minterm
    // Note there are usually "few" edges leaving a state
    // and map has shown to be faster than unordered_map for
    // syntcomp examples
    std::map<unsigned, std::pair<unsigned, bdd>> env_edge_hash;
    typedef std::map<unsigned, std::pair<unsigned, bdd>>::mapped_type eeh_t;

    small_cacher_t small_cacher;
    small_cacher.fill(aut, output_bdd);

    // Cache vector for all outgoing edges of this states
    std::vector<e_info_t> e_cache;

    // Vector of destinations actually reachable for a given
    // minterm in ins
    // Automatically "almost" sorted due to the sorting of e_cache
    std::vector<const e_info_t*> dests;

    // If a completion is demanded we might have to create sinks
    // Sink controlled by player
    auto get_sink_con_state = [&split]()
      {
        static unsigned sink_con=0;
        if (SPOT_UNLIKELY(sink_con == 0))
          sink_con = split->new_state();
        return sink_con;
      };

    // Loop over all states
    for (unsigned src = 0; src < aut->num_states(); ++src)
      {
        env_edge_hash.clear();
        e_cache.clear();

        auto out_cont = aut->out(src);
        // Short-cut if we do not want to
        // split the edges of nodes that have
        // a single outgoing edge
        if (do_simplify
            && (++out_cont.begin()) == out_cont.end())
          {
            // "copy" the edge
            const auto& e = *out_cont.begin();
            split->new_edge(src, e.dst, e.cond, e.acc);
            // Check if it needs to be completed
            if (complete_env)
              {
                bdd missing = bddtrue - bdd_exist(e.cond, output_bdd);
                if (missing != bddfalse)
                  split->new_edge(src, get_sink_con_state(), missing);
              }
            // We are done for this state
            continue;
          }

        // Avoid looping over all minterms
        // we only loop over the minterms that actually exist
        bdd all_letters = bddfalse;
        bdd support = bddtrue;

        for (const auto& e : out_cont)
          {
            e_cache.emplace_back(e, small_cacher);
            all_letters |= e_cache.back().einsup.first;
            support &= e_cache.back().einsup.second;
          }
        // Complete for env
        if (complete_env && (all_letters != bddtrue))
            split->new_edge(src, get_sink_con_state(), bddtrue - all_letters);

        // Sort to avoid that permutations of the same edges
        // get different intermediate states
        std::sort(e_cache.begin(), e_cache.end(), less_info);

        while (all_letters != bddfalse)
          {
            bdd one_letter = bdd_satoneset(all_letters, support, bddtrue);
            all_letters -= one_letter;

            dests.clear();
            for (const auto& e_info : e_cache)
              // implies is faster than and
              if (bdd_implies(one_letter, e_info.einsup.first))
                {
                  e_info.econdout =
                      bdd_appex(e_info.econd, one_letter,
                                bddop_and, input_bdd);
                  dests.push_back(&e_info);
                  assert(e_info.econdout != bddfalse);
                }
            // By construction this should not be empty
            assert(!dests.empty());
            // # dests is almost sorted -> insertion sort
            if (dests.size()>1)
              for (auto it = dests.begin(); it != dests.end(); ++it)
                std::rotate(std::upper_bound(dests.begin(), it, *it,
                                             less_info_ptr),
                            it, it + 1);

            bool to_add = true;
            size_t h = fnv<size_t>::init;
            for (const auto& t: dests)
              h ^= t->hash();

            auto range_h = env_hash.equal_range(h);
            for (auto it_h = range_h.first; it_h != range_h.second; ++it_h)
              {
                unsigned i = it_h->second;
                auto out = split->out(i);
                if (std::equal(out.begin(), out.end(),
                               dests.begin(), dests.end(),
                               [](const twa_graph::edge_storage_t& x,
                                  const e_info_t* y)
                               {
                                 return   x.dst == y->dst
                                          &&  x.acc == y->acc
                                          &&  x.cond.id() == y->econdout.id();
                               }))
                  {
                    to_add = false;
                    auto it = env_edge_hash.find(i);
                    if (it != env_edge_hash.end())
                      it->second.second |= one_letter;
                    else
                      env_edge_hash.emplace(i,
                          eeh_t(split->new_edge(src, i, bddtrue), one_letter));
                    break;
                  }
              }

            if (to_add)
              {
                unsigned d = split->new_state();
                unsigned n_e = split->new_edge(src, d, bddtrue);
                env_hash.emplace(h, d);
                env_edge_hash.emplace(d, eeh_t(n_e, one_letter));
                for (const auto &t: dests)
                  split->new_edge(d, t->dst, t->econdout, t->acc);
              }
          } // letters
        // save locally stored condition
        for (const auto& elem : env_edge_hash)
          split->edge_data(elem.second.first).cond = elem.second.second;
      } // v-src

    split->merge_edges();
    split->prop_universal(spot::trival::maybe());

    // The named property
    // compute the owners
    // env is equal to false
    std::vector<bool>* owner =
        new std::vector<bool>(split->num_states(), false);
    // All "new" states belong to the player
    std::fill(owner->begin()+aut->num_states(), owner->end(), true);
    split->set_named_prop("state-player", owner);
    // Done
    return split;
  }

  twa_graph_ptr unsplit_2step(const const_twa_graph_ptr& aut)
  {
    twa_graph_ptr out = make_twa_graph(aut->get_dict());
    out->copy_acceptance_of(aut);
    out->copy_ap_of(aut);
    out->new_states(aut->num_states());
    out->set_init_state(aut->get_init_state_number());

    // split_2step is not guaranteed to produce
    // states that alternate between env and player do to do_simplify
    auto owner_ptr = aut->get_named_prop<std::vector<bool>>("state-player");
    if (!owner_ptr)
      throw std::runtime_error("unsplit requires the named prop "
                               "state-player as set by split_2step");

    std::vector<bool> seen(aut->num_states(), false);
    std::deque<unsigned> todo;
    todo.push_back(aut->get_init_state_number());
    seen[aut->get_init_state_number()] = true;
    while (!todo.empty())
      {
        unsigned cur = todo.front();
        todo.pop_front();
        seen[cur] = true;

        for (const auto& i : aut->out(cur))
          {
            // if the dst is also owned env
            if (!(*owner_ptr)[i.dst])
              {
                // This can only happen if there is only
                // one outgoing edges for cur
                assert(([&aut, cur]()->bool
                          {
                            auto out_cont = aut->out(cur);
                            return (++(out_cont.begin()) == out_cont.end());
                          })());
                out->new_edge(cur, i.dst, i.cond, i.acc);
                if (!seen[i.dst])
                  todo.push_back(i.dst);
                continue; // Done with cur
              }
            for (const auto& o : aut->out(i.dst))
              {
                out->new_edge(cur, o.dst, i.cond & o.cond, i.acc | o.acc);
                if (!seen[o.dst])
                  todo.push_back(o.dst);
              }
            }
      }
    out->merge_edges();
    out->merge_states();
    return out;
  }


  spot::twa_graph_ptr
  apply_strategy(const spot::twa_graph_ptr& arena,
                 bool unsplit, bool keep_acc)
  {
    std::vector<bool>* w_ptr =
      arena->get_named_prop<std::vector<bool>>("state-winner");
    std::vector<unsigned>* s_ptr =
      arena->get_named_prop<std::vector<unsigned>>("strategy");
    std::vector<bool>* sp_ptr =
      arena->get_named_prop<std::vector<bool>>("state-player");

    if (!w_ptr || !s_ptr || !sp_ptr)
      throw std::runtime_error("Arena missing state-winner, strategy "
                               "or state-player");

    if (!(w_ptr->at(arena->get_init_state_number())))
      throw std::runtime_error("Player does not win initial state, strategy "
                               "is not applicable");

    std::vector<bool>& w = *w_ptr;
    std::vector<unsigned>& s = *s_ptr;

    auto strat_aut = spot::make_twa_graph(arena->get_dict());
    strat_aut->copy_ap_of(arena);
    if (keep_acc)
      strat_aut->copy_acceptance_of(arena);

    constexpr unsigned unseen_mark = std::numeric_limits<unsigned>::max();
    std::vector<unsigned> todo{arena->get_init_state_number()};
    std::vector<unsigned> pg2aut(arena->num_states(), unseen_mark);
    strat_aut->set_init_state(strat_aut->new_state());
    pg2aut[arena->get_init_state_number()] =
        strat_aut->get_init_state_number();

    while (!todo.empty())
      {
        unsigned v = todo.back();
        todo.pop_back();

        // Check if a simplification occurred
        // in the aut and we have env -> env

        // Env edge -> keep all
        for (auto &e1: arena->out(v))
          {
            assert(w.at(e1.dst));
            // Check if a simplification occurred
            // in the aut and we have env -> env
            if (!(*sp_ptr)[e1.dst])
              {
                assert(([&arena, v]()
                         {
                           auto out_cont = arena->out(v);
                           return (++(out_cont.begin()) == out_cont.end());
                         })());
                // If so we do not need to unsplit
                if (pg2aut[e1.dst] == unseen_mark)
                  {
                    pg2aut[e1.dst] = strat_aut->new_state();
                    todo.push_back(e1.dst);
                  }
                // Create the edge
                strat_aut->new_edge(
                              pg2aut[v],
                              pg2aut[e1.dst],
                              e1.cond,
                              keep_acc ? e1.acc : spot::acc_cond::mark_t({}));
                // Done
                continue;
              }

            if (!unsplit)
              {
                if (pg2aut[e1.dst] == unseen_mark)
                  pg2aut[e1.dst] = strat_aut->new_state();
                strat_aut->new_edge(
                              pg2aut[v], pg2aut[e1.dst], e1.cond,
                              keep_acc ? e1.acc : spot::acc_cond::mark_t({}));
              }
            // Player strat
            auto &e2 = arena->edge_storage(s[e1.dst]);
            if (pg2aut[e2.dst] == unseen_mark)
              {
                pg2aut[e2.dst] = strat_aut->new_state();
                todo.push_back(e2.dst);
              }

            strat_aut->new_edge(
                          unsplit ? pg2aut[v] : pg2aut[e1.dst],
                          pg2aut[e2.dst],
                          unsplit ? (e1.cond & e2.cond) : e2.cond,
                          keep_acc ? e2.acc : spot::acc_cond::mark_t({}));
          }
      }

      if (bdd* obdd = arena->get_named_prop<bdd>("synthesis-outputs"))
        strat_aut->set_named_prop("synthesis-outputs", new bdd(*obdd));
      else
        throw std::runtime_error("Missing named property "
                                 "\"synthesis-outputs\".\n");

    // If no unsplitting is demanded, it remains a two-player arena
    // We do not need to track winner as this is a
    // strategy automaton
    if (!unsplit)
      {
        const std::vector<bool>& sp_pg = * sp_ptr;
        std::vector<bool> sp_aut(strat_aut->num_states());
        std::vector<unsigned> str_aut(strat_aut->num_states());
        for (unsigned i = 0; i < arena->num_states(); ++i)
          {
            if (pg2aut[i] == unseen_mark)
              // Does not appear in strategy
              continue;
            sp_aut[pg2aut[i]] = sp_pg[i];
            str_aut[pg2aut[i]] = s[i];
          }
        strat_aut->set_named_prop(
            "state-player", new std::vector<bool>(std::move(sp_aut)));
        strat_aut->set_named_prop(
            "state-winner", new std::vector<bool>(strat_aut->num_states(),
                                                  true));
        strat_aut->set_named_prop(
            "strategy", new std::vector<unsigned>(std::move(str_aut)));
      }
    return strat_aut;

  }

  static spot::translator
  create_translator(spot::option_map& extra_options, spot::solver sol,
                    spot::bdd_dict_ptr dict)
  {
    for (auto&& p : std::vector<std::pair<const char*, int>>
                      {{"simul", 0},
                       {"ba-simul", 0},
                       {"det-simul", 0},
                       {"tls-impl", 1},
                       {"wdba-minimize", 2}})
      extra_options.set(p.first, extra_options.get(p.first, p.second));

    spot::translator trans(dict, &extra_options);
    // extra_options.report_unused_options();
    switch (sol)
    {
    case spot::solver::LAR:
      SPOT_FALLTHROUGH;
    case spot::solver::LAR_OLD:
      trans.set_type(spot::postprocessor::Generic);
      trans.set_pref(spot::postprocessor::Deterministic);
      break;
    case spot::solver::DPA_SPLIT:
      trans.set_type(spot::postprocessor::ParityMaxOdd);
      trans.set_pref(spot::postprocessor::Deterministic | spot::postprocessor::Colored);
      break;
    case spot::solver::DET_SPLIT:
      SPOT_FALLTHROUGH;
    case spot::solver::SPLIT_DET:
      break;
    }
    return trans;
  }

  spot::twa_graph_ptr
  create_game(const spot::formula& f,
              const std::set<std::string>& all_outs,
              option_map& extra_opt,
              game_info& gi)
  {
    auto trans = create_translator(extra_opt, gi.s, gi.dict);
    // Shortcuts
    auto& bv = gi.bv;
    auto& vs = gi.verbose_stream;

    spot::stopwatch sw;

    if (bv)
      sw.start();
    auto aut = trans.run(f);
    if (bv)
      bv->trans_time = sw.stop();

    if (vs)
      {
        assert(bv);
        *vs << "translating formula done in "
            << bv->trans_time << " seconds\n";
        *vs << "automaton has " << aut->num_states()
            << " states and " << aut->num_sets() << " colors\n";
      }
    auto tobdd = [&aut](const std::string& ap_name)
      {
        return bdd_ithvar(aut->register_ap(ap_name));
      };

    // Check for each ap that actually appears in the graph
    // whether its an in or out
    bdd ins = bddtrue;
    bdd outs = bddtrue;
    for (auto&& aap : aut->ap())
      {
        if (all_outs.count(aap.ap_name()) != 0)
          outs &= tobdd(aap.ap_name());
        else
          ins &= tobdd(aap.ap_name());
      }

    spot::twa_graph_ptr dpa = nullptr;

    switch (gi.s)
    {
      case solver::DET_SPLIT:
      {
        if (bv)
          sw.start();
        auto tmp = ntgba2dpa(aut, gi.force_sbacc);
        if (vs)
          *vs << "determinization done\nDPA has "
              << tmp->num_states() << " states, "
              << tmp->num_sets() << " colors\n";
        tmp->merge_states();
        if (bv)
          bv->paritize_time = sw.stop();
        if (vs)
          *vs << "simplification done\nDPA has "
              << tmp->num_states() << " states\n"
              << "determinization and simplification took "
              << bv->paritize_time << " seconds\n";
        if (bv)
          sw.start();
        dpa = split_2step(tmp, outs, true, false);
        spot::colorize_parity_here(dpa, true);
        if (bv)
          bv->split_time = sw.stop();
        if (vs)
          *vs << "split inputs and outputs done in " << bv->split_time
              << " seconds\nautomaton has "
              << tmp->num_states() << " states\n";
        break;
      }
      case solver::DPA_SPLIT:
      {
        if (bv)
          sw.start();
        aut->merge_states();
        if (bv)
          bv->paritize_time = sw.stop();
        if (vs)
          *vs << "simplification done in " << bv->paritize_time
              << " seconds\nDPA has " << aut->num_states()
              << " states\n";
        if (bv)
          sw.start();
        dpa = split_2step(aut, outs, true, false);
        spot::colorize_parity_here(dpa, true);
        if (bv)
          bv->split_time = sw.stop();
        if (vs)
          *vs << "split inputs and outputs done in " << bv->split_time
              << " seconds\nautomaton has "
              << dpa->num_states() << " states\n";
        break;
      }
      case solver::SPLIT_DET:
      {
        sw.start();
        auto split = split_2step(aut, outs,
                                true, false);
        if (bv)
          bv->split_time = sw.stop();
        if (vs)
          *vs << "split inputs and outputs done in " << bv->split_time
              << " seconds\nautomaton has "
              << split->num_states() << " states\n";
        if (bv)
          sw.start();
        dpa = ntgba2dpa(split, gi.force_sbacc);
        if (vs)
          *vs << "determinization done\nDPA has "
              << dpa->num_states() << " states, "
              << dpa->num_sets() << " colors\n";
        dpa->merge_states();
        if (bv)
          bv->paritize_time = sw.stop();
        if (vs)
          *vs << "simplification done\nDPA has "
              << dpa->num_states() << " states\n"
              << "determinization and simplification took "
              << bv->paritize_time << " seconds\n";
        // The named property "state-player" is set in split_2step
        // but not propagated by ntgba2dpa
        alternate_players(dpa);
        break;
      }
      case solver::LAR:
        SPOT_FALLTHROUGH;
      case solver::LAR_OLD:
      {
        if (bv)
          sw.start();
        if (gi.s == solver::LAR)
          {
            dpa = spot::to_parity(aut);
            // reduce_parity is called by to_parity(),
            // but with colorization turned off.
            spot::colorize_parity_here(dpa, true);
          }
        else
          {
            dpa = spot::to_parity_old(aut);
            dpa = reduce_parity_here(dpa, true);
          }
        spot::change_parity_here(dpa, spot::parity_kind_max,
                                 spot::parity_style_odd);
        if (bv)
          bv->paritize_time = sw.stop();
        if (vs)
          *vs << "LAR construction done in " << bv->paritize_time
              << " seconds\nDPA has "
              << dpa->num_states() << " states, "
              << dpa->num_sets() << " colors\n";

        if (bv)
          sw.start();
        dpa = split_2step(dpa, outs, true, false);
        spot::colorize_parity_here(dpa, true);
        if (bv)
          bv->split_time = sw.stop();
        if (vs)
          *vs << "split inputs and outputs done in " << bv->split_time
              << " seconds\nautomaton has "
              << dpa->num_states() << " states\n";
        break;
      }
    } //end switch solver
    // Set the named properties
    assert(dpa->get_named_prop<std::vector<bool>>("state-player")
           && "DPA has no state-players");
    dpa->set_named_prop<bdd>("synthesis-outputs", new bdd(outs));
    return dpa;
  }

  spot::twa_graph_ptr
  create_game(const formula& f,
              const std::set<std::string>& all_outs)
  {
    option_map dummy1;
    game_info dummy2;
    return create_game(f, all_outs, dummy1, dummy2);
  }

  bool solve_game(twa_graph_ptr arena, game_info& gi)
  {
    // todo adapt to new interface
    spot::stopwatch sw;
    if (gi.bv)
      sw.start();
    auto ret = spot::solve_parity_game(arena);
    if (gi.bv)
      gi.bv->solve_time = sw.stop();
    if (gi.verbose_stream)
      *(gi.verbose_stream) << "parity game solved in "
                           << gi.bv->solve_time << " seconds\n";
    return ret;
  }

  bool
  solve_game(twa_graph_ptr arena)
  {
    game_info dummy1;
    return solve_game(arena, dummy1);
  }

  twa_graph_ptr
  create_strategy(twa_graph_ptr arena, game_info& gi, option_map& opt)
  {
    if (!arena)
      throw std::runtime_error("Arena can not be null");

    auto& bv = gi.bv;
    spot::stopwatch sw;

    if (auto* sw = arena->get_named_prop<std::vector<bool>>("state-winner"))
      {
        if (not (*sw)[arena->get_init_state_number()])
          return nullptr;
      }
    else
      throw std::runtime_error("Arena has no named property"
                                "\"state-winner\". Game not solved?\n");

    if (bv)
      sw.start();
    twa_graph_ptr strat_aut = apply_strategy(arena, true, false);

    strat_aut->prop_universal(true);
    minimize_strategy_here(strat_aut, opt);

    if (bv)
        bv->strat2aut_time = sw.stop();

    return strat_aut;
  }

  // TODO:
  // In the context of synthesis, we have more LTL equivalences. For example
  // if 'a' is the input and 'b' the output, GF(a) <-> GF(b) is equivalent to
  // GF(a <-> b). It is false for subformulas. For example
  // (GF(a) <-> GF(b)) & (G(a <-> !b)) is not equivalent to
  // GF(a <-> b) & G(a <-> !b).
  // static formula
  // simplify_ltl_for_synthesis(formula f, std::vector<std::string> ins,
  //                           std::vector<std::string> outs)
  // {
  //   (void) f;
  //   (void) ins;
  //   (void) outs;
  //   SPOT_UNIMPLEMENTED();
  // }

  static bool
  has_props(formula f, std::vector<std::string> in_aps, bool in)
  {
    auto f_props = atomic_prop_collect(f);
    for (auto& prop : *f_props)
    {
      auto name = prop.ap_name();
      if ((std::find(in_aps.begin(), in_aps.end(), name) == in_aps.end()) == in)
        return false;
    }
    return true;
  }

  // TODO:
  // If a formula is G(o₀ <-> o₁) & G(i₁ <-> o₀), we can create a strategy for
  // G(i₁ <-> o₀) and assign o₁ to the edges with o₀.
  // bdd
  // get_output_constrains(formula f, std::vector<std::string> outs)
  // {
  //   if (f.kind() != op::G)
  //     return bddfalse;
  //   bdd result = bddtrue;
  //   if (f[0].kind() == op::Or)
  //   {
  //     for (auto elem : f[0])
  //     {
  //       TODO: Args?
  //       result &= formula_to_bdd(elem);
  //     }
  //   }
  //   else if (f[0].is_boolean())
  //     return formula_to_bdd(f[0]);
  //   else
  //     return bddfalse;
  // }

  twa_graph_ptr
  try_create_strategy_from_simple(formula f,
                              std::vector<std::string> output_aps,
                              option_map &extra_opt,
                              game_info &gi)
  {
    // TODO: game_info not updated
    auto trans = create_translator(extra_opt, gi.s, gi.dict);
    trans.set_type(postprocessor::Buchi);
    trans.set_pref(postprocessor::Complete);
    trans.set_pref(postprocessor::Deterministic);
    if (f.kind() == op::Equiv)
    {
      // A strategy for recurrence <-> GF(bool) can be created by translating
      // the left part to a deterministic Terminal Büchi automaton and adding
      // bool to the transitions with {0}.
      // TODO: It is the same for guarantee <-> FG(bool)
      formula left, right;
      if ((f[0].kind() == op::G) && (f[0][0].kind() == op::F)
                                       && f[0][0][0].is_boolean())
      {
        left = f[1];
        right = f[0];
      }
      else
      {
        left = f[0];
        right = f[1];
      }
      if (right.kind() == op::G && right[0].kind() == op::F && right[0][0].is_boolean())
      {
        // If left has an output or right has an input, we stop
        if (!has_props(left, output_aps, false) || !has_props(right, output_aps, true))
          return nullptr;
        // We want a deterministic Büchi automaton. Do we want to translate?
        // if (!(left.is_syntactic_recurrence() || left.is_syntactic_safety()))
        //   return nullptr;

        auto left_aut = trans.run(left);

        if (!spot::is_recurrence(left, left_aut) && !spot::is_safety_automaton(left_aut))
          return nullptr;
        if (!is_complete(left_aut))
            left_aut = complete(left_aut);

        if (!spot::is_deterministic(left_aut))
        {
          left_aut = tgba_determinize(left_aut);
          assert(left_aut->acc().is_buchi());
        }

        bdd right_bdd = formula_to_bdd(right[0][0], left_aut->get_dict(), left_aut);
        bdd neg_right_bdd = bdd_not(right_bdd);

        bdd output_bdd = bddtrue;
        for (auto& out : output_aps)
          output_bdd &= bdd_ithvar(left_aut->register_ap(out));

        spot::scc_info si(left_aut, spot::scc_info_options::TRACK_STATES);
        for (auto& e : left_aut->edges())
        {
          if (si.scc_of(e.src) == si.scc_of(e.dst))
            e.cond &= e.acc ? right_bdd : neg_right_bdd;
          e.acc = {};
        }

        left_aut->set_named_prop("synthesis-outputs", new bdd(output_bdd));
        left_aut->set_acceptance(spot::acc_cond::acc_code::t());
        return left_aut;
      }
    }
    return nullptr;
  }

} // spot