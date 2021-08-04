// -*- coding: utf-8 -*-
// Copyright (C) 2021 Laboratoire de Recherche et Developpement de
// l'Epita (LRDE).
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
#include <iostream>
#include <spot/twaalgos/zlktree.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <deque>
#include "spot/priv/bddalloc.hh"

namespace spot
{
  zielonka_tree::zielonka_tree(const acc_cond& cond)
  {
    const acc_cond::acc_code& code = cond.get_acceptance();
    auto used = code.used_sets();
    unsigned c = used.count();
    unsigned max = used.max_set();

    bdd_allocator ba;
    int base = ba.allocate_variables(c);
    assert(base == 0);
    std::vector<bdd> col_to_bdd(max ? max : 1, bddfalse);
    std::vector<unsigned> bdd_to_col(c);
    bdd all_neg = bddtrue;
    for (unsigned i = 0; i < max; ++i)
      if (used.has(i))
        {
          bdd_to_col[base] = i;
          all_neg &= bdd_nithvar(base);
          col_to_bdd[i] = bdd_ithvar(base++);
        }

    bdd poscond = code.to_bdd(col_to_bdd.data());
    bdd negcond = !poscond;

    nodes_.emplace_back();
    nodes_[0].parent = 0;
    nodes_[0].colors = used;
    nodes_[0].level = 0;

    // Or goal is the find the list of maximal models for a formula named
    // cond and defined later for each node.
    //
    // For instance if cond is satisfied by {1}, {3}, {1,2}, {1,2,3},
    // {0,3}, and {0,1,3}, then the maximal models are {1,2,3} and
    // {0,1,3}.
    //
    // To do that we build a list of models ordered by decreasing
    // size.  When inserting a model, we will compare it to all
    // model of larger size first, and abort the insertion if
    // needed.  Otherwise we insert it, and then compare it to
    // smaller models to possibly remove them.
    //
    // "models" is the variable where we store those ordered models.
    // This list is local to each node, but we reuse the vector
    // between each iteration to avoid unnecessary allocations.
    struct size_model
    {
      unsigned size;
      acc_cond::mark_t model;
    };
    std::vector<size_model> models;

    // This loop is a BFS over the increasing set of nodes.
    for (unsigned node = 0; node < nodes_.size(); ++node)
    {
      acc_cond::mark_t colors = nodes_[node].colors;
      bool is_accepting = code.accepting(colors);
      if (node == 0)
        is_even_ = is_accepting;

      // colors that do not appear in this node should
      // be set to false in the acceptance.
      bdd to_remove = bddtrue;
      for (unsigned c: (colors ^ used).sets())
        to_remove &= !col_to_bdd[c];
      bdd cond = bdd_restrict(is_accepting ? negcond : poscond, to_remove);

      // These is where we will store the ordered list of models, as
      // explained in the declation of that vector.
      models.clear();

      while (cond != bddfalse)
        {
          // Find one model of cond.  If it has some don't cares
          // variable, we interpret them as true, so in effect, we can
          // start from a model where all colors are sets, and only
          // unset those that are negative in the output of
          // bdd_satone.
          bdd one = bdd_satone(cond);
          cond -= one;
          acc_cond::mark_t curmodel = colors;
          while (one != bddtrue)
            {
              unsigned v = bdd_to_col[bdd_var(one)];
              if (bdd_high(one) == bddfalse)
                {
                  curmodel.clear(v);
                  one = bdd_low(one);
                }
              else
                {
                  one = bdd_high(one);
                }
            }
          //
          unsigned sz = curmodel.count();
          if (sz == 0)
            // ignore the empty set
            continue;
          auto iter = models.begin();
          while (iter != models.end())
            {
              if (iter->size < sz)
                // We have checked all larger models.
                break;
              if (curmodel.subset(iter->model))
                // curmodel is covered by iter->model.
                goto donotinsert;
              ++iter;
            }
          // insert the model
          iter = models.insert(iter, {sz, curmodel});
          ++iter;
          // erase all models it contains
          models.erase(std::remove_if(iter, models.end(),
                                      [&](auto& mod) {
                                        return mod.model.subset(curmodel);
                                      }), models.end());
        donotinsert:;
        }
      if (models.empty()) // This is a leaf of the tree.
        {
          if (num_branches_++ == 0)
            one_branch_ = node;
          continue;
        }
      unsigned first = nodes_.size();
      nodes_[node].first_child = first;
      unsigned num_children = models.size();
      nodes_.reserve(first + num_children);
      for (auto& m: models)
        nodes_.push_back({node, static_cast<unsigned>(nodes_.size() + 1),
                          0, nodes_[node].level + 1, m.model});
      nodes_.back().next_sibling = first;

      if (num_children > 1)
        {
          if (is_accepting)
            has_rabin_shape_ = false;
          else
            has_streett_shape_ = false;
        }
    };
  }

  void zielonka_tree::dot(std::ostream& os) const
  {
    os << "digraph zielonka_tree {\n";
    unsigned ns = nodes_.size();
    for (unsigned n = 0; n < ns; ++n)
      {
        os << "  " << n << " [label=\"" << nodes_[n].colors;
        unsigned first_child = nodes_[n].first_child;
        if (!first_child)
            os << "\n<" << n << '>';
        os << "\", shape="
           << (((nodes_[n].level & 1) ^ is_even_) ? "ellipse" : "box")
           << "]\n";
        if (first_child)
          {
            unsigned child = first_child;
            do
              {
                os << "  " << n << " -> " << child << '\n';
                child = nodes_[child].next_sibling;
              }
            while (child != first_child);
          }
      }
    os << "}\n";
  }

  std::pair<unsigned, unsigned>
  zielonka_tree::step(unsigned branch, acc_cond::mark_t colors) const
  {
    if (SPOT_UNLIKELY(nodes_.size() < branch || nodes_[branch].first_child))
      throw std::runtime_error
        ("zielonka_tree::next_branch(): incorrect branch number");

    if (!colors)
      return {branch, nodes_[branch].level + 1};

    unsigned child = 0;
    for (;;)
      {
        colors -= nodes_[branch].colors;
        if (!colors)
          break;
        child = branch;
        branch = nodes_[branch].parent;
      }
    unsigned lvl = nodes_[branch].level;
    if (child != 0)
      {
        // The following computation could be precomputed.
        branch = nodes_[child].next_sibling;
        while (nodes_[branch].first_child)
          branch = nodes_[branch].first_child;
      }
    return {branch, lvl};
  }

  namespace
  {
    // A state in the zielonka_tree_transform output corresponds to a
    // state in the input associated to a branch of the tree.
    typedef std::pair<unsigned, unsigned> zlk_state;

    struct zlk_state_hash
    {
      size_t
      operator()(const zlk_state& s) const noexcept
      {
        return wang32_hash(s.first ^ wang32_hash(s.second));
      }
    };
  }

  twa_graph_ptr
  zielonka_tree_transform(const const_twa_graph_ptr& a)
  {
    auto res = make_twa_graph(a->get_dict());
    res->copy_ap_of(a);
    zielonka_tree zlk(a->get_acceptance());

    // Preserve determinism, weakness, and stutter-invariance
    res->prop_copy(a, { false, true, true, true, true, true });

    auto orig_states = new std::vector<unsigned>();
    auto branches = new std::vector<unsigned>();
    unsigned ns = a->num_states();
    orig_states->reserve(ns); // likely more are needed.
    res->set_named_prop("original-states", orig_states);
    res->set_named_prop("degen-levels", branches);

    // Associate each zlk_state to its number.
    typedef std::unordered_map<zlk_state, unsigned, zlk_state_hash> zs2num_map;
    zs2num_map zs2num;

    // Queue of states to be processed.
    std::deque<zlk_state> todo;

    auto new_state = [&](zlk_state zs)
    {
      if (auto i = zs2num.find(zs); i != zs2num.end())
        return i->second;

      unsigned ns = res->new_state();
      zs2num[zs] = ns;
      todo.emplace_back(zs);

      unsigned orig = zs.first;
      assert(ns == orig_states->size());
      orig_states->emplace_back(orig);
      branches->emplace_back(zs.second);
      return ns;
    };

    zlk_state s(a->get_init_state_number(), zlk.first_branch());
    new_state(s);
    unsigned max_color = 0;
    while (!todo.empty())
      {
        s = todo.front();
        todo.pop_front();
        int src = zs2num[s];
        unsigned branch = s.second;

        for (auto& i: a->out(s.first))
          {
            auto [newbranch, prio] = zlk.step(branch, i.acc);
            zlk_state d(i.dst, newbranch);
            unsigned dst = new_state(d);
            max_color = std::max(max_color, prio);
            res->new_edge(src, dst, i.cond, {prio});
          }
      }

    res->set_acceptance(max_color + 1,
                        acc_cond::acc_code::parity_min(!zlk.is_even(),
                                                       max_color + 1));

    // compose original-states with the any previously existing one.
    // We do that now, because for the bottommost copy below, it's better
    // if we compose everything.
    if (auto old_orig_states =
        a->get_named_prop<std::vector<unsigned>>("original-states"))
      for (auto& s: *orig_states)
        s = (*old_orig_states)[s];

    // Now we will iterate over the SCCs in topological order to
    // remember the "bottommost" SCCs that contain each original
    // state.  If an original state is duplicated in a higher SCC,
    // it can be shunted away.  Amen.
    scc_info si_res(res, scc_info_options::TRACK_STATES);
    unsigned res_scc_count = si_res.scc_count();
    unsigned maxorig = *std::max_element(orig_states->begin(),
                                         orig_states->end());
    std::vector<unsigned> bottommost_occurence(maxorig + 1);
    {
      unsigned n = res_scc_count;
      do
        for (unsigned s: si_res.states_of(--n))
          bottommost_occurence[(*orig_states)[s]] = s;
      while (n);
    }
    unsigned res_ns = res->num_states();
    std::vector<unsigned> retarget(res_ns);
    for (unsigned n = 0; n < res_ns; ++n)
      {
        unsigned other = bottommost_occurence[(*orig_states)[n]];
        retarget[n] =
          (si_res.scc_of(n) != si_res.scc_of(other)) ? other : n;
      }
    for (auto& e: res->edges())
      e.dst = retarget[e.dst];
    res->set_init_state(retarget[res->get_init_state_number()]);
    res->purge_unreachable_states();

    return res;
  }
}
