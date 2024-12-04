// -*- coding: utf-8 -*-
// Copyright (C) by the Spot authors, see the AUTHORS file for details.
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
#include <queue>
#include <unordered_map>
#include <algorithm>
#include <spot/misc/bddlt.hh>
#include <spot/misc/escape.hh>
#include <spot/twaalgos/ltlf2dfa.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/tl/apcollect.hh>
#include <spot/tl/print.hh>
#include <spot/priv/robin_hood.hh>

constexpr int hash_key_and = 1;
constexpr int hash_key_or = 2;
constexpr int hash_key_implies = 3;
constexpr int hash_key_equiv = 4;
constexpr int hash_key_xor = 5;
constexpr int hash_key_not = 6;
constexpr int hash_key_rename = 7;

namespace spot
{

  ltlf_translator::ltlf_translator(bdd_dict_ptr& dict)
    : dict_(dict)
  {
    bdd_extcache_init(&cache_, 0);

    terminal_to_formula_.reserve(32);
  }

  ltlf_translator::~ltlf_translator()
  {
    bdd_extcache_done(&cache_);
    dict_->unregister_all_my_variables(this);
  }

  formula ltlf_translator::terminal_to_formula(int v) const
  {
    v /= 2;
    assert((unsigned) v < terminal_to_formula_.size());
    return terminal_to_formula_[v];
  }

  std::pair<formula, bool> ltlf_translator::leaf_to_formula(int v) const
  {
    if (v == 0)
      return {formula::ff(), false};
    if (v == 1)
      return {formula::tt(), true};
    v = bdd_get_terminal(v);
    return {terminal_to_formula(v), v & 1};
  }

  int ltlf_translator::formula_to_terminal(formula f, bool maystop)
  {
    if (auto it = formula_to_terminal_.find(f);
        it != formula_to_terminal_.end())
      return 2 * it->second + maystop;

    int v = terminal_to_formula_.size();
    terminal_to_formula_.push_back(f);
    formula_to_terminal_[f] = v;
    return 2 * v + maystop;
  }

  bdd ltlf_translator::formula_to_terminal_bdd(formula f, bool maystop)
  {
    if (SPOT_UNLIKELY(f.is_ff() && !maystop))
      return bddfalse;
    else if (SPOT_UNLIKELY(f.is_tt() && maystop))
      return bddtrue;
    else
      return bdd_terminal(formula_to_terminal(f, maystop));
  }

  static ltlf_translator* term_combine_trans;
  static int term_combine_and(int left, int right)
  {
    formula ll = term_combine_trans->terminal_to_formula(left);
    formula rr = term_combine_trans->terminal_to_formula(right);
    formula res = formula::And({ll, rr});
    return term_combine_trans->formula_to_terminal(res,
                                                   left & right & 1);
  }

  static int term_combine_or(int left, int right)
  {
    formula ll = term_combine_trans->terminal_to_formula(left);
    formula rr = term_combine_trans->terminal_to_formula(right);
    formula res = formula::Or({ll, rr});
    return term_combine_trans->formula_to_terminal(res,
                                                   (left | right) & 1);
  }

  static int term_combine_implies(int left, int right)
  {
    auto [lf, lb] = term_combine_trans->leaf_to_formula(left);
    auto [rf, rb] = term_combine_trans->leaf_to_formula(right);
    formula res = formula::Implies(lf, rf);
    return term_combine_trans->formula_to_terminal_bdd(res, !lb | rb).id();
  }

  static int term_combine_equiv(int left, int right)
  {
    auto [lf, lb] = term_combine_trans->leaf_to_formula(left);
    auto [rf, rb] = term_combine_trans->leaf_to_formula(right);
    formula res = formula::Equiv(lf, rf);
    return term_combine_trans->formula_to_terminal_bdd(res, lb == rb).id();
  }

  static int term_combine_xor(int left, int right)
  {
    auto [lf, lb] = term_combine_trans->leaf_to_formula(left);
    auto [rf, rb] =  term_combine_trans->leaf_to_formula(right);
    formula res = formula::Xor(lf, rf);
    return term_combine_trans->formula_to_terminal_bdd(res, lb != rb).id();
  }

  static int term_combine_not(int left)
  {
    formula ll = term_combine_trans->terminal_to_formula(left);
    formula res = formula::Not(ll);
    return term_combine_trans->formula_to_terminal(res, !(left & 1));
  }

  bdd ltlf_translator::combine_and(bdd left, bdd right)
  {
    term_combine_trans = this;
    bdd r = bdd_mt_apply2(left, right,
                          term_combine_and, &cache_, hash_key_and,
                          bddop_and);
    return r;
  }

  bdd ltlf_translator::combine_or(bdd left, bdd right)
  {
    term_combine_trans = this;
    bdd r = bdd_mt_apply2(left, right,
                          term_combine_or, &cache_, hash_key_or,
                          bddop_or);
    return r;
  }

  bdd ltlf_translator::combine_implies(bdd left, bdd right)
  {
    term_combine_trans = this;
    bdd r = bdd_mt_apply2b(left, right,
                           term_combine_implies, &cache_, hash_key_implies,
                           bddop_imp);
    return r;
  }

  bdd ltlf_translator::combine_equiv(bdd left, bdd right)
  {
    term_combine_trans = this;
    bdd r = bdd_mt_apply2b(left, right,
                           term_combine_equiv, &cache_, hash_key_equiv,
                           bddop_biimp);
    return r;
  }

  bdd ltlf_translator::combine_xor(bdd left, bdd right)
  {
    term_combine_trans = this;
    bdd r = bdd_mt_apply2b(left, right,
                           term_combine_xor, &cache_, hash_key_xor,
                           bddop_xor);
    return r;
  }

  bdd ltlf_translator::combine_not(bdd left)
  {
    term_combine_trans = this;
    bdd r = bdd_mt_apply1(left, term_combine_not,
                          bddtrue, bddfalse,
                          &cache_, hash_key_not);
    return r;
  }

  bdd ltlf_translator::ltlf_to_mtbdd(formula f)
  {
    if (auto it = formula_to_bdd_.find(f); it != formula_to_bdd_.end())
      return it->second;

    bdd res = bddfalse;
    if (f.is_boolean())
      {
        res = formula_to_bdd(f, dict_, this);
      }
    else
      {
        switch (f.kind())
          {
          case op::eword:
          case op::tt:
          case op::ff:
          case op::ap:
            // already handled in f.is_boolean() above
            SPOT_UNREACHABLE();
          case op::Not:
            res = combine_not(ltlf_to_mtbdd(f[0]));
            break;
          case op::Xor:
            {
              bdd left = ltlf_to_mtbdd(f[0]);
              bdd right = ltlf_to_mtbdd(f[1]);
              res = combine_xor(left, right);
              break;
            }
          case op::Implies:
            {
              bdd left = ltlf_to_mtbdd(f[0]);
              bdd right = ltlf_to_mtbdd(f[1]);
              res = combine_implies(left, right);
              break;
            }
          case op::Equiv:
            {
              bdd left = ltlf_to_mtbdd(f[0]);
              bdd right = ltlf_to_mtbdd(f[1]);
              res = combine_equiv(left, right);
              break;
            }
            /*
          case op::Not:
          case op::Xor:
          case op::Implies:
          case op::Equiv:
            throw std::runtime_error("ltlf_to_mtbdd: input formula should be "
                                     "in negative normal form");
            */
          case op::AndNLM:
          case op::AndRat:
          case op::Closure:
          case op::Concat:
          case op::EConcat:
          case op::EConcatMarked:
          case op::first_match:
          case op::FStar:
          case op::Fusion:
          case op::NegClosure:
          case op::NegClosureMarked:
          case op::OrRat:
          case op::Star:
          case op::UConcat:
            throw std::runtime_error("ltlf_to_mtbdd: unsupported operator");
          case op::And:
            {
              unsigned n = f.size();
              res = ltlf_to_mtbdd(f[0]);
              for (unsigned i = 1; i < n; ++i)
                res = combine_and(res, ltlf_to_mtbdd(f[i]));
              break;
            }
          case op::Or:
            {
              unsigned n = f.size();
              res = ltlf_to_mtbdd(f[0]);
              for (unsigned i = 1; i < n; ++i)
                res = combine_or(res, ltlf_to_mtbdd(f[i]));
              break;
            }
          case op::X:
            res = formula_to_terminal_bdd(f[0], true);
            break;
          case op::strong_X:
            res = formula_to_terminal_bdd(f[0]);
            break;
          case op::U:
            {
              bdd f0 = ltlf_to_mtbdd(f[0]);
              bdd f1 = ltlf_to_mtbdd(f[1]);
              bdd term = formula_to_terminal_bdd(f);
              res = combine_or(f1, combine_and(f0, term));
              break;
            }
          case op::W:
            {
              bdd f0 = ltlf_to_mtbdd(f[0]);
              bdd f1 = ltlf_to_mtbdd(f[1]);
              bdd term = formula_to_terminal_bdd(f, true);
              res = combine_or(f1, combine_and(f0, term));
              break;
            }
          case op::R:
            {
              bdd f0 = ltlf_to_mtbdd(f[0]);
              bdd f1 = ltlf_to_mtbdd(f[1]);
              bdd term = formula_to_terminal_bdd(f, true);
              res = combine_and(f1, combine_or(f0, term));
              break;
            }
          case op::M:
            {
              bdd f0 = ltlf_to_mtbdd(f[0]);
              bdd f1 = ltlf_to_mtbdd(f[1]);
              bdd term = formula_to_terminal_bdd(f);
              res = combine_and(f1, combine_or(f0, term));
              break;
            }
          case op::G:
            {
              bdd term = formula_to_terminal_bdd(f, true);
              res = combine_and(ltlf_to_mtbdd(f[0]), term);
              break;
            }
          case op::F:
            res = combine_or(ltlf_to_mtbdd(f[0]), formula_to_terminal_bdd(f));
            break;
          }
      }
    formula_to_bdd_[f] = res;
    return res;
  }

  static std::unordered_map<int, int> terminal_to_state_map;

  static int terminal_to_state(int terminal)
  {
#if NDEBUG
    int v = terminal_to_state_map[terminal / 2];
#else
    int v = terminal_to_state_map.at(terminal / 2);
#endif
    return 2 * v + (terminal & 1);
  }


  mtdfa_ptr ltlf_to_mtdfa(formula f, bdd_dict_ptr& dict,
                          bool fuse_same_bdds)
  {
    mtdfa_ptr dfa = std::make_shared<mtdfa>(dict);
    // collect all atomic propositions in f, and pre-register them for
    // the DFA.   We do that to ensure that the "promise" created by
    // the ltlf_translator is registered with a higher level.
    atomic_prop_set f_aps;
    atomic_prop_collect(f, &f_aps);
    for (formula f: f_aps)
      dict->register_proposition(f, dfa);

    ltlf_translator trans(dict);

    std::unordered_map<bdd, int, bdd_hash> bdd_to_state;
    std::unordered_map<formula, int> formula_to_state;
    std::vector<bdd> states;
    std::vector<formula> names;
    std::queue<formula> todo;
    terminal_to_state_map.clear();
    todo.push(f);
    while (!todo.empty())
      {
        formula label = todo.front();
        int label_term = trans.formula_to_terminal(label) / 2;
        todo.pop();

        // already processed
        if (terminal_to_state_map.find(label_term)
            != terminal_to_state_map.end())
          continue;

        bdd b = trans.ltlf_to_mtbdd(label);
        if (fuse_same_bdds)
          if (auto it = bdd_to_state.find(b); it != bdd_to_state.end())
            {
              formula_to_state[label] = it->second;
              terminal_to_state_map[label_term] = it->second;
              continue;
            }
        unsigned n = states.size();
        formula_to_state[label] = n;
        bdd_to_state[b] = n;
        states.push_back(b);
        names.push_back(label);
        terminal_to_state_map[label_term] = n;

        for (bdd leaf: leaves_of(b))
          {
            if (leaf == bddfalse || leaf == bddtrue)
              continue;
            int term = bdd_get_terminal(leaf);
            if (terminal_to_state_map.find(term / 2)
                == terminal_to_state_map.end())
              todo.push(trans.terminal_to_formula(term));
          }
      }

    // Currently, state[i] contains a bdd representing outgoing
    // transitions from state i, however the terminal values represent
    // formulas.  We need to remap the terminal values to state values.
    bddExtCache* cache = trans.get_cache();
    unsigned sz = states.size();
    for (unsigned i = 0; i < sz; ++i)
      states[i] = bdd_mt_apply1(states[i], terminal_to_state,
                                bddfalse, bddtrue,
                                cache, hash_key_rename);

    dfa->states = std::move(states);
    dfa->names = std::move(names);
    dict->register_all_variables_of(&trans, dfa);
    return dfa;
  }


  std::ostream& mtdfa::print_dot(std::ostream& os,
                                 int state, bool labels) const
  {
    std::ostringstream edges;

    os << "digraph mtdfa {\n  rankdir=TB;\n  node [shape=circle];\n";

    int statemin = 0;
    int statemax = states.size();
    if (state >= 0 && state < statemax)
      {
        statemin = state;
        statemax = state + 1;
      }
    else
      {
        os << "  { rank = source; I [label=\"\", style=invis, width=0]; }\n";
        edges << "  I -> S0\n";
      }

    os << "  { rank = same;\n";
    for (int i = statemin; i < statemax; ++i)
      {
        os << "    S" << i << " [shape=invhouse, label=\"";
        if (labels)
          escape_str(os, str_psl(names[i]));
        else
          os << i;
        os <<  "\"];\n";
      }

    for (int i = statemin; i < statemax; ++i)
      edges << "  S" << i << " -> B" << states[i].id() << ";\n";

    // This is a heap of BDD nodes, with smallest level at the top.
    std::vector<bdd> nodes;
    robin_hood::unordered_set<int> seen;

    nodes.reserve(states.size());
    for (int i = statemin; i < statemax; ++i)
      if (bdd b = states[i]; seen.insert(b.id()).second)
        nodes.push_back(b);

    auto bylvl = [&] (bdd a, bdd b) {
      return bdd_level(a) > bdd_level(b);
    };
    std::make_heap(nodes.begin(), nodes.end(), bylvl);

    int oldvar = -1;

    while (!nodes.empty())
      {
        std::pop_heap(nodes.begin(), nodes.end(), bylvl);
        bdd n = nodes.back();
        nodes.pop_back();
        if (n.id() <= 1)
          {
            if (oldvar != -2)
              os << "  }\n  { rank = sink;\n";
            os << "    B" << n.id()
               << " [shape=box, label=\"" << n.id() << '"';
            if (n.id() == 1)
              os << ", peripheries=2";
            os << "];\n";
            oldvar = -2;
            continue;
          }
        if (bdd_is_terminal(n))
          {
            if (oldvar != -2)
              os << "  }\n  { rank = sink;\n";
            os << "    B" << n.id() << " [shape=house, label=\"";
            int t = bdd_get_terminal(n);
            bool acc = t & 1;
            t /= 2;
            if (labels)
              {
                assert((unsigned) t < names.size());
                formula f = names[t];
                escape_str(os, str_psl(f)) << '"';
              }
            else
              {
                os << t << '"';
              }
            if (acc)
              os << ", peripheries=2";
            os << "];\n";
            oldvar = -2;
            continue;
          }
        int var = bdd_var(n);
        if (var != oldvar)
          {
            os << "  }\n  { rank = same;\n";
            oldvar = var;
          }
        os << "    B" << n.id() << " [label=\"";
        if ((unsigned) var < dict_->bdd_map.size()
            && dict_->bdd_map[bdd_var(n)].type == bdd_dict::var)
          escape_str(os, str_psl(dict_->bdd_map[var].f));
        else
          os << "bogus" << var;
        os << "\"];\n";

        bdd low = bdd_low(n);
        bdd high = bdd_high(n);
        if (seen.insert(low.id()).second)
          {
            nodes.push_back(low);
            std::push_heap(nodes.begin(), nodes.end(), bylvl);
          }
        if (seen.insert(high.id()).second)
          {
            nodes.push_back(high);
            std::push_heap(nodes.begin(), nodes.end(), bylvl);
          }
        edges << "  B" << n.id() << " -> B" << low.id()
              << " [style=dotted];\n  B" << n.id()
              << " -> B" << high.id() << " [style=filled];\n";
      }

    os << "  }\n";
    os << edges.str();
    os << "}\n";
    return os;
  }

  // convert the MTBDD DFA representation into a DFA.
  twa_graph_ptr mtdfa::as_twa(bool labels) const
  {
    twa_graph_ptr res = make_twa_graph(dict_);
    res->set_buchi();
    res->prop_state_acc(false);

    unsigned n = states.size();

    int true_state = -1;

    assert(n > 0);

    dict_->register_all_variables_of(this, res);
    res->register_aps_from_dict();

    std::vector<std::string>* names = nullptr;
    if (labels)
      {
        names = new std::vector<std::string>;
        names->reserve(n);
        for (unsigned i = 0; i < n; ++i)
          names->push_back(str_psl(this->names[i]));
        res->set_named_prop("state-names", names);
      }

    res->new_states(n);
    for (unsigned i = 0; i < n; ++i)
      for (auto [b, t]: paths_mt_of(states[i]))
        {
          if (t != bddtrue)
            {
              int v = bdd_get_terminal(t);
              assert((unsigned) v / 2 < n);
              res->new_acc_edge(i, v / 2, b, v & 1);
            }
          else
            {
              if (true_state == -1)
                {
                  true_state = res->new_state();
                  res->new_acc_edge(true_state, true_state, bddtrue, true);
                  if (names)
                    names->push_back("1");
                }
              res->new_acc_edge(i, true_state, bddtrue, true);
            }
        }

    res->merge_edges();
    return res;
  }

  static std::vector<int> classes;
  static int num_states;
  static bool accepting_false_seen;
  static bool rejecting_true_seen;

  static int rename_class(int val)
  {
    assert((unsigned) val/2 < classes.size());
    bool accepting = val & 1;
    val = classes[val / 2];
    if (val == num_states + accepting)
      {
        if (accepting)
          accepting_false_seen = true;
        else
          rejecting_true_seen = true;
      }
    return 2 * val + accepting;
  }

  mtdfa_ptr minimize_mtdfa(mtdfa_ptr dfa)
  {
    bddExtCache cache;
    bdd_extcache_init(&cache, 0);
    int iteration = 0;

    unsigned n = num_states = dfa->num_roots();

    // std::cerr << "-- input --\n";
    // for (unsigned i = 0; i < n; ++i)
    //   {
    //     std::cerr << i << "  " << dfa->names[i] << '\n';
    //     std::cerr << "   " << dfa->states[i] << '\n';
    //   }

    classes.clear();
    classes.resize(n + 2, 0);

    std::unordered_map<bdd, std::vector<int>, bdd_hash> groups;
    std::vector<bdd> states;
    states.reserve(n);
    for (;;)
      {
        ++iteration;
        bdd true_term = bdd_terminal(2 * classes[n] + 1);
        bdd false_term = bdd_terminal(2 * classes[n + 1]);
        accepting_false_seen = false;
        rejecting_true_seen = false;
        for (unsigned i = 0; i < n; ++i)
          {
            bdd sig = bdd_mt_apply1(dfa->states[i], rename_class,
                                    false_term, true_term,
                                    &cache, iteration);
            auto& v = groups[sig];
            if (v.empty())
              states.push_back(sig);
            v.push_back(i);
          }
        // Add the true_term to its group.
        {
          auto& v = groups[true_term];
          if (v.empty())
            states.push_back(true_term);
          v.push_back(n);
        }
        // Add the false_term to its group.
        {
          auto& v = groups[false_term];
          if (v.empty())
            states.push_back(false_term);
          v.push_back(n + 1);
        }

        int curclass = 0;
        // { // debug
        //   std::cerr << "iteration " << iteration << '\n';
        //   std::cerr << states.size() << " states\n";
        // }
        bool changed = false;
        // in this order, the initial state will always have class 0.
        for (bdd sig: states)
          {
            int mapclass = curclass++;
            auto& v = groups[sig];
            unsigned vb = v.back();
            if (vb >= n)
              mapclass = vb;
            for (unsigned i: v)
              if (classes[i] != mapclass)
                {
                  changed = true;
                  classes[i] = mapclass;
                }
            // { // debug
            //   std::cerr << "class " << mapclass << ':';
            //   for (unsigned i: v)
            //     std::cerr << ' ' << i;
            //   if (mapclass == (int) n)
            //     std::cerr << "  (true)";
            //   else if (mapclass == (int) n + 1)
            //     std::cerr << "  (false)";
            //   std::cerr << "\n      " << sig << '\n';
            // }
          }
        // for (unsigned i = 0; i <= n + 1; ++i)
        //   std::cerr << "classes[" << i << "]=" << classes[i] << '\n';
        if (!changed)
          break;
        groups.clear();
        states.clear();
      }

    // The BDDs in STATES are actually our new MTBDD representation.
    // We just have get rid of the terms we introduced to replace
    // bddfalse, and get rid of the states equivalent to bddfalse.
    //
    // And we have to keep one name per class for display.
    std::vector<formula> names;
    names.reserve(states.size());
    unsigned sz = states.size();
    unsigned j = 0;
    ++iteration;
    bdd true_term = bdd_terminal(2 * classes[n] + 1);
    bdd false_term = bdd_terminal(2 * classes[n + 1]);
    bool need_remap = false;
    for (unsigned i = 0; i < sz; ++i)
      {
        bdd sig = states[i];
        auto& v = groups[sig];
        assert(!v.empty());
        unsigned vb = v.back();
        if (vb == n + 1)      // equivalent to false!
          {
            if (i == 0) // the source state is false
              {
                assert(v.front() == 0);
                names.push_back(formula::ff());
                states[0] = bddfalse;
                ++j;
                break;
              }
            if (!accepting_false_seen)
              continue;
            classes[n + 1] = j;
            need_remap = true;
          }
        if (vb == n)      // equivalent to true!
          {
            if (i == 0) // the source state is true
              {
                assert(v.front() == 0);
                names.push_back(formula::tt());
                states[0] = bddtrue;
                ++j;
                break;
              }
            if (!rejecting_true_seen)
              continue;
            classes[n] = j;
            need_remap = true;
          }
        assert((unsigned) v.front() < dfa->names.size());
        names.push_back(dfa->names[v.front()]);
        sig = bdd_terminal_to_const(sig, false_term, true_term,
                                    &cache, iteration);
        classes[i] = j;
        if (i != j)
          need_remap = true;
        states[j++] = sig;
      }
    if (j < sz)
      states.resize(j);

    // std::cerr << "accepting_false_seen = " << accepting_false_seen << '\n';
    // std::cerr << "rejecting_true_seen = " << rejecting_true_seen << '\n';

    // std::cerr << "need_remap = " << need_remap << '\n';
    if (need_remap)
      {
        ++iteration;
        for (bdd& sig: states)
          sig = bdd_mt_apply1(sig, rename_class, bddfalse, bddtrue,
                              &cache, iteration);
      }
    // for (unsigned i = 0; i < j; ++i)
    //   {
    //     std::cerr << i << "  " << names[i] << '\n';
    //     std::cerr << "   " << states[i] << '\n';
    //   }

    mtdfa_ptr res = std::make_shared<mtdfa>(dfa->dict_);
    res->dict_->register_all_variables_of(dfa, res);
    std::swap(res->names, names);
    std::swap(res->states, states);

    bdd_extcache_done(&cache);
    return res;
  }
}
