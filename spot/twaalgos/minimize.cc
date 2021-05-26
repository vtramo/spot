// -*- coding: utf-8 -*-
// Copyright (C) 2010-2020 Laboratoire de Recherche et Développement
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

#define PRINTCSV
//#define TRACE
#ifdef TRACE
#  define trace std::cerr
#else
#  define trace while (0) std::cerr
#endif

#include "config.h"
#include <queue>
#include <deque>
#include <set>
#include <list>
#include <vector>
#include <sstream>
#include <type_traits>
#include <spot/twaalgos/minimize.hh>
#include <spot/misc/hash.hh>
#include <spot/misc/bddlt.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/gtec/gtec.hh>
#include <spot/twaalgos/strength.hh>
#include <spot/twaalgos/sccfilter.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/ltl2tgba_fm.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/dualize.hh>
#include <spot/twaalgos/remfin.hh>
#include <spot/twaalgos/alternation.hh>
#include <spot/twaalgos/game.hh>
#include <spot/tl/hierarchy.hh>
#include <spot/misc/satsolver.hh>
#include <spot/twaalgos/hoa.hh>

#include <spot/priv/synt_utils.hh>

namespace spot
{
  // This is called hash_set for historical reason, but we need the
  // order inside hash_set to be deterministic.
  typedef std::set<unsigned> hash_set;

  namespace
  {
    static std::ostream&
    dump_hash_set(const hash_set* hs,
                  std::ostream& out)
    {
      out << '{';
      const char* sep = "";
      for (auto i: *hs)
        {
          out << sep << i;
          sep = ", ";
        }
      out << '}';
      return out;
    }

    static std::string
    format_hash_set(const hash_set* hs)
    {
      std::ostringstream s;
      dump_hash_set(hs, s);
      return s.str();
    }

    // Find all states of an automaton.
    static void
    build_state_set(const const_twa_graph_ptr& a, hash_set* seen)
    {
      std::stack<unsigned> todo;
      unsigned init = a->get_init_state_number();
      todo.push(init);
      seen->insert(init);
      while (!todo.empty())
        {
          unsigned s = todo.top();
          todo.pop();
          for (auto& e: a->out(s))
            if (seen->insert(e.dst).second)
              todo.push(e.dst);
        }
    }

    // From the base automaton and the list of sets, build the minimal
    // resulting automaton
    static twa_graph_ptr
    build_result(const const_twa_graph_ptr& a,
                 std::list<hash_set*>& sets,
                 hash_set* final)
    {
      auto dict = a->get_dict();
      auto res = make_twa_graph(dict);
      res->copy_ap_of(a);
      res->prop_state_acc(true);

      // For each set, create a state in the output automaton.  For an
      // input state s, state_num[s] is the corresponding the state in
      // the output automaton.
      std::vector<unsigned> state_num(a->num_states(), -1U);
      {
        unsigned num = res->new_states(sets.size());
        for (hash_set* h: sets)
          {
            for (unsigned s: *h)
              state_num[s] = num;
            ++num;
          }
      }

      if (!final->empty())
        res->set_buchi();

      // For each transition in the initial automaton, add the
      // corresponding transition in res.
      for (hash_set* h: sets)
        {
          // Pick one state.
          unsigned src = *h->begin();
          unsigned src_num = state_num[src];
          bool accepting = (final->find(src) != final->end());

          // Connect it to all destinations.
          for (auto& e: a->out(src))
            {
              unsigned dn = state_num[e.dst];
              if ((int)dn < 0)  // Ignore useless destinations.
                continue;
              res->new_acc_edge(src_num, dn, e.cond, accepting);
            }
        }
      res->merge_edges();
      if (res->num_states() > 0)
        res->set_init_state(state_num[a->get_init_state_number()]);
      else
        res->set_init_state(res->new_state());
      return res;
    }

    static twa_graph_ptr minimize_dfa(const const_twa_graph_ptr& det_a,
                                      hash_set* final, hash_set* non_final)
    {
      typedef std::list<hash_set*> partition_t;
      partition_t cur_run;
      partition_t next_run;

      // The list of equivalent states.
      partition_t done;

      std::vector<unsigned> state_set_map(det_a->num_states(), -1U);

      // Size of det_a
      unsigned size = final->size() + non_final->size();
      // Use bdd variables to number sets.  set_num is the first variable
      // available.
      unsigned set_num =
        det_a->get_dict()->register_anonymous_variables(size, det_a);

      std::set<int> free_var;
      for (unsigned i = set_num; i < set_num + size; ++i)
        free_var.insert(i);
      std::map<int, int> used_var;

      hash_set* final_copy;

      if (!final->empty())
        {
          unsigned s = final->size();
          used_var[set_num] = s;
          free_var.erase(set_num);
          if (s > 1)
            cur_run.emplace_back(final);
          else
            done.emplace_back(final);
          for (auto i: *final)
            state_set_map[i] = set_num;

          final_copy = new hash_set(*final);
        }
      else
        {
          final_copy = final;
        }

      if (!non_final->empty())
        {
          unsigned s = non_final->size();
          unsigned num = set_num + 1;
          used_var[num] = s;
          free_var.erase(num);
          if (s > 1)
            cur_run.emplace_back(non_final);
          else
            done.emplace_back(non_final);
          for (auto i: *non_final)
            state_set_map[i] = num;
        }
      else
        {
          delete non_final;
        }

      // A bdd_states_map is a list of formulae (in a BDD form)
      // associated with a destination set of states.
      typedef std::map<bdd, hash_set*, bdd_less_than> bdd_states_map;

      bool did_split = true;

      while (did_split)
        {
          did_split = false;
          while (!cur_run.empty())
            {
              // Get a set to process.
              hash_set* cur = cur_run.front();
              cur_run.pop_front();

              trace << "processing " << format_hash_set(cur)
                    << std::endl;

              bdd_states_map bdd_map;
              for (unsigned src: *cur)
                {
                  bdd f = bddfalse;
                  for (auto si: det_a->out(src))
                    {
                      unsigned i = state_set_map[si.dst];
                      if ((int)i < 0)
                        // The destination state is not in our
                        // partition.  This can happen if the initial
                        // FINAL and NON_FINAL supplied to the algorithm
                        // do not cover the whole automaton (because we
                        // want to ignore some useless states).  Simply
                        // ignore these states here.
                        continue;
                      f |= (bdd_ithvar(i) & si.cond);
                    }

                  // Have we already seen this formula ?
                  bdd_states_map::iterator bsi = bdd_map.find(f);
                  if (bsi == bdd_map.end())
                    {
                      // No, create a new set.
                      hash_set* new_set = new hash_set;
                      new_set->insert(src);
                      bdd_map[f] = new_set;
                    }
                  else
                    {
                      // Yes, add the current state to the set.
                      bsi->second->insert(src);
                    }
                }

              auto bsi = bdd_map.begin();
              if (bdd_map.size() == 1)
                {
                  // The set was not split.
                  trace << "set " << format_hash_set(bsi->second)
                        << " was not split" << std::endl;
                  next_run.emplace_back(bsi->second);
                }
              else
                {
                  did_split = true;
                  for (; bsi != bdd_map.end(); ++bsi)
                    {
                      hash_set* set = bsi->second;
                      // Free the number associated to these states.
                      unsigned num = state_set_map[*set->begin()];
                      assert(used_var.find(num) != used_var.end());
                      unsigned left = (used_var[num] -= set->size());
                      // Make sure LEFT does not become negative (hence bigger
                      // than SIZE when read as unsigned)
                      assert(left < size);
                      if (left == 0)
                        {
                          used_var.erase(num);
                          free_var.insert(num);
                        }
                      // Pick a free number
                      assert(!free_var.empty());
                      num = *free_var.begin();
                      free_var.erase(free_var.begin());
                      used_var[num] = set->size();
                      for (unsigned s: *set)
                        state_set_map[s] = num;
                      // Trivial sets can't be split any further.
                      if (set->size() == 1)
                        {
                          trace << "set " << format_hash_set(set)
                                << " is minimal" << std::endl;
                          done.emplace_back(set);
                        }
                      else
                        {
                          trace << "set " << format_hash_set(set)
                                << " should be processed further" << std::endl;
                          next_run.emplace_back(set);
                        }
                    }
                }
              delete cur;
            }
          if (did_split)
            trace << "splitting did occur during this pass." << std::endl;
          else
            trace << "splitting did not occur during this pass." << std::endl;
          std::swap(cur_run, next_run);
        }

      done.splice(done.end(), cur_run);

#ifdef TRACE
      trace << "Final partition: ";
      for (hash_set* hs: done)
        trace << format_hash_set(hs) << ' ';
      trace << std::endl;
#endif

      // Build the result.
      auto res = build_result(det_a, done, final_copy);

      // Free all the allocated memory.
      delete final_copy;

      for (hash_set* hs: done)
        delete hs;

      return res;
    }
  }

  twa_graph_ptr minimize_monitor(const const_twa_graph_ptr& a)
  {
    if (!a->is_existential())
      throw std::runtime_error
        ("minimize_monitor() does not support alternation");

    hash_set* final = new hash_set;
    hash_set* non_final = new hash_set;
    twa_graph_ptr det_a = tgba_powerset(a);

    // non_final contain all states.
    // final is empty: there is no acceptance condition
    build_state_set(det_a, non_final);
    auto res = minimize_dfa(det_a, final, non_final);
    res->prop_copy(a, { false, false, false, false, true, true });
    res->prop_universal(true);
    res->prop_weak(true);
    res->prop_state_acc(true);
    // Quickly check if this is a terminal automaton
    for (auto& e: res->edges())
      if (e.src == e.dst && e.cond == bddtrue)
        {
          res->prop_terminal(true);
          break;
        }
    return res;
  }

  twa_graph_ptr minimize_wdba(const const_twa_graph_ptr& a,
                              const output_aborter* aborter)
  {
    if (!a->is_existential())
      throw std::runtime_error
        ("minimize_wdba() does not support alternation");

    hash_set* final;
    hash_set* non_final;

    twa_graph_ptr det_a;
    bool has_sinks = false;
    {
      bool input_is_det = is_deterministic(a);
      if (input_is_det)
        {
          det_a = std::const_pointer_cast<twa_graph>(a);
        }
      else
        {
          // Find any accepting sink state, to speed up the
          // determinization by merging all states containing a sink
          // state.
          std::vector<unsigned> acc_sinks;
          unsigned ns = a->num_states();
          if (!a->prop_terminal().is_true())
            {
              // We only consider as "accepting sink" any state
              // that has an accepting self-loop labeled by true.
              for (unsigned n = 0; n < ns; ++n)
                for (auto& e: a->out(n))
                  if (e.dst == n && e.cond == bddtrue
                      && a->acc().accepting(e.acc))
                    {
                      acc_sinks.push_back(n);
                      break;
                    }
            }
          else
            {
              // All accepting SCCs are terminal.
              scc_info si(a, scc_info_options::NONE);
              for (unsigned n = 0; n < ns; ++n)
                if (si.is_accepting_scc(si.scc_of(n)))
                  acc_sinks.push_back(n);
            }
          has_sinks = !acc_sinks.empty();
          det_a = tgba_powerset(a, aborter, &acc_sinks);
          if (!det_a)
            return nullptr;
        }

      // For each SCC of the deterministic automaton, determine if it
      // is accepting or not.

      // This corresponds to the algorithm in Fig. 1 of "Efficient
      // minimization of deterministic weak omega-automata" written by
      // Christof Löding and published in Information Processing
      // Letters 79 (2001) pp 105--109.

      // We also keep track of whether an SCC is useless
      // (i.e., it is not the start of any accepting word).

      scc_info sm(det_a);
      unsigned scc_count = sm.scc_count();

      // SCCs of det_a are assumed accepting if any of their loop
      // corresponds to an accepted word in the original automaton.
      // If the automaton is the same as det_a, we can simply ask that
      // to sm.
      std::vector<char> is_accepting_scc(scc_count, 0);
      if (input_is_det)
        {
          sm.determine_unknown_acceptance();
          for (unsigned m = 0; m < scc_count; ++m)
            is_accepting_scc[m] = sm.is_accepting_scc(m);
        }
      else if (a->prop_terminal())
        {
          // tgba_powerset has gathered all terminal states on
          // powerstate 0.
          if (has_sinks)
            is_accepting_scc[sm.scc_of(0)] = true;
        }
      else
        {
          twa_graph_ptr prod = spot::product(a, det_a, aborter);
          if (!prod)
            return nullptr;

          const product_states* pmap =
            prod->get_named_prop<product_states>("product-states");
          assert(pmap);
          scc_info sip(prod, scc_info_options::TRACK_STATES_IF_FIN_USED);
          sip.determine_unknown_acceptance();
          unsigned prod_scc_count = sip.scc_count();
          for (unsigned m = 0; m < prod_scc_count; ++m)
            if (sip.is_accepting_scc(m))
              {
                unsigned right_state = (*pmap)[sip.one_state_of(m)].second;
                is_accepting_scc[sm.scc_of(right_state)] = true;
              }
        }

      final = new hash_set;
      non_final = new hash_set;

      // SCC that have been marked as useless.
      std::vector<bool> useless(scc_count);
      // The "color".  Even number correspond to
      // accepting SCCs.
      std::vector<unsigned> d(scc_count);

      // An even number larger than scc_count.
      unsigned k = (scc_count | 1) + 1;

      // SCC are numbered in topological order
      // (but in the reverse order as Löding's)
      for (unsigned m = 0; m < scc_count; ++m)
        {
          bool is_useless = true;
          bool transient = sm.is_trivial(m);
          auto& succ = sm.succ(m);

          // Compute the minimum color l of the successors.  Also SCCs
          // are useless if all their successor are useless.  Note
          // that Löding uses k-1 as level for non-final SCCs without
          // successors but that seems bogus: using k+1 will make sure
          // that a non-final SCCs without successor (i.e., a useless
          // SCC) will be ignored in the computation of the level.
          unsigned l = k + 1;
          for (unsigned j: succ)
            {
              is_useless &= useless[j];
              unsigned dj = d[j];
              if (dj < l)
                l = dj;
            }

          if (transient)
            {
              d[m] = l;
            }
          else
            {
              if (is_accepting_scc[m])
                {
                  is_useless = false;
                  d[m] = l & ~1; // largest even number inferior or equal
                }
              else
                {
                  if (succ.empty())
                    is_useless = true;
                  d[m] = (l - 1) | 1; // largest odd number inferior or equal
                }
            }

          useless[m] = is_useless;

          if (!is_useless)
            {
              hash_set* dest_set = (d[m] & 1) ? non_final : final;
              auto& con = sm.states_of(m);
              dest_set->insert(con.begin(), con.end());
            }
        }
    }

    auto res = minimize_dfa(det_a, final, non_final);
    res->prop_copy(a, { false, false, false, false, false, true });
    res->prop_universal(true);
    res->prop_weak(true);
    // If the input was terminal, then the output is also terminal.
    // FIXME:
    // (1) We should have a specialized version of this function for
    // the case where the input is terminal.  See issue #120.
    // (2) It would be nice to have a more precise detection of
    // terminal automata in the output.  Calling
    // is_terminal_automaton() seems overkill here.  But maybe we can
    // add a quick check inside minimize_dfa.
    if (a->prop_terminal())
      res->prop_terminal(true);
    return res;
  }

  // Declared in tl/hierarchy.cc, but defined here because it relies on
  // other internal functions from this file.
  SPOT_LOCAL bool is_wdba_realizable(formula f, twa_graph_ptr aut = nullptr);

  bool is_wdba_realizable(formula f, twa_graph_ptr aut)
  {
    if (f.is_syntactic_obligation())
      return true;

    if (aut == nullptr)
      aut = ltl_to_tgba_fm(f, make_bdd_dict(), true);

    if (!aut->is_existential())
      throw std::runtime_error
        ("is_wdba_realizable() does not support alternation");

    if ((f.is_syntactic_persistence() || aut->prop_weak())
        && (f.is_syntactic_recurrence() || is_deterministic(aut)))
      return true;

    if (is_terminal_automaton(aut))
      return true;

    // FIXME: we do not need to minimize the wdba to test realizability.
    auto min_aut = minimize_wdba(aut);

    twa_graph_ptr aut_neg;
    if (is_deterministic(aut))
      {
        aut_neg = remove_fin(dualize(aut));
      }
    else
      {
        aut_neg = ltl_to_tgba_fm(formula::Not(f), aut->get_dict());
        aut_neg = scc_filter(aut_neg, true);
      }

    if (is_terminal_automaton(aut_neg))
      return true;

    return product(min_aut, aut_neg)->is_empty();
  }

  bool minimize_obligation_garanteed_to_work(const const_twa_graph_ptr& aut_f,
                                             formula f)
  {
    // WDBA-minimization necessarily work for obligations
    return ((f && f.is_syntactic_obligation())
            // Weak deterministic automata are obligations
            || (aut_f->prop_weak().is_true() && is_deterministic(aut_f))
            // Guarantee automata are obligations as well.
            || is_terminal_automaton(aut_f));
  }

  twa_graph_ptr
  minimize_obligation(const const_twa_graph_ptr& aut_f,
                      formula f,
                      const_twa_graph_ptr aut_neg_f,
                      bool reject_bigger,
                      const output_aborter* aborter)
  {
    if (!aut_f->is_existential())
      throw std::runtime_error
        ("minimize_obligation() does not support alternation");

    bool minimization_will_be_correct = false;
    if (minimize_obligation_garanteed_to_work(aut_f, f))
      {
        minimization_will_be_correct = true;
      }
    else if (!aut_neg_f)
      {
        // The minimization might not be correct and will need to
        // be checked.   Are we able to build aut_neg_f?
        if (!(is_deterministic(aut_f) || f || is_very_weak_automaton(aut_f)))
          return nullptr;
      }

    // FIXME: We should build scc_info once, and reuse it between
    //  minimize_wdba is_terminal_automaton(), is_weak_automaton(),
    //  and is_very_weak_automaton().
    auto min_aut_f = minimize_wdba(aut_f, aborter);

    if (!min_aut_f)
      return std::const_pointer_cast<twa_graph>(aut_f);
    if (reject_bigger)
      {
        // Abort if min_aut_f has more states than aut_f.
        unsigned orig_states = aut_f->num_states();
        if (orig_states < min_aut_f->num_states())
          return std::const_pointer_cast<twa_graph>(aut_f);
      }

    if (minimization_will_be_correct)
      return min_aut_f;

    // The minimization might not be correct and will need to
    // be checked.   Build negation automaton if not supplied.
    if (!aut_neg_f)
      {
        if (is_deterministic(aut_f))
          {
            // If the automaton is deterministic, complementing is
            // easy.
            aut_neg_f = dualize(aut_f);
          }
        else if (f)
          {
            // If we know the formula, simply build the automaton for
            // its negation.
            aut_neg_f = ltl_to_tgba_fm(formula::Not(f), aut_f->get_dict());
            // Remove useless SCCs.
            aut_neg_f = scc_filter(aut_neg_f, true);
          }
        else if (is_very_weak_automaton(aut_f))
          {
            // Very weak automata are easy to complement.
            aut_neg_f = remove_alternation(dualize(aut_f));
          }
        else
          {
            // Otherwise, we don't try to complement the automaton and
            // therefore we cannot check if the minimization is safe.
            return nullptr;
          }
      }
    // Make sure the minimized WDBA does not accept more words than
    // the input.
    auto prod = product(min_aut_f, aut_neg_f, aborter);
    if (prod && prod->is_empty())
      {
        assert((bool)min_aut_f->prop_weak());
        return min_aut_f;
      }
    else
      {
        return std::const_pointer_cast<twa_graph>(aut_f);
      }
  }
}

namespace
{
  // Anonymous for minimize_mealy_fast
  using namespace spot;

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

  // This part is just a copy of a part of simulation.cc only suitable for
  // deterministic monitors.
  class sig_calculator final
  {
  protected:
    typedef std::unordered_map<bdd, bdd, bdd_hash> map_bdd_bdd;
    int acc_vars;
    acc_cond::mark_t all_inf_;

  public:

    sig_calculator(twa_graph_ptr aut, bool implications) : a_(aut),
        po_size_(0),
        want_implications_(implications)
    {
      size_a_ = a_->num_states();
      // Now, we have to get the bdd which will represent the
      // class. We register one bdd by state, because in the worst
      // case, |Class| == |State|.
      unsigned set_num = a_->get_dict()
                           ->register_anonymous_variables(size_a_, this);

      bdd init = bdd_ithvar(set_num++);

      used_var_.emplace_back(init);

      // Initialize all classes to init.
      previous_class_.resize(size_a_);
      for (unsigned s = 0; s < size_a_; ++s)
        previous_class_[s] = init;
      for (unsigned i = set_num; i < set_num + size_a_ - 1; ++i)
        free_var_.push(i);

      relation_.reserve(size_a_);
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

      while (nb_partition_before != bdd_lstate_.size()
          || nb_po_before != po_size_)
      {
        update_previous_class();
        nb_partition_before = bdd_lstate_.size();
        nb_po_before = po_size_;
        po_size_ = 0;
        update_sig();
        go_to_next_it();
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

      assert((bdd_lstate_.size() == used_var_.size())
          || (bdd_lstate_.find(bddfalse) != bdd_lstate_.end()
            && bdd_lstate_.size() == used_var_.size() + 1));

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
  };

  // This class is a tree where the root is ⊤ and a node implies its parent
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
                  // If a child contains a BDD that implies the value, we
                  // create a new bdd_tree. It must contains all the children
                  // that imply value
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
      if (children.empty())
        return label;
      return children[0].get_lowest_bdd();
    }

    unsigned
    flatten_aux(std::map<bdd, unsigned, bdd_less_than> &res)
    {
      if (children.empty())
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
  };

  // Associate to a state a representative
  std::vector<unsigned>
  get_repres(twa_graph_ptr& a, bool rec)
  {
    const auto a_num_states = a->num_states();
    // We can only assign a new destination for the transitions that
    // go to a controller state.
    auto owner_ptr = a->get_named_prop<std::vector<bool>>("state-player");

    std::vector<unsigned> repr(a_num_states);
    bdd_tree tree;
    std::unordered_set<bdd, spot::bdd_hash> bdd_done;
    bdd_done.insert(bddtrue);
    std::vector<bdd> signatures(a_num_states);
    sig_calculator red(a, rec);
    red.main_loop();
    for (unsigned i = 0; i < a_num_states; ++i)
      {
        if (owner_ptr && (*owner_ptr)[i] == 0)
          continue;
        bdd sig = red.compute_sig(i);
        signatures.insert(signatures.begin() + i, sig);
        if (bdd_done.find(sig) == bdd_done.end())
          {
            tree.add_child(sig, i, rec);
            bdd_done.insert(sig);
          }
      }
    auto repr_map = tree.flatten();
    for (unsigned i = 0; i < a_num_states; ++i)
    {
      if (owner_ptr && (*owner_ptr)[i] == 0)
        repr[i] = i;
      else
        repr[i] = repr_map[signatures[i]];
    }
    // With rec we are able to change the initial state if the automaton is
    // splitted.
    if (rec && owner_ptr)
    {
      unsigned orig_init = a->get_init_state_number();
      unsigned new_init = orig_init;
      bdd init_bdd = red.compute_sig(new_init);
      for (unsigned i = 0; i < a_num_states; ++i)
      {
        if ((*owner_ptr)[i] == 0)
        {
          bdd other_bdd = red.compute_sig(i);
          if (bdd_implies(other_bdd, init_bdd))
          {
            new_init = i;
            init_bdd = other_bdd;
          }
        }
      }
      repr[orig_init] = new_init;
    }
    else if (!rec && owner_ptr)
    {
      unsigned orig_init = a->get_init_state_number();
      bdd init_bdd = red.compute_sig(orig_init);
      for (auto& e : a->edges())
        if ((*owner_ptr)[e.dst] == 0)
        {
          auto other_bdd = red.compute_sig(e.dst);
          if (other_bdd == init_bdd)
          {
            repr[orig_init] = e.dst;
            break;
          }
        }
    }
    return repr;
  }
}

namespace spot
{
  twa_graph_ptr minimize_mealy_fast(const const_twa_graph_ptr& mm,
                                    bool use_inclusion)
  {
    auto mmc = make_twa_graph(mm, twa::prop_set::all());
    mmc->copy_ap_of(mm);
    mmc->copy_acceptance_of(mm);
    auto sp = mm->get_named_prop<std::vector<bool>>("state-player");
    assert(sp);
    auto nsp = new std::vector<bool>(*sp);
    mmc->set_named_prop("state-player", nsp);
    minimize_mealy_fast_here(mmc, use_inclusion);
    // Try to set outputs
    if (bdd* outptr = mm->get_named_prop<bdd>("synthesis-outputs"))
      mmc->set_named_prop("synthesis-outputs", new bdd(*outptr));
    return mmc;
  }

  void minimize_mealy_fast_here(twa_graph_ptr& mm, bool use_inclusion)
  {
    // Only consider infinite runs
    mm->purge_dead_states();

    if (mm->num_states() == 1)
      return;

    auto repr = get_repres(mm, use_inclusion);
    // Check if no reduction is possible
    // This is the case if there are as many classes and states
    // and in this case each state simply represents itself
    {
      bool has_reduc = false;
      for (size_t i = 0; i < repr.size(); ++i)
        if (repr[i] != i)
          {
            has_reduc = true;
            break;
          }
      if (!has_reduc)
        return;
    }

    auto init = repr[mm->get_init_state_number()];
    mm->set_init_state(init);
    std::stack<unsigned> todo;
    std::vector<bool> done(mm->num_states(), false);
    todo.emplace(init);
    while (!todo.empty())
      {
        auto current = todo.top();
        todo.pop();
        done[current] = true;
        for (auto& e : mm->out(current))
          {
            if (e.dst == current)
              continue;
            auto repr_dst = repr[e.dst];
            e.dst = repr_dst;
            if (!done[repr_dst])
              todo.emplace(repr_dst);
          }
      }
    mm->purge_unreachable_states();
    if (mm->get_named_prop<std::vector<bool>>("state-player"))
      alternate_players(mm, false, false);
  }
}



// Anonymous for mealy minimization
namespace
{
  using namespace spot;
  using namespace minutils;

  struct info_struct_t
  {
    double t_premin;
    double red_split;
    double incomp;
    double build_cover;
    double build_closure;
    double sat_part_time;
    double sat_time;
    double build_time;
    unsigned sigma;
    unsigned sigma_red;
    unsigned n_trans;
    unsigned n_part_vars;
    unsigned n_vars;
    unsigned n_part_clauses;
    unsigned n_clauses;
    int part_feas;
  }info_struct;

  template<class IT>
  void print_help(IT beg, IT end, std::string init = "", std::string sep = " ")
  {
#ifndef TRACE
    return;
#endif
    std::cout << init << '\n';
    for (; beg != end; ++beg)
      std::cout << *beg << sep;
    std::cout << '\n';
  }
  void printlit(std::initializer_list<int> L)
  {
#ifndef TRACE
    return;
#endif
    size_t count = 0;
    for (int alit : L)
    {
      ++count;
      if (alit == 0)
        trace << alit << '\n';
      else
        trace << alit << ' ';
    }
    assert(count == L.size());
  }

  template<class SP>
  auto reduce_and_split(const const_twa_graph_ptr& mm, const SP& spref)
    {
      // First step
      // Compute a "reduced" input alphabet
      // That is a set of bdd's that partitions all input conditions appearing
      // in the mm into disjoint bdd's
      // todo faster?
      std::deque<bdd> used_bdds;
      for (const auto& e : mm->edges())
        {
          if (spref[e.src])
            continue; // Skip player states
          bdd rcond = e.cond;
          assert(rcond != bddfalse && "Inactive edges are forbiden");
          // Check against all currently used "letters"
          const size_t osize = used_bdds.size();
          for (size_t i = 0; i < osize; ++i)
            {
              assert(used_bdds[i] != bddfalse);
              // Check if they are equal
              // If so we are done
              if (used_bdds[i] == rcond)
                {
                  rcond = bddfalse;
                  break;
                }
              bdd inter = used_bdds[i] & rcond;
              if (inter == bddfalse)
                continue; // No intersection
              if (used_bdds[i] != inter)
                {
                  used_bdds[i] -= inter;
                  used_bdds.push_back(inter);
                }
              rcond -= inter;
              // Early exit?
              if (rcond == bddfalse)
                break;
            }
          // Leftovers?
          if (rcond != bddfalse)
            used_bdds.push_back(rcond);
        }
      // Sort the used_bdds with respect to their id
      std::sort(used_bdds.begin(), used_bdds.end(),
                [](const auto& c1, const auto& c2){return c1.id() < c2.id(); });
      assert([&](){
        for (size_t i1 = 0; i1 < used_bdds.size(); ++i1)
          for (size_t i2 = i1+1; i2 < used_bdds.size(); ++i2)
            if ((used_bdds[i1] & used_bdds[i2]) != bddfalse)
              return false;
        return true; }());

#ifdef TRACE
      trace << "Resulting alphabet has size " << used_bdds.size() <<'\n';
      for (const auto& b : used_bdds)
        trace << b.id() << " : " << b << '\n';
      trace << std::endl;
#endif
      const unsigned n_sigma = used_bdds.size();

      // We determined our "alphabet"
      // Now we construct a new automaton that has env
      // edges labeled by the new alphabet
      auto splitmm = make_twa_graph(mm->get_dict());
      splitmm->copy_ap_of(mm);

      // We want the env state to be the "first"
      std::unordered_map<unsigned, unsigned> smap; //mm->splitmm
      smap.reserve(mm->num_states());
      const size_t n_player = std::count(spref.cbegin(), spref.cend(), true);
      size_t next_player = mm->num_states() - n_player;
      size_t next_env = 0;
      // Fill the map
      for (unsigned i = 0; i < mm->num_states(); ++i)
        {
          if (spref[i])
            {
              assert(next_player < mm->num_states());
              smap[i] = next_player;
              ++next_player;
            }
          else
            {
              smap[i] = next_env;
              ++next_env;
            }
        }
      splitmm->new_states(mm->num_states());
      splitmm->set_init_state(smap[mm->get_init_state_number()]);
      // Split all the env edges
      // only keep active edges
      // Copy player edges
      std::vector<unsigned> dst_cache(n_sigma);
      for (unsigned s = 0; s < mm->num_states(); ++s)
        {
          if (spref[s])
            {
              // Player edge
              auto eit = mm->out(s);
              auto itb = eit.begin();
              assert(itb->cond != bddfalse);
              splitmm->new_edge(smap.at(itb->src), smap.at(itb->dst),
                                itb->cond);
              assert(++itb == eit.end()); // No multistrat
            }
          else
            {
              // Split all edges
              // Cache the dsts to get the edge in order
              std::fill(dst_cache.begin(), dst_cache.end(), -1u);
              for (const auto& e : mm->out(s))
                {
                  bdd rcond = e.cond;
                  for (unsigned a = 0; a < n_sigma; ++a)
                    {
                      const bdd& b = used_bdds[a];
                      if (bdd_implies(b, rcond))
                        {
                          assert(dst_cache[a] == -1u);
                          // The outgoing edges are also sorted by id
                          dst_cache[a] = e.dst;
                          rcond -= b;
                          // todo: we could also not construct rcond and test all
                          // tradeoff construction vs early exit
                        }
                      if (rcond == bddfalse)
                        break; // Done
                    }
                  assert(rcond == bddfalse);
                }
              // Create the actual edges
              unsigned split_src = smap.at(s);
              for (unsigned a = 0; a < n_sigma; ++a)
                if (dst_cache[a] != -1u)
                  // There is a transition for this letter
                  splitmm->new_edge(split_src, smap.at(dst_cache[a]),
                                    used_bdds[a]);
            }
        }

      // Compute a further reduction
      // If there exist two letters a and b such that
      // for any state si the successor under a and b is the same
      // (including unspecified behaviour)
      // then we can use solely a or b in the sat problem
      // Note: Only in the sat, not to determine the incomp matrix
//      auto vctr_hash = [](const auto& v) -> size_t
//        {
//          size_t h = wang32_hash(v.size());
//          for (auto e : v)
//            h = wang32_hash(h ^ ((size_t) e));
//          return h;
//        };
      auto vctr_hash = [](const auto& v) -> size_t
        {
          size_t vs = v.size();
          size_t h = wang32_hash(vs);
          size_t hh;
          // FIXME: When size % 3 != 0
          for (size_t i = 0; i < vs; i += 3)
            {
              hh = v[i];
              hh <<= 20;
              hh += v[i+1];
              hh <<= 20;
              hh += v[i+2];
              h = h ^ wang32_hash(hh);
            }
          return wang32_hash(h);
        };

      std::unordered_multimap<size_t,
                    std::pair<unsigned, std::vector<unsigned>>> tgt_map;
      // Check for all letters if there is one with the same tgts
      const size_t n_env = splitmm->num_states() - n_player;
      //{equiv class, linear idx}
      std::vector<std::pair<unsigned, unsigned>> reduction_map;
      reduction_map.reserve(used_bdds.size());
      std::vector<unsigned> tgt_of_a(n_env, -1u);
      std::vector<decltype(splitmm->out(0).begin())> edge_it;
      edge_it.reserve(n_env);
      for (unsigned s = 0; s < n_env; ++s)
        edge_it.push_back(splitmm->out(s).begin());
      // All nodes have at least one outgoing
      // Note, not all states have the same number of outgoing edges!
      int lin_idx = 0;

      auto gss = [&](const auto& eit)->unsigned
        {
          // We get an env edge and want the next env state
          return splitmm->out(eit->dst).begin()->dst;
        };

      for (unsigned a = 0; a < used_bdds.size(); ++a)
        {
          std::fill(tgt_of_a.begin(), tgt_of_a.end(), -1u);
          for (unsigned s = 0; s < n_env; ++s)
            {
              // Check if the state s has a succ for a
              // If so, set and advance, otherwise it is smaller
              // and only a advance
              if (used_bdds[a].id() == edge_it[s]->cond.id())
                {
                  tgt_of_a[s] = gss(edge_it[s]);
                  ++edge_it[s];
                  assert(tgt_of_a[s] < n_env);
                }
              assert((edge_it[s] == splitmm->out(s).end())
                      || (used_bdds[a].id() < edge_it[s]->cond.id()));
            }
          // Hash the vector
          size_t th = vctr_hash(tgt_of_a);
          // Check if existing
          auto [it, it_end] = tgt_map.equal_range(th);
          bool found = false;
          for (; it != it_end; ++it)
            if (it->second.second == tgt_of_a)
              {
                // Found it
                reduction_map.emplace_back(reduction_map.at(it->second.first));
                found = true;
                break;
              }
          // If it does not exist -> emplace it with a new index
          if (!found)
            {
              tgt_map.emplace(th, std::make_pair(reduction_map.size(),
                                                 tgt_of_a));
              reduction_map.emplace_back(a, lin_idx++);
            }
          // A letter is a minimal letter if it defines it own class
        }
      assert([&]()
        {
          for (unsigned s = 0; s < n_env; ++s)
            if (edge_it[s] != splitmm->out(s).end())
              return false;
          return true;
        }());

      return std::make_tuple(splitmm, used_bdds, reduction_map,
                             n_env, lin_idx);
    }

  square_matrix<uint8_t> incomp_mat(const const_twa_graph_ptr& splitmm,
                                    const size_t n_env)
  {
    // States are incompatible if they
    // (1) If there exists an input for which no common output exists
    //     If one the states has no defined behaviour for the letter they are
    //     automatically compatible
    // (2) If there exists an input such that the successors are incompatible

    // We need a transposed "graph" for env states
    // We only store cond and target
    // If {c_in, i} is in trans[j] then in the graph there is
    // (i) - c_in > (pij) - c_out > (j)
    // For c_in != bddfalse
    // This does not rely on completeness
    std::vector<std::vector<std::pair<bdd, unsigned>>> trans(n_env);
    for (unsigned env_src = 0; env_src < n_env; ++env_src)
      {
        for (const auto& eenvply : splitmm->out(env_src))
          {
            assert(eenvply.dst >= n_env);
            if (eenvply.cond == bddfalse)
              continue;
            auto eit = splitmm->out(eenvply.dst);
            auto itb = eit.begin();
            trans[itb->dst].emplace_back(eenvply.cond, env_src);
            assert(++itb == eit.end());
//            bool is_multi = false;
//            for (const auto& eplyenv : splitmm->out(eenvply.dst))
//              {
//                signal_multi(is_multi);
//                assert(eplyenv.dst < n_env);
//                assert(eenvply.cond != bddfalse);
//                is_multi = true;
//                trans[eplyenv.dst].emplace_back(eenvply.cond, env_src);
//              }
          }
      }
    // Sort all the vectors with respect to the id of the condition
    std::for_each(trans.begin(), trans.end(),
                 [](auto& v){
                   std::sort(v.begin(), v.end(),
                     [](const auto& p1,
                        const auto& p2){ return p1.first.id()
                                                < p2.first.id(); }); });

    // We only need incompatibility for env states
    square_matrix<uint8_t> incompmat(n_env, false); //Everyone is compatible

    // If a pair of incompatible states has a predescessor under
    // the same input, then they are also incompatible
    // todo this has to change for multistrat
    auto tag_common_pred = [&](unsigned s0, unsigned s1)
      {
        static std::vector<std::pair<unsigned, unsigned>> todo_;
        assert(todo_.empty());

        todo_.emplace_back(s0, s1);

        while (!todo_.empty())
          {
            auto [si, sj] = todo_.back();
            todo_.pop_back();

            // The edges in trans are sorted, so we can iterate over them jointly
            auto itpredi = trans[si].cbegin();
            auto itpredi_e = trans[si].cend();
            auto itpredj = trans[sj].cbegin();
            auto itpredj_e = trans[sj].cend();

            // The only way a state can have no predescessors
            // is if it is the init state
            assert((itpredi != itpredi_e)
                   || (si == splitmm->get_init_state_number()));
            assert((itpredj != itpredj_e)
                   || (sj == splitmm->get_init_state_number()));

            while ((itpredi != itpredi_e)
                  && (itpredj != itpredj_e))
              {
                if (itpredi->first.id() < itpredj->first.id())
                  ++itpredi;
                else if (itpredj->first.id() < itpredi->first.id())
                  ++itpredj;
                else
                  {
                    // itpredi and itpredj point to the beginning
                    // of possibly a block of common inputs
                    // 1) Find the respective ends
                    auto itpredi_eloc = itpredi;
                    auto itpredj_eloc = itpredj;
                    while ((itpredi_eloc != itpredi_e)
                           && (itpredi->first == itpredi_eloc->first))
                      ++itpredi_eloc;
                    while ((itpredj_eloc != itpredj_e)
                          && (itpredj->first == itpredj_eloc->first))
                      ++itpredj_eloc;
                    // Declare all combinations as incompatible and add the
                    // pairs to todo
                    for (auto iti = itpredi; iti != itpredi_eloc; ++iti)
                      for (auto itj = itpredj; itj != itpredj_eloc; ++itj)
                        {
                          if (incompmat(iti->second, itj->second))
                            {
                              assert(incompmat(itj->second, iti->second)
                                     && "Must be sym");
                              continue; //Have already been incomp
                            }
                          incompmat(iti->second, itj->second) = true;
                          incompmat(itj->second, iti->second) = true;
                          todo_.emplace_back(iti->second, itj->second);
                        }
                    // Resume after the blocks
                    itpredi = itpredi_eloc;
                    itpredj = itpredj_eloc;
                  }

              }
          }// All tagged
      };


    // As we tag all predescessors directly, we only need to loop once
    for (unsigned si = 0; si < n_env; ++si)
      for (unsigned sj = si + 1; sj < n_env; ++sj)
        {
          // if they are incomp -> done
          if (incompmat(si, sj))
            continue;

          // Check if for all the inputs, the output is compatible
          // Note that if for a letter one of the states has no successor
          // it is ok. They only need to agree on specified behaviour
          auto ei = splitmm->out(si).begin();
          auto ei_end = splitmm->out(si).end();
          auto ej = splitmm->out(sj).begin();
          auto ej_end = splitmm->out(sj).end();
          // Every state needs an outgoing state
          assert(ei != ei_end);
          assert(ej != ej_end);
          auto succ_ocond = [&splitmm](const auto& eit) ->const bdd&
            {
              // Get the outcond associated
              return splitmm->out(eit->dst).begin()->cond;
            };
          while ((ei != ei_end)
                && (ej != ej_end))
            {
              if (ei->cond.id() < ej->cond.id())
                ++ei;
              else if (ej->cond.id() < ei->cond.id())
                ++ej;
              else
                {
                  // We got a matching letter
                  // Check if outs are compatible
                  if ((succ_ocond(ei) & succ_ocond(ej)) == bddfalse)
                    {
                      // No common ocond possible
                      incompmat(si, sj) = true;
                      incompmat(sj, si) = true; //sym
                      // tag predescessors
                      tag_common_pred(si, sj);
                      // We do not need to continue
                      break;
                    }
                  else
                    {
                      // Advance if compatible
                      ++ei;
                      ++ej;
                    }
                }
            } // while
          assert(ei == ei_end || ej == ej_end || incompmat(si, sj));
        } // sj
    //si
#ifdef TRACE
    trace << "incomp mat\n";
    incompmat.print();
#endif
    return incompmat;
  }

  struct greedy_cover_t
  {
    // Rows -> classes
    // Cols -> Incomp state
    //(i,j) == 1 -> state j can not be in class i
    const square_matrix<uint8_t>& incomp_ref_;
    unsigned n_classes_;
    const part_sol_t& partsol_;
    unsigned idx_distrib; // Number of states already treated
    square_matrix<uint8_t> incomp_classes;

    greedy_cover_t(const square_matrix<uint8_t>& incomp_ref,
                   unsigned n_classes,
                   const part_sol_t& partsol)
      : incomp_ref_(incomp_ref)
      , n_classes_(n_classes)
      , partsol_(partsol)
      , idx_distrib(0)
    {
      // Check if we can build a greedy cover
      // using n_classes_
      assert(n_classes_ >= partsol_.psol_v.size());
      if (n_classes_ == incomp_ref_.dim())
        // In this case we do not need to build anything
        // as no minimization is possible
        idx_distrib = incomp_ref_.dim();
      else
        {
          assert(n_classes_ < incomp_ref_.dim());
          incomp_classes = square_matrix<uint8_t>(incomp_ref.dim());

          //First use the partial solution
          size_t n_psol = partsol_.psol_v.size();
          for (unsigned i = 0; i < n_psol; ++i)
            {
              auto cline_it = incomp_ref_.get_cline(partsol.psol_v[i]);
              std::copy(cline_it.first, cline_it.second,
                        incomp_classes.get_line(i).first);
            }

          // (Try to) distribute the remaining states
          while (add_one());
        }
    }

    bool add_one()
    {
      assert(incomp_classes.dim() == incomp_ref_.dim());
      // Get the next state that was not part of
      // the partial solution and add it to some class
      // if this did not succeed return false
      while (partsol_.psol_s.count(idx_distrib) != 0)
        ++idx_distrib;
      if (idx_distrib >= incomp_ref_.dim())
        return false;

      // Search for a compatible class
      // and add the state
      unsigned iclass = -1u;
      for (unsigned i = 0; i < n_classes_; ++i)
        if (!incomp_classes(i, idx_distrib))
          {
            iclass = i;
            break;
          }
      if (iclass == -1u)
        // Could not find a suitable class
        return false;
      // Put idx_distrib into iclass
      // This means that this class becomes incompatible
      // with all state incompatible with idx_distrib
      auto [l_dist, l_dist_e] = incomp_ref_.get_cline(idx_distrib);
      auto [l_incomp, l_incomp_e] = incomp_classes.get_line(iclass);
      for (; l_incomp != l_incomp_e; ++l_incomp, ++l_dist)
        *l_incomp |= *l_dist;
      ++idx_distrib;
      return true;
    }

    bool inc_classes()
    {
      if (feasible())
        return true;
      assert(n_classes_ < incomp_ref_.dim());
      ++n_classes_;
      while (add_one());
      return feasible();
    }

    bool feasible() const
    {
      // All states have been distributed
      return idx_distrib >= incomp_ref_.dim();
    }

  };

#ifdef USE_OPT_LIT
  template <class MAT>
  auto try_build_sol(const const_twa_graph_ptr &splitmm,
                     const std::deque<bdd>& used_bdds,
                     const MAT& incompmat,
                     const part_sol_t& partsol,
                     const greedy_cover_t& gc,
                     const std::vector<
                            std::pair<unsigned, unsigned>>& reduction_map,
                     const size_t n_classes, const size_t n_sigma_red) {
    assert(partsol.psol_v.size() <= n_classes);
    stopwatch sw;
    sw.start();
    // we have two types of literals:
    // Note: Sigma is the reduced alphabet
    // Note: Not all states have a successor under each letter
    // s_x_i: state x is in class i
    // x -> |Q|
    // i -> [0, n_classes[
    // less than |Q|*n_classes literals as we only need s_x_x for the partial
    // solution Z_i_a_j : All states in i go to j under a
    // -> less than |Sigma|*n_classes^2
    // 0 -> Terminal lit
    const auto& psol_v = partsol.psol_v;
    const size_t n_env = incompmat.dim();
    const size_t n_psol = psol_v.size();
    const size_t n_sigma = reduction_map.size();
    trace << "n_psol " << n_psol << '\n';

    // Create the solver
    auto Sptr = std::make_shared<satsolver>();
    auto& S = *Sptr;

    lit_mapper lm(Sptr, n_classes, n_env, n_sigma_red);

    // Creating sxi
    lm.unfreeze_xi();

    // Partial solution
    // Order does not matter -> s_part_sol[0] -> get class 0
    for (unsigned i = 0; i < n_psol; ++i)
      {
//        S.add({lm.sxi2lit({psol_v[i], i}), 0});
        lm.add({lm.sxi2lit({psol_v[i], i}), 0});
        printlit({lm.sxi2lit({psol_v[i], i}), 0});
      }

    // Covering condition
    // Each state must be in AT LEAST one class
    // For the partial solution classes only add if possible
    for (unsigned x = 0; x < n_env; ++x)
      {
        for (unsigned i = 0; i < n_classes; ++i)
          {
            if ((i < n_psol) && incompmat(psol_v[i], x))
              // Skip this literal
              continue;
//            S.add(lm.sxi2lit({x, i}));
            lm.add(lm.sxi2lit({x, i}));
            printlit({lm.sxi2lit({x, i})});
          }
        // terminate clause
//        S.add(0);
        lm.add(0);
        printlit({0});
      }

    // Incompatibility
    // 1) Set clauses for all states that are incompatible with the
    //    partial solution
    trace << "Icomp 1\n";
    for (unsigned i = 0; i < n_psol; ++i)
      for (unsigned x = 0; x < n_env; ++x)
        if (incompmat(psol_v[i], x))
          {
//            S.add({-lm.sxi2lit({x, i}), 0}); // x can not be in class i
            lm.add({-lm.sxi2lit({x, i}), 0}); // x can not be in class i
            printlit({-lm.sxi2lit({x, i}), 0});
          }
    // All sxi exist now
    lm.freeze_xi();

    // 2) The "rest" :
    //    If for a class i the state x is compatible with
    //    the state defining this class -> Set clauses for all incompatible
    //    states
    trace << "Icomp 2\n";
    for (unsigned x = 0; x < n_env; ++x)
      for (unsigned i = 0; i < n_classes; ++i)
        {
          // Check possible partial sol
          if (i < n_psol && incompmat(psol_v[i], x))
            continue; // Already taken care of in step 1
          // Get all the incompatible states
          for (unsigned y = x + 1; y < n_env; ++y)
            {
              if (i < n_psol && incompmat(psol_v[i], y))
                continue; // Already taken care of in step 1
              if (incompmat(x, y))
                {
//                  S.add({-lm.sxi2lit({x, i}), -lm.sxi2lit({y, i}), 0});
                  lm.add({-lm.sxi2lit({x, i}), -lm.sxi2lit({y, i}), 0});
                  printlit({-lm.sxi2lit({x, i}), -lm.sxi2lit({y, i}), 0});
                }
            }
        }

    info_struct.build_cover = sw.stop();

    // Check if the greedy cover exists, if not check
    // if there can be a solution
    info_struct.part_feas = -1;
    if (!gc.feasible())
      {
        info_struct.part_feas = 1;
        lm.finalize();
        trace << "#partial prob\np cnf " << S.get_nb_vars()
              << ' ' << S.get_nb_clauses()
              << std::endl;
        info_struct.n_part_vars = S.get_nb_vars();
        info_struct.n_part_clauses = S.get_nb_clauses();

        // Solve it
        sw.start();
        auto solpair = S.get_solution();
        info_struct.sat_part_time = sw.stop();
        if (solpair.second.empty())
          {
            // The partial prob is infeas -> early exit
            info_struct.part_feas = 0;
            return std::make_tuple(false, solpair.second, lm);
          }
      }
    sw.start();

    // Closure condition
    // List of possible successor classes
    std::vector<char> succ_classes(n_classes);
    // Loop over all minimal letters
    // We need a vector of iterators to make it efficient
    // Attention not all states have successors for all letters
    using edge_it_type = decltype(splitmm->out(0).begin());
    std::vector<std::pair<edge_it_type, edge_it_type>> edge_it;
    edge_it.reserve(n_env);
    for (unsigned s = 0; s < n_env; ++s)
      edge_it.emplace_back(splitmm->out(s).begin(),
                           splitmm->out(s).end());
    auto get_dst = [&](const auto& eit)
      {
        return splitmm->out(eit->dst).begin()->dst;
      };

    // todo char vs bool debate
    // has_a_edge[i] stores if i has an edge under a
    // No? -> -1u
    // Yes -> dst state
    std::vector<unsigned> has_a_edge_(n_env);
    std::vector<char> active_edge_(n_env);

    trace << "Closure\n";
    for (unsigned a = 0; a < n_sigma; ++a)
      {
        const auto abddid = used_bdds[a].id(); // Current id
        // Advance all iterators if necessary
        // also check if finished.
        // if all edges are treated we can stop
        // Drive by check if a exists in outs
        auto h_a_it = has_a_edge_.begin();
        std::for_each(edge_it.begin(), edge_it.end(),
                      [&abddid, &h_a_it, &get_dst](auto& eit)
                        {
                          *h_a_it = -1u;
                          if ((eit.first != eit.second)
                               && (eit.first->cond.id() < abddid))
                              ++eit.first;
                          if ((eit.first != eit.second)
                              && (eit.first->cond.id() == abddid))
                            *h_a_it = get_dst(eit.first);
                          ++h_a_it;
                        });
        assert(h_a_it == has_a_edge_.end());

        auto [aclass, aidx] = reduction_map[a];
        if (a != aclass)
          // This letter is "bisimilar" to aclass
          continue;
        assert(aidx < n_sigma_red);

        //Loop over src classes
        for (unsigned i = 0; i < n_classes; ++i)//src class
          {
            // Reset active
            std::fill(active_edge_.begin(), active_edge_.end(), false);
            // Check for possible successor classes of class i
            // If class i is a partial solution:
            // Only state compatible to i can be in it
            // Otherwise any state is a possible src
            std::fill(succ_classes.begin(), succ_classes.end(), false);
            for (unsigned isrc = 0; isrc < n_env; ++isrc)
              {
//                if (edge_it[isrc].first == edge_it[isrc].second)
//                  continue; // Already all edges treated
//                if (edge_it[isrc].first->cond.id() != abddid)
//                  // No successor for this letter
//                  continue;
                if (has_a_edge_[isrc] == -1u)
                  continue;
                if ((i < n_psol) && (incompmat(isrc, psol_v[i])))
                  continue; // isrc can not be in i
                unsigned dst = get_dst(edge_it[isrc].first);
                // This edge is active
                active_edge_[isrc] = true;
                // Check all target classes
                for (unsigned j = 0; j < n_classes; ++j)
                  {
                    if (succ_classes[j])
                      continue; //Already possible
                    if ((j < n_psol) && incompmat(psol_v[j], dst))
                      continue; //dst can not be in class j
                    succ_classes[j] = true;
                  }
//                if (std::all_of(succ_classes.begin(), succ_classes.end(),
//                                [](auto e){return e;}))
//                  break; // Every class can be a successor
              }
            // We have checked which are possible successor classes
            // It can happen that a state has no successor class under a
            // if the initial machine is not complete
            if (std::none_of(succ_classes.begin(), succ_classes.end(),
                             [](auto e){ return e; }))
              continue;
            // Z_iaj -> Under a all states of i go to j
            // First condition: For each i and a there must exist an j
            lm.unfreeze_iaj();
            for (unsigned j = 0; j < n_classes; ++j)
              {
                if (succ_classes[j])
                  {
//                    S.add(lm.ziaj2lit({i, aidx, j}));
                    lm.add(lm.ziaj2lit({i, aidx, j}));
                    printlit({lm.ziaj2lit({i, aidx, j})});
                  }
              }
//            S.add(0);
            lm.add(0);
            printlit({0});
            lm.freeze_iaj();

            // todo if dst is incompatible, I the condition can possibly
            // be simplified

            // Second condition:
            // All states of i must go to j under a if there is a successor
            // Note that not all states are possible src in i
            for (unsigned j = 0; j < n_classes; ++j) // dst class
              {
                if (!succ_classes[j])//Not possible
                  continue;
//                for (auto& eit : edge_it)
//                  {
//                    if (eit.first == eit.second)
//                      continue; // Already all edges treated
//                    if (eit.first->cond.id() != abddid)//Has no successor
//                      continue;
//                    // If src can not be in i -> skip
//                    unsigned x = eit.first->src;
//                    if ((i < n_psol) && incompmat(psol_v[i], x))
//                      continue;
//                    unsigned xprime = get_dst(eit.first);
                for (unsigned x = 0; x < n_env; ++x)
                  {
                    // Check if edge is active
                    if (!active_edge_[x])
                      continue;
                    unsigned xprime = has_a_edge_[x];
                    assert(xprime != -1u);
                    // Add the clause
//                    S.add({-lm.ziaj2lit({i, aidx, j}),
//                           -lm.sxi2lit({x, i}), lm.sxi2lit({xprime, j}), 0});
                    lm.add({-lm.ziaj2lit({i, aidx, j}),
                            -lm.sxi2lit({x, i}), lm.sxi2lit({xprime, j}), 0});
                    printlit({-lm.ziaj2lit({i, aidx, j}),
                              -lm.sxi2lit({x, i}), lm.sxi2lit({xprime, j}), 0});
                  }
              } // dst class
          } // src class
      }//letter
    // check if all have been used
    assert(std::all_of(edge_it.begin(), edge_it.end(),
                       [](auto& eit)
                       {
                           return ((eit.first == eit.second)
                                   || ((++eit.first) == eit.second));
                       }));
    lm.finalize();
    info_struct.build_closure = sw.stop();
    trace << "p cnf " << S.get_nb_vars() << ' ' << S.get_nb_clauses()
          << std::endl;
    info_struct.n_vars = S.get_nb_vars();
    info_struct.n_clauses = S.get_nb_clauses();

    // Solve it
    sw.start();
    auto solpair = S.get_solution();
    info_struct.sat_time = sw.stop();

    trace << "Solution exists " << (!solpair.second.empty()) << '\n';
    // What is the format of the return type I don't understand!
    if (solpair.second.empty())
      return std::make_tuple(false, solpair.second, lm);
    else
      {
        // MODIFICATION
        // We prepend the solver solution with 0, so that the number of the
        // literal corresponds to the index of the solution vector
        decltype(solpair.second) sol;
        sol.reserve(solpair.second.size()+1);
        sol.push_back(0);
        sol.insert(sol.end(), solpair.second.begin(), solpair.second.end());
        return std::make_tuple(true, sol, lm);
      }
  }
#else
  template<class MAT>
  auto try_build_sol(const const_twa_graph_ptr& splitmm,
                     const std::deque<bdd>& used_bdds,
                     const MAT& incompmat,
                     const part_sol_t& partsol,
                     const std::vector<
                                std::pair<unsigned, unsigned>>& reduction_map,
                     const size_t n_classes,
                     const size_t n_sigma_red)
  {
    assert(partsol.psol_v.size() <= n_classes);
    // we have two types of literals:
    // Note: Sigma is the reduced alphabet
    // s_x_i: state x is in class i
    // x -> |Q|
    // i -> [0, n_classes[
    // -> |Q|*n_classes literals
    // Z_i_a_j : All states in i go to j under a
    // -> |Sigma|*n_classes^2
    // 0 -> Terminal lit
    // s_x_i -> 1 + x*n_classes + i negation is negative
    // Z_i_a_j -> 1 + |Q|*n_classes + i*|Sigma|*n_classes + #(a)*n_classes + j
    // Note that this is an upper bound as not all states
    // have successors under all letters
    const auto& psol_v = partsol.psol_v;
    const size_t n_env = incompmat.dim();
    const size_t n_psol = psol_v.size();
    const size_t n_sigma = reduction_map.size();
    trace << "n_psol " << n_psol << '\n';

    lit_mapper lm(n_classes, n_env, n_sigma_red);

    const int n_lit_sxi = n_classes*n_env;
    const int n_lit_ziaj = n_sigma_red*n_classes*n_classes;

    // Helper function to get env successor of env edge
    auto get_dst = [&splitmm](const auto& eit)
      {
        return splitmm->out(eit->dst).begin()->dst;
      };

    // Create the solver
    satsolver S;

    // Set number of literals
    S.adjust_nvars(n_lit_sxi+n_lit_ziaj);

    // Partial solution
    // Order does not matter -> s_part_sol[0] -> get class 0
    for (unsigned i = 0; i < n_psol; ++i)
      {
        S.add({lm.sxi2lit({psol_v[i], i}), 0});
        printlit({lm.sxi2lit({psol_v[i], i}), 0});
      }

    // Base
    // Each state has to belong to (at least) one class
    for (unsigned x = 0; x < n_env; ++x)
      {
        for (unsigned i = 0; i < n_classes; ++i)
          {
            S.add(lm.sxi2lit({x, i}));
            printlit({lm.sxi2lit({x, i})});
          }
        // terminate clause
        S.add(0);
        printlit({0});
      }

    // Incompatibility
    // Base version
    // Incompatible states can't be in the same class
    for (unsigned i = 0; i < n_classes; ++i)
      for (unsigned x = 0; x < n_env; ++x)
        {
          for (unsigned y = x + 1; y < n_env; ++y)
            {
              if (incompmat(x, y))
                {
                  S.add({-lm.sxi2lit({x, i}), -lm.sxi2lit({y, i}), 0});
                  printlit({-lm.sxi2lit({x, i}), -lm.sxi2lit({y, i}), 0});
                }
            }
        }

    // Z_iaj -> Under a all states of i go to j
    // First condition: For each i and a there must exist an j
    for (unsigned i = 0; i < n_classes; ++i)
      for (unsigned a = 0; a < n_sigma_red; ++a)
        {
          for (unsigned j = 0; j < n_classes; ++j)
            {
              S.add(lm.ziaj2lit({i, a, j}));
              printlit({lm.ziaj2lit({i, a, j})});
            }
          S.add(0);
          printlit({0});
        }
    // Second condition:
    // All states of i must go to j under a
    // Transitions are ordered by the condition id
    // States having no successor under a are skipped,
    // as they can have any successor in this case

    for (unsigned x = 0; x < n_env; ++x)
      {
        // The alphabet
        auto eit = splitmm->out(x).begin();
        auto eit_end = splitmm->out(x).end();
        for (unsigned a = 0; a < n_sigma; ++a)
          {
            if (eit == eit_end)
              break;
            assert(used_bdds[a].id() <= eit->cond.id());
            if (used_bdds[a].id() < eit->cond.id())
              // No successor under this letter
              continue;
            // Here we have a successor
            assert(used_bdds[a].id() == eit->cond.id());

            auto [aclass, aidx] = reduction_map[a];
            if (a != aclass)
              {
                // "Bisimilar" letter
                ++eit; // Having two places for incrementation is :/
                continue; // This letter is "bisimilar" to aclass
              }

            // Successor under a
            unsigned xprime = get_dst(eit);

            // Get all combinations of classes
            for (unsigned i = 0; i < n_classes; ++i) // src class
              for (unsigned j = 0; j < n_classes; ++j) // dst class
                // Add the clause
                {
                  S.add({-lm.ziaj2lit({i, aidx, j}),
                         -lm.sxi2lit({x, i}), lm.sxi2lit({xprime, j}), 0});
                  printlit({-lm.ziaj2lit({i, aidx, j}),
                            -lm.sxi2lit({x, i}), lm.sxi2lit({xprime, j}), 0});
                }
            //Increment the edge
            ++eit;
          }
        //Check if all edges have been treated
        assert(eit == splitmm->out(x).end() && "Untreated edge");
      }

    trace << "p cnf " << S.get_nb_vars() << ' ' << S.get_nb_clauses()
          << std::endl;

    // Solve it
    auto solpair = S.get_solution();
    trace << "Solution exists " << (!solpair.second.empty()) << '\n';
    // What is the format of the return type I don't understand!
    if (solpair.second.empty())
      return std::make_tuple(false, solpair.second, lm);
    else
    {
      // MODIFICATION
      // We prepend the solver solution with 0, so that the number of the
      // literal corresponds to the index of the solution vector
      decltype(solpair.second) sol;
      sol.reserve(solpair.second.size());
      sol.push_back(0);
      sol.insert(sol.end(), solpair.second.begin(), solpair.second.end());
      return std::make_tuple(true, sol, lm);
    }
  }
#endif

  template<class MAT>
  bool check_sat_sol(
                     const MAT& incompmat,
                     const lit_mapper& lm,
                     const part_sol_t& partsol,
                     const size_t n_classes,
                     const size_t n_sigma_red,
                     const std::vector<bool>& sol)
  {
    const auto& psol_v = partsol.psol_v;

    const size_t n_env = incompmat.dim();
    const size_t n_psol = psol_v.size();

    // Check partial sol
    for (unsigned i = 0; i < n_psol; ++i)
      assert(sol[lm.sxi2lit({psol_v[i], i})] && "pSol violated.");

    // Check covering for state not in a
    // partial solution
    for (unsigned x = 0; x < n_env; ++x)
      {
        if (std::find(psol_v.begin(), psol_v.end(), x)
            != psol_v.end())
          continue;
        bool covered = false;
        for (unsigned i = 0; i < n_classes; ++i)
          {
            try
              {
                covered |= sol[lm.sxi2lit({x, i})];
              }
            catch (const std::out_of_range&)
              {
                assert(incompmat(psol_v[i], x));
              }
          }
        assert(covered && "Cover violated!");
      }
    // Check if a successor class exists
    // for each class and input
//    for (unsigned i = 0; i < n_classes; ++i)
//      //Note only loop over minimal letters
//      for (unsigned aidx = 0; aidx < n_sigma_red; ++aidx)
//        {
//          bool has_succ = false;
//          for (unsigned j = 0; j < n_classes; ++j)
//            try
//              {
//                has_succ |= sol[lm.ziaj2lit({i, aidx, j})];
//              }
//            catch (const std::out_of_range&)
//              {
//              }
//          trace << "Class has no successor under a\n";
//        }
    //Check that no incompatible states are in the same class
    trace << n_sigma_red << '\n';
    return true;
  }


  twa_graph_ptr cstr_min_machine(const const_twa_graph_ptr& splitmm,
                                 const std::deque<bdd>& used_bdds,
                                 const lit_mapper& lm,
                                 const std::vector<
                                  std::pair<unsigned, unsigned>>& reduction_map,
                                 const size_t n_env,
                                 const size_t n_classes,
                                 const size_t n_sigma_red,
                                 const std::vector<bool>& sol)
  {
    print_help(sol.begin(), sol.end(), "Solution");

    const size_t n_sigma = reduction_map.size();

    auto minmach = make_twa_graph(splitmm->get_dict());
    minmach->copy_ap_of(splitmm);

    // We have as many states as classes
    minmach->new_states(n_classes);

    // Get the init state
    unsigned x_init = splitmm->get_init_state_number();
    assert(x_init < n_env);
    {
      unsigned initclass = -1u;
      for (unsigned i = 0; i < n_classes; ++i)
        {
          int litsxi = lm.get_sxi({x_init, i});
          if (litsxi && sol.at(litsxi))
            {
              // x_init belongs class i
              minmach->set_init_state(i);
              initclass = i;
              break;
            }
        }
      assert(initclass != -1u);
    }


    // transitions
    // Ziaj indicates that under a all states of i go to j
    // however a might not be a minimal letter. In this case,
    // use the corresponding minimal one
    // If there are multiple such j's one can chose
    // todo heuristic
    // If a state in a class has no successor for a certain input
    // -> ingnore it

    // Save which class has which states
    // Note it almost costs nothing to build sets since they are naturally
    // ordered and we can add asserts
    std::vector<std::set<unsigned>> x_in_class(n_classes);
    for (unsigned x = 0; x < n_env; ++x)
      for (unsigned i = 0; i < n_classes; ++i)
        {
          int litsxi = lm.get_sxi({x, i});
          if (litsxi && sol.at(litsxi))
            x_in_class[i].emplace_hint(x_in_class[i].end(), x);
        }

    // Get all the outconds
    // Better than iterating each time?
    // Using a map avoids storing false for non-existent
    // id of a -> outcond, dst
    std::vector<std::map<int, std::pair<bdd, unsigned>>> x_a_ocond(n_env);
    for (unsigned x = 0; x < n_env; ++x)
      {
        std::for_each(splitmm->out(x).begin(), splitmm->out(x).end(),
                      [&m = x_a_ocond[x], &splitmm](const auto& e)
                      { m.emplace_hint(m.end(), e.cond.id(),
                          std::make_pair(splitmm->out(e.dst).begin()->cond,
                                         splitmm->out(e.dst).begin()->dst));
                      });
      }
    // Have edges of states contiguous
    //(dst, ocond) -> player state
    std::unordered_map<unsigned long long, unsigned> player_hash;
    for (unsigned i = 0; i < n_classes; ++i)
      for (unsigned a = 0; a < n_sigma; ++a)
        {
          // Get the class and the linear index
          auto [aclass, aidx] = reduction_map[a];
          assert(aidx <= aclass); //Condition for minimal letter
          assert(aidx < n_sigma_red);
          // todo heuristic to chose
          // Take the first possible target class
          unsigned j = -1u; // target class
          for (unsigned jj=0; jj < n_classes; ++jj)
            {
              int jjlit = lm.get_iaj({i, aidx, jj});
              if ((jjlit != 0) && sol[jjlit])
                {
                  j = jj;
                  break;
                }
            }
          // The out-condition is the conjunction of all
          // transitions in the class
          bdd ocond = bddtrue;
          bool has_trans = false;
          for (auto x : x_in_class[i])
            {
              //Use the actual a here
              auto it = x_a_ocond[x].find(used_bdds[a].id());
              if (it != x_a_ocond[x].end())
                {
                  assert(sol.at(lm.get_sxi({it->second.second, j})));
                  has_trans = true;
                  ocond &= it->second.first;
                }
              assert((ocond != bddfalse) && "Incompatible states in class");
            }
          // There should be no successor if j == -1u
          if (j == -1u)
            {
              assert(!has_trans);
              continue; //No successor of this class under this letter
            }
          // Does this out to this state exist?
          // Cheap identifier for bounded pairs
          unsigned long long id_dc = j;
          id_dc <<= 32;
          id_dc += ocond.id(); // This is unique
          auto it = player_hash.find(id_dc);
          if (it == player_hash.end())
            {
              // Create a new state
              // and connect it
              unsigned x_env = minmach->new_state();
              //Again use actual a here
              minmach->new_edge(i, x_env, used_bdds[a]);
              minmach->new_edge(x_env, j, ocond);
              player_hash[id_dc] = x_env;
            }
          else
              // Reuse
             //Again use actual a here
              minmach->new_edge(i, it->second, used_bdds[a]);
        }

    // Set state players
    // todo add in and out conditions as named prop?
    auto spptr =
        minmach->get_or_set_named_prop<std::vector<bool>>("state-player");

    spptr->resize(minmach->num_states());
    std::fill(spptr->begin(), spptr->begin()+n_classes, false);
    std::fill(spptr->begin()+n_classes, spptr->end(), true);
    // Check up
    assert(std::all_of(minmach->edges().begin(), minmach->edges().end(),
                       [&spref = *spptr](const auto& e)
                         {return spref.at(e.src) != spref.at(e.dst); }));
    // Debug
    trace << "final env count " << n_classes << std::endl;
//    minmach->merge_edges();
    return minmach;
  }

  template<class MAT>
  twa_graph_ptr build_min_machine(
      const const_twa_graph_ptr& splitmm,
      const std::deque<bdd>& used_bdds,
      const MAT& incompmat,
      const part_sol_t& partsol,
      const greedy_cover_t& gc,
      const std::vector<std::pair<unsigned, unsigned>>&
          reduction_map,
      const size_t n_classes,
      const size_t n_sigma_red)
  {
    auto [succ, sol, lm] = try_build_sol(splitmm, used_bdds, incompmat,
                                         partsol,
                                         gc,
                                         reduction_map,
                                         n_classes, n_sigma_red);
    // Debug
    stopwatch sw;
    trace << "nc " << n_classes << " : " << succ << std::endl;

    if (succ)
      {
        assert(check_sat_sol(incompmat, lm, partsol,
                             n_classes, n_sigma_red, sol));
        sw.start();
        auto minmach = cstr_min_machine(splitmm, used_bdds, lm, reduction_map,
                                        incompmat.dim(), n_classes,
                                        n_sigma_red, sol);
        info_struct.build_time = sw.stop();
        return minmach;
      }
    else
      return nullptr;
  }
}//anonymous

namespace spot
{
  using namespace minutils;

  twa_graph_ptr minimize_mealy(const const_twa_graph_ptr& mm,
                               int preminfast)
    {
      static_assert(sizeof(unsigned) == 4);
      static_assert(sizeof(int) == 4);
      static_assert(sizeof(unsigned long long) == 8);

      if ((preminfast < -1) || (preminfast > 1))
        throw std::runtime_error("preminfast has to be -1, 0 or 1");

      stopwatch sw;

      if (!mm->acc().is_t())
        throw std::runtime_error("Mealy machine needs true acceptance!\n");

      // Check if finite traces exist
      // If so, deactivate fast minimization
      if ([&]()
          {
            for (unsigned s = 0; s < mm->num_states(); ++s)
              {
                auto eit = mm->out(s);
                if (eit.begin() == eit.end())
                  return true;
              }
            return false;
          }())
        preminfast = -1;

      auto do_premin = [&]()->const_twa_graph_ptr
        {
          if (preminfast == -1)
            return mm;
          else
            {
              auto mm_res = minimize_mealy_fast(mm, preminfast == 1);
              // alternate_players(mm_res, false, false);
              return mm_res;
            }
        };

      sw.start();
      const const_twa_graph_ptr mmw = do_premin();
      info_struct.t_premin = sw.stop();

      // 0 -> "Env" next is input props
      // 1 -> "Player" next is output prop
      auto spptr = mmw->get_named_prop<std::vector<bool>>("state-player");
      if (!spptr)
        throw std::runtime_error("\"state-player\" must be defined!");
      const auto& spref = *spptr;
      assert((spref.size() == mmw->num_states())
             && "Inconsistent state players");

      // Compute the alphabet and create new edges
      // Also the machine is such that
      // [0, n_env[ -> env states
      // [n_env, mmw->num_states()[ -> player states
      sw.start();
      auto [splitmm, used_bdds, reduction_map, n_env, n_sigma_red]
          = reduce_and_split(mmw, spref);
      info_struct.red_split = sw.stop();
      info_struct.sigma = reduction_map.size();
      info_struct.sigma_red = n_sigma_red;
      info_struct.n_trans = splitmm->num_edges();

      // Now we need to compute the incompatibility matrix
      sw.start();
      auto incompmat = incomp_mat(splitmm, n_env);
      info_struct.incomp = sw.stop();
#ifdef TRACE
      incompmat.print();
#endif

      // Compute the (greedy) partial solution
      // -> Vector of states that have to belong to different classes
      auto partsol = get_part_sol(incompmat);
      const auto& psol_v = partsol.psol_v;
      print_help(psol_v.begin(), psol_v.end(), "Partial sol");

      // Now we can search for an actual instance of the problem
      // todo How can we reuse the CNFs?
      // Do we really have to rebuild it each time in its totality?!

      // Debug
      trace << "npsol " << psol_v.size() << " n_env " << n_env << std::endl;
      greedy_cover_t gc(incompmat, psol_v.size(), partsol);

      twa_graph_ptr minmachine = nullptr;
      for (size_t n_classes = psol_v.size();
           n_classes < n_env; ++n_classes)
        {
          minmachine = build_min_machine(splitmm, used_bdds, incompmat,
                                         partsol, gc, reduction_map,
                                         n_classes, n_sigma_red);
#ifdef PRINTCSV
          std::cerr << "## nc" << n_classes << " premin "
                    << info_struct.t_premin << "  rs "
                    << info_struct.red_split << " inc "
                    << info_struct.incomp << " bco "
                    << info_struct.build_cover << " bcl "
                    << info_struct.build_closure << " spt "
                    << info_struct.sat_part_time << " st "
                    << info_struct.sat_time << " pf "
                    << info_struct.part_feas << " bt "
                    << info_struct.build_time << " si "
                    << info_struct.sigma << " sir "
                    << info_struct.sigma_red << " nt "
                    << info_struct.n_trans << " npv "
                    << info_struct.n_part_vars << " nv "
                    << info_struct.n_vars << " npc "
                    << info_struct.n_part_clauses << " nc "
                    << info_struct.n_clauses << std::endl;
#endif
          if (minmachine)
              break;
          // Give the greedy cover one more class
          gc.inc_classes();
        }
      // Is already minimal -> Return a copy
      // Set state players!
      if (!minmachine)
        {
          minmachine = make_twa_graph(mmw, twa::prop_set::all());
          assert(spptr != nullptr);
          minmachine->set_named_prop("state-player",
                                     new std::vector<bool>(*spptr));
        }
      // Try to set outputs
      if (bdd* outptr = mm->get_named_prop<bdd>("synthesis-outputs"))
        minmachine->set_named_prop("synthesis-outputs", new bdd(*outptr));
      return minmachine;
  }
}