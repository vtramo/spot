// -*- coding: utf-8 -*-
// Copyright (C) 2018-2020 Laboratoire de Recherche et Développement
// de l'Epita.
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
#include <spot/twaalgos/toparity.hh>
#include <spot/twaalgos/sccinfo.hh>

#include <deque>
#include <utility>
#include <spot/twa/twa.hh>
#include <spot/twaalgos/cleanacc.hh>
#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/toparity.hh>
#include <spot/twaalgos/dualize.hh>
#include <spot/twaalgos/genem.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/parity.hh>
// TODO: Besoin ?
#include <spot/twaalgos/remfin.hh>
#include <spot/twaalgos/totgba.hh>

#include <numeric>
#include <optional>
#include <unistd.h>
namespace spot
{

  // Old version of IAR.
  namespace
  {

    using perm_t = std::vector<unsigned>;
    struct iar_state
    {
      unsigned state;
      perm_t perm;

      bool
      operator<(const iar_state& other) const
      {
        return state == other.state ? perm < other.perm : state < other.state;
      }
    };

    template<bool is_rabin>
    class iar_generator
    {
      // helper functions: access fin and inf parts of the pairs
      // these functions negate the Streett condition to see it as a Rabin one
      const acc_cond::mark_t&
      fin(unsigned k) const
      {
        if (is_rabin)
          return pairs_[k].fin;
        else
          return pairs_[k].inf;
      }
      acc_cond::mark_t
      inf(unsigned k) const
      {
        if (is_rabin)
          return pairs_[k].inf;
        else
          return pairs_[k].fin;
      }
    public:
      explicit iar_generator(const const_twa_graph_ptr& a,
                             const std::vector<acc_cond::rs_pair>& p,
                             const bool pretty_print)
      : aut_(a)
      , pairs_(p)
      , scc_(scc_info(a))
      , pretty_print_(pretty_print)
      , state2pos_iar_states(aut_->num_states(), -1U)
      {}

      twa_graph_ptr
      run()
      {
        res_ = make_twa_graph(aut_->get_dict());
        res_->copy_ap_of(aut_);

        build_iar_scc(scc_.initial());

        {
          // resulting automaton has acceptance condition: parity max odd
          // for Rabin-like input and parity max even for Streett-like input.
          // with priorities ranging from 0 to 2*(nb pairs)
          // /!\ priorities are shifted by -1 compared to the original paper
          unsigned sets = 2 * pairs_.size() + 1;
          res_->set_acceptance(sets, acc_cond::acc_code::parity_max(is_rabin,
                                                                    sets));
        }
        {
          unsigned s = iar2num.at(state2iar.at(aut_->get_init_state_number()));
          res_->set_init_state(s);
        }

        if (pretty_print_)
        {
          unsigned nstates = res_->num_states();
          auto names = new std::vector<std::string>(nstates);
          for (auto e : res_->edges())
          {
            unsigned s = e.src;
            iar_state iar = num2iar.at(s);
            std::ostringstream st;
            st << iar.state << ' ';
            if (iar.perm.empty())
              st << '[';
            char sep = '[';
            for (unsigned h: iar.perm)
            {
              st << sep << h;
              sep = ',';
            }
            st << ']';
            (*names)[s] = st.str();
          }
          res_->set_named_prop("state-names", names);
        }

        // there could be quite a number of unreachable states, prune them
        res_->purge_unreachable_states();
        return res_;
      }

      void
      build_iar_scc(unsigned scc_num)
      {
        // we are working on an SCC: the state we start from does not matter
        unsigned init = scc_.one_state_of(scc_num);

        std::deque<iar_state> todo;
        auto get_state = [&](const iar_state& s)
          {
            auto it = iar2num.find(s);
            if (it == iar2num.end())
              {
                unsigned nb = res_->new_state();
                iar2num[s] = nb;
                num2iar[nb] = s;
                unsigned iar_pos = iar_states.size();
                unsigned old_newest_pos = state2pos_iar_states[s.state];
                state2pos_iar_states[s.state] = iar_pos;
                iar_states.push_back({s, old_newest_pos});
                todo.push_back(s);
                return nb;
              }
            return it->second;
          };

        auto get_other_scc = [this](unsigned state)
          {
            auto it = state2iar.find(state);
            // recursively build the destination SCC if we detect that it has
            // not been already built.
            if (it == state2iar.end())
              build_iar_scc(scc_.scc_of(state));
            return iar2num.at(state2iar.at(state));
          };

        if (scc_.is_trivial(scc_num))
          {
            iar_state iar_s{init, perm_t()};
            state2iar[init] = iar_s;
            unsigned src_num = get_state(iar_s);
            // Do not forget to connect to subsequent SCCs
            for (const auto& e : aut_->out(init))
              res_->new_edge(src_num, get_other_scc(e.dst), e.cond);
            return;
          }

        // determine the pairs that appear in the SCC
        auto colors = scc_.acc_sets_of(scc_num);
        std::set<unsigned> scc_pairs;
        for (unsigned k = 0; k != pairs_.size(); ++k)
          if (!inf(k) || (colors & (pairs_[k].fin | pairs_[k].inf)))
            scc_pairs.insert(k);

        perm_t p0;
        for (unsigned k : scc_pairs)
          p0.push_back(k);

        iar_state s0{init, p0};
        get_state(s0); // put s0 in todo

        // the main loop
        while (!todo.empty())
          {
            iar_state current = todo.front();
            todo.pop_front();

            unsigned src_num = get_state(current);

            for (const auto& e : aut_->out(current.state))
              {
                // connect to the appropriate state
                if (scc_.scc_of(e.dst) != scc_num)
                  res_->new_edge(src_num, get_other_scc(e.dst), e.cond);
                else
                  {
                    // find the new permutation
                    perm_t new_perm = current.perm;
                    // Count pairs whose fin-part is seen on this transition
                    unsigned seen_nb = 0;
                    // consider the pairs for this SCC only
                    for (unsigned k : scc_pairs)
                      if (e.acc & fin(k))
                        {
                          ++seen_nb;
                          auto it = std::find(new_perm.begin(),
                                              new_perm.end(),
                                              k);
                          // move the pair in front of the permutation
                          std::rotate(new_perm.begin(), it, it+1);
                        }

                    iar_state dst;
                    unsigned dst_num = -1U;

                    // Optimization: when several indices are seen in the
                    // transition, they move at the front of new_perm in any
                    // order. Check whether there already exists an iar_state
                    // that matches this condition.

                    auto iar_pos = state2pos_iar_states[e.dst];
                    while (iar_pos != -1U)
                    {
                      iar_state& tmp = iar_states[iar_pos].first;
                      iar_pos = iar_states[iar_pos].second;
                      if (std::equal(new_perm.begin() + seen_nb,
                        new_perm.end(),
                        tmp.perm.begin() + seen_nb))
                      {
                        dst = tmp;
                        dst_num = iar2num[dst];
                        break;
                      }
                    }
                    // if such a state was not found, build it
                    if (dst_num == -1U)
                      {
                        dst = iar_state{e.dst, new_perm};
                        dst_num = get_state(dst);
                      }

                    // find the maximal index encountered by this transition
                    unsigned maxint = -1U;
                    for (int k = current.perm.size() - 1; k >= 0; --k)
                      {
                        unsigned pk = current.perm[k];
                        if (!inf(pk) ||
                            (e.acc & (pairs_[pk].fin | pairs_[pk].inf))) {
                              maxint = k;
                              break;
                            }
                      }

                    acc_cond::mark_t acc = {};
                    if (maxint == -1U)
                      acc = {0};
                    else if (e.acc & fin(current.perm[maxint]))
                      acc = {2*maxint+2};
                    else
                      acc = {2*maxint+1};

                    res_->new_edge(src_num, dst_num, e.cond, acc);
                  }
              }
          }

        // Optimization: find the bottom SCC of the sub-automaton we have just
        // built. To that end, we have to ignore edges going out of scc_num.
        auto leaving_edge = [&](unsigned d)
          {
            return scc_.scc_of(num2iar.at(d).state) != scc_num;
          };
        auto filter_edge = [](const twa_graph::edge_storage_t&,
                              unsigned dst,
                              void* filter_data)
          {
            decltype(leaving_edge)* data =
              static_cast<decltype(leaving_edge)*>(filter_data);

            if ((*data)(dst))
              return scc_info::edge_filter_choice::ignore;
            return scc_info::edge_filter_choice::keep;
          };
        scc_info sub_scc(res_, get_state(s0), filter_edge, &leaving_edge);
        // SCCs are numbered in reverse topological order, so the bottom SCC
        // has index 0.
        const unsigned bscc = 0;
        assert(sub_scc.succ(0).empty());
        assert(
            [&]()
            {
              for (unsigned s = 1; s != sub_scc.scc_count(); ++s)
                if (sub_scc.succ(s).empty())
                  return false;
              return true;
            } ());

        assert(sub_scc.states_of(bscc).size()
            >= scc_.states_of(scc_num).size());

        // update state2iar
        for (unsigned scc_state : sub_scc.states_of(bscc))
          {
            iar_state& iar = num2iar.at(scc_state);
            if (state2iar.find(iar.state) == state2iar.end())
              state2iar[iar.state] = iar;
          }
      }

    private:
      const const_twa_graph_ptr& aut_;
      const std::vector<acc_cond::rs_pair>& pairs_;
      const scc_info scc_;
      twa_graph_ptr res_;
      bool pretty_print_;

      // to be used when entering a new SCC
      // maps a state of aut_ onto an iar_state with the appropriate perm
      std::map<unsigned, iar_state> state2iar;

      std::map<iar_state, unsigned> iar2num;
      std::map<unsigned, iar_state> num2iar;

      std::vector<unsigned> state2pos_iar_states;
      std::vector<std::pair<iar_state, unsigned>> iar_states;
    };

    // Make this a function different from iar_maybe(), so that
    // iar() does not have to call a deprecated function.
    static twa_graph_ptr
    iar_maybe_(const const_twa_graph_ptr& aut, bool pretty_print)
    {
      std::vector<acc_cond::rs_pair> pairs;
      if (!aut->acc().is_rabin_like(pairs))
        if (!aut->acc().is_streett_like(pairs))
          return nullptr;
        else
          {
            iar_generator<false> gen(aut, pairs, pretty_print);
            return gen.run();
          }
      else
        {
          iar_generator<true> gen(aut, pairs, pretty_print);
          return gen.run();
        }
    }
  }

  twa_graph_ptr
  iar_maybe(const const_twa_graph_ptr& aut, bool pretty_print)
  {
    return iar_maybe_(aut, pretty_print);
  }

  twa_graph_ptr
  iar(const const_twa_graph_ptr& aut, bool pretty_print)
  {
    if (auto res = iar_maybe_(aut, pretty_print))
      return res;
    throw std::runtime_error("iar() expects Rabin-like or Streett-like input");
  }

// New version for paritizing
namespace
{
struct node
{
    // A color of the permutation or a state.
    unsigned label;
    std::vector<node*> children;
    // is_leaf is true if the label is a state of res_.
    bool is_leaf;

    node()
        : node(0, 0){
    }

    node(int label_, bool is_leaf_)
        : label(label_)
        , is_leaf(is_leaf_){
    }

    ~node()
    {
        for (auto c : children)
            delete c;
    }

    // Add a permutation to the tree.
    void
    add_new_perm(const std::vector<unsigned>& permu, int pos,
                  unsigned res_state)
    {
        if (pos == -1)
            children.push_back(new node(res_state, true));
        else
        {
            auto lab = permu[pos];
            auto child = std::find_if(children.begin(), children.end(),
                [lab](node* n){
                    return n->label == lab;
                });
            if (child == children.end())
            {
                node* new_child = new node(lab, false);
                children.push_back(new_child);
                new_child->add_new_perm(permu, pos - 1, res_state);
            }
            else
                (*child)->add_new_perm(permu, pos - 1, res_state);
        }
    }

    node*
    get_sub_tree(const std::vector<unsigned>& elements, int pos)
    {
        if (pos < 0)
            return this;
        unsigned lab = elements[pos];
        auto child = std::find_if(children.begin(), children.end(),
                [lab](node* n){
                    return n->label == lab;
                });
        assert(child != children.end());
        return (*child)->get_sub_tree(elements, pos - 1);
    }

    // Gives a state of res_ (if it exists) reachable from this node.
    // If use_last is true, we take the most recent, otherwise we take
    // the oldest.
    unsigned
    get_end(bool use_last)
    {
        if (children.empty())
        {
            if (!is_leaf)
                return -1U;
            return label;
        }
        int pos = use_last ? children.size() - 1 : 0;
        return children[pos]->get_end(use_last);
    }

    // Try to find a state compatible with the permu when seen_nb colors are
    // moved.
    unsigned
    get_existing(const std::vector<unsigned>& permu, unsigned seen_nb, int pos,
                 bool use_last)
    {
        if (pos < (int) seen_nb)
            return get_end(use_last);
        else
        {
            auto lab = permu[pos];
            auto child = std::find_if(children.begin(), children.end(),
                [lab](node* n){
                    return n->label == lab;
                });
            if (child == children.end())
                return -1U;
            return (*child)->get_existing(permu, seen_nb, pos - 1, use_last);
        }
    }
};

class state_2_lar_scc
{
std::vector<node> nodes;

public:
state_2_lar_scc(unsigned nb_states)
    : nodes(nb_states, node()){
}

// Try to find a state compatible with the permu when seen_nb colors are
// moved. If use_last is true, it return the last created compatible state.
// If it is false, it returns the oldest.
unsigned
get_res_state(unsigned state, const std::vector<unsigned>& permu,
              unsigned seen_nb, bool use_last)
{
    return nodes[state].get_existing(permu, seen_nb,
                                     permu.size() - 1, use_last);
}

void
add_res_state(unsigned initial, unsigned res_state,
              const std::vector<unsigned>& permu)
{
    assert(!permu.empty());
    nodes[initial].add_new_perm(permu, ((int) permu.size()) - 1, res_state);
}

node*
get_sub_tree(const std::vector<unsigned>& elements, unsigned state)
{
    return nodes[state].get_sub_tree(elements, elements.size() - 1);
}
};

class to_parity_generator
{
  static std::vector<twa_graph_ptr>
  split_aut(scc_info si, std::vector<bool> keep)
  {
    auto aut = si.get_aut();
    auto aut_acc = aut->acc();
    unsigned nb_scc = si.scc_count();
    std::vector<twa_graph_ptr> result(nb_scc);
    std::vector<unsigned> state2num;
    std::vector<std::vector<unsigned>*> orig_states(nb_scc);
    for (unsigned scc = 0; scc < nb_scc; ++scc)
    {
      result[scc] = make_twa_graph(aut->get_dict());
      orig_states[scc] = new std::vector<unsigned>();
      result[scc]->set_named_prop("original-states", orig_states[scc]);
      result[scc]->copy_ap_of(aut);
      result[scc]->prop_state_acc(aut->prop_state_acc());
      result[scc]->set_acceptance(aut_acc);
    }
    const unsigned aut_num_states = aut->num_states();
    for (unsigned state = 0; state < aut_num_states; ++state)
    {
      unsigned scc = si.scc_of(state);
      unsigned num = result[scc]->new_state();
      state2num.push_back(num);
      orig_states[scc]->push_back(state);
    }
    for (auto& e : aut->edges())
    {
      auto index = aut->edge_number(e);
      unsigned scc_src = si.scc_of(e.src);
      unsigned num_src = state2num[e.src];
      unsigned num_dst = state2num[e.dst];
      if (scc_src == si.scc_of(e.dst) && keep[index])
        result[scc_src]->new_edge(num_src, num_dst, e.cond, e.acc);
    }

    return result;
  }


enum algorithm {
  // Try to have a Büchi condition if we have Rabin.
  Rabin_to_Buchi,
  Streett_to_co_Buchi,
  // IAR
  IAR_Streett,
  IAR_Rabin,
  // CAR
  CAR,
  TAR,
  // Changing colors transforms acceptance to max even/odd copy.
  Copy_even,
  Copy_odd,
  // If a condition is "t" or "f", we just have to copy the automaton.
  False_clean,
  True_clean,
  // We don't apply any algorithm (a trivial SCC)
  None,
  // Convert a Büchi-type automaton to Büchi
  Buchi_type_to_Buchi,
  // Convert a co-Büchi-type automaton to co-Büchi
  Co_Buchi_type_to_co_Buchi,
  // Convert a parity-type automaton to parity
  Parity_type,
  // Remove a prefix of the condition that is parity.
  Parity_prefix,
  // TODO:
  Parity_prefix_general,
};


static std::string
algorithm_to_str(algorithm algo)
{
  switch (algo)
  {
    case IAR_Streett:
      return "IAR (Streett)";
    case IAR_Rabin:
      return "IAR (Rabin)";
    case CAR:
      return "CAR";
    case TAR:
      return "TAR";
    case Copy_even:
      return "Copy even";
    case Copy_odd:
      return "Copy odd";
    case False_clean:
      return "False clean";
    case True_clean:
      return "True clean";
    case Streett_to_co_Buchi:
      return "Streett to co-Büchi";
    case Rabin_to_Buchi:
      return "Rabin to Büchi";
    case Buchi_type_to_Buchi:
      return "Büchi type to Büchi";
    case Co_Buchi_type_to_co_Buchi:
      return "Co-Büchi type to Co-Büchi";
    case None:
      return "None";
    case Parity_type:
      return "Parity type to parity";
    case Parity_prefix:
      return "Parity prefix";
    case Parity_prefix_general:
      return "Parity prefix general";
  }
  SPOT_UNREACHABLE();
}

using perm_t = std::vector<unsigned>;

struct to_parity_state
{
    // State of the original automaton
    unsigned original_state;
    // We create a new automaton for each SCC of the original automaton
    // so we keep a link between a to_parity_state and the state of the
    // subautomaton.
    unsigned scc_state;
    // Permutation used by IAR and CAR.
    perm_t perm;

    bool
    operator<(const to_parity_state &other) const
    {
        if (original_state < other.original_state)
            return true;
        if (original_state > other.original_state)
            return false;
        if (perm < other.perm)
            return true;
        if (perm > other.perm)
            return false;
        return scc_state < other.scc_state;
    }

    std::string
    to_str(algorithm algo) const
    {
        std::stringstream s;
        s << original_state;
        unsigned ps = perm.size();
        if (ps > 0)
        {
            s << " [";
            for (unsigned i = 0; i != ps; ++i)
            {
                if (i > 0)
                    s << ',';
                s << perm[i];
            }
            s << ']';
        }
        s << ", ";
        s << algorithm_to_str(algo);
        return s.str();
    }
};

const acc_cond::mark_t &
fin(const std::vector<acc_cond::rs_pair>& pairs, unsigned k, algorithm algo)
const
{
    if (algo == IAR_Rabin)
        return pairs[k].fin;
    else
        return pairs[k].inf;
}

acc_cond::mark_t
inf(const std::vector<acc_cond::rs_pair>& pairs, unsigned k, algorithm algo)
const
{
    if (algo == IAR_Rabin)
        return pairs[k].inf;
    else
        return pairs[k].fin;
}

// Gives for each state a set of marks incoming to this state.
std::vector<std::set<acc_cond::mark_t>>
get_inputs_states(const twa_graph_ptr& aut)
{
    auto used = aut->acc().get_acceptance().used_sets();
    std::vector<std::set<acc_cond::mark_t>> inputs(aut->num_states());
    for (const auto& e : aut->edges())
    {
        auto elements = e.acc & used;
        if (elements.has_many())
            inputs[e.dst].insert(elements);
    }
    return inputs;
}

// Gives for each state a set of pairs incoming to this state.
std::vector<std::set<std::vector<unsigned>>>
get_inputs_iar(const twa_graph_ptr& aut, algorithm algo,
               const std::set<unsigned>& perm_elem,
               const std::vector<acc_cond::rs_pair>& pairs)
{
    std::vector<std::set<std::vector<unsigned>>> inputs(aut->num_states());
    for (const auto& e : aut->edges())
    {
        auto acc = e.acc;
        std::vector<unsigned> new_vect;
        for (unsigned k : perm_elem)
            if (acc & fin(pairs, k, algo))
                new_vect.push_back(k);
        std::sort(std::begin(new_vect), std::end(new_vect));
        inputs[e.dst].insert(new_vect);
    }
    return inputs;
}

// Give an order from the set of marks
std::vector<unsigned>
group_to_vector(const std::set<acc_cond::mark_t>& group)
{
    // In this function, we have for example the marks {1, 2}, {1, 2, 3}, {2}
    // A compatible order is [2, 1, 3]
    std::vector<acc_cond::mark_t> group_vect(group.begin(), group.end());

    // We sort the elements by inclusion. This function is called on a
    // set of marks such that each mark is included or includes the others.
    std::sort(group_vect.begin(), group_vect.end(),
              [](const acc_cond::mark_t& left, const acc_cond::mark_t& right)
                {
                    return (left != right) && ((left & right) == left);
                });
    // At this moment, we have the vector [{2}, {1, 2}, {1, 2, 3}].
    // In order to create the order, we add the elements of the first element.
    // Then we add the elements of the second mark (without duplication), etc.
    std::vector<unsigned> result;
    for (const auto& mark : group_vect)
    {
        for (unsigned col : mark.sets())
            if (std::find(result.begin(), result.end(), col) == result.end())
                result.push_back(col);
    }
    return result;
}

// Give an order from the set of indices of pairs
std::vector<unsigned>
group_to_vector_iar(const std::set<std::vector<unsigned>>& group)
{
    std::vector<std::vector<unsigned>> group_vect(group.begin(), group.end());
    for (auto& vec : group_vect)
        std::sort(std::begin(vec), std::end(vec));
    std::sort(group_vect.begin(), group_vect.end(),
              [](const std::vector<unsigned>& left,
                 const std::vector<unsigned>& right)
                {
                    return (right != left)
                        && std::includes(right.begin(), right.end(),
                                         left.begin(), left.end());
                });
    std::vector<unsigned> result;
    for (auto vec : group_vect)
        for (unsigned col : vec)
            if (std::find(result.begin(), result.end(), col) == result.end())
                result.push_back(col);
    return result;
}

// Give a correspondance between a mark and an order for CAR
std::map<acc_cond::mark_t, std::vector<unsigned>>
get_groups(const std::set<acc_cond::mark_t>& marks_input)
{
    std::map<acc_cond::mark_t, std::vector<unsigned>> result;

    std::vector<std::set<acc_cond::mark_t>> groups;
    for (acc_cond::mark_t mark : marks_input)
    {
        bool added = false;
        for (unsigned group = 0; group < groups.size(); ++group)
        {
            if (std::all_of(groups[group].begin(), groups[group].end(),
                            [mark](acc_cond::mark_t element)
                            {
                                return ((element | mark) == mark)
                                    || ((element | mark) == element);
                            }))
            {
                groups[group].insert(mark);
                added = true;
                break;
            }
        }
        if (!added)
            groups.push_back({mark});
    }
    for (auto& group : groups)
    {
        auto new_vector = group_to_vector(group);
        for (auto mark : group)
            result.insert({mark, new_vector});
    }
    return result;
}

// Give a correspondance between a mark and an order for IAR
std::map<std::vector<unsigned>, std::vector<unsigned>>
get_groups_iar(const std::set<std::vector<unsigned>>& marks_input)
{
    std::map<std::vector<unsigned>, std::vector<unsigned>> result;

    std::vector<std::set<std::vector<unsigned>>> groups;
    for (auto vect : marks_input)
    {
        bool added = false;
        for (unsigned group = 0; group < groups.size(); ++group)
            if (std::all_of(groups[group].begin(), groups[group].end(),
                            [vect](std::vector<unsigned> element)
                            {
                                return std::includes(vect.begin(), vect.end(),
                                               element.begin(), element.end())
                              || std::includes(element.begin(), element.end(),
                                                     vect.begin(), vect.end());
                            }))
            {
                groups[group].insert(vect);
                added = true;
                break;
            }
        if (!added)
            groups.push_back({vect});
    }
    for (auto& group : groups)
    {
        auto new_vector = group_to_vector_iar(group);
        for (auto vect : group)
            result.insert({vect, new_vector});
    }
    return result;
}

// Give for each state the correspondance between a mark and an order (CAR)
std::vector<std::map<acc_cond::mark_t, std::vector<unsigned>>>
get_mark_to_vector(const twa_graph_ptr& aut)
{
    std::vector<std::map<acc_cond::mark_t, std::vector<unsigned>>> result;
    auto inputs = get_inputs_states(aut);
    for (unsigned state = 0; state < inputs.size(); ++state)
        result.push_back(get_groups(inputs[state]));
    return result;
}

// Give for each state the correspondance between a mark and an order (IAR)
std::vector<std::map<std::vector<unsigned>, std::vector<unsigned>>>
get_iar_to_vector(const twa_graph_ptr& aut, algorithm algo,
                  const std::set<unsigned>& perm_elem,
                  const std::vector<acc_cond::rs_pair>& pairs)
{
    std::vector<std::map<std::vector<unsigned>, std::vector<unsigned>>> result;
    auto inputs = get_inputs_iar(aut, algo, perm_elem, pairs);
    for (unsigned state = 0; state < inputs.size(); ++state)
        result.push_back(get_groups_iar(inputs[state]));
    return result;
}



public:
explicit to_parity_generator(const const_twa_graph_ptr& a,
                           const to_parity_options options)
    : aut_(a)
    , scc_(scc_info(a))
    , is_odd(false)
    , state2ps(a->num_states(), std::nullopt)
    , state2nums(a->num_states())
    , options(options)
{
  orig_states = new std::vector<unsigned>();
    if (options.pretty_print)
        names = new std::vector<std::string>();
    else
        names = nullptr;
}

// Add a state to the resulting automaton. Use this function instead
// of res_->new_state().
unsigned
add_res_state(algorithm algo, const std::vector<unsigned>& permu,
                unsigned scc_state, unsigned initial_state)
{
    to_parity_state new_ps = { initial_state, scc_state, permu };
    auto new_state = res_->new_state();
    orig_states->push_back(initial_state);
    ps2num[new_ps] = new_state;
    num2ps.insert(num2ps.begin() + new_state, new_ps);
    state2nums[initial_state].push_back(new_state);
    if (options.pretty_print)
        names->push_back(new_ps.to_str(algo));
    // The algorithms that apply LAR can use a bottom-SCC optimisation. That is
    // why they modify state2ps and we don't do it here.
    if (algo != CAR && algo != IAR_Streett && algo != IAR_Rabin && algo != TAR)
      state2ps[initial_state] = new_ps;
    return new_state;
}

// Add an edge to the resulting automaton. Use this function instead of
// res_->new_edge().
unsigned
add_res_edge(unsigned src, unsigned dst, bdd cond, acc_cond::mark_t acc)
{
    auto result = res_->new_edge(src, dst, cond, acc);
    auto mark_set = acc.max_set();
    auto mark_color = mark_set ? mark_set - 1 : 0;
    // Update the value of the maximum color used to create the
    // parity automaton.
    max_used_color = std::max(max_used_color, mark_color);
    // Update the maximum color of the SCC.
    current_scc_max_color = std::max(current_scc_max_color, mark_color);
    return result;
}

// During the creation of the states, we had to choose between a set of
// compatible states. But it is possible to create another compatible state
// after. This function checks if a compatible state was created after and
// use it.
void
change_transitions_destination(twa_graph_ptr& aut,
                               const std::vector<unsigned>& states,
                               std::map<unsigned, std::vector<unsigned>>&
                                  partial_history,
                               state_2_lar_scc& state_2_ps)
{
    for (auto s : states)
        for (auto& edge : aut->out(s))
        {
            unsigned
                src = edge.src,
                dst = edge.dst;
            // We don't change loops
            if (src == dst)
                continue;
            unsigned dst_scc = num2ps[dst].scc_state;
            auto cant_change = partial_history[aut->edge_number(edge)];
            edge.dst = state_2_ps.get_sub_tree(cant_change, dst_scc)
                                ->get_end(true);
        }
}

// If an automaton has the acceptance condition ⊤ or ⊥, we just have to copy
// the automaton and add the correct color to all the transitions.
unsigned
apply_false_true_clean(const twa_graph_ptr& sub_automaton, bool is_true)
{
    assert(sub_automaton->acc().is_f() || sub_automaton->acc().is_t());
    // The color is 0 if and only if the condition is ⊤ and we are creating an
    // automaton with a parity max even condition or if the condition is ⊥ and
    // we are creating a parity max odd automaton.
    unsigned col = is_true ^ !is_odd;

    auto init_states = sub_automaton->
        get_named_prop<std::vector<unsigned>>("original-states");

    const auto sub_automaton_num_states = sub_automaton->num_states();

    // For pretty print
    auto algo = is_true ? True_clean : False_clean;

    // Associate to each state to sub_automaton a state of the result. Used to
    // create the edges when all states are added.
    std::vector<unsigned> sub_state2num;

    for (unsigned state = 0; state < sub_automaton_num_states; ++state)
    {
        unsigned s_aut = (*init_states)[state];

        sub_state2num.push_back(add_res_state(algo, perm_t(), state, s_aut));
    }

    for (auto& e : sub_automaton->edges())
    {
        unsigned src_res_state = sub_state2num[e.src];
        unsigned dst_res_state = sub_state2num[e.dst];

        add_res_edge(src_res_state, dst_res_state, e.cond, { col });
    }
    return sub_automaton_num_states;
}

// If the current res_ has parity max even condition, it is converted to max
// odd.
void
change_to_odd()
{
    if (!is_odd)
    {
        // We change the parity of res_.
        res_->set_acceptance(acc_cond(
                acc_cond::acc_code::parity(true, is_odd, max_used_color + 1)));
        is_odd = true;
        change_parity_here(res_, parity_kind::parity_kind_max,
            parity_style::parity_style_odd);

        // We update the value of the maximum color in a transition of res_.
        max_used_color = 0;
        for (auto& edge : res_->edge_vector())
        {
            auto max_set = edge.acc.max_set();
            if (max_set)
                max_used_color = std::max(max_used_color, max_set - 1);
        }
    }
}

unsigned
apply_copy(twa_graph_ptr& sub_automaton, std::vector<int>& permut,
            bool copy_odd)
{
    // If res_ is a max even
    if (copy_odd)
        change_to_odd();
    // If the condition of sub_automaton is parity even and res_ is parity odd
    // we need to add 1.
    bool is_even_in_odd_world = !copy_odd && is_odd;
    auto init_states = sub_automaton
        ->get_named_prop<std::vector<unsigned>>("original-states");

    const unsigned sub_automaton_num_states = sub_automaton->num_states();
    auto algo = copy_odd ? Copy_odd : Copy_even;
    // Copy the states of the automaton.
    for (unsigned state = 0; state < sub_automaton_num_states; ++state)
    {
        auto s_aut = (*init_states)[state];
        add_res_state(algo, perm_t(), state, s_aut);
    }

    // Used to only copy the useful colors on the transitions.
    auto cond_col = sub_automaton->acc().get_acceptance().used_sets();

    // We reverse the order of the color in order to use index as value.
    // For example with Inf(3) | (Fin(2) & Inf(4)), we reverse in order to get
    // [4 2 3] and 4 ↦ 0, 2 ↦ 1, 3 ↦ 2.
    std::reverse(permut.begin(), permut.end());

    for (auto& e : sub_automaton->edges())
    {
        int max_edge = -1;
        // Add 0 to a transition without color when we translate it to odd.
        if (!e.acc.min_set() && is_even_in_odd_world)
            max_edge = 0;
        else
            for (auto col : e.acc.sets())
                if (cond_col.has(col))
                {
                    auto col_it = std::find(permut.begin(), permut.end(), col);
                    assert(col_it != permut.end());
                    int index = std::distance(permut.begin(), col_it);
                    unsigned new_color = index + is_even_in_odd_world;
                    max_edge = std::max(max_edge, (int) new_color);
                }
        auto mark = max_edge != -1 ? acc_cond::mark_t { (unsigned) max_edge } :
                                acc_cond::mark_t {};
        to_parity_state src = { (*init_states)[e.src], e.src, perm_t() },
                  dst = { (*init_states)[e.dst], e.dst, perm_t() };
        unsigned src_state = ps2num[src],
                 dst_state = ps2num[dst];
        add_res_edge(src_state, dst_state, e.cond, mark);
    }
    return sub_automaton_num_states;
}

unsigned
apply_to_buchi(twa_graph_ptr& sub_automaton,
               algorithm algo,
               twa_graph_ptr (*buch_fun)(const const_twa_graph_ptr&))
{
    // The version with a co-Büchi condition.
    auto buchi_version = buch_fun(sub_automaton);
    if (buchi_version == nullptr)
        return -1U;
    const unsigned sub_automaton_num_states = sub_automaton->num_states();

    auto init_states = sub_automaton
        ->get_named_prop<std::vector<unsigned>>("original-states");

    std::vector<unsigned> sub_aut2num;
    for (unsigned state = 0; state < sub_automaton_num_states; ++state)
    {
        unsigned s_aut = (*init_states)[state];
        sub_aut2num.push_back(add_res_state(algo, perm_t(), state, s_aut));
    }

    bool odd_algo = algo == Co_Buchi_type_to_co_Buchi
                    || algo == Streett_to_co_Buchi;
    if (odd_algo)
        change_to_odd();

    for (const auto& e : buchi_version->edges())
    {
        unsigned shift = !odd_algo && is_odd;
        acc_cond::mark_t mark;
        unsigned min_set = e.acc.min_set();
        if (min_set != 0)
            mark = { min_set - 1 + shift };
        else if (shift)
            mark = { 0 };
        else
            mark = {};

        auto src_res_num = sub_aut2num[e.src];
        auto dst_res_num = sub_aut2num[e.dst];
        add_res_edge(src_res_num, dst_res_num, e.cond, mark);
    }
    return sub_automaton_num_states;
}

bool
try_apply_to_parity_type(twa_graph_ptr& sub_automaton)
{
  // We can try to get a parity-type automaton with a condition that starts
  // with Inf or Fin if it does not exist.
  twa_graph_ptr parit = parity_type_to_parity(sub_automaton);
  // If the automaton is not parity type, we stop
  if (parit == nullptr)
    return false;

  // Did we get a parity odd or even condition ?
  bool max, is_odd_parit;
  parit->acc().is_parity(max, is_odd_parit, true);

  // If it is odd, we have to update the current res_.
  if (is_odd_parit)
    change_to_odd();

  int shift = is_odd && !is_odd_parit;
  const unsigned sub_automaton_num_states = sub_automaton->num_states();
  auto init_states = sub_automaton
                    ->get_named_prop<std::vector<unsigned>>("original-states");

  std::vector<unsigned> sub_aut2num;

  // If it is parity-type, we just have to copy the states…
  for (unsigned state = 0; state < sub_automaton_num_states; ++state)
  {
    unsigned s_aut = (*init_states)[state];
    to_parity_state new_ps = { s_aut, state, perm_t() };
    sub_aut2num.push_back(add_res_state(Parity_type, perm_t(), state, s_aut));
  }

  // …and the transitions
  for (auto& e : parit->edges())
  {
    unsigned edge_col = e.acc.max_set() - 1 + shift;
    auto edge_mark = (edge_col == -1U) ? acc_cond::mark_t {} :
                                         acc_cond::mark_t { edge_col };

    auto src_res_num = sub_aut2num[e.src];
    auto dst_res_num = sub_aut2num[e.dst];
    add_res_edge(src_res_num, dst_res_num, e.cond, edge_mark);
  }
  return true;
}

bool
try_apply_to_buchi(twa_graph_ptr& sub_automaton,
                        bool general_case,
                        twa_graph_ptr (*buch_fun)(const const_twa_graph_ptr&))
{
  auto algo = general_case ? Buchi_type_to_Buchi : Rabin_to_Buchi;
  if (apply_to_buchi(sub_automaton, algo, buch_fun) != -1U)
      return true;
  auto old_code = sub_automaton->get_acceptance();
  sub_automaton->set_acceptance(acc_cond(old_code.complement()));
  algo = general_case ? Co_Buchi_type_to_co_Buchi : Streett_to_co_Buchi;

  unsigned other_test = apply_to_buchi(sub_automaton, algo, buch_fun);
  sub_automaton->set_acceptance(acc_cond(old_code));
  return other_test != -1U;
}

bool
try_apply_rabin_to_buchi(twa_graph_ptr& sub_automaton)
{
    return try_apply_to_buchi(sub_automaton, false,
                              &rabin_to_buchi_if_realizable);
}

bool
try_apply_to_buchi(twa_graph_ptr& sub_automaton)
{
  return try_apply_to_buchi(sub_automaton, true, &buchi_type_to_buchi);
}

// If possible a part of the acceptance condition that is parity is removed.
// The transitions with a color of this part are removed and the paritization
// is applied on the resulting SCC.
// If there is no such prefix, false is returned.
bool
try_apply_parity_prefix(twa_graph_ptr& sub_automaton)
{
    acc_cond new_acc;
    // colors contains the colors that are removed from the
    // acceptance condition.
    std::vector<unsigned> colors;
    auto start_inf = sub_automaton->acc().has_parity_prefix(new_acc, colors);
    auto init_states = sub_automaton->
                    get_named_prop<std::vector<unsigned> >("original-states");
    // If there exists a parity prefix, we remove the edges from this
    // automaton.
    if (colors.size() > 0)
    {
        // We don't want to apply parity prefix recursively
        options.parity_prefix = false;
        // We just work on the rest of the acceptance condition.
        sub_automaton->set_acceptance(new_acc);
        auto sub_edge_vector = sub_automaton->edge_vector();
        const auto sub_edge_vector_size = sub_edge_vector.size();
        // The colors that are in the prefix
        auto tocut = std::accumulate(colors.begin(), colors.end(),
          acc_cond::mark_t {}, [](acc_cond::mark_t mark, unsigned value)
          {
              return mark | acc_cond::mark_t {value};
          });

        std::vector<twa_graph::edge_storage_t> removed_edges;
        for (unsigned i = 0; i < sub_edge_vector_size; ++i)
        {
          auto& edge = sub_edge_vector[i];
          if (edge.acc & tocut)
            removed_edges.push_back(edge);
        }

        scc_and_mark_filter filt(sub_automaton, tocut);
        scc_info si(filt);

        unsigned scc_max_color = 0;
        const unsigned scc_nb = si.scc_count();
        std::vector<bool> keep(sub_automaton->edge_vector().size(), true);
        auto sub_auts = split_aut(si, keep);
        for (unsigned scc = 0; scc < scc_nb; ++scc)
        {
          auto sub_sub = sub_auts[scc];
          auto init_states_sub_sub = sub_sub->
                  get_named_prop<std::vector<unsigned> >("original-states");
          const unsigned sub_sub_num_states = sub_sub->num_states();
          for (unsigned state = 0; state < sub_sub_num_states; ++state)
          {
            // We need a correspondance between a state of sub_sub and a state
            // of aut_ during the paritization.
            (*init_states_sub_sub)[state] =
              (*init_states)[(*init_states_sub_sub)[state]];
          }
          if (sub_sub->num_edges() == 0)
            add_res_state(Parity_prefix, perm_t(), 0,
                            (*init_states_sub_sub)[0]);
          else
            build_scc(sub_sub);
          scc_max_color = std::max(scc_max_color, current_scc_max_color);
        }

        options.parity_prefix = true;
        unsigned max_prefix_color = scc_max_color + colors.size();
        max_prefix_color += (max_prefix_color % 2) + (is_odd ^ !start_inf);
        // We add the edges that parity prefix was able to color.
        for (auto e : removed_edges)
        {
          auto src = (*init_states)[e.src];
          auto dst = (*init_states)[e.dst];
          unsigned min_index = -1U;
          for (auto i : e.acc.sets())
          {
            auto element = std::find(colors.begin(), colors.end(), i);
            if (element != colors.end())
            {
              unsigned pos = std::distance(colors.begin(), element);
              min_index = std::min(min_index, pos);
            }
          }
          assert(min_index != -1U);
          for (auto s : state2nums[src])
          {
            auto col = max_prefix_color - min_index;
            add_res_edge(s, ps2num[state2ps[dst].value()], e.cond, { col });
          }
        }
        // If we have an automaton like 0 -{1}-> 1, 1 -{}-> 0 with tocut = {1},
        // the first transition is in removed_edges but not the second one but
        // the transition is removed by scc_info as it links two SCCs. Here we
        // add this kind of edges.
        for (auto& e : sub_automaton->edges())
          if (si.scc_of(e.src) != si.scc_of(e.dst) && !(e.acc & tocut))
          {
            auto src = (*init_states)[e.src];
            auto dst = (*init_states)[e.dst];
            assert(!state2nums[src].empty());
            for (auto s : state2nums[src])
              add_res_edge(s, ps2num[state2ps[dst].value()], e.cond, { });
          }
        return true;
    }
    return false;
}

bool
try_apply_parity_prefix_general(const const_twa_graph_ptr& sub_automaton)
{
  // We don't want a recursive call to this function.
  options.parity_prefix_general = false;
  std::vector<int> status;
  auto partially_paritized = partial_parity_type(sub_automaton, status);
  auto acc_part = partially_paritized->acc();
  bool odd, max;
  acc_part.is_parity(max, odd);

  // If all edges are colored, we don't need to paritize
  // sub-SCCs.
  if (std::find(status.begin(), status.end(), 2) == status.end())
  {
  // We need to associate to each state of sub_automaton the number of the
  // state of res when we create edges.
    std::vector<unsigned> state_subaut2num_local;
    auto init_states = sub_automaton
            ->get_named_prop<std::vector<unsigned>>("original-states");
    const unsigned sub_num_states = sub_automaton->num_states();
    for (unsigned state = 0; state < sub_num_states; ++state)
    {
      unsigned num = add_res_state(Parity_prefix_general, {}, state,
                                    (*init_states)[state]);
      state_subaut2num_local.push_back(num);
    }

    bool diff = odd != is_odd;
    for (auto &e : partially_paritized->edges())
    {
      unsigned src = e.src,
               dst = e.dst;
      unsigned src_num = state_subaut2num_local[src],
               dst_num = state_subaut2num_local[dst];
      acc_cond::mark_t mark;
      if (!e.acc)
        mark = diff ? acc_cond::mark_t { 0 } : acc_cond::mark_t {};
      else
        mark = { e.acc.min_set() - 1 + diff };
      add_res_edge(src_num, dst_num, e.cond, mark);
    }
    // This option was disabled.
    options.parity_prefix_general = true;
    return true;
  }
  // If partial_parity_type was not able to assign a color, we can't work.
  if (std::find(status.begin() + 1, status.end(), 1) == status.end())
  {
    options.parity_prefix_general = false;
    return false;
  }

  // keep = ⊤ ⇔ partial_parity_type was not able to assign a color.
  std::vector<bool> keep;
  std::transform(status.begin(), status.end(), std::back_inserter(keep),
                  [](int x) { return x == 2; });

  assert(keep.size() == partially_paritized->edge_vector().size());

  using filter_data_t = std::pair<const const_twa_graph_ptr, std::vector<bool>>;
  auto filter_edge = [](const twa_graph::edge_storage_t& e,
                        unsigned,
                        void *filter_data)
    {
      auto& d = *static_cast<filter_data_t*>(filter_data);
      auto& sub_automaton = d.first;
      auto& keep = d.second;
      auto edge_number = sub_automaton->edge_number(e);
      if (keep[edge_number])
        return scc_info::edge_filter_choice::keep;
      return scc_info::edge_filter_choice::cut;
    };

    filter_data_t filter_data { sub_automaton, keep };

    scc_info si(sub_automaton,
                sub_automaton->get_init_state_number(),
                filter_edge, &filter_data);

    const unsigned scc_nb = si.scc_count();
    // We need to know what is the maximum color used during the paritization
    // of the sub-SCCs.
    auto init_states = sub_automaton->
                    get_named_prop<std::vector<unsigned>>("original-states");
    unsigned scc_max_color = 0;
    auto sub_auts = split_aut(si, keep);
    for (unsigned scc = 0; scc < scc_nb; ++scc)
    {
      auto sub_sub = sub_auts[scc];
      auto init_states_sub_sub = sub_sub->
                    get_named_prop<std::vector<unsigned>>("original-states");
      const unsigned sub_sub_num_states = sub_sub->num_states();
      for (unsigned state = 0; state < sub_sub_num_states; ++state)
      {
        // We need a correspondance between a state of sub_sub and a state
        // of aut_ during the paritization.
        (*init_states_sub_sub)[state] =
            (*init_states)[(*init_states_sub_sub)[state]];
      }
      if (sub_sub->num_edges() == 0)
        add_res_state(Parity_prefix_general, perm_t(), 0,
                        (*init_states_sub_sub)[0]);
      else
        build_scc(sub_sub);
      scc_max_color = std::max(scc_max_color, current_scc_max_color);
    }

    // We add the edges that partial_parity_type was able to color.

    // If the parity prefix is max odd and the current res is odd or the
    // opposite, we need to add 1 to the transitions of partially_paritized.
    // We also avoid to get a color used in a recursive paritisation.
    auto x = ((odd != is_odd) + scc_max_color) % 2;
    unsigned prefix_shift = x + scc_max_color + 2 * (1 - x);
    for (auto& e : partially_paritized->edges())
    {
      auto edge_number = partially_paritized->edge_number(e);
      if (status[edge_number] == 1)
      {
        unsigned src = (*init_states)[e.src],
                 dst = (*init_states)[e.dst];
        auto src_copies = state2nums[src];
        auto dst_copy = state2nums[dst][0];
        acc_cond::mark_t mark { e.acc.max_set() - 1 + prefix_shift };
        for (unsigned st : src_copies)
          add_res_edge(st, dst_copy, e.cond, mark);
      }
    }

    // Some edges are removed by scc_info but are not colored by
    // partial_parity_type
    for (auto& e : sub_automaton->edges())
    {
      auto edge_number = sub_automaton->edge_number(e);
      if (si.scc_of(e.src) != si.scc_of(e.dst) && status[edge_number] == 2)
      {
        auto src = (*init_states)[e.src];
        auto dst = (*init_states)[e.dst];
        assert(!state2nums[src].empty());
        for (auto s : state2nums[src])
          add_res_edge(s, ps2num[state2ps[dst].value()], e.cond, { });
      }
    }
    options.parity_prefix_general = true;
    return true;
}

void
initial_perm_iar(std::set<unsigned> &perm_elem, perm_t &p0,
                 algorithm algo, const acc_cond::mark_t& colors,
                 const std::vector<acc_cond::rs_pair>& pairs)
{
    for (unsigned k = 0; k != pairs.size(); ++k)
        if (!inf(pairs, k, algo) || (colors & (pairs[k].fin | pairs[k].inf)))
        {
            perm_elem.insert(k);
            p0.push_back(k);
        }
}

// Create a permutation for the first state of a SCC (CAR)
void
initial_perm_car(perm_t &p0, const acc_cond::mark_t &colors)
{
    auto cont = colors.sets();
    p0.assign(cont.begin(), cont.end());
}

void
find_new_perm_iar(perm_t &new_perm,
                  const std::vector<acc_cond::rs_pair> &pairs,
                  const acc_cond::mark_t &acc,
                  algorithm algo, const std::set<unsigned> &perm_elem,
                  unsigned &seen_nb)
{
    for (unsigned k : perm_elem)
        if (acc & fin(pairs, k, algo))
        {
            ++seen_nb;
            auto it = std::find(new_perm.begin(), new_perm.end(), k);

            // move the pair in front of the permutation
            std::rotate(new_perm.begin(), it, it + 1);
        }
}

// Given the set acc of colors appearing on an edge, create a new
// permutation new_perm, and give the number seen_nb of colors moved to
// the head of the permutation.
void
find_new_perm_car(perm_t &new_perm, const acc_cond::mark_t &acc,
                  unsigned &seen_nb, unsigned &h)
{
    for (unsigned k : acc.sets())
    {
        auto it = std::find(new_perm.begin(), new_perm.end(), k);
        if (it != new_perm.end())
        {
            h = std::max(h, unsigned(it - new_perm.begin()) + 1);
            std::rotate(new_perm.begin(), it, it + 1);
            ++seen_nb;
        }
    }
}

void
get_acceptance_iar(algorithm algo, const perm_t &current_perm,
                   const std::vector<acc_cond::rs_pair> &pairs,
                   const acc_cond::mark_t &e_acc, acc_cond::mark_t &acc)
{
    unsigned delta_acc = (algo == IAR_Streett) && is_odd;

    // find the maximal index encountered by this transition
    unsigned maxint = -1U;

    for (int k = current_perm.size() - 1; k >= 0; --k)
    {
        unsigned pk = current_perm[k];

        if (!inf(pairs, pk, algo)
            || (e_acc & (pairs[pk].fin | pairs[pk].inf)))
        {
            maxint = k;
            break;
        }
    }
    unsigned value;

    if (maxint == -1U)
        value = delta_acc;
    else if (e_acc & fin(pairs, current_perm[maxint], algo))
        value = 2 * maxint + 2 + delta_acc;
    else
        value = 2 * maxint + 1 + delta_acc;
    acc = { value };
}

void
get_acceptance_car(const acc_cond &sub_aut_cond, const perm_t &new_perm,
                   unsigned h, acc_cond::mark_t &acc)
{
    acc_cond::mark_t m(new_perm.begin(), new_perm.begin() + h);
    bool rej = !sub_aut_cond.accepting(m);
    unsigned value = 2 * h + rej + is_odd;
    acc = { value };
}

// TODO: Doc
unsigned
apply_car_iar(twa_graph_ptr sub_automaton, std::vector<acc_cond::rs_pair>
                   pairs, const algorithm algo)
{
    if (algo == IAR_Rabin)
        change_to_odd();

    std:: vector<unsigned> added_states;
    unsigned nb_created_states = 0;
    std::map<unsigned, std::vector<unsigned>> edge_to_colors;
    // Maps a state of sub_automaton to a parity state
    auto state_2_lar = state_2_lar_scc(sub_automaton->num_states());
    auto init_states = sub_automaton->
        get_named_prop<std::vector<unsigned>>("original-states");
    std::deque<to_parity_state> todo;
    auto get_state =
        [&](const to_parity_state &s){
            auto it = ps2num.find(s);
            if (it == ps2num.end())
            {
                ++nb_created_states;
                unsigned nb = add_res_state(algo, s.perm,
                                            s.scc_state, s.original_state);
                if (options.search_ex)
                    state_2_lar.add_res_state(s.scc_state, nb, s.perm);
                if (!options.bscc && !state2ps[s.original_state].has_value())
                  state2ps[s.original_state] = s;
                added_states.push_back(nb);
                todo.push_back(s);
                return nb;
            }
            return it->second;
        };

    auto colors = sub_automaton->acc().get_acceptance().used_sets();
    std::set<unsigned> perm_elem;

    perm_t p0 = { };
    switch (algo)
    {
    case IAR_Streett:
    case IAR_Rabin:
        initial_perm_iar(perm_elem, p0, algo, colors, pairs);
        break;
    case CAR:
        initial_perm_car(p0, colors);
        break;
    default:
        SPOT_UNREACHABLE();
        break;
    }

    std::vector<std::map<acc_cond::mark_t, std::vector<unsigned>>> maps;
    std::vector<std::map<std::vector<unsigned>, std::vector<unsigned>>>
      iar_maps;
    if (algo == CAR)
        maps = get_mark_to_vector(sub_automaton);
    else
        iar_maps = get_iar_to_vector(sub_automaton, algo, perm_elem, pairs);

    to_parity_state s0{ (*init_states)[0], 0, p0 };
    get_state(s0);         // put s0 in todo

    // the main loop
    while (!todo.empty())
    {
        to_parity_state current = todo.front();
        todo.pop_front();

        unsigned src_num = get_state(current);
        for (const auto &e : sub_automaton->out(current.scc_state))
        {
            perm_t new_perm = current.perm;

            // Count pairs whose fin-part is seen on this transition
            unsigned seen_nb = 0;

            // consider the pairs for this SCC only
            unsigned h = 0;

            switch (algo)
            {
            case IAR_Rabin:
            case IAR_Streett:
                find_new_perm_iar(new_perm, pairs, e.acc, algo,
                                  perm_elem, seen_nb);
                break;
            case CAR:
                find_new_perm_car(new_perm, e.acc, seen_nb, h);
                break;
            default:
                SPOT_UNREACHABLE();
            }

            std::vector<unsigned> not_moved(new_perm.begin() + seen_nb,
                                            new_perm.end());

            if (options.force_order)
            {
                if (algo == CAR && seen_nb > 1)
                {
                    auto map = maps[e.dst];
                    acc_cond::mark_t first_vals(
                        new_perm.begin(), new_perm.begin() + seen_nb);
                    auto new_start = map.find(first_vals);
                    assert(new_start->second.size() >= seen_nb);
                    assert(new_start != map.end());
                    for (unsigned i = 0; i < seen_nb; ++i)
                        new_perm[i] = new_start->second[i];
                }
                else if ((algo == IAR_Streett || algo == IAR_Rabin)
                        && seen_nb > 1)
                {
                    auto map = iar_maps[e.dst];
                    std::vector<unsigned> first_vals(
                            new_perm.begin(), new_perm.begin() + seen_nb);
                    std::sort(std::begin(first_vals), std::end(first_vals));
                    auto new_start = map.find(first_vals);
                    assert(new_start->second.size() >= seen_nb);
                    assert(new_start != map.end());
                    for (unsigned i = 0; i < seen_nb; ++i)
                        new_perm[i] = new_start->second[i];
                }
            }

            // Optimization: when several indices are seen in the
            // transition, they move at the front of new_perm in any
            // order. Check whether there already exists a to_parity_state
            // that matches this condition.
            to_parity_state dst;
            unsigned dst_num = -1U;

            if (options.search_ex)
                dst_num = state_2_lar.get_res_state(e.dst, new_perm, seen_nb,
                            options.use_last);

            if (dst_num == -1U)
            {
                auto dst = to_parity_state{ (*init_states)[e.dst],
                                            e.dst, new_perm };
                dst_num = get_state(dst);
            }

            acc_cond::mark_t acc = { };

            switch (algo)
            {
            case IAR_Rabin:
            case IAR_Streett:
                get_acceptance_iar(algo, current.perm, pairs, e.acc, acc);
                break;
            case CAR:
                get_acceptance_car(sub_automaton->acc(), new_perm, h, acc);
                break;
            default:
                SPOT_UNREACHABLE();
            }

            unsigned acc_col = acc.min_set() - 1;
            auto new_e = add_res_edge(src_num, dst_num, e.cond, { acc_col });
            edge_to_colors.insert({new_e, not_moved});
        }
    }
    if (options.search_ex && options.use_last)
        change_transitions_destination(res_, added_states, edge_to_colors,
                                       state_2_lar);

    if (options.bscc)
    {
      scc_info sub_scc(res_, get_state(s0));
      // SCCs are numbered in reverse topological order, so the bottom SCC has
      // index 0.
      const unsigned bscc = 0;
      assert(sub_scc.scc_count() != 0);
      assert(sub_scc.succ(0).empty());
      assert(
          [&](){
                      for (unsigned s = 1; s != sub_scc.scc_count(); ++s)
                          if (sub_scc.succ(s).empty())
                              return false;

                      return true;
                  } ());

      assert(sub_scc.states_of(bscc).size() >= sub_automaton->num_states());

      // update state2ps
      for (unsigned scc_state : sub_scc.states_of(bscc))
      {
          to_parity_state &ps = num2ps.at(scc_state);

          if (!state2ps[ps.original_state].has_value())
              state2ps[ps.original_state] = ps;
      }
      return sub_scc.states_of(bscc).size();
    }
    return nb_created_states;
}

// This function is the same as apply_car_iar but As we cannot apply any
// optimization as the choice of the order when moving elements, we create
// an other function.
unsigned
apply_tar(twa_graph_ptr sub_automaton)
{
    auto& edge_vector = sub_automaton->edge_vector();
    unsigned nb_created_states = 0;
    auto init_states = sub_automaton->
                    get_named_prop<std::vector<unsigned>>("original-states");
    std::deque<to_parity_state> todo;
    auto get_state =
        [&](const to_parity_state &s){
            auto it = ps2num.find(s);

            if (it == ps2num.end())
            {
                ++nb_created_states;
                unsigned nb = add_res_state(TAR, s.perm,
                                            s.scc_state, s.original_state);
                if (!options.bscc && !state2ps[s.original_state].has_value())
                  state2ps[s.original_state] = s;
                todo.push_back(s);
                return nb;
            }
            return it->second;
        };

    std::vector<unsigned> p0(edge_vector.size() - 1);
    std::iota(p0.begin(), p0.end(), 1);

    to_parity_state s0{ (*init_states)[0], 0, p0 };
    get_state(s0);

    // the main loop
    while (!todo.empty())
    {
        to_parity_state current = todo.front();
        todo.pop_front();

        unsigned src_num = get_state(current);
        for (const auto &e : sub_automaton->out(current.scc_state))
        {
            auto edge_number = sub_automaton->edge_number(e);
            perm_t new_perm = current.perm;

            auto pivot = std::find(new_perm.begin(), new_perm.end(),
                          edge_number);
            assert(pivot != new_perm.end());
            unsigned index = std::distance(new_perm.begin(), pivot);


            std::rotate(new_perm.begin(), pivot, pivot + 1);

            auto dst = to_parity_state{(*init_states)[e.dst], e.dst, new_perm};
            auto dst_num = get_state(dst);


            acc_cond::mark_t acc = { };
            for (unsigned i = 0; i <= index; ++i)
              acc |= edge_vector[new_perm[i]].acc;

            auto is_acc = sub_automaton->acc().accepting(acc);

            unsigned acc_col = 2 * (index + 1) + is_odd + !is_acc;
            add_res_edge(src_num, dst_num, e.cond, { acc_col });
        }
    }

    if (options.bscc)
    {
      scc_info sub_scc(res_, get_state(s0));

      // SCCs are numbered in reverse topological order, so the bottom SCC has
      // index 0.
      const unsigned bscc = 0;
      assert(sub_scc.scc_count() != 0);
      assert(sub_scc.succ(0).empty());
      assert(
          [&](){
                      for (unsigned s = 1; s != sub_scc.scc_count(); ++s)
                          if (sub_scc.succ(s).empty())
                              return false;

                      return true;
                  } ());

      assert(sub_scc.states_of(bscc).size() >= sub_automaton->num_states());

      // update state2ps
      for (unsigned scc_state : sub_scc.states_of(bscc))
      {
          to_parity_state &car = num2ps.at(scc_state);

          if (!state2ps[car.original_state].has_value())
            state2ps[car.original_state] = car;
      }
      return sub_scc.states_of(bscc).size();
    }
    return nb_created_states;
}

// Given a vector of pairs, remove duplicates. Only the first occurence is kept
// and the order is not modified.
static void
remove_duplicates(std::vector<acc_cond::rs_pair>& elements)
{
  std::vector<acc_cond::rs_pair> result;
  for (auto& value : elements)
  {
    if (std::find(result.begin(), result.end(), value) == result.end())
      result.push_back(value);
  }
  elements = result;
}

algorithm
choose_lar(acc_cond scc_condition, std::vector<acc_cond::rs_pair>& pairs,
            unsigned num_edges)
{
    std::vector<acc_cond::rs_pair> pairs1;
    std::vector<acc_cond::rs_pair> pairs2;
    bool is_r_like = scc_condition.is_rabin_like(pairs1);
    bool is_s_like = scc_condition.is_streett_like(pairs2);
    // Avoid to have 2 pairs with the same elements.
    remove_duplicates(pairs1);
    remove_duplicates(pairs2);
    unsigned num_cols = scc_condition.get_acceptance().used_sets().count();

    // We take the minimum between the number of pairs (Streett/Rabin),
    // colors, transitions (in this order if equality)

    std::vector<unsigned long> number_elements =
    {
      (options.iar && is_s_like) ? pairs2.size() : -1UL,
      (options.iar && is_r_like) ? pairs1.size() : -1UL,
      num_cols,
      options.tar ? num_edges : -1UL
    };

    std::vector<algorithm> algos = { IAR_Streett, IAR_Rabin, CAR, TAR };

    int minElementIndex = std::min_element(
                              number_elements.begin(),
                              number_elements.end()) - number_elements.begin();
    algorithm result = algos[minElementIndex];

    if (result == IAR_Rabin)
      pairs = pairs1;
    else if (result == IAR_Streett)
      pairs = pairs2;

    return result;
}


void
apply_lar(twa_graph_ptr sub_automaton)
{
    std::vector<acc_cond::rs_pair> pairs;
    algorithm lar_algo = choose_lar(sub_automaton->acc(), pairs,
                                    sub_automaton->num_edges());
    if (lar_algo != TAR)
    {
      // Here we can only use IAR/CAR. A mark propagation can help CAR/IAR.
      // The function could have been called before simplify_acceptance but
      // simplify_acceptance can remove colors on edges.
      if (options.propagate_col)
        propagate_marks_here(sub_automaton);
      apply_car_iar(sub_automaton, pairs, lar_algo);
    }
    else
      // This version of LAR can't be optimized with the optimizations based
      // on the order of the elements so we create a new function to be more
      // readable.
      apply_tar(sub_automaton);
}

// Decide if we keep the result of a partial degeneralization.
bool keep_deg(twa_graph_ptr original, twa_graph_ptr deg)
{
    unsigned nb_col_original = original->get_acceptance().used_sets().count();
    std::vector<acc_cond::rs_pair> pairs1;

    // We keep the result if we have less colors or if we create a Rabin/
    // Streett condition with less pairs than colors.
    return
        !options.reduce_col_deg
    || (deg->get_acceptance().used_sets().count() < nb_col_original)
    || (deg->acc().is_rabin_like(pairs1) && pairs1.size() < nb_col_original)
    || (deg->acc().is_streett_like(pairs1) && pairs1.size() < nb_col_original);
}

void
build_scc(twa_graph_ptr& sub_automaton)
{
    if (sub_automaton->num_edges() == 0)
    {
      auto init_states = sub_automaton->
          get_named_prop<std::vector<unsigned>>("original-states");
      add_res_state(None, perm_t {}, 0, (*init_states)[0]);
    }
    current_scc_max_color = 0;
    while (true)
    {
        // A propagation + simplification
        if (options.acc_clean)
          simplify_acceptance_here(sub_automaton);
        if (options.propagate_col)
            propagate_marks_here(sub_automaton);
        if (options.acc_clean)
            simplify_acceptance_here(sub_automaton);
        // We check if the acceptance condition can be renumbered to get parity.
        if (options.parity_equiv)
        {
          auto scc_condition = sub_automaton->acc();
          std::vector<int> permut_tmp;
          // Is the condition equivalent to parity ?
          bool par = false;
          algorithm copy_kind = None;
          if (scc_condition.is_parity_max_equiv(permut_tmp, true))
          {
            par = true;
            copy_kind = Copy_even;
          }
          else
          {
            permut_tmp.clear();
            if (scc_condition.is_parity_max_equiv(permut_tmp, false))
            {
              par = true;
              copy_kind = Copy_odd;
            }
          }
          if (par)
          {
            apply_copy(sub_automaton, permut_tmp, copy_kind == Copy_odd);
            return;
          }
        }

        // We can check if the condition has a parity prefix. In this case,
        // this function will paritize the SCC created by removing the colors
        // in the prefix. That is why we don't do anything after this call.
        if (options.parity_prefix && try_apply_parity_prefix(sub_automaton))
          return;

        if (options.parity_prefix_general &&
            try_apply_parity_prefix_general(sub_automaton))
          return;

        auto sub_aut_acc = sub_automaton->get_acceptance();
        bool is_true = sub_aut_acc.is_t();
        if (is_true || sub_aut_acc.is_f() ||
            (options.generic_emptiness &&
             generic_emptiness_check(sub_automaton)))
        {
          apply_false_true_clean(sub_automaton, is_true);
          return;
        }
        if (!options.buchi_type_to_buchi && options.rabin_to_buchi &&
              try_apply_rabin_to_buchi(sub_automaton))
          return;
        if (options.buchi_type_to_buchi &&
              try_apply_to_buchi(sub_automaton))
          return;
        if (options.parity_type_to_parity &&
              try_apply_to_parity_type(sub_automaton))
          return;
        if (options.use_generalized_rabin)
        {
          auto orig = sub_automaton->
                    get_named_prop<std::vector<unsigned>>("original-states");
          auto orig_vector = new std::vector<unsigned>(*orig);
          sub_automaton = to_generalized_rabin(sub_automaton);
          sub_automaton->set_named_prop("original-states", orig_vector);
        }

        if (options.partial_degen)
        {
            bool is_partially_degen =
                is_partially_degeneralizable(sub_automaton)
                != acc_cond::mark_t {};
            if (is_partially_degen)
            {
                twa_graph_ptr deg = partial_degeneralize(sub_automaton);
                simplify_acceptance_here(deg);
                if (keep_deg(sub_automaton, deg))
                {
                    sub_automaton = deg;
                    continue;
                }
            }
        }
        break;
    }
    apply_lar(sub_automaton);
}

twa_graph_ptr
run()
{
    res_ = make_twa_graph(aut_->get_dict());
    res_->copy_ap_of(aut_);
    const unsigned scc_nb = scc_.scc_count();
    std::vector<bool> keep(aut_->edge_vector().size(), true);
    auto sub_auts = split_aut(scc_, keep);
    for (unsigned scc = 0; scc < scc_nb; ++scc)
    {
        if (!scc_.is_useful_scc(scc))
          continue;
        auto sub_automaton = sub_auts[scc];
        build_scc(sub_automaton);
    }

    const unsigned res_num_states = res_->num_states();
    for (unsigned state = 0; state < res_num_states; ++state)
    {
        unsigned original_state = num2ps.at(state).original_state;
        auto state_scc = scc_.scc_of(original_state);
        for (auto& edge : aut_->out(original_state))
            if (scc_.scc_of(edge.dst) != state_scc)
            {
                auto ps = state2ps[edge.dst];
                if (ps.has_value())
                {
                    unsigned res_dst = ps2num.at(ps.value());
                    add_res_edge(state, res_dst, edge.cond, {});
                }
            }
    }

    unsigned initial_state = aut_->get_init_state_number();
    auto initial_ps_opt = state2ps[initial_state];
    to_parity_state initial_car;
    // If we take an automaton with one state and without transition,
    // the SCC was useless so state2ps doesn't have initial_state
    if (!initial_ps_opt.has_value())
    {
      assert(res_->num_states() == 0);
      auto new_num = add_res_state(None, perm_t(), initial_state, 0);
      initial_car = num2ps[new_num];
    }
    else
        initial_car = initial_ps_opt.value();
    auto initial_state_res = ps2num.find(initial_car);
    if (initial_state_res != ps2num.end())
        res_->set_init_state(initial_state_res->second);
    else
        add_res_state(None, perm_t(), 0, 0);

    res_->set_acceptance(acc_cond(
            acc_cond::acc_code::parity(true, is_odd, max_used_color + 1)));

    if (options.pretty_print)
        res_->set_named_prop("state-names", names);
    res_->set_named_prop("original-states", orig_states);
    res_->purge_unreachable_states();
    return res_;
}

private:
const const_twa_graph_ptr &aut_;
const scc_info scc_;
twa_graph_ptr res_;
// Says if we constructing an odd or even max
bool is_odd;
unsigned max_used_color = 0;

std::vector<to_parity_state> num2ps;
std::vector<std::optional<to_parity_state>> state2ps;
std::map<to_parity_state, unsigned> ps2num;
// Maps for each state of the input a set of states of the result.
// The opposite of num2state
std::vector<std::vector<unsigned>> state2nums;
// The maximum color used for the current SCC. Used by parity prefix
// to avoid to use big colors
unsigned current_scc_max_color = 0;

to_parity_options options;

std::vector<std::string>* names;
std::vector<unsigned>* orig_states;
};
}

twa_graph_ptr
to_parity(const const_twa_graph_ptr& aut, const to_parity_options options)
  {
    if (!aut->is_existential())
      throw std::runtime_error("LAR does not handle alternation");

    to_parity_generator gen(aut, options);
    return gen.run();
  }

  // Old version of CAR.
  namespace
  {
    struct lar_state
    {
      unsigned state;
      std::vector<unsigned> perm;

      bool operator<(const lar_state& s) const
      {
        return state == s.state ? perm < s.perm : state < s.state;
      }

      std::string to_string() const
      {
        std::stringstream s;
        s << state << " [";
        unsigned ps = perm.size();
        for (unsigned i = 0; i != ps; ++i)
          {
            if (i > 0)
              s << ',';
            s << perm[i];
          }
        s << ']';
        return s.str();
      }
    };

    class lar_generator
    {
      const const_twa_graph_ptr& aut_;
      twa_graph_ptr res_;
      const bool pretty_print;

      std::map<lar_state, unsigned> lar2num;
    public:
      explicit lar_generator(const const_twa_graph_ptr& a, bool pretty_print)
      : aut_(a)
      , res_(nullptr)
      , pretty_print(pretty_print)
      {}

      twa_graph_ptr run()
      {
        res_ = make_twa_graph(aut_->get_dict());
        res_->copy_ap_of(aut_);

        std::deque<lar_state> todo;
        auto get_state = [this, &todo](const lar_state& s)
          {
            auto it = lar2num.emplace(s, -1U);
            if (it.second) // insertion took place
              {
                unsigned nb = res_->new_state();
                it.first->second = nb;
                todo.push_back(s);
              }
            return it.first->second;
          };

        std::vector<unsigned> initial_perm(aut_->num_sets());
        std::iota(initial_perm.begin(), initial_perm.end(), 0);
        {
          lar_state s0{aut_->get_init_state_number(), initial_perm};
          res_->set_init_state(get_state(s0));
        }

        scc_info si(aut_, scc_info_options::NONE);
        // main loop
        while (!todo.empty())
          {
            lar_state current = todo.front();
            todo.pop_front();

            // TODO: todo could store this number to avoid one lookup
            unsigned src_num = get_state(current);

            unsigned source_scc = si.scc_of(current.state);
            for (const auto& e : aut_->out(current.state))
              {
                // find the new permutation
                std::vector<unsigned> new_perm = current.perm;
                unsigned h = 0;
                for (unsigned k : e.acc.sets())
                  {
                    auto it = std::find(new_perm.begin(), new_perm.end(), k);
                    h = std::max(h, unsigned(new_perm.end() - it));
                    std::rotate(it, it+1, new_perm.end());
                  }

                if (source_scc != si.scc_of(e.dst))
                  {
                    new_perm = initial_perm;
                    h = 0;
                  }

                lar_state dst{e.dst, new_perm};
                unsigned dst_num = get_state(dst);

                // Do the h last elements satisfy the acceptance condition?
                // If they do, emit 2h, if they don't emit 2h+1.
                acc_cond::mark_t m(new_perm.end() - h, new_perm.end());
                bool rej = !aut_->acc().accepting(m);
                res_->new_edge(src_num, dst_num, e.cond, {2*h + rej});
              }
          }

        // parity max even
        unsigned sets = 2*aut_->num_sets() + 2;
        res_->set_acceptance(sets, acc_cond::acc_code::parity_max_even(sets));

        if (pretty_print)
          {
            auto names = new std::vector<std::string>(res_->num_states());
            for (const auto& p : lar2num)
              (*names)[p.second] = p.first.to_string();
            res_->set_named_prop("state-names", names);
          }

        return res_;
      }
    };
  }

  twa_graph_ptr
  to_parity_old(const const_twa_graph_ptr& aut, bool pretty_print)
  {
    if (!aut->is_existential())
      throw std::runtime_error("LAR does not handle alternation");
    // if aut is already parity return it as is
    if (aut->acc().is_parity())
      return std::const_pointer_cast<twa_graph>(aut);

    lar_generator gen(aut, pretty_print);
    return gen.run();
  }

  enum cond_kind
  {
      BUCHI,
      CO_BUCHI,
      // A parity condition that starts with a Inf
      INF_PARITY,
      // A parity condition that starts with a Fin
      FIN_PARITY
  };

  static twa_graph_ptr
  cond_type_main(const const_twa_graph_ptr &aut, const cond_kind kind,
                 bool need_equivalent, std::vector<int> &status)
  {
      auto res = make_twa_graph(aut, twa::prop_set::all());
      // 0 : not marked, 1 : marked, 2 : impossible to mark,
      // 3 : link between 2 SCCs.
      status = std::vector<int>(res->edge_vector().size(), 0);
      // Used by accepting_transitions_scc.
      std::vector<bool> keep(aut->edge_vector().size(), true);
      auto &res_vector = res->edge_vector();

      // We need to say that a transition between 2 SCC doesn't have to get a
      // color.
      scc_info si(aut, aut->get_init_state_number());
      status[0] = 3;
      for (auto &e : aut->edges())
      {
          auto edge_number = aut->edge_number(e);
          if (si.scc_of(e.src) != si.scc_of(e.dst))
              status[edge_number] = 3;
          res_vector[edge_number].acc = {};
      }

      // If we need to convert to (co-)Büchi, we have to search one accepting
      // set. With parity there is no limit.
      bool want_parity = kind == cond_kind::FIN_PARITY ||
                         kind == cond_kind::INF_PARITY;
      unsigned max_iter = want_parity ? -1U : 1;

      unsigned color = want_parity ? SPOT_MAX_ACCSETS - 3 : 0;
      // Do we want always accepting transitions?
      bool search_inf = kind == cond_kind::BUCHI ||
                        kind == cond_kind::INF_PARITY;

      using filter_data_t = std::pair<const_twa_graph_ptr, std::vector<int> &>;

      scc_info::edge_filter filter =
          [](const twa_graph::edge_storage_t &t, unsigned, void *data)
          -> scc_info::edge_filter_choice {
          auto &d = *static_cast<filter_data_t *>(data);
          // We only keep transitions that can be marked
          if (d.second[d.first->edge_number(t)] == 0)
              return scc_info::edge_filter_choice::keep;
          else
              return scc_info::edge_filter_choice::cut;
      };

      for (unsigned iter = 0; iter < max_iter && color != -1U; ++iter)
      {
          std::vector<bool> not_decidable_transitions(
              aut->edge_vector().size(), false);
          auto cond = acc_cond(search_inf ? aut->get_acceptance().complement() :
                                            aut->get_acceptance());
          auto filter_data = filter_data_t{aut, status};
          scc_info si(aut, aut->get_init_state_number(), filter, &filter_data);
          bool worked = false;
          for (unsigned scc = 0; scc < si.scc_count(); ++scc)
          {
              accepting_transitions_scc(si, scc, cond, {},
                                        not_decidable_transitions, keep);

              for (auto &e : si.inner_edges_of(scc))
              {
                  auto edge_number = aut->edge_number(e);
                  if (!not_decidable_transitions[edge_number])
                  {
                      res_vector[edge_number].acc = {color};
                      status[edge_number] = 1;
                      keep[edge_number] = false;
                      worked = true;
                  }
              }
          }
          --color;
          search_inf = !search_inf;
          // If we were not able to add color, we have to add status 2 to
          // remaining transitions.
          if (!worked)
          {
              for (unsigned i = 0; i < status.size(); ++i)
                  if (status[i] == 0)
                      status[i] = 2;
              break;
          }
      }

      acc_cond::acc_code new_code;
      switch (kind)
      {
      case cond_kind::BUCHI:
          new_code = acc_cond::acc_code::buchi();
          break;
      case cond_kind::CO_BUCHI:
          new_code = acc_cond::acc_code::cobuchi();
          break;
      case cond_kind::INF_PARITY:
      case cond_kind::FIN_PARITY:
          new_code = acc_cond::acc_code::parity_max(
                        kind == cond_kind::INF_PARITY, SPOT_MAX_ACCSETS);
          break;
      }

      // We check parity
      if (need_equivalent)
      {
          // For parity, it's equivalent if every transition has a color
          // (status 1) or links 2 SCCs.
          if (kind == cond_kind::INF_PARITY || kind == cond_kind::FIN_PARITY)
          {
              if (std::find(status.begin(), status.end(), 2) != status.end())
                  return nullptr;
          }
          else
          {
              // For Büchi, we remove the transitions that have {0} in res from
              // aut and if there is an accepting cycle, res is not equivalent
              // to aut.
              // For co-Büchi, it's the same but we don't want to find a
              // rejecting cycle.
              auto old_cond = aut->get_acceptance();
              auto cond = acc_cond(kind == cond_kind::BUCHI ?
                                                old_cond :
                                                old_cond.complement());

              using filter_data_t = std::pair<const_twa_graph_ptr,
                                              std::vector<bool> &>;

              scc_info::edge_filter filter =
                  [](const twa_graph::edge_storage_t &t, unsigned, void *data)
                  -> scc_info::edge_filter_choice {
                  auto &d = *static_cast<filter_data_t *>(data);
                  if (d.second[d.first->edge_number(t)])
                      return scc_info::edge_filter_choice::keep;
                  else
                      return scc_info::edge_filter_choice::cut;
              };

              filter_data_t filter_data = {aut, keep};
              scc_info si(aut, aut->get_init_state_number(), filter,
                          &filter_data);

              si.determine_unknown_acceptance();
              for (unsigned scc = 0; scc < si.scc_count(); ++scc)
                  if ((kind == cond_kind::BUCHI && si.is_accepting_scc(scc)) ||
                      (kind == cond_kind::CO_BUCHI && si.is_rejecting_scc(scc)))
                      return nullptr;
          }
      }
      res->set_acceptance(acc_cond(new_code));
      if (want_parity)
          cleanup_acceptance_here(res, true);
      return res;
  }

  twa_graph_ptr
  parity_type_to_parity(const const_twa_graph_ptr &aut)
  {
      bool odd_cond, max_cond;
      bool parit = aut->acc().is_parity(max_cond, odd_cond);
      // If it is parity, we just copy
      if (parit && max_cond)
          return make_twa_graph(aut, twa::prop_set::all());
      std::vector<int> status;
      // If the automaton is parity-type with a condition that starts with a Inf
      auto res = cond_type_main(aut, cond_kind::INF_PARITY, true, status);
      if (res != nullptr)
          return res;
      // If the previous call to cond_type_main was not able to color any
      // transition, it is perhaps possible if we begin with rejecting
      // transitions.
      if (std::find(status.begin(), status.end(), 1) == status.end())
          return cond_type_main(aut, cond_kind::FIN_PARITY, true, status);
      return nullptr;
  }

  twa_graph_ptr
  buchi_type_to_buchi(const const_twa_graph_ptr &aut)
  {
      std::vector<int> status;
      return cond_type_main(aut, cond_kind::BUCHI, true, status);
  }

  twa_graph_ptr
  co_buchi_type_to_co_buchi(const const_twa_graph_ptr &aut)
  {
      std::vector<int> status;
      return cond_type_main(aut, cond_kind::CO_BUCHI, true, status);
  }

  twa_graph_ptr
  partial_parity_type(const const_twa_graph_ptr &aut, std::vector<int> &status)
  {
      auto r1 = cond_type_main(aut, cond_kind::INF_PARITY, false, status);
      // The first element of status is not an edge
      if (std::find(status.begin() + 1, status.end(), 1) == status.end())
      {
          // If the first call did not assign any color, we restart by searching
          // rejecting transitions
          return cond_type_main(aut, cond_kind::FIN_PARITY, false, status);
      }
      return r1;
  }
}
