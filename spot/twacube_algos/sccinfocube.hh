// -*- coding: utf-8 -*-
// Copyright (C) 2020 Laboratoire de Recherche et Développement
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

#pragma once

#include <vector>
#include <spot/twacube/twacube.hh>
#include <spot/twaalgos/emptiness.hh>
#include <spot/twaalgos/sccinfo.hh>

namespace spot
{
  class SPOT_API scc_infocube
  {
  protected:
    typedef std::shared_ptr<scc_info> scc_info_ptr;

    scc_info_ptr sccinfo_;
    std::unordered_map<int, int> twa_to_cube_;
    std::unordered_map<int, int> cube_to_twa_;

#ifndef SWIG
  private:
    [[noreturn]] static void report_need_track_states();
    [[noreturn]] static void report_need_track_succs();
    [[noreturn]] static void report_incompatible_stop_on_acc();
#endif

  public:
    /// @{
    /// \brief Create the scc_infocube map for \a aut
    scc_infocube(const_twa_graph_ptr aut,
             std::unordered_map<int, int> binder,
             // Use ~0U instead of -1U to work around a bug in Swig.
             // See https://github.com/swig/swig/issues/993
             unsigned initial_state = ~0U,
             edge_filter filter = nullptr,
             void* filter_data = nullptr,
             scc_info_options options = scc_info_options::ALL);

    scc_infocube(const_twa_graph_ptr aut, scc_info_options options,
                 std::unordered_map<int, int> binder)
      : scc_infocube(aut, binder, ~0U, nullptr, nullptr, options)
      {
      }
    /// @}

    const_twa_graph_ptr get_aut() const
    {
      return sccinfo_->get_aut();
    }

    scc_info_options get_options() const
    {
      return sccinfo_->get_options();
    }

    edge_filter get_filter() const
    {
      return sccinfo_->get_filter();
    }

    const void* get_filter_data() const
    {
      return sccinfo_->get_filter_data();
    }

    unsigned scc_count() const
    {
      return sccinfo_->scc_count();
    }

    /// \brief Return the number of one accepting SCC if any, -1 otherwise.
    ///
    /// If an accepting SCC has been found, return its number.
    /// Otherwise return -1.  Note that when the acceptance condition
    /// contains Fin, -1 does not implies that all SCCs are rejecting:
    /// it just means that no accepting SCC is known currently.  In
    /// that case, you might want to call
    /// determine_unknown_acceptance() first.
    int one_accepting_scc() const
    {
      return sccinfo_->one_accepting_scc();
    }

    bool reachable_state(unsigned st) const
    {
      return sccinfo_->reachable_state(twa_to_cube_.at(st));
    }

    unsigned scc_of(unsigned st) const
    {
      st = cube_to_twa_.at(st);
      return sccinfo_->scc_of(st);
    }

    std::vector<scc_info::scc_node>::const_iterator begin() const
    {
      return sccinfo_->begin();
    }

    std::vector<scc_info::scc_node>::const_iterator end() const
    {
      return sccinfo_->end();
    }

    std::vector<scc_info::scc_node>::const_iterator cbegin() const
    {
      return sccinfo_->cbegin();
    }

    std::vector<scc_info::scc_node>::const_iterator cend() const
    {
      return sccinfo_->cend();
    }

    std::vector<scc_info::scc_node>::const_reverse_iterator rbegin() const
    {
      return sccinfo_->rbegin();
    }

    std::vector<scc_info::scc_node>::const_reverse_iterator rend() const
    {
      return sccinfo_->rend();
    }

    std::vector<unsigned> states_of(unsigned scc) const
    {
      std::vector<unsigned> res;
      auto& states = sccinfo_->states_of(scc);
      for (unsigned i = 0; i < res.size(); ++i)
        res[i] = twa_to_cube_.at(states[i]);
      return res;
    }

    /// \brief A fake container to iterate over all edges leaving any
    /// state of an SCC.
    ///
    /// The difference with inner_edges_of() is that edges_of() include
    /// outgoing edges from all the states, even if they leave the SCC.
    internal::scc_edges<const twa_graph::graph_t, internal::keep_all>
    edges_of(unsigned scc) const
    {
      return sccinfo_->edges_of(scc);
    }

    /// \brief A fake container to iterate over all edges between
    /// states of an SCC.
    ///
    /// The difference with edges_of() is that inner_edges_of()
    /// ignores edges leaving the SCC.  In the case of an
    /// alternating automaton, an edge is considered to be part of the
    /// SCC of one of its destination is in the SCC.
    internal::scc_edges<const twa_graph::graph_t, internal::keep_inner_scc>
    inner_edges_of(unsigned scc) const
    {
      return sccinfo_->inner_edges_of(scc);
    }

    unsigned one_state_of(unsigned scc) const
    {
      return sccinfo_->one_state_of(scc);
    }

    /// \brief Get number of the SCC containing the initial state.
    unsigned initial() const
    {
      return sccinfo_->initial();
    }

    const scc_info::scc_succs& succ(unsigned scc) const
    {
      return sccinfo_->succ(scc);
    }

    bool is_trivial(unsigned scc) const
    {
      return sccinfo_->is_trivial(scc);
    }

    SPOT_DEPRECATED("use acc_sets_of() instead")
    acc_cond::mark_t acc(unsigned scc) const
    {
      return acc_sets_of(scc);
    }

    bool is_accepting_scc(unsigned scc) const
    {
      return sccinfo_->is_accepting_scc(scc);
    }

    bool is_rejecting_scc(unsigned scc) const
    {
      return sccinfo_->is_rejecting_scc(scc);
    }

    /// \brief Study the SCCs that are currently reported neither as
    /// accepting nor as rejecting because of the presence of Fin sets
    ///
    /// This simply calls check_scc_emptiness() on undeterminate SCCs.
    void determine_unknown_acceptance();

    /// \brief Recompute whether an SCC is accepting or not.
    ///
    /// This is an internal function of
    /// determine_unknown_acceptance().
    bool check_scc_emptiness(unsigned n) const;

    /// \brief Retrieves an accepting run of the automaton whose cycle is in the
    /// SCC.
    ///
    /// \param scc an accepting scc
    /// \param r a run to fill
    ///
    /// This method needs the STOP_ON_ACC option.
    void get_accepting_run(unsigned scc, twa_run_ptr r) const;

    bool is_useful_scc(unsigned scc) const
    {
      return sccinfo_->is_useful_scc(scc);
    }

    bool is_useful_state(unsigned st) const
    {
      st = twa_to_cube_.at(st);
      return sccinfo_->reachable_state(st) && is_useful_scc(sccinfo_->scc_of(st));
    }

    /// \brief Returns, for each accepting SCC, the set of all marks appearing
    /// in it.
    std::vector<std::set<acc_cond::mark_t>> marks() const;
    std::set<acc_cond::mark_t> marks_of(unsigned scc) const;

    // Same as above, with old names.
    SPOT_DEPRECATED("use marks() instead")
    std::vector<std::set<acc_cond::mark_t>> used_acc() const
    {
      return sccinfo_->marks();
    }
    SPOT_DEPRECATED("use marks_of() instead")
    std::set<acc_cond::mark_t> used_acc_of(unsigned scc) const
    {
      return sccinfo_->marks_of(scc);
    }

    /// \brief Returns, for a given SCC, the set of all colors appearing in it.
    /// It is the set of colors that appear in some mark among those returned by
    /// marks_of().
    acc_cond::mark_t acc_sets_of(unsigned scc) const
    {
      return sccinfo_->acc_sets_of(scc);
    }

    /// Returns, for a given SCC, the set of colors that appear on all of its
    /// transitions.
    acc_cond::mark_t common_sets_of(unsigned scc) const
    {
      return sccinfo_->common_sets_of(scc);
    }

    std::vector<bool> weak_sccs() const;

    bdd scc_ap_support(unsigned scc) const;

    /// \brief Split an SCC into multiple automata separated by some
    /// acceptance sets.
    ///
    /// Pretend that the transitions of SCC \a scc that belong to any
    /// of the sets given in \a sets have been removed, and return a
    /// set of automata necessary to cover all remaining states.
    ///
    /// Set \a preserve_names to True if you want to keep the original
    /// name of each states for display.  (This is a bit slower.)
    std::vector<twa_graph_ptr> split_on_sets(unsigned scc,
                                             acc_cond::mark_t sets,
                                             bool preserve_names = false) const;
  protected:
    /// \brief: Recursive function used by states_on_acc_cycle_of().
    void
    states_on_acc_cycle_of_rec(unsigned scc,
                               acc_cond::mark_t all_fin,
                               acc_cond::mark_t all_inf,
                               unsigned nb_pairs,
                               std::vector<acc_cond::rs_pair>& pairs,
                               std::vector<unsigned>& res,
                               std::vector<unsigned>& old) const;
  public:
    /// \brief: Get all states visited by any accepting cycles of the 'scc'.
    ///
    /// Throws an exception if the automaton does not have a 'Streett-like'
    /// acceptance condition.
    std::vector<unsigned>
    states_on_acc_cycle_of(unsigned scc) const;
  };
}
