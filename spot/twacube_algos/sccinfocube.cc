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

#include "config.h"
#include <spot/twacube_algos/sccinfocube.hh>
#include <stack>
#include <algorithm>
#include <queue>
#include <spot/twa/bddprint.hh>
#include <spot/twaalgos/bfssteps.hh>
#include <spot/twaalgos/mask.hh>
#include <spot/twaalgos/genem.hh>
#include <spot/misc/escape.hh>

namespace spot
{
  void scc_infocube::report_need_track_states()
  {
    throw std::runtime_error
      ("scc_infocube was not run with option TRACK_STATES");
  }

  void scc_infocube::report_need_track_succs()
  {
    throw std::runtime_error
      ("scc_infocube was not run with option TRACK_SUCCS");
  }

  void scc_infocube::report_incompatible_stop_on_acc()
  {
    throw std::runtime_error
      ("scc_infocube was run with option STOP_ON_ACC");
  }

  scc_infocube::scc_infocube(const_twa_graph_ptr aut,
                     std::unordered_map<int, int> binder,
                     unsigned initial_state,
                     edge_filter filter,
                     void* filter_data,
                     scc_info_options options)
  {
    sccinfo_ = std::make_shared<scc_info>(aut, initial_state, filter,
                                          filter_data, options);
    twa_to_cube_ = binder;
    for (auto it = binder.begin(); it != binder.end(); ++it)
      cube_to_twa_[it->second] = it->first;
  }

  std::set<acc_cond::mark_t> scc_infocube::marks_of(unsigned scc) const
  {
    return sccinfo_->marks_of(scc);
  }

  std::vector<std::set<acc_cond::mark_t>> scc_infocube::marks() const
  {
    return sccinfo_->marks();
  }

  std::vector<bool> scc_infocube::weak_sccs() const
  {
    return sccinfo_->weak_sccs();
  }

  bdd scc_infocube::scc_ap_support(unsigned scc) const
  {
    return sccinfo_->scc_ap_support(scc);
  }

  bool scc_infocube::check_scc_emptiness(unsigned n) const
  {
    return sccinfo_->check_scc_emptiness(n);
  }

  void scc_infocube::determine_unknown_acceptance()
  {
    return sccinfo_->determine_unknown_acceptance();
  }

  void scc_infocube::get_accepting_run(unsigned scc, twa_run_ptr r) const
  {
    return sccinfo_->get_accepting_run(scc, r);
  }

  std::vector<twa_graph_ptr>
  scc_infocube::split_on_sets(unsigned scc, acc_cond::mark_t sets,
                              bool preserve_names) const
  {
    return sccinfo_->split_on_sets(scc, sets, preserve_names);
  }

  std::vector<unsigned>
  scc_infocube::states_on_acc_cycle_of(unsigned scc) const
  {
    return sccinfo_->states_on_acc_cycle_of(scc);
  }

  bool are_equivalent(std::shared_ptr<scc_infocube> sccinfocube,
                      std::shared_ptr<scc_info> sccinfo)
  {
    return sccinfocube->get_aut() == sccinfo->get_aut();
  }
}
