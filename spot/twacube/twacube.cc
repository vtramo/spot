// -*- coding: utf-8 -*-
// Copyright (C) 2015, 2016, 2018, 2020 Laboratoire de Recherche et
// Developpement de l'EPITA (LRDE).
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
#include "twacube.hh"
#include <iostream>

#include "spot/priv/merge_edges.hh"

namespace spot
{
  cstate::cstate(cstate&&) noexcept
  { }

  transition::transition(transition&& t) noexcept:
  cube_(std::move(t.cube_)), acc(std::move(t.acc))
  { }

  transition::transition(const cube& cube,
                         acc_cond::mark_t acc):
    cube_(cube),  acc(acc)
  { }

  twacube::twacube(const std::vector<std::string> aps):
    init_(0U), aps_(aps), cubeset_(aps.size())
  { }

  twacube::~twacube()
  {
    const spot::cubeset cs = get_cubeset();
    for (unsigned i = 1; i <= theg_.num_edges(); ++i)
      cs.release(theg_.edge_data(i).cube_);
  }

  transition& transition::operator=(transition&& t)
    {
      //FIXME this == t
      cube_ = t.cube_;
      t.cube_ = nullptr;
      acc = t.acc;
      return *this;
    }

  acc_cond& twacube::acc()
  {
    return acc_;
  }

  acc_cond twacube::acc() const
  {
    return acc_;
  }

  std::vector<std::string> twacube::ap() const
  {
    return aps_;
  }

  unsigned twacube::new_state()
  {
    return theg_.new_state();
  }

  void twacube::set_init_state(unsigned init)
  {
    init_ = init;
  }

  unsigned twacube::get_init_state_number() const
  {
    if (theg_.num_states() == 0)
      throw std::runtime_error("automaton has no state at all");

    return init_;
  }

  cstate* twacube::state_from_int(unsigned i)
  {
    return &theg_.state_data(i);
  }

  void
  twacube::create_transition(unsigned src, const cube& cube,
                             const acc_cond::mark_t& mark, unsigned dst)
  {
    theg_.new_edge(src, dst, cube, mark);
  }

  const cubeset&
  twacube::get_cubeset()  const
  {
    return cubeset_;
  }

  bool
  twacube::succ_contiguous() const
  {
    unsigned i = 1;
    while (i <= theg_.num_edges())
      {
        unsigned j = i;

        // Walk first bucket of successors
        while (j <= theg_.num_edges() &&
               theg_.edge_storage(i).src == theg_.edge_storage(j).src)
          ++j;

        // Remove the next bucket
        unsigned itmp = j;

        // Look if there are some transitions missing in this bucket.
        while (j <= theg_.num_edges())
          {
            if (theg_.edge_storage(i).src == theg_.edge_storage(j).src)
              return false;
            ++j;
          }
        i = itmp;
      }
    return true;
  }

  void twacube::merge_edges()
  {
    theg_.remove_dead_edges_();

    twa_merge_edges(*this);

    // FIXME add properties.
  }

  std::ostream&
  operator<<(std::ostream& os, const twacube& twa)
  {
    spot::cubeset cs = twa.get_cubeset();
    os << "init : " << twa.init_ << '\n';
     for (unsigned i = 1; i <= twa.theg_.num_edges(); ++i)
       os << twa.theg_.edge_storage(i).src << "->"
          << twa.theg_.edge_storage(i).dst <<  " : "
          << cs.dump(twa.theg_.edge_data(i).cube_, twa.aps_)
          << ' ' << twa.theg_.edge_data(i).acc
          << '\n';
    return os;
  }
}
