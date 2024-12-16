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

#pragma once

#include <spot/twa/twagraph.hh>
#include <spot/misc/bddlt.hh>

namespace spot
{
  struct SPOT_API mtdtwa
  {
  public:
    mtdtwa(const bdd_dict_ptr& dict) noexcept
      : dict_(dict)
     {
     }

    ~mtdtwa()
    {
      dict_->unregister_all_my_variables(this);
    }

    std::vector<bdd> states;
    acc_cond acc;
    bdd_dict_ptr dict_;
    std::vector<std::pair<acc_cond::mark_t, unsigned>> terminal_data;

    unsigned num_roots() const
    {
      return states.size();
    }

    // unsigned num_states() const
    // {
    //   bool has_true = false;
    //   // FIXME: I'd like a BuDDy function that checks if a BDD node
    //   // can be reached from a given set of BDD nodes.  Returning just
    //   // a boolean will be more efficient than creating the array of
    //   // leaves.
    //   for (bdd b: leaves_of(states))
    //     if (b == bddtrue)
    //       {
    //         has_true = true;
    //         break;
    //       }
    //   return states.size() + has_true;
    // }

    // Print the MTBDD.  If index >= 0, print only one state.
    std::ostream& print_dot(std::ostream& os) const;

    // convert to twa
    // twa_graph_ptr as_twa(bool state_based = false, bool labels = true) const;
  };


  typedef std::shared_ptr<mtdtwa> mtdtwa_ptr;
  typedef std::shared_ptr<const mtdtwa> const_mtdtwa_ptr;

  SPOT_API mtdtwa_ptr dtwa_to_mtdtwa(const twa_graph_ptr& aut);
}
