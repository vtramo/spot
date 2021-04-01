// -*- coding: utf-8 -*-
// Copyright (C) 2020 Laboratoire de Recherche et Developpement de
// l'Epita
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

#include <spot/kripke/kripke.hh>
#include <spot/mc/mc_instanciator.hh>
#include <spot/mc/deadlock.hh>
#include <spot/mc/deadlock_bitstate2.hh>
//#include <spot/mc/deadlock_bitstate.hh>
#include <spot/misc/memusage.hh>
#include <spot/misc/timer.hh>

#include <string>
#include <vector>

using namespace spot;

template<typename kripke_ptr, typename State,
         typename Iterator, typename Hash, typename Equal>
ec_stats run_deadlock_ref(kripke_ptr sys)
{
  return instanciate<swarmed_deadlock2<State, Iterator, Hash, Equal, std::true_type>,
                     kripke_ptr, State, Iterator, Hash, Equal> (sys, nullptr, false, 1000000);
}

template<typename kripke_ptr, typename State,
         typename Iterator, typename Hash, typename Equal>
ec_stats run_deadlock_bitstate(kripke_ptr sys)
{
  return instanciate<swarmed_deadlock_bitstate<State, Iterator, Hash, Equal, std::true_type>,
        kripke_ptr, State, Iterator, Hash, Equal> (sys);
}

template<typename kripke_ptr, typename State,
         typename Iterator, typename Hash, typename Equal>
void bench_deadlock(kripke_ptr sys, std::vector<size_t> mem_sizes)
{
  spot::timer_map timer;
  int mem_used;

  int mem_used_ref = spot::memusage();
  auto ref = run_deadlock_ref<spot::ltsmin_kripkecube_ptr,
       spot::cspins_state,
       spot::cspins_iterator,
       spot::cspins_state_hash,
       spot::cspins_state_equal>
       (sys);
  mem_used_ref = spot::memusage() - mem_used_ref;
  std::cout << "Reference:\n" << ref << "\n";
  std::cout << "mem_used (nb pages): " << mem_used_ref << "\n";

  for (size_t mem_size : mem_sizes)
  {
    const std::string round = "Using " + std::to_string(mem_size) + " bits";

    timer.start(round);
    mem_used = spot::memusage();
    // TODO: pass mem_size parameter
    auto res = run_deadlock_bitstate<spot::ltsmin_kripkecube_ptr,
       spot::cspins_state,
       spot::cspins_iterator,
       spot::cspins_state_hash,
       spot::cspins_state_equal>
       (sys);
    mem_used = spot::memusage() - mem_used;
    timer.stop(round);

    std::cout << "\n" << round << "\n";
    std::cout << "Bitstate version:\n" << res << "\n";
    std::cout << "mem_used (nb pages): " << mem_used_ref << "\n";
  }

  std::cout << "\n";
  timer.print(std::cout);
}
