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

#include "config.h"
#include "bin/common_conv.hh"
#include "bin/common_setup.hh"
#include "bin/common_output.hh"

#include <spot/kripke/kripkegraph.hh>
#include <spot/ltsmin/ltsmin.hh>
#include <spot/ltsmin/spins_kripke.hh>
#include <spot/misc/memusage.hh>
#include <spot/misc/timer.hh>

#include <ostream>
#include <string>
#include <thread>
#include <vector>

#include "bitstate.hh"

template<typename kripke_ptr, typename State,
         typename Iterator, typename Hash, typename Equal>
void run(kripke_ptr sys, std::ofstream& csv, std::vector<size_t> mem_sizes)
{
  spot::timer_map timer;
  int mem_used;
  using algo_name = bitstate_hashing_stats<State, Iterator, Hash, Equal>;

  csv <<
    "memory (bits),"
    "nb states reached,"
    "total memory used (nb pages),"
    "user time (seconds),"
    "sys time (seconds),"
    "wall time (seconds)\n";

  for (size_t mem_size : mem_sizes)
  {
    auto bh = new algo_name(*sys, 0, mem_size);

    const std::string round = "Using " + std::to_string(mem_size) + " bits";
    timer.start(round);
    mem_used = spot::memusage();

    bh->run();

    mem_used = spot::memusage() - mem_used;
    timer.stop(round);

    csv << mem_size << ','
        << bh->get_nb_reached_states() << ','
        << mem_used << ','
        << (float) timer.timer(round).utime() / CLOCKS_PER_SEC << ','
        << (float) timer.timer(round).stime() / CLOCKS_PER_SEC << ','
        << (float) timer.timer(round).walltime() / CLOCKS_PER_SEC
        << '\n';

    delete bh;
  }

  timer.print(std::cout);
}

int main(int argc, char** argv)
{
  if (argc != 4)
  {
    std::cout << "Usage: ./bitstate [MODEL] [LOG_FILE] [MEM_SIZES]";
    return 1;
  }

  const unsigned compression_level = 0;
  const unsigned nb_threads = 1;

  std::string model_path = argv[1];
  std::ofstream log_file(argv[2]);
  // Parse comma separated values
  std::vector<size_t> mem_sizes;
  std::istringstream iss(argv[3]);
  std::string mem_size;
  while (std::getline(iss, mem_size, ','))
    mem_sizes.push_back(std::atoi(mem_size.c_str()));

  // Load model
  spot::ltsmin_kripkecube_ptr modelcube = nullptr;
  try
  {
    modelcube = spot::ltsmin_model::load(model_path)
      .kripkecube({}, spot::formula::ff(), compression_level, nb_threads);
  }
  catch (const std::runtime_error& e)
  {
    std::cerr << e.what() << '\n';
  }

  if (!modelcube)
    return 2;

  run<spot::ltsmin_kripkecube_ptr,
      spot::cspins_state,
      spot::cspins_iterator,
      spot::cspins_state_hash,
      spot::cspins_state_equal>
    (modelcube, log_file, mem_sizes);

  return 0;
}
