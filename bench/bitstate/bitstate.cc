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

#include <ostream>
#include <string>
#include <thread>
#include <vector>

#include "bitstate.hh"

template<typename kripke_ptr, typename State,
         typename Iterator, typename Hash, typename Equal>
void run(kripke_ptr sys, std::ofstream& csv, std::vector<size_t> mem_sizes)
{
  std::string header("memory (bits), nb states reached");
  csv << header << '\n';

  // TODO: add timer and memory usage (misc/memusage and misc/timer)
  for (auto mem_size : mem_sizes)
  {
    using algo_name = bitstate_hashing_stats<State, Iterator, Hash, Equal>;
    auto bh = new algo_name(*sys, mem_size);

    bh->run();
    csv << mem_size << ',' << bh->get_nb_reached_states() << '\n';

    delete bh;
  }
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

  run<spot::ltsmin_kripkecube_ptr,
      spot::cspins_state,
      spot::cspins_iterator,
      spot::cspins_state_hash,
      spot::cspins_state_equal>
    (modelcube, log_file, mem_sizes);

  return 0;
}
