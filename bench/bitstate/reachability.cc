// -*- coding: utf-8 -*-
// Copyright (C) 2021 Laboratoire de Recherche et Developpement de
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

/* Final benchmarks done in 2021 to gather data about bitstate hashing for the
 * Reachability algorithm. TODO: add more explanations */

#include "config.h"
#include "bin/common_conv.hh"
#include "bin/common_setup.hh"
#include "bin/common_output.hh"

#include <spot/kripke/kripke.hh>
#include <spot/kripke/kripkegraph.hh>
#include <spot/ltsmin/ltsmin.hh>
#include <spot/ltsmin/spins_kripke.hh>
#include <spot/mc/deadlock.hh>
#include <spot/mc/mc_instanciator.hh>

#include <string>
#include <thread>
#include <vector>

using Kripke_ptr = spot::ltsmin_kripkecube_ptr;
using State = spot::cspins_state;
using Iterator = spot::cspins_iterator;
using Hash = spot::cspins_state_hash;
using Equal = spot::cspins_state_equal;

static spot::ltsmin_kripkecube_ptr load_model(std::string path,
                                              unsigned nb_threads)
{
  const unsigned compression_level = 0;

  try
  {
    return spot::ltsmin_model::load(path)
      .kripkecube({}, spot::formula::ff(), compression_level, nb_threads);
  }
  catch (const std::runtime_error& e)
  {
    std::cerr << e.what() << '\n';
  }

  return nullptr;
}

static void run_one_reachability_bench(spot::ltsmin_kripkecube_ptr sys,
                                       std::size_t hs_size,
                                       std::size_t bf_size,
                                       std::string model_name,
                                       unsigned repartition)
{
  spot::timer_map tm;
  tm.start("run");


  spot::ec_stats stats;

  if (repartition)
    stats =
      spot::instanciate
      <spot::swarmed_deadlock<State, Iterator, Hash, Equal, std::false_type,
                              std::true_type>,
       Kripke_ptr, State, Iterator, Hash, Equal>(sys, nullptr, false,
                                                 hs_size, bf_size);
  else // do not use bloom filter but restrict size of the Hashmap
    stats =
      spot::instanciate
      <spot::swarmed_deadlock<State, Iterator, Hash, Equal, std::false_type,
                              std::false_type>,
       Kripke_ptr, State, Iterator, Hash, Equal>(sys, nullptr, false,
                                                 hs_size, bf_size);


  tm.stop("run");

  // Print stats
  std::cout << "#model,nb_threads,%ht-bf,ht_size,bf_size,time,states,throughput"
            << std::endl;
  std::cout << model_name << ','
            << sys->get_threads() << ','
            << repartition << ','
            << hs_size << ","
            << bf_size << ","
            << tm.timer("run").walltime()
            << ','
            << stats.unique_states
            << ','
            << stats.unique_states / tm.timer("run").walltime()
            << "\n";
}

int main(int argc, char** argv)
{
  if (argc != 5)
    {
      std::cout << "Usage: ./reachability-2021 [model] [nbthread]"
                << "[mem (size)] [bloomfilter repartition]\n";
      return 1;
    }

  std::string model = argv[1];
  unsigned nb_threads = (unsigned) atoi(argv[2]);
  unsigned mem = (unsigned) atoi(argv[3]);
  unsigned bf_percentage = (unsigned) atoi(argv[4]);

  auto sys = load_model(model, nb_threads);
  if (!sys)
    {
      std::cerr << "Could not load model: "  << model << " (skipping)\n";
      exit(1);
    }

  // FIXME: Here mem is splitted in two parts:
  //   - the size of the bloom filter
  //   - the size of the hashmap
  // This is OK for the Bloom Filter but this could be refined for the
  // Hashmap. Indeed, the size of the hashmap is an underapproximation
  // since the real size (in octe) should take in account the size of
  // each states.
  std::size_t hash_set_size = mem * (double) (100-bf_percentage) / 100.;
  std::size_t bloom_filter_size = mem - hash_set_size;

  run_one_reachability_bench(sys, hash_set_size,
                             bloom_filter_size, model, bf_percentage);

  return 0;
}
