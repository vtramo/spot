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

struct reachability_model
{
  std::string path;
  std::size_t nb_states;
};

using Kripke_ptr = spot::ltsmin_kripkecube_ptr;
using State = spot::cspins_state;
using Iterator = spot::cspins_iterator;
using Hash = spot::cspins_state_hash;
using Equal = spot::cspins_state_equal;

static std::vector<reachability_model> parse_config(std::string path)
{
  std::vector<reachability_model> models;
  std::ifstream config(path);
  std::string line;

  while (std::getline(config, line))
  {
    if (line.empty() || line[0] == '#')
      continue;

    std::stringstream linestream(line);
    std::string model_path;
    std::size_t model_nb_states;
    linestream >> model_path >> model_nb_states;
    models.push_back({model_path, model_nb_states});
  }

  return models;
}

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
  auto stats =
    spot::instanciate
    <spot::swarmed_deadlock<State, Iterator, Hash, Equal, std::false_type>,
     Kripke_ptr, State, Iterator, Hash, Equal>(sys, nullptr, false);
  tm.stop("run");

  // Print stats
  std::cout << "#model,nb_threads,%ht-bf,ht_size,bf_size,time,states"
            << std::endl;
  std::cout << model_name << ','
            << sys->get_threads() << ','
            << repartition << ','
            << hs_size << ","
            << bf_size << ","
            <<  tm.timer("run").walltime()
            << ','
            << stats.unique_states
            << "\n";
}

int main(int argc, char** argv)
{
  if (argc != 3)
    {
      std::cout << "Usage: ./reachability-2021 [CONFIG_PATH] nb_threads\n";
      return 1;
    }

  auto models = parse_config(argv[1]);
  unsigned nb_threads = (unsigned) atoi(argv[2]);

  for (auto model : models)
    {
      auto sys = load_model(model.path, nb_threads);
      if (!sys)
        {
          std::cerr << "Could not load model: "
                    << model.path << " (skipping)\n";
          continue;
        }

      // XXX: we allow for only 80% memory based on what we should use
      // to explore the full graph
      std::size_t allowed_mem = model.nb_states * 0.8f;
      for (int i = 5; i < 100; i += 5)
        {
          std::size_t hash_set_size = allowed_mem * (double) i / 100.;
          std::size_t bloom_filter_size = allowed_mem - hash_set_size;

          run_one_reachability_bench(sys, hash_set_size,
                                     bloom_filter_size, model.path, i);
        }
    }

  return 0;
}
