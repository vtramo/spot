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
 * Deadlock algorithm. TODO: add more explanations */

#include "config.h"
#include "bin/common_conv.hh"
#include "bin/common_setup.hh"
#include "bin/common_output.hh"

#include <spot/kripke/kripke.hh>
#include <spot/kripke/kripkegraph.hh>
#include <spot/ltsmin/ltsmin.hh>
#include <spot/ltsmin/spins_kripke.hh>
#include <spot/mc/deadlock.hh>
#include <spot/mc/deadlock_bitstate.hh>
#include <spot/mc/mc_instanciator.hh>

#include <string>
#include <thread>
#include <vector>

struct deadlock_model
{
  std::string path;
  std::size_t hm_size;
  std::size_t filter_size;
};

enum deadlock_type
{
  REF,
  CUSTOM_BF_DISABLE,
  CUSTOM_BF_ENABLE,
};

using Kripke_ptr = spot::ltsmin_kripkecube_ptr;
using State = spot::cspins_state;
using Iterator = spot::cspins_iterator;
using Hash = spot::cspins_state_hash;
using Equal = spot::cspins_state_equal;

static void run_one_deadlock_bench(deadlock_model model, deadlock_type type)
{
  // Load model
  const unsigned compression_level = 0;
  const unsigned nb_threads = 4;
  spot::ltsmin_kripkecube_ptr sys = nullptr;
  try
  {
    sys = spot::ltsmin_model::load(model.path)
      .kripkecube({}, spot::formula::ff(), compression_level, nb_threads);
  }
  catch (const std::runtime_error& e)
  {
    std::cerr << e.what() << '\n';
  }
  if (!sys)
    std::exit(2);

  // Run model
  spot::ec_stats stats = {};
  if (type == deadlock_type::REF)
  {
    stats = instanciate<
      spot::swarmed_deadlock<State, Iterator, Hash, Equal, std::false_type>,
      Kripke_ptr, State, Iterator, Hash, Equal> (sys);
  }
  else if (type == deadlock_type::CUSTOM_BF_DISABLE)
  {
    stats = instanciate<spot::swarmed_deadlock_bitstate<State, Iterator, Hash,
                                                        Equal, std::false_type>,
                        Kripke_ptr, State, Iterator, Hash, Equal>(
      sys, nullptr, false, model.hm_size + (model.filter_size / 32), 0);
  }
  else if (type == deadlock_type::CUSTOM_BF_ENABLE)
  {
    stats = instanciate<spot::swarmed_deadlock_bitstate<State, Iterator, Hash,
                                                        Equal, std::false_type>,
                        Kripke_ptr, State, Iterator, Hash, Equal>(
      sys, nullptr, false, model.hm_size, model.filter_size);
  }

  // Print stats
  std::cout << model.path.substr(model.path.rfind("/") + 1, model.path.size())
  // XXX: for deadlock use map_.stats().used
  // XXX: for deadlock_bitstate use an atomic integer to count map insert
            << "," << stats.states[0]
            << "\n";
}

int main(int argc, char** argv)
{
  if (argc != 2)
  {
    std::cout << "Usage: ./deadlock-2021 [CONFIG_PATH]\n";
    return 1;
  }

  std::vector<deadlock_model> models;
  std::ifstream config(argv[1]);
  std::string model_path;
  std::size_t model_hm_size;
  std::size_t model_filter_size;
  while (config >> model_path >> model_hm_size >> model_filter_size)
    models.push_back({model_path, model_hm_size, model_filter_size});

  std::cout << "Ref\n";
  for (auto model : models)
    run_one_deadlock_bench(model, deadlock_type::REF);
  std::cout << "Custom (BF disable)\n";
  for (auto model : models)
    run_one_deadlock_bench(model, deadlock_type::CUSTOM_BF_DISABLE);
  std::cout << "Custom (BF enable)\n";
  for (auto model : models)
    run_one_deadlock_bench(model, deadlock_type::CUSTOM_BF_ENABLE);

  return 0;
}
