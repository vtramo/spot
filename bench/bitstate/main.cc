#include "config.h"
#include "bin/common_conv.hh"
#include "bin/common_setup.hh"
#include "bin/common_output.hh"

#include <spot/kripke/kripkegraph.hh>
#include <spot/ltsmin/ltsmin.hh>
#include <spot/ltsmin/spins_kripke.hh>

#include <string>
#include <thread>

#include "bitstate.hh"
#include "deadlock.hh"

int main(int argc, char** argv)
{
  if (argc != 4)
  {
    std::cout << "Usage: ./bench [MODEL] [ALGO] [MEM_SIZES]\n";
    return 1;
  }

  const unsigned compression_level = 0;
  const unsigned nb_threads = 4;

  std::string model_path = argv[1];
  std::string algo = argv[2];
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

  if (algo == "bitstate")
  {
    bench_bitstate<spot::ltsmin_kripkecube_ptr,
        spot::cspins_state,
        spot::cspins_iterator,
        spot::cspins_state_hash,
        spot::cspins_state_equal>
        (modelcube, mem_sizes);
  }
  else if (algo == "deadlock")
  {
    bench_deadlock<spot::ltsmin_kripkecube_ptr,
        spot::cspins_state,
        spot::cspins_iterator,
        spot::cspins_state_hash,
        spot::cspins_state_equal>
        (modelcube, mem_sizes);
  }
  else
    std::cerr << "Unknown algo: " << algo << "\n";

  return 0;
}
