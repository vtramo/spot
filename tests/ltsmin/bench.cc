#include "config.h"

#include <argp.h>
#include <cassert>
#include <thread>

#include "bin/common_setup.hh"
#include "bin/common_conv.hh"

#include <spot/kripke/kripke.hh>
#include <spot/misc/timer.hh>
#include <spot/parseaut/public.hh>
#include <spot/tl/apcollect.hh>
#include <spot/tl/defaultenv.hh>
#include <spot/tl/parse.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/powerset.hh>
#include <spot/twaalgos/sccfilter.hh>
#include <spot/twaalgos/simulation.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/twacube_algos/convert.hh>
#include <spot/twacube_algos/twacube_determinize.hh>

const char argp_program_doc[] =
"Bench determinization";

struct mc_options_
{
  bool twa = false;
  bool twa_opt = false;
  bool twacube = false;
  bool simulation = false;
  unsigned nb_threads = 1;
  unsigned wanted = 0;
  unsigned min = 0;
  unsigned max_states = 0;
} mc_options;

static int
parse_opt_finput(int key, char* arg, struct argp_state*)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case 'a':
      mc_options.twa = true;
      break;
    case 'A':
      mc_options.twa_opt = true;
      break;
    case 'c':
      mc_options.twacube = true;
      break;
    case 'm':
      mc_options.min = to_unsigned(arg, "-m/--min");
      break;
    case 'p':
      mc_options.nb_threads = to_unsigned(arg, "-p/--parallel");
      break;
    case 's':
      mc_options.max_states = to_unsigned(arg, "-s/--max-states");
      break;
    case 'S':
      mc_options.simulation = true;
    case 'w':
      mc_options.wanted = to_unsigned(arg, "-w/--wanted");
      break;
    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}

static const argp_option options[] =
  {
    // Keep each section sorted
    // ------------------------------------------------------------
    { nullptr, 0, nullptr, 0, "Process options:", 1 },
    { "parallel", 'p', "INT", 0, "use INT threads (when possible)", 0 },
    { "simulation", 'S', nullptr, 0, "use simulation on twacube", 0 },
    { "twa", 'a', nullptr, 0, "determinize using twa algo", 0 },
    { "twa_opt", 'A', nullptr, 0, "determinize using twa optimized algo", 0 },
    { "twacube", 'c', nullptr, 0, "determinize using twacube algo", 0 },
    // ------------------------------------------------------------
    { nullptr, 0, nullptr, 0, "Output options:", 2 },
    { "wanted", 'w', "INT", 0, "number of auts to bench", 0 },
    { "min", 'm', "INT", 0, "min det time in seconds", 0 },
    { "max-states", 's', "INT", 0, "max num of states before abort", 0 },
    // ------------------------------------------------------------

    { nullptr, 0, nullptr, 0, "General options:", 3 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
  };

const struct argp finput_argp = { options, parse_opt_finput,
                                  nullptr, nullptr, nullptr,
                                  nullptr, nullptr };

const struct argp_child children[] =
  {
    { &finput_argp, 0, nullptr, 1 },
    { &misc_argp, 0, nullptr, -1 },
    { nullptr, 0, nullptr, 0 }
  };

static int
checked_main()
{
  auto dict = spot::make_bdd_dict();
  spot::const_twa_graph_ptr aut = nullptr;
  spot::twacube_ptr aut_cube = nullptr;
  spot::formula f = nullptr;
  spot::atomic_prop_set ap;
  size_t count = 0;
  spot::output_aborter* aborter = nullptr;

  int exit_code = 0;

  if (mc_options.max_states != 0)
    {
      aborter = new spot::output_aborter(mc_options.max_states);
    }

  auto parser = spot::automaton_stream_parser("/dev/stdin");

  std::cout << "nb_threads: " << mc_options.nb_threads << std::endl;

  std::cout << "formula,"
            << "walltime"
            << std::endl;

  spot::parsed_aut_ptr res = nullptr;
  while ((res = parser.parse(dict))->aut != nullptr)
    {
      spot::twa_graph_ptr aut = res->aut;

      if (mc_options.simulation)
        {
          aut = spot::simulation(spot::scc_filter(aut));
        }

      std::string formula = *aut->get_named_prop<std::string>("automaton-name");

      assert(!res->aborted);
      assert(res->errors.empty());

      spot::timer_map tm;

      spot::twa_graph_ptr det_aut = nullptr;
      if (mc_options.twa)
        {
          tm.start("determinize");
          det_aut = tgba_determinize(aut, false, false, false, false);
          tm.stop("determinize");
        }

      if (mc_options.twa_opt)
        {
          tm.start("determinize");
          det_aut = tgba_determinize(aut, false, true, true, true);
          tm.stop("determinize");
        }

      spot::twacube_ptr cube_det_aut = nullptr;

      if (mc_options.twacube)
        {
          spot::twacube_ptr cube_aut = twa_to_twacube(aut);
          tm.start("determinize");
          cube_det_aut = twacube_determinize(cube_aut, mc_options.nb_threads);
          tm.stop("determinize");

          spot::const_twa_graph_ptr ref = spot::tgba_determinize(aut);
          if (!spot::are_equivalent(cube_det_aut, ref))
            exit(1);
        }

      auto duration = tm.timer("determinize").walltime();

      if (duration >= mc_options.min * size_t(1000))
        {
          count++;

          std::cout << formula << ',' << duration << std::endl;

          if (mc_options.wanted != 0 && count >= mc_options.wanted)
            return exit_code;
        }

    }

  if (aborter != nullptr)
    delete aborter;

  return exit_code;
}

int
main(int argc, char** argv)
{
  setup(argv);
  const argp ap = { nullptr, nullptr, nullptr,
                    argp_program_doc, children, nullptr, nullptr };

  if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
    exit(err);

  auto exit_code = checked_main();

  return exit_code;
}
