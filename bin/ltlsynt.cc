// -*- coding: utf-8 -*-
// Copyright (C) 2017-2020 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#include <config.h>

#include <string>
#include <sstream>
#include <unordered_map>
#include <vector>

#include "argmatch.h"

#include "common_aoutput.hh"
#include "common_finput.hh"
#include "common_setup.hh"
#include "common_sys.hh"

#include <spot/misc/bddlt.hh>
#include <spot/misc/escape.hh>
#include <spot/misc/timer.hh>
#include <spot/tl/formula.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/aiger.hh>
#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/game.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/parity.hh>
#include <spot/twaalgos/sbacc.hh>
#include <spot/twaalgos/simulation.hh>
#include <spot/twaalgos/synthesis.hh>
#include <spot/twaalgos/toparity.hh>
#include <spot/twaalgos/totgba.hh>
#include <spot/twaalgos/translate.hh>

enum
{
  OPT_ALGO = 256,
  OPT_CSV,
  OPT_INPUT,
  OPT_OUTPUT,
  OPT_PRINT,
  OPT_PRINT_AIGER,
  OPT_PRINT_HOA,
  OPT_REAL,
  OPT_VERBOSE
};

// TODO: Une option "tlsf"
static const argp_option options[] =
  {
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Input options:", 1 },
    { "ins", OPT_INPUT, "PROPS", 0,
      "comma-separated list of uncontrollable (a.k.a. input) atomic"
      " propositions", 0},
    { "outs", OPT_OUTPUT, "PROPS", 0,
      "comma-separated list of controllable (a.k.a. output) atomic"
      " propositions", 0},
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Fine tuning:", 10 },
    { "algo", OPT_ALGO, "sd|ds|ps|lar|lar.old", 0,
      "choose the algorithm for synthesis:\n"
      " - sd:   translate to tgba, split, then determinize (default)\n"
      " - ds:   translate to tgba, determinize, then split\n"
      " - ps:   translate to dpa, then split\n"
      " - lar:  translate to a deterministic automaton with arbitrary"
      " acceptance condition, then use LAR to turn to parity,"
      " then split\n"
      " - lar.old:  old version of LAR, for benchmarking.\n", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Output options:", 20 },
    { "print-pg", OPT_PRINT, nullptr, 0,
      "print the parity game in the pgsolver format, do not solve it", 0},
    { "print-game-hoa", OPT_PRINT_HOA, "options", OPTION_ARG_OPTIONAL,
      "print the parity game in the HOA format, do not solve it", 0},
    { "realizability", OPT_REAL, nullptr, 0,
      "realizability only, do not compute a winning strategy", 0},
    { "aiger", OPT_PRINT_AIGER, "ITE|ISOP", OPTION_ARG_OPTIONAL,
      "prints a winning strategy as an AIGER circuit.  With argument \"ISOP\""
      " conditions are converted to DNF, while the default \"ITE\" uses the "
      "if-the-else normal form.", 0},
    { "verbose", OPT_VERBOSE, nullptr, 0,
      "verbose mode", -1 },
    { "csv", OPT_CSV, "[>>]FILENAME", OPTION_ARG_OPTIONAL,
      "output statistics as CSV in FILENAME or on standard output "
      "(if '>>' is used to request append mode, the header line is "
      "not output)", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Miscellaneous options:", -1 },
    { "extra-options", 'x', "OPTS", 0,
        "fine-tuning options (see spot-x (7))", 0 },
    { nullptr, 0, nullptr, 0, nullptr, 0 },
  };

static const struct argp_child children[] =
  {
    { &finput_argp_headless, 0, nullptr, 0 },
    { &aoutput_argp, 0, nullptr, 0 },
    //{ &aoutput_o_format_argp, 0, nullptr, 0 },
    { &misc_argp, 0, nullptr, 0 },
    { nullptr, 0, nullptr, 0 }
  };

const char argp_program_doc[] = "\
Synthesize a controller from its LTL specification.\v\
Exit status:\n\
  0   if the input problem is realizable\n\
  1   if the input problem is not realizable\n\
  2   if any error has been reported";

static std::vector<std::string> input_aps;
static std::vector<std::string> output_aps;

static const char* opt_csv = nullptr;
static bool opt_print_pg = false;
static bool opt_print_hoa = false;
static const char* opt_print_hoa_args = nullptr;
static bool opt_real = false;
static const char* opt_print_aiger = nullptr;
static spot::option_map extra_options;

static spot::game_info gi;

static char const *const solver_names[] =
  {
   "ds",
   "sd",
   "ps",
   "lar",
   "lar.old"
  };

static char const *const solver_args[] =
{
  "detsplit", "ds",
  "splitdet", "sd",
  "dpasplit", "ps",
  "lar",
  "lar.old",
  nullptr
};
static spot::solver const solver_types[] =
{
  spot::DET_SPLIT, spot::DET_SPLIT,
  spot::SPLIT_DET, spot::SPLIT_DET,
  spot::DPA_SPLIT, spot::DPA_SPLIT,
  spot::LAR,
  spot::LAR_OLD,
};
ARGMATCH_VERIFY(solver_args, solver_types);

static bool verbose = false;

namespace
{

  auto str_tolower = [] (std::string s)
    {
      std::transform(s.begin(), s.end(), s.begin(),
                     [](unsigned char c){ return std::tolower(c); });
      return s;
    };

  // TODO: Un point à régler sur le CSV est que lorsque l'on va découper
  // la formule, il va y avoir plusieurs temps de traduction. On se contente
  // d'en faire la somme ?
  static void
  print_csv(spot::formula f, bool realizable)
  {
    auto& vs = gi.verbose_stream;
    auto& bv = gi.bv;
    if (not bv)
      raise std::runtime_error("No information available for csv!");
    if (vs)
      vs << "writing CSV to " << opt_csv << '\n';

    output_file outf(opt_csv);
    std::ostream& out = outf.ostream();

    // Do not output the header line if we append to a file.
    // (Even if that file was empty initially.)
    if (!outf.append())
      {
        out << ("\"formula\",\"algo\",\"trans_time\","
                "\"split_time\",\"todpa_time\"");
        if (!opt_print_pg && !opt_print_hoa)
          {
            out << ",\"solve_time\"";
            if (!opt_real)
              out << ",\"strat2aut_time\"";
            out << ",\"realizable\"";
          }
        out << ",\"dpa_num_states\",\"parity_game_num_states\""
            << '\n';
      }
    std::ostringstream os;
    os << f;
    spot::escape_rfc4180(out << '"', os.str());
    out << "\",\"" << solver_names[opt_solver]
        << "\"," << bv->trans_time
        << ',' << bv->split_time
        << ',' << bv->paritize_time;
    if (!opt_print_pg && !opt_print_hoa)
      {
        out << ',' << bv->solve_time;
        if (!opt_real)
          out << ',' << bv->strat2aut_time;
        out << ',' << bv->realizable;
      }
    out << ',' << bv->nb_states_arena
        << ',' << bv->nb_states_parity_game
        << '\n';
    outf.close(opt_csv);
  }

  int
  solve_formula(spot::formula f, std::vector<std::string> input_aps, std::vector<std::string> output_aps, spot::translator trans)
  {
    // TODO: Les bench_var sont passés par copie…
    std::vector<spot::formula> ins, outs;
    std::transform(input_aps.begin(), input_aps.end(), std::back_inserter(ins),
    [](std::string name) { return spot::formula::ap(name); });
    std::transform(output_aps.begin(), output_aps.end(), std::back_inserter(outs),
    [](std::string name) { return spot::formula::ap(name); });
    if (opt_print_pg || opt_print_hoa)
    {
      auto dpa = create_game(f, ins, outs, trans, opt_solver, verbose);
      if (opt_print_pg)
        pg_print(std::cout, dpa);
      else
        spot::print_hoa(std::cout, dpa, opt_print_hoa_args) << '\n';
      return 0;
    }
    else if (!opt_print_aiger)
    {
      auto strat_aut = create_strategy(f, ins, outs, trans, verbose, opt_solver);
      if (strat_aut == nullptr)
      {
        std::cout << "UNREALIZABLE" << std::endl;
        return 1;
      }
      std::cout << "REALIZABLE" << std::endl;
      return 0;
    }
    else
    {
      // FIXME: Là c'est un AIGER qui est renvoyé, il faudrait un
      // truc dans le cas où le circuit n'existe pas.
      auto circuit = create_aiger_circuit(f, ins, outs, trans, opt_print_aiger, verbose, opt_solver);
      // if (circuit != nullptr)
      // {
        std::cout << "REALIZABLE" << std::endl;
        print_aiger(std::cout, circuit, "circuit");
        return 0;
      // }
      // else
      // {
      //   std::cout << "UNREALIZABLE" << std::endl;
      //   return 1;
      // }
    }
    // TODO: Print csv
  }

  class ltl_processor final : public job_processor
  {
  private:
    spot::translator &trans_;
    // TODO: Ces trucs là j'ai l'impression qu'il n'y a pas d'intérêt à
    // les avoir en vecteur de string.
    // Gardons le pour le moment, c'est quoi l'advantage des les avoir
    // comme formule? Après je vais faire
    // aut.register_ap(af.ap_name())
    // ce n'est pas plus pratique
    std::vector<std::string> input_aps_;
    std::vector<std::string> output_aps_;

  public:
    ltl_processor(spot::translator &trans,
                  std::vector<std::string> input_aps_,
                  std::vector<std::string> output_aps_)
        : trans_(trans), input_aps_(input_aps_), output_aps_(output_aps_)
    {
    }

    int solve_formula(spot::formula f)
    {
      // Le trans_ est un argument passé aux create_XX().
      spot::process_timer timer;
      timer.start();

      auto arena = spot::create_game(f, input_aps_, output_aps_, trans_, gi);

      if (cgi.bv)
        cgi.bv->nb_states_arena = dpa->num_states();

      if (opt_print_pg)
        {
          timer.stop();
          pg_print(std::cout, dpa);
          return 0;
        }
      if (opt_print_hoa)
        {
          timer.stop();
          spot::print_hoa(std::cout, dpa, opt_print_hoa_args) << '\n';
          return 0;
        }

      auto [winning, strat] = spot::create_strategy(arena, gi);

      if (winning)
        {
          if (opt_print_aiger)
            spot::print_aiger(std::cout, strat_aut, opt_print_aiger);
          else
            {
              automaton_printer printer;
              printer.print(strat_aut, timer);
            }
          return 0;
        }
      else
        {
          std::cout << "UNREALIZABLE\n";
          return 1;
        }
    }

    int process_formula(spot::formula f, const char*, int) override
    {
      unsigned res = solve_formula(f);
      if (opt_csv)
        print_csv(f, res == 0);
      return res;
    }
  };
}

  static int
  parse_opt(int key, char *arg, struct argp_state *)
{
  // Called from C code, so should not raise any exception.
  BEGIN_EXCEPTION_PROTECT;
  switch (key)
    {
    case OPT_ALGO:
      gi.s = XARGMATCH("--algo", arg, solver_args, solver_types);
      break;
    case OPT_CSV:
      opt_csv = arg ? arg : "-";
      if (not gi.bv)
        gi.bv = spot::bench_var()
      break;
    case OPT_INPUT:
      {
        std::istringstream aps(arg);
        std::string ap;
        while (std::getline(aps, ap, ','))
          {
            ap.erase(remove_if(ap.begin(), ap.end(), isspace), ap.end());
            input_aps.push_back(str_tolower(ap));
          }
        break;
      }
    case OPT_OUTPUT:
      {
        std::istringstream aps(arg);
        std::string ap;
        while (std::getline(aps, ap, ','))
          {
            ap.erase(remove_if(ap.begin(), ap.end(), isspace), ap.end());
            output_aps.push_back(str_tolower(ap));
          }
        break;
      }
    case OPT_PRINT:
      opt_print_pg = true;
      gi.force_sbacc = true;
      break;
    case OPT_PRINT_HOA:
      opt_print_hoa = true;
      opt_print_hoa_args = arg;
      break;
    case OPT_PRINT_AIGER:
      opt_print_aiger = arg ? arg : "INF";
      break;
    case OPT_REAL:
      opt_real = true;
      gi.apply_strat = false;
      break;
    case OPT_VERBOSE:
      gi.verbose_stream = std::cerr;
      if (not gi.bv)
        gi.bv = spot::bench_var()
      break;
    case 'x':
      {
        const char* opt = extra_options.parse_options(arg);
        if (opt)
          error(2, 0, "failed to parse --options near '%s'", opt);
      }
      break;
    }
  END_EXCEPTION_PROTECT;
  return 0;
}

int
main(int argc, char **argv)
{
  return protected_main(argv, [&] {
      extra_options.set("simul", 0);
      extra_options.set("ba-simul", 0);
      extra_options.set("det-simul", 0);
      extra_options.set("tls-impl", 1);
      extra_options.set("wdba-minimize", 2);
      const argp ap = { options, parse_opt, nullptr,
                        argp_program_doc, children, nullptr, nullptr };
      if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
        exit(err);
      check_no_formula();

      // Setup the dictionary now, so that BuDDy's initialization is
      // not measured in our timings.
      spot::bdd_dict_ptr dict = spot::make_bdd_dict();
      spot::translator trans(dict, &extra_options);
      ltl_processor processor(trans, input_aps, output_aps);

      // Diagnose unused -x options
      extra_options.report_unused_options();
      return processor.run();
    });
}
