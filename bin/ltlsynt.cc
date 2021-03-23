// -*- coding: utf-8 -*-
// Copyright (C) 2017-2021 Laboratoire de Recherche et Développement
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

#include <sstream>
#include <unordered_map>
#include <vector>
#include <regex>

#include "argmatch.h"

#include "common_aoutput.hh"
#include "common_finput.hh"
#include "common_setup.hh"
#include "common_sys.hh"

#include <spot/misc/bddlt.hh>
#include <spot/misc/escape.hh>
#include <spot/misc/timer.hh>
#include <spot/tl/apcollect.hh>
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
    { "outs", OPT_OUTPUT, "PROPS", 0,
      "comma-separated list of controllable (a.k.a. output) atomic"
      " propositions", 0},
    { "ins", OPT_INPUT, "PROPS", OPTION_ARG_OPTIONAL,
      "comma-separated list of controllable (a.k.a. output) atomic"
      " propositions. If unspecified its the complement of \"outs\"", 0},
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

static std::set<std::string> all_output_aps;
static std::set<std::string> all_input_aps;

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
  spot::solver::DET_SPLIT, spot::solver::DET_SPLIT,
  spot::solver::SPLIT_DET, spot::solver::SPLIT_DET,
  spot::solver::DPA_SPLIT, spot::solver::DPA_SPLIT,
  spot::solver::LAR,
  spot::solver::LAR_OLD,
};
ARGMATCH_VERIFY(solver_args, solver_types);

namespace
{

  // TODO: Alexandre propose que --ins et --outs puissent être donnés par
  // regex.
  // static std::pair<std::set<std::string>, std::set<std::string>>
  // regexes_to_ins_outs(spot::formula f, std::string reg_in, std::string reg_out)
  // {
  //   std::regex left_ex(reg_in), right_ex(reg_out);
  //   spot::atomic_prop_set f_props;
  //   std::set<std::string> lefts, rights;
  //   spot::atomic_prop_collect(f, &f_props);
  //   for (auto prop : f_props)
  //   {
  //     auto prop_name = prop.ap_name();
  //     bool is_ok_left = false;
  //     if (std::regex_match(prop_name, left_ex))
  //     {
  //       lefts.insert(prop_name);
  //       is_ok_left = true;
  //     }
  //     if (std::regex_match(prop_name, right_ex))
  //     {
  //       if (is_ok_left)
  //       {
  //         throw std::runtime_error("A proposition cannot be matched by 2 regex!");
  //       }
  //       rights.insert(prop_name);
  //     }
  //   }
  //   return {lefts, rights};
  // }

  auto str_tolower = [] (std::string s)
    {
      std::transform(s.begin(), s.end(), s.begin(),
                     [](unsigned char c){ return std::tolower(c); });
      return s;
    };

//  std::string exec(const char* cmd)
//    {
//      std::array<char, 256> buffer;
//      std::string result;
//
//      int ret_code = 0;
//      auto closer = [&](auto&& myfile)
//        {
//          auto rc = pclose(myfile);
//          if(WIFEXITED(rc))
//            ret_code = WEXITSTATUS(rc);
//        };
//      {
//        std::unique_ptr<FILE, decltype(closer)> pipe(popen(cmd, "r"), closer);
//        if (!pipe)
//          throw std::runtime_error("popen() failed!");
//        while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr)
//          result += buffer.data();
//      }
//      if (ret_code != 0)
//        throw std::runtime_error("Nonzero exit code\n");
//      return result;
//    }

  // TODO: Un point à régler sur le CSV est que lorsque l'on va découper
  // la formule, il va y avoir plusieurs temps de traduction. On se contente
  // d'en faire la somme ?
  static void
  print_csv(const spot::formula& f)
  {
    auto& vs = gi.verbose_stream;
    auto& bv = gi.bv;
    if (not bv)
      throw std::runtime_error("No information available for csv!");
    if (vs)
      *vs << "writing CSV to " << opt_csv << '\n';

    output_file outf(opt_csv);
    std::ostream& out = outf.ostream();

    // Do not output the header line if we append to a file.
    // (Even if that file was empty initially.)
    if (!outf.append())
      {
        out << ("\"formula\",\"algo\",\"tot_time\",\"trans_time\","
                "\"split_time\",\"todpa_time\"");
        if (!opt_print_pg && !opt_print_hoa)
          {
            out << ",\"solve_time\"";
            if (!opt_real)
              out << ",\"strat2aut_time\"";
            out << ",\"realizable\""; //-1: Unknown, 0: Unreal, 1: Real
          }
        out << ",\"dpa_num_states\",\"parity_game_num_states\""
            << '\n';
      }
    std::ostringstream os;
    os << f;
    spot::escape_rfc4180(out << '"', os.str());
    out << "\",\"" << solver_names[(int) gi.s]
        << "\"," << bv->trans_time
        << ',' << bv->total_time
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
  solve_formula(const spot::formula& f,
                const std::set<std::string>& input_aps,
                const std::set<std::string>& output_aps)
  {
    spot::stopwatch sw;
    if (gi.bv)
      sw.start();

    int is_winning = -1;
    auto safe_tot_time = [&]()
    {
      if (gi.bv)
        gi.bv->total_time = sw.stop();
    };

    // We always need an arena, specific needs are passed via gi
    auto arena = spot::create_game(f, output_aps, extra_options, gi);
    // FIXME: Voir tout en bas
    extra_options.report_unused_options();
    if (gi.bv)
      gi.bv->nb_states_arena = arena->num_states();

    if (opt_print_pg)
      {
        pg_print(std::cout, arena);
        safe_tot_time();
        return 0;
      }
    if (opt_print_hoa)
      {
        spot::print_hoa(std::cout, arena, opt_print_hoa_args) << '\n';
        safe_tot_time();
        return 0;
      }

    // We need a solved game
    is_winning = (int) spot::solve_game(arena, gi);
    if (gi.bv)
      gi.bv->realizable = is_winning;

    if (opt_real)
      {
        std::cout << (is_winning ? "REALIZABLE" : "UNREALIZABLE") << std::endl;
        safe_tot_time();
        return (int) not is_winning;
      }
    // From here on we need the strat if winning
    std::cout << (is_winning ? "REALIZABLE" : "UNREALIZABLE") << std::endl;
    if (is_winning)
      {
        // We need the strategy automaton
        if (gi.bv)
          sw.start();
        auto strat_aut = spot::create_strategy(arena, gi);
        if (gi.bv)
          gi.bv->strat2aut_time = sw.stop();
        if (opt_print_aiger)
          spot::print_aiger(std::cout,
                            spot::strategy_to_aig(strat_aut, opt_print_aiger,
                                                  input_aps,
                                                  output_aps), "circuit");
        else
          {
            spot::process_timer timer;
            automaton_printer printer;
            printer.print(strat_aut, timer);
          }
      }

    safe_tot_time();
    return (int) not is_winning;
  }

  class ltl_processor final : public job_processor
  {
  private:
    // TODO: Ces trucs là j'ai l'impression qu'il n'y a pas d'intérêt à
    // les avoir en vecteur de string.
    // Gardons le pour le moment, c'est quoi l'advantage des les avoir
    // comme formule? Après je vais faire
    // aut.register_ap(af.ap_name())
    // ce n'est pas plus pratique
    std::set<std::string> input_aps_;
    std::set<std::string> output_aps_;

  public:
    ltl_processor(std::set<std::string> input_aps_,
                  std::set<std::string> output_aps_)
        : input_aps_(std::move(input_aps_)),
          output_aps_(std::move(output_aps_))
    {
    }

    int process_formula(spot::formula f, const char*, int) override
    {
      int res = solve_formula(f, input_aps_, output_aps_);
      if (opt_csv)
        print_csv(f);
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
        gi.bv = spot::game_info::bench_var();
      break;
    case OPT_INPUT:
      {
        std::istringstream aps(arg);
        std::string ap;
        while (std::getline(aps, ap, ','))
          {
            ap.erase(remove_if(ap.begin(), ap.end(), isspace), ap.end());
            all_input_aps.emplace(str_tolower(ap));
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
            all_output_aps.emplace(str_tolower(ap));
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
      break;
    case OPT_VERBOSE:
      gi.verbose_stream = &std::cerr;
      if (not gi.bv)
        gi.bv = spot::game_info::bench_var();
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
      extra_options.set("simul", 0);     // no simulation, except...
      extra_options.set("dpa-simul", 1); // ... after determinization
      extra_options.set("tls-impl", 1);  // no automata-based implication check
      extra_options.set("wdba-minimize", 2); // minimize only syntactic oblig
      const argp ap = { options, parse_opt, nullptr,
                        argp_program_doc, children, nullptr, nullptr };
      if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
        exit(err);
      check_no_formula();

      // Check if inputs and outputs are distinct
      // Inputs can be empty, outputs not
      if (not all_input_aps.empty())
        {
          std::vector<std::string> inter;
          std::set_intersection(all_input_aps.begin(), all_input_aps.end(),
                                all_output_aps.begin(), all_output_aps.end(),
                                std::back_inserter(inter));
          if (not inter.empty())
            {
              for (auto&& e : inter)
                std::cerr << e << '\n';
              throw std::runtime_error("The above aps appear in \"ins\" and"
                                       "\"outs\"");
            }
        }

      ltl_processor processor(all_input_aps, all_output_aps);

      // Diagnose unused -x options
      // FIXME: Maintenant que c'est déplacé, il ne voit pas que les options
      // sont utilisées
      // extra_options.report_unused_options();
      return processor.run();
    });
}
