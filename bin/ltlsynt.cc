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
#include <spot/twaalgos/game.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/synthesis.hh>
#include <spot/twaalgos/product.hh>

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
  OPT_VERBOSE,
  OPT_VERIFY
};

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
    { "verify", OPT_VERIFY, nullptr, 0,
       "verifies the strategy or (if demanded) aiger against the spec.", -1 },
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
static bool opt_do_verify = false;
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
            << ",\"strat_num_states\",\"strat_num_edges\"";
        if (opt_print_aiger)
            out << ",\"nb latches\",\"nb gates\"";
        out << '\n';
      }
    std::ostringstream os;
    os << f;
    spot::escape_rfc4180(out << '"', os.str());
    out << "\",\"" << solver_names[(int) gi.s]
        << "\"," << bv->total_time
        << ',' << bv->trans_time
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
        << ',' << bv->nb_strat_states
        << ',' << bv->nb_strat_edges;

    if (opt_print_aiger)
    {
      out << "," << bv->nb_latches
          << "," << bv->nb_gates;
    }
    out << '\n';
    outf.close(opt_csv);
  }

  int
  solve_formula(const spot::formula& f,
                const std::set<std::string>& input_aps,
                const std::set<std::string>& output_aps)
  {
    //Negated specification if verify is demanded
    spot::twa_graph_ptr neg_spec = nullptr;

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
    if (opt_do_verify)
      {
        spot::translator trans(arena->get_dict(), &extra_options);
        neg_spec = trans.run(spot::formula::Not(f));
      }
    // FIXME: Voir tout en bas
    // extra_options.report_unused_options();
    if (gi.bv)
      gi.bv->nb_states_arena = arena->num_states();

    /////////// TODO: This part split
    auto [sub_form, sub_outs] = split_independant_formulas(f, output_aps);
    std::vector<std::set<std::string>> sub_outs_str(sub_form.size());
    unsigned pos = 0;
    for (auto& x : sub_outs)
    {
      for (auto& y : x)
        sub_outs_str[pos].insert(y.ap_name());
      ++pos;
    }
    std::vector<spot::twa_graph_ptr> arenas;

    // We always need an arena, specific needs are passed via gi
    for (auto sub : sub_form)
    {
      auto arena = spot::create_game(f, output_aps, extra_options, gi);
      arenas.push_back(arena);
      // FIXME: Est-ce que c'est vraiment la somme des tailles des sous-arènes ?
      if (gi.bv)
        gi.bv->nb_states_arena += arena->num_states();
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
    }

    if (gi.bv)
      gi.bv->realizable = true;
    for (auto& arena : arenas)
    {
      is_winning = (int) spot::solve_game(arena, gi);
      if (gi.bv)
        gi.bv->realizable &= is_winning;
    }
    // We need a solved game

    if (opt_real)
      {
        std::cout << (is_winning ? "REALIZABLE" : "UNREALIZABLE") << std::endl;
        safe_tot_time();
        return (int) not is_winning;
      }
    std::vector<spot::twa_graph_ptr> strategies;
    // From here on we need the strat if winning
    std::cout << (is_winning ? "REALIZABLE" : "UNREALIZABLE") << std::endl;
    if (is_winning)
      {
        spot::twa_graph_ptr tot_strat;
        for (auto& arena : arenas)
        {
          // We need the strategy automaton
          if (gi.bv)
            sw.start();
          auto strat_aut = spot::create_strategy(arena, extra_options, gi);
          if (gi.bv)
          {
            gi.bv->strat2aut_time += sw.stop();
            gi.bv->nb_strat_states = strat_aut->num_states();
            gi.bv->nb_strat_edges = strat_aut->num_edges();
          }
          strategies.push_back(strat_aut);
        }
        spot::aig_ptr saig;
        if (opt_print_aiger)
        {
          saig = spot::strategies_to_aig(strategies, opt_print_aiger,
                                              input_aps,
                                              sub_outs_str);
          if (gi.bv)
          {
            gi.bv->nb_latches = saig->num_latches();
            gi.bv->nb_gates = saig->num_gates();
          }
          spot::print_aiger(std::cout, saig, "circuit");
        }
        else
          {
            spot::process_timer timer;
            automaton_printer printer;
            // FIXME: On fait quoi là ?
            // Product of all "local" strategies
            // -> "global" strategy
            tot_strat = strategies.front();
            for (size_t i = 1; i < strategies.size(); ++i)
              tot_strat = product(tot_strat, strategies[i]);
            printer.print(tot_strat, timer);
          }

        if (opt_do_verify)
          {
            // Test the aiger
            if (opt_print_aiger)
              {
                auto saigaut = saig->aig2aut(false);
                if (neg_spec->intersects(saigaut))
                  throw std::runtime_error("Aiger and negated specification "
                                           "do intersect -> strategy not OK.");
                std::cout << "#Circuit was verified\n";
              }
            else
              {
                // Test the strat
                if (neg_spec->intersects(tot_strat))
                  throw std::runtime_error("Strategy and negated specification "
                                           "do intersect -> strategy not OK.");
                std::cout << "/*Strategy was verified*/\n";
              }
          }
      }

    safe_tot_time();
    return (int) not is_winning;
  }

  class ltl_processor final : public job_processor
  {
  private:
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
    case OPT_VERIFY:
      opt_do_verify = true;
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

      auto res = processor.run();
      // Diagnose unused -x options
      extra_options.report_unused_options();
      return res;
    });
}
