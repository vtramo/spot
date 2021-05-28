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
#include <spot/twaalgos/minimize.hh>

#include <spot/priv/synt_utils_struct.hh>

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
    { "aiger", OPT_PRINT_AIGER, "ITE|ISOP|ISOPMIN|OPTIM", OPTION_ARG_OPTIONAL,
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
  split_fast_here(spot::twa_graph_ptr strat)
  {
    // Pre : Acceptance is true
    //       The graph is uncolored
    //       all edge conds have the form in&out
    // Post : edges are env state - in > player state - out > env_state

    bdd all_outs = bddtrue;
    if (auto* outsptr = strat->get_named_prop<bdd>("synthesis-outputs"))
      all_outs = *outsptr;
    else
      throw std::runtime_error("Need \"synthesis-outputs\"!");

    using dst_cond_t = spot::minutils::xi_t;
    std::unordered_map<dst_cond_t, unsigned,
                       spot::minutils::hash_xi,
                       spot::minutils::equal_to_xi> player_map;

    auto get_ps = [&](unsigned dst, const bdd& ocond)
      {
        dst_cond_t key{dst, (unsigned) ocond.id()};
        auto it = player_map.find(key);
        if (it != player_map.end())
          return it->second;
        unsigned value = strat->new_state();
        strat->new_edge(value, dst, ocond);
        player_map[key] = value;
        return value;
      };

    std::vector<unsigned> to_treat(strat->num_edges());
    std::transform(strat->edges().begin(), strat->edges().end(),
                   to_treat.begin(), [&](const auto& e)
                   {return strat->edge_number(e);});

    std::for_each(to_treat.begin(), to_treat.end(),
                  [&](unsigned eidx)
                  {
                    const auto& e = strat->edge_storage(eidx);
                    assert(!e.acc.count() && "Uncolored only!");
                    bdd incond = bdd_exist(e.cond, all_outs);
                    bdd outcond = bdd_existcomp(e.cond, all_outs);
                    assert(((incond&outcond) == e.cond) && "Precondition violated");
                    // Modify
                    unsigned new_dst = get_ps(e.dst, outcond);
                    strat->edge_storage(eidx).dst = new_dst;
                    strat->edge_storage(eidx).cond = incond;
                  });

    auto* sp_ptr =
        strat->get_or_set_named_prop<std::vector<bool>>("state-player");

    sp_ptr->resize(strat->num_states());
    std::fill(sp_ptr->begin(), sp_ptr->end(), false);
    for (auto& eit : player_map)
      (*sp_ptr)[eit.second] = true;
    //Done
  }

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
            if (opt_print_aiger)
              out << ",\"aig_time\"";
            out << ",\"realizable\""; //-1: Unknown, 0: Unreal, 1: Real
          }
        out << ",\"dpa_num_states\",\"dpa_num_states_env\""
            << ",\"parity_game_num_states\""
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
        if (opt_print_aiger)
          out << ',' << bv->aig_time;
        out << ',' << bv->realizable;
      }
    out << ',' << bv->nb_states_arena
        << ',' << bv->nb_states_arena_env
        << ',' << bv->nb_states_parity_game
        << ',' << bv->nb_strat_states
        << ',' << bv->nb_strat_edges;

    if (opt_print_aiger)
    {
      out << ',' << bv->nb_latches
          << ',' << bv->nb_gates;
    }
    out << '\n';
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

    bool opt_decompose_ltl = extra_options.get("specification-decomposition", 0);
    std::vector<spot::formula> sub_form;
    std::vector<std::set<spot::formula>> sub_outs;
    if (opt_decompose_ltl)
    {
      auto subs = split_independant_formulas(f, output_aps);
      if (subs.first.size() > 1)
      {
        sub_form = subs.first;
        sub_outs = subs.second;
      }
    }
    // When trying to split the formula, we can apply transformations that
    // increase its size. This is why we will use the original formula if it
    // has not been cut.
    if (!opt_decompose_ltl || sub_form.empty())
    {
      sub_form = { f };
      sub_outs.resize(1);
      std::transform(output_aps.begin(), output_aps.end(),
            std::inserter(sub_outs[0], sub_outs[0].begin()),
            [](const std::string& name) {
              return spot::formula::ap(name);
            });
    }
    std::vector<std::set<std::string>> sub_outs_str;
    std::transform(sub_outs.begin(), sub_outs.end(),
                   std::back_inserter(sub_outs_str),
                   [](std::set<spot::formula> forms)
                    {
                      std::set<std::string> r;
                      for (auto f : forms)
                        r.insert(f.ap_name());
                      return r;
                    });
    // We always need an arena, specific needs are passed via gi
//    auto arena = spot::create_game(f, output_aps, extra_options, gi);

//    // FIXME: Voir tout en bas
//    // extra_options.report_unused_options();
//    if (gi.bv)
//      gi.bv->nb_states_arena = arena->num_states();

    assert((sub_form.size() == sub_outs.size())
           && (sub_form.size() == sub_outs_str.size()));

    const bool want_game = opt_print_pg || opt_print_hoa;

    std::vector<spot::twa_graph_ptr> arenas;

    auto sub_f = sub_form.begin();
    auto sub_o = sub_outs_str.begin();
    spot::twa_graph_ptr game_prod = nullptr;
    std::vector<spot::twa_graph_ptr> strategies;

    for (; sub_f != sub_form.end(); ++sub_f, ++sub_o)
    {
      // if we don't want a game, we can try to create a strategy from the
      // formula
      if (!want_game)
      {
        // FIXME: N'utilise pas encore la minimisation car n'est pas splitté.
        auto [simp_aut, code] = try_create_strategy_from_simple(*sub_f, *sub_o, extra_options, gi);
        if (code == -1)
        {
          std::cout << "UNREALIZABLE" << std::endl;
          // FIXME: C'est quoi la valeur de retour ?
          if (opt_real)
            return (int)!is_winning;
        }
        else if (simp_aut != nullptr)
        {
          //Unused fix
          unsigned n_before_ = simp_aut->num_states();
          bool do_split = 3 <= extra_options.get("minimization-level", 1);
          if (do_split)
            split_fast_here(simp_aut);
          minimize_strategy_here(simp_aut, extra_options);
          if (do_split)
            simp_aut = spot::unsplit_2step(simp_aut);
          if (simp_aut->num_states() < n_before_)
            std::cout << "### Direct sim red " << n_before_ << " -> " << simp_aut->num_states() << "\n";
          strategies.push_back(simp_aut);
          continue;
        }
      }
      // 1) We create a game
      auto arena = spot::create_game(*sub_f, *sub_o, extra_options, gi);
      arenas.push_back(arena);
      if (gi.bv)
      {
        gi.bv->nb_states_arena += arena->num_states();
        auto spptr = arena->get_named_prop<std::vector<bool>>("state-player");
        assert(spptr);
        gi.bv->nb_states_arena_env +=
            std::count(spptr->cbegin(), spptr->cend(), false);
        assert((spptr->at(arena->get_init_state_number()) == false)
               && "Env needs first turn");
      }

      // 2) If the goal is to show the game, we do the product
      if (want_game)
      {
        if (game_prod == nullptr)
          game_prod = arena;
        else
          game_prod = spot::product(game_prod, arena);
      }
      else
      {
        // 3) Otherwise, we solve the game…
        is_winning = (int) spot::solve_game(arena, gi);
        if (gi.bv)
          gi.bv->realizable &= is_winning;
        // 4) If this part is not realizable, we can stop
        if (!is_winning)
          break;
      }
    }

    if (!want_game)
      std::cout << (is_winning ? "REALIZABLE" : "UNREALIZABLE") << std::endl;
    if (gi.bv)
      gi.bv->realizable = is_winning;

    if (opt_real)
      return (int) !is_winning;
    else if (want_game)
    {
      spot::alternate_players(game_prod);
      if (opt_print_pg)
        pg_print(std::cout, game_prod);
      else
        spot::print_hoa(std::cout, game_prod, opt_print_hoa_args) << '\n';
      return 0;
    }

    ///////////// AU DESSUS C'EST CA REECRIT
    // std::vector<spot::twa_graph_ptr> strategies(sub_form.size(), nullptr);

    // auto sub_f = sub_form.begin();
    // auto sub_o = sub_outs.begin();
    // for (; sub_f != sub_form.end(); ++sub_f, ++sub_o)
    // {
    //   std::set<std::string> ao;
    //   std::for_each(sub_o->begin(), sub_o->end(),
    //                  [&ao](auto& af){ao.insert(af.ap_name());});
    //   auto arena = spot::create_game(*sub_f, ao, extra_options, gi);
    //   arenas.push_back(arena);
    //   if (gi.bv)
    //     gi.bv->nb_states_arena += arena->num_states();
    // }

    // if (want_game)
    // {
    //   spot::twa_graph_ptr arena = arenas.front();
    //   for (size_t i = 1; i < arenas.size(); ++i)
    //     arena = spot::product(arena, arenas[i]);
    //   spot::alternate_players(arena, false, false);
    //   if (opt_print_pg)
    //     pg_print(std::cout, arena);
    //   else
    //     spot::print_hoa(std::cout, arena, opt_print_hoa_args) << '\n';
    //   safe_tot_time();
    //   return 0;
    // }

    // if (gi.bv)
    //   gi.bv->realizable = true;
    // for (auto& arena : arenas)
    // {
    //   is_winning = (int) spot::solve_game(arena, gi);
    //   if (gi.bv)
    //     gi.bv->realizable &= is_winning;
    //   // If one of the arenas is unrealizable, there is no need to
    //   // process the others
    //   if (!is_winning)
    //     break;
    // }
    // We need a solved game
    // std::cout << (is_winning ? "REALIZABLE" : "UNREALIZABLE") << std::endl;
    // if (opt_real)
    //   {
    //     safe_tot_time();
    //     return (int) not is_winning;
    //   }
    // From here on we need the strat if winning
    if (is_winning)
      {
        //Negated specification if verify is demanded
        spot::twa_graph_ptr neg_spec = nullptr;
        if (opt_do_verify)
        {
          // TODO: Là on traduit avec les mêmes options que celles qui permettent
          // de traduire la formule LTL de départ. On considère ça comme un
          // équilibre entre taille de l'automate et vitesse. Là la taille est
          // peut être moins importante, on pourrait chercher à traduire plus vite.
          spot::translator trans(gi.dict, &extra_options);
          neg_spec = trans.run(spot::formula::Not(f));
        }
        spot::twa_graph_ptr tot_strat;
        for (const auto& arena : arenas)
          // We need the strategy automaton
          strategies.push_back(spot::create_strategy(arena, extra_options, gi));

        spot::aig_ptr saig;
        if (opt_print_aiger)
        {
          if (strategies.size() != 1)
            std::cerr << "#### nstrats " << strategies.size() << "\n";
          spot::stopwatch sw2;
          if (gi.bv)
            sw2.start();
          saig = spot::strategies_to_aig(strategies, opt_print_aiger,
                                         input_aps,
                                         sub_outs_str);
          if (gi.bv)
            {
              gi.bv->aig_time = sw2.stop();
              gi.bv->nb_latches = saig->num_latches();
              gi.bv->nb_gates = saig->num_gates();
            }
          spot::print_aiger(std::cout, saig);
        }
        else
        {
          spot::process_timer timer;
          automaton_printer printer;
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
                std::cout << "c\nCircuit was verified\n";
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
      else
        // ltlsynt has an option minimization-level not used when the
        // specification is unrealizable. We need to "use" this option
        // so that report_unused_option does not pose a problem.
        extra_options.get("minimization-level");
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

      auto res = processor.run();
      // Diagnose unused -x options
      // FIXME:
      // extra_options.report_unused_options();
      return res;
    });
}
