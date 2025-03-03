// -*- coding: utf-8 -*-
// Copyright (C) by the Spot authors, see the AUTHORS file for details.
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
#include "common_hoaread.hh"
#include "common_setup.hh"
#include "common_sys.hh"
#include "common_trans.hh"
#include "common_ioap.hh"

#include <spot/misc/bddlt.hh>
#include <spot/misc/escape.hh>
#include <spot/misc/timer.hh>
#include <spot/priv/robin_hood.hh>
#include <spot/tl/formula.hh>
#include <spot/tl/apcollect.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/aiger.hh>
#include <spot/twaalgos/game.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/dot.hh>
#include <spot/twaalgos/minimize.hh>
#include <spot/twaalgos/mealy_machine.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/synthesis.hh>
#include <spot/twaalgos/translate.hh>

enum
{
  OPT_AIGER = 256,
  OPT_ALGO,
  OPT_BYPASS,
  OPT_CSV_WITH_FORMULA,
  OPT_CSV_WITHOUT_FORMULA,
  OPT_DECOMPOSE,
  OPT_DOT,
  OPT_FROM_PGAME,
  OPT_GEQUIV,
  OPT_HIDE,
  OPT_INPUT,
  OPT_OUTPUT,
  OPT_PART_FILE,
  OPT_POLARITY,
  OPT_PRINT,
  OPT_PRINT_HOA,
  OPT_REAL,
  OPT_SIMPLIFY,
  OPT_SPLITTYPE,
  OPT_TLSF,
  OPT_VERBOSE,
  OPT_VERIFY
};

static const argp_option options[] =
  {
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Input options:", 1 },
    { "outs", OPT_OUTPUT, "PROPS", 0,
      "comma-separated list of controllable (a.k.a. output) atomic"
      " propositions, , interpreted as a regex if enclosed in slashes", 0 },
    { "ins", OPT_INPUT, "PROPS", 0,
      "comma-separated list of uncontrollable (a.k.a. input) atomic"
      " propositions, interpreted as a regex if enclosed in slashes", 0 },
    { "part-file", OPT_PART_FILE, "FILENAME", 0,
      "read the I/O partition of atomic propositions from FILENAME", 0 },
    { "tlsf", OPT_TLSF, "FILENAME", 0,
      "Read a TLSF specification from FILENAME, and call syfco to "
      "convert it into LTL", 0 },
    { "from-pgame", OPT_FROM_PGAME, "FILENAME", 0,
      "Read a parity game in Extended HOA format instead of building it.",
      0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Fine tuning:", 10 },
    { "algo", OPT_ALGO, "sd|ds|ps|lar|lar.old|acd", 0,
      "choose the algorithm for synthesis:"
      " \"sd\": translate to tgba, split, then determinize;"
      " \"ds\": translate to tgba, determinize, then split;"
      " \"ps\": translate to dpa, then split;"
      " \"lar\": translate to a deterministic automaton with arbitrary"
      " acceptance condition, then use LAR to turn to parity,"
      " then split (default);"
      " \"lar.old\": old version of LAR, for benchmarking;"
      " \"acd\": translate to a deterministic automaton with arbitrary"
      " acceptance condition, then use ACD to turn to parity,"
      " then split.\n", 0 },
    { "bypass", OPT_BYPASS, "yes|no", 0,
      "whether to try to avoid to construct a parity game "
      "(enabled by default)", 0},
    { "decompose", OPT_DECOMPOSE, "yes|no", 0,
      "whether to decompose the specification as multiple output-disjoint "
      "problems to solve independently (enabled by default)", 0 },
    { "polarity", OPT_POLARITY, "yes|no|before-decompose", 0,
      "whether to remove atomic propositions that always have the same "
      "polarity in the formula to speed things up (enabled by default, "
      "both before and after decomposition)", 0 },
    { "global-equivalence", OPT_GEQUIV, "yes|no|before-decompose", 0,
      "whether to remove atomic propositions that are always equivalent to "
      "another one (enabled by default, both before and after decomposition)",
      0 },
    { "simplify", OPT_SIMPLIFY, "no|bisim|bwoa|sat|bisim-sat|bwoa-sat", 0,
      "simplification to apply to the controller (no) nothing, "
      "(bisim) bisimulation-based reduction, (bwoa) bisimulation-based "
      "reduction with output assignment, (sat) SAT-based minimization, "
      "(bisim-sat) SAT after bisim, (bwoa-sat) SAT after bwoa.  Defaults "
      "to 'bwoa'.", 0 },
    { "splittype", OPT_SPLITTYPE, "expl|semisym|fullysym|auto", 0,
      "Selects the algorithm to use to transform the automaton into "
      "a game graph. Defaults to 'auto'.", 0},
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Output options:", 20 },
    { "print-pg", OPT_PRINT, nullptr, 0,
      "print the parity game in the pgsolver format, do not solve it", 0 },
    { "print-game-hoa", OPT_PRINT_HOA, "options", OPTION_ARG_OPTIONAL,
      "print the parity game in the HOA format, do not solve it", 0 },
    { "realizability", OPT_REAL, nullptr, 0,
      "realizability only, do not compute a winning strategy", 0 },
    { "aiger", OPT_AIGER, "ite|isop|both[+ud][+dc]"
                                 "[+sub0|sub1|sub2]", OPTION_ARG_OPTIONAL,
      "encode the winning strategy as an AIG circuit and print it in AIGER"
      " format. The first word indicates the encoding to used: \"ite\" for "
      "If-Then-Else normal form; "
      "\"isop\" for irreducible sum of products; "
      "\"both\" tries both and keeps the smaller one. "
      "Other options further "
      "refine the encoding, see aiger::encode_bdd. Defaults to \"ite\".", 0 },
    { "dot", OPT_DOT, "options", OPTION_ARG_OPTIONAL,
      "Use dot format when printing the result (game, strategy, or "
      "AIG circuit, depending on other options).  The options that "
      "may be passed to --dot depend on the nature of what is printed. "
      "For games and strategies, standard automata rendering "
      "options are supported (e.g., see ltl2tgba --dot).  For AIG circuit, "
      "use (h) for horizontal and (v) for vertical layouts.", 0 },
    { "csv", OPT_CSV_WITHOUT_FORMULA, "[>>]FILENAME", OPTION_ARG_OPTIONAL,
      "output statistics as CSV in FILENAME or on standard output "
      "(if '>>' is used to request append mode, the header line is "
      "not output)", 0 },
    { "csv-without-formula", 0, nullptr, OPTION_ALIAS, nullptr, 0 },
    { "csv-with-formula", OPT_CSV_WITH_FORMULA, "[>>]FILENAME",
      OPTION_ARG_OPTIONAL,
      "like --csv, but with an additional 'fomula' column", 0 },
    { "hide-status", OPT_HIDE, nullptr, 0,
      "Hide the REALIZABLE or UNREALIZABLE line.  (Hint: exit status "
      "is enough of an indication.)", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Miscellaneous options:", -1 },
    { "extra-options", 'x', "OPTS", 0,
        "fine-tuning options (see spot-x (7))", 0 },
    { "verbose", OPT_VERBOSE, nullptr, 0, "verbose mode", 0 },
    { "verify", OPT_VERIFY, nullptr, 0,
       "verify the strategy or (if demanded) AIG against the formula", 0 },
    { nullptr, 0, nullptr, 0, nullptr, 0 },
  };

static const struct argp_child children[] =
  {
    { &finput_argp_headless, 0, nullptr, 0 },
    { &aoutput_argp, 0, nullptr, 0 },
    { &misc_argp, 0, nullptr, 0 },
    { nullptr, 0, nullptr, 0 }
  };

static const char argp_program_doc[] = "\
Synthesize a controller from its LTL specification.\v\
Exit status:\n\
  0   if all input problems were realizable\n\
  1   if at least one input problem was not realizable\n\
  2   if any error has been reported";

static const char* opt_csv = nullptr;
static bool opt_csv_with_formula = true;
static bool opt_print_pg = false;
static bool opt_print_hoa = false;
static const char* opt_print_hoa_args = nullptr;
static bool opt_real = false;
static bool opt_do_verify = false;
static const char* opt_aiger = nullptr;
static const char* opt_dot_arg = nullptr;
static bool opt_dot = false;
static spot::synthesis_info* gi;
static bool show_status = true;

static char const *const algo_names[] =
  {
   "ds",
   "sd",
   "ps",
   "lar",
   "lar.old",
   "acd",
  };

static char const *const algo_args[] =
{
  "detsplit", "ds",
  "splitdet", "sd",
  "dpasplit", "ps",
  "lar",
  "lar.old",
  "acd",
  nullptr
};
static spot::synthesis_info::algo const algo_types[] =
{
  spot::synthesis_info::algo::DET_SPLIT, spot::synthesis_info::algo::DET_SPLIT,
  spot::synthesis_info::algo::SPLIT_DET, spot::synthesis_info::algo::SPLIT_DET,
  spot::synthesis_info::algo::DPA_SPLIT, spot::synthesis_info::algo::DPA_SPLIT,
  spot::synthesis_info::algo::LAR,
  spot::synthesis_info::algo::LAR_OLD,
  spot::synthesis_info::algo::ACD,
};
ARGMATCH_VERIFY(algo_args, algo_types);

static const char* const bypass_args[] =
  {
    "yes", "true", "enabled", "1",
    "no", "false", "disabled", "0",
    nullptr
  };
static bool bypass_values[] =
  {
    true, true, true, true,
    false, false, false, false,
  };
ARGMATCH_VERIFY(bypass_args, bypass_values);
bool opt_bypass = true;

static const char* const decompose_args[] =
  {
    "yes", "true", "enabled", "1",
    "no", "false", "disabled", "0",
    nullptr
  };
static bool decompose_values[] =
  {
    true, true, true, true,
    false, false, false, false,
  };
ARGMATCH_VERIFY(decompose_args, decompose_values);
static const char* const polarity_args[] =
  {
    "yes", "true", "enabled", "1",
    "no", "false", "disabled", "0",
    "before-decompose",
    nullptr
  };
enum polarity_choice { pol_no, pol_yes, pol_before_decompose };
static polarity_choice polarity_values[] =
  {
    pol_yes, pol_yes, pol_yes, pol_yes,
    pol_no, pol_no, pol_no, pol_no,
    pol_before_decompose
  };
ARGMATCH_VERIFY(polarity_args, polarity_values);

bool opt_decompose_ltl = true;
polarity_choice opt_polarity = pol_yes;
polarity_choice opt_gequiv = pol_yes;

static const char* const simplify_args[] =
  {
    "no", "false", "disabled", "0",
    "bisim", "1",
    "bwoa", "bisim-with-output-assignment", "2",
    "sat", "3",
    "bisim-sat", "4",
    "bwoa-sat", "5",
    nullptr
  };
static unsigned simplify_values[] =
  {
    0, 0, 0, 0,
    1, 1,
    2, 2, 2,
    3, 3,
    4, 4,
    5, 5,
  };
ARGMATCH_VERIFY(simplify_args, simplify_values);

static const char* const splittype_args[] =
  {
    "auto",
    "expl",
    "semisym",
    "fullysym",
    nullptr
  };
static spot::synthesis_info::splittype splittype_values[] =
  {
    spot::synthesis_info::splittype::AUTO,
    spot::synthesis_info::splittype::EXPL,
    spot::synthesis_info::splittype::SEMISYM,
    spot::synthesis_info::splittype::FULLYSYM,
  };
ARGMATCH_VERIFY(splittype_args, splittype_values);

namespace
{
  static bool want_game()
  {
    return opt_print_pg || opt_print_hoa;
  }

  static void
  dispatch_print_hoa(spot::twa_graph_ptr& game,
                     const spot::realizability_simplifier* rs = nullptr)
  {
    // Add any AP we removed. This is a game, so player moves are
    // separated.  Consequently at this point we cannot deal with
    // removed signals such as "o1 <-> i2": if the game has to be
    // printed, we can only optimize for signals such as o1 <-> o2.
    if (rs)
      rs->patch_game(game);

    if (opt_dot)
      spot::print_dot(std::cout, game, opt_dot_arg);
    else if (opt_print_pg)
      spot::print_pg(std::cout, game);
    else
      spot::print_hoa(std::cout, game, opt_print_hoa_args) << '\n';
  }


  // If filename is passed, it is printed instead of the formula.  We
  // use that when processing games since we have no formula to print.
  // It would be cleaner to have two columns: one for location (that's
  // filename + line number if known), and one for formula (if known).
  static void
  print_csv(const spot::formula& f, const char* filename, bool was_game)
  {
    auto& vs = gi->verbose_stream;
    auto& bv = gi->bv;
    if (!bv)
      error(2, 0, "no information available for csv (please report bug)");
    if (vs)
      *vs << "writing CSV to " << opt_csv << '\n';

    static bool not_first_time = false;
    output_file outf(opt_csv, not_first_time);
    not_first_time = true;      // force append on next print.
    std::ostream& out = outf.ostream();

    // Do not output the header line if we append to a file.
    // (Even if that file was empty initially.)
    if (!outf.append())
      {
        out << "source";
        if (opt_csv_with_formula)
          out << ",formula";
        if (!was_game)
          {
            out << ",subspecs";
            out << ",algo";
          }
        out << ",split,total_time";
        if (!was_game)
          out << ",sum_trans_time";
        out << ",sum_split_time";
        if (!was_game)
          out << ",sum_todpa_time";
        if (!opt_print_pg && !opt_print_hoa)
          {
            out << ",sum_solve_time";
            if (!opt_real)
              out << ",sum_strat2aut_time";
            if (opt_aiger)
              out << ",aig_time";
            out << ",realizable"; //-1: Unknown, 0: Unreal, 1: Real
          }
        if (!was_game)
          out << (",max_trans_states,max_trans_edges"
                  ",max_trans_colors,max_trans_ap");
        out << ",max_game_states,max_game_colors";
        if (!opt_real)
          {
            out << ",max_strat_states,max_strat_edges";
            if (!was_game)
              out << ",sum_strat_states,sum_strat_edges";
            out << ",max_simpl_strat_states,max_simpl_strat_edges";
            if (!was_game)
              out << ",sum_simpl_strat_states,sum_simpl_strat_edges";
          }
        if (opt_aiger)
          out << ",aig_latches,aig_gates";
        out << '\n';
      }
    {
      std::ostringstream os;
      if (filename)
        {
          os << filename;
          spot::escape_rfc4180(out << '"', os.str()) << '"';
          os.str("");
          os.clear();
        }
      out << ',';
      if (opt_csv_with_formula)
        {
          if (was_game)
            os << filename;
          else
            os << f;
          spot::escape_rfc4180(out << '"', os.str()) << "\",";
        }
    }
    if (!was_game)
      {
        out << bv->sub_specs << ',';
        out << algo_names[(int) gi->s] << ',';
      }
    out << splittype_args[(int) gi->sp] << ',' << bv->total_time;
    if (!was_game)
      out << ',' << bv->sum_trans_time;
    out << ',' << bv->sum_split_time;
    if (!was_game)
      out << ',' << bv->sum_paritize_time;
    if (!opt_print_pg && !opt_print_hoa)
      {
        out << ',' << bv->sum_solve_time;
        if (!opt_real)
          out << ',' << bv->sum_strat2aut_time;
        if (opt_aiger)
          out << ',' << bv->aig_time;
        out << ',' << bv->realizable;
      }
    if (!was_game)
      out << ',' << bv->max_trans_states
          << ',' << bv->max_trans_edges
          << ',' << bv->max_trans_colors
          << ',' << bv->max_trans_ap;
    out << ',' << bv->max_game_states
        << ',' << bv->max_game_colors;
    if (!opt_real)
      {
        out << ',' << bv->max_strat_states
            << ',' << bv->max_strat_edges;
        if (!was_game)
          out << ',' << bv->sum_strat_states
              << ',' << bv->sum_strat_edges;
        out << ',' << bv->max_simpl_strat_states
            << ',' << bv->max_simpl_strat_edges;
        if (!was_game)
          out << ',' << bv->sum_simpl_strat_states
              << ',' << bv->sum_simpl_strat_edges;
      }
    if (opt_aiger)
      out << ',' << bv->aig_latches
          << ',' << bv->aig_gates;
    out << '\n';
    outf.close(opt_csv);
  }

  static int
  solve_formula(spot::formula original_f,
                const std::vector<std::string>& input_aps,
                const std::vector<std::string>& output_aps)
  {
    spot::formula f = original_f;
    if (opt_csv)              // reset benchmark data
      gi->bv = spot::synthesis_info::bench_var();
    spot::stopwatch sw;
    if (gi->bv)
      sw.start();

    auto safe_tot_time = [&]()
    {
      if (gi->bv)
        gi->bv->total_time = sw.stop();
    };

    // Attempt to remove superfluous atomic propositions
    spot::realizability_simplifier* rs = nullptr;
    if (opt_polarity != pol_no || opt_gequiv != pol_no)
      {
        unsigned opt = 0;
        if (opt_polarity != pol_no)
          opt |= spot::realizability_simplifier::polarity;
        if (opt_gequiv != pol_no)
          {
            if (want_game())
              opt |= spot::realizability_simplifier::global_equiv_output_only;
            else
              opt |= spot::realizability_simplifier::global_equiv;
          }
        rs =
          new spot::realizability_simplifier(original_f, input_aps, opt,
                                             gi ? gi->verbose_stream : nullptr);
        f = rs->simplified_formula();
      }

    std::vector<spot::formula> sub_form;
    std::vector<std::set<spot::formula>> sub_outs;
    if (opt_decompose_ltl)
    {
      auto subs = split_independent_formulas(f, output_aps);
      if (gi->verbose_stream)
        {
          *gi->verbose_stream << "there are "
                              << subs.first.size()
                              << " subformulas\n";
        }
      if (subs.first.size() > 1)
        {
          sub_form = subs.first;
          sub_outs = subs.second;
        }
    }
    // When trying to split the formula, we can apply transformations that
    // increase its size. This is why we will use the original formula if it
    // has not been cut.
    if (sub_form.empty())
      {
        sub_form = { f };
        sub_outs.resize(1);
        if (rs)
          {
            robin_hood::unordered_set<spot::formula> removed_outputs;
            for (auto [from, from_is_input, to] : rs->get_mapping())
              {
                (void) to;
                if (!from_is_input)
                  removed_outputs.insert(from);
              }
            for (const std::string& apstr: output_aps)
              {
                spot::formula ap = spot::formula::ap(apstr);
                if (removed_outputs.find(ap) == removed_outputs.end())
                  sub_outs[0].insert(ap);
              }
          }
        else
          {
            for (const std::string& apstr: output_aps)
              sub_outs[0].insert(spot::formula::ap(apstr));
          }

      }
    if (gi->bv)
      gi->bv->sub_specs = sub_form.size();
    std::vector<std::vector<std::string>> sub_outs_str;
    std::transform(sub_outs.begin(), sub_outs.end(),
                   std::back_inserter(sub_outs_str),
                   [](const auto& forms) {
                     std::vector<std::string> r;
                     r.reserve(forms.size());
                     for (auto f: forms)
                       r.push_back(f.ap_name());
                     return r;
                   });

    assert((sub_form.size() == sub_outs.size())
           && (sub_form.size() == sub_outs_str.size()));

    std::vector<spot::twa_graph_ptr> arenas;

    auto sub_f = sub_form.begin();
    auto sub_o = sub_outs_str.begin();
    std::vector<spot::mealy_like> mealy_machines;
    unsigned numsubs = sub_form.size();

    for (; sub_f != sub_form.end(); ++sub_f, ++sub_o)
    {
      spot::mealy_like m_like
              {
                spot::mealy_like::realizability_code::UNKNOWN,
                nullptr,
                bddfalse
              };

      if (numsubs > 1 && (opt_polarity == pol_yes || opt_gequiv == pol_yes))
        {
          unsigned opt = 0;
          if (opt_polarity == pol_yes)
            opt |= spot::realizability_simplifier::polarity;
          if (opt_gequiv == pol_yes)
            {
              if (want_game())
                opt |= spot::realizability_simplifier::global_equiv_output_only;
              else
                opt |= spot::realizability_simplifier::global_equiv;
            }
          if (gi->verbose_stream)
            *gi->verbose_stream << "working on subformula " << *sub_f << '\n';
          spot::realizability_simplifier rsub(*sub_f, input_aps, opt,
                                              gi ?
                                              gi->verbose_stream : nullptr);
          *sub_f = rsub.simplified_formula();
          rs->merge_mapping(rsub);
        }

      // If we want to print a game,
      // we never use the direct approach
      if (!want_game() && opt_bypass)
        m_like =
            spot::try_create_direct_strategy(*sub_f, *sub_o, *gi, !opt_real);

      switch (m_like.success)
      {
      case spot::mealy_like::realizability_code::UNREALIZABLE:
        {
          if (show_status)
            std::cout << "UNREALIZABLE" << std::endl;
          safe_tot_time();
          return 1;
        }
      case spot::mealy_like::realizability_code::UNKNOWN:
        {
          auto arena = spot::ltl_to_game(*sub_f, *sub_o, *gi);
#ifndef NDEBUG
          auto spptr =
            arena->get_named_prop<std::vector<bool>>("state-player");
          assert(spptr);
          assert((spptr->at(arena->get_init_state_number()) == false)
                 && "Env needs first turn");
#endif
          if (gi->bv)
            {
              unsigned ns = arena->num_states();
              unsigned nc = arena->num_sets();
              if (std::tie(gi->bv->max_game_states, gi->bv->max_game_colors)
                  < std::tie(ns, nc))
                {
                  gi->bv->max_game_states = ns;
                  gi->bv->max_game_colors = nc;
                }
            }
          if (want_game())
            {
              dispatch_print_hoa(arena, rs);
              continue;
            }
          if (!spot::solve_game(arena, *gi))
            {
              if (show_status)
                std::cout << "UNREALIZABLE" << std::endl;
              safe_tot_time();
              return 1;
            }
          // Create the (partial) strategy
          // only if we need it
          if (!opt_real)
            {
              spot::mealy_like ml;
              ml.success =
                spot::mealy_like::realizability_code::REALIZABLE_REGULAR;
              // By default this produces a split machine
              ml.mealy_like =
                  spot::solved_game_to_mealy(arena, *gi);
              // Keep the machine split for aiger
              // else -> separated
              spot::simplify_mealy_here(ml.mealy_like, *gi, opt_aiger);
              ml.glob_cond = bddfalse;
              mealy_machines.push_back(ml);
            }
          break;
        }
      case spot::mealy_like::realizability_code::REALIZABLE_REGULAR:
        {
          // the direct approach yielded a strategy
          // which can now be minimized
          // We minimize only if we need it
          assert(opt_real ||
            (m_like.mealy_like && "Expected success but found no mealy!"));
          if (!opt_real)
            {
              // Keep the machine split for aiger
              // else -> separated
              spot::simplify_mealy_here(m_like.mealy_like, *gi, opt_aiger);
            }
          SPOT_FALLTHROUGH;
        }
      case spot::mealy_like::realizability_code::REALIZABLE_DTGBA:
        if (!opt_real)
          mealy_machines.push_back(m_like);
        break;
      default:
        error(2, 0, "unexpected success code during mealy machine generation "
              "(please send bug report)");
      }
    }
    if (gi->bv)
      gi->bv->realizable = true;

    // If we only wanted to print the game we are done
    if (want_game())
      {
        safe_tot_time();
        return 0;
      }

    if (show_status)
      std::cout << "REALIZABLE" << std::endl;
    if (opt_real)
      {
        safe_tot_time();
        return 0;
      }
    // If we reach this line
    // a strategy was found for each subformula
    assert(mealy_machines.size() == sub_form.size()
           && ("There are subformula for which no mealy like object"
               " has been created."));

    spot::aig_ptr saig = nullptr;
    spot::twa_graph_ptr tot_strat = nullptr;
    automaton_printer printer;
    spot::process_timer timer_printer_dummy;

    if (opt_aiger)
      {
        spot::stopwatch sw2;
        if (gi->bv)
          sw2.start();
        saig = spot::mealy_machines_to_aig(mealy_machines, opt_aiger,
                                           input_aps, sub_outs_str, rs);
        if (gi->bv)
          {
            gi->bv->aig_time = sw2.stop();
            gi->bv->aig_latches = saig->num_latches();
            gi->bv->aig_gates = saig->num_gates();
          }
        if (gi->verbose_stream)
          {
            *gi->verbose_stream << "AIG circuit was created in "
                               << gi->bv->aig_time
                               << " seconds and has " << saig->num_latches()
                               << " latches and "
                               << saig->num_gates() << " gates\n";
          }
        if (opt_dot)
          spot::print_dot(std::cout, saig, opt_dot_arg);
        else if (automaton_format != Quiet)
          spot::print_aiger(std::cout, saig) << '\n';
      }
    else
      {
        assert(std::all_of(
           mealy_machines.begin(), mealy_machines.end(),
           [](const auto& ml)
           {return ml.success ==
               spot::mealy_like::realizability_code::REALIZABLE_REGULAR; })
               && "ltlsynt: Cannot handle TGBA as strategy.");
        tot_strat = mealy_machines.front().mealy_like;
        for (size_t i = 1; i < mealy_machines.size(); ++i)
          tot_strat = spot::mealy_product(tot_strat,
                                          mealy_machines[i].mealy_like);
        if (rs)        // Add any AP we removed
          rs->patch_mealy(tot_strat);
        printer.print(tot_strat, timer_printer_dummy);
      }

    // Final step: Do verification if demanded
    if (!opt_do_verify)
      {
        safe_tot_time();
        return 0;
      }


    // TODO: different options to speed up verification?!
    spot::translator trans(gi->dict, &gi->opt);
    auto neg_spec = trans.run(spot::formula::Not(original_f));
    if (saig)
      {
        // Test the aiger
        auto saigaut = saig->as_automaton(false);
        if (neg_spec->intersects(saigaut))
          error(2, 0, "Aiger and negated specification do intersect: "
                "circuit is not OK.");
        std::cout << "c\nCircuit was verified\n";
      }
    else if  (tot_strat)
      {
        // Test the strategy
        if (neg_spec->intersects(tot_strat))
          error(2, 0, "Strategy and negated specification do intersect: "
                "strategy is not OK.");
        std::cout << "/*Strategy was verified*/\n";
      }
    // Done

    safe_tot_time();
    return 0;
  }


  class ltl_processor final : public job_processor
  {
  public:
    ltl_processor()
    {
    }

    int process_formula(spot::formula f,
                        const char* filename, int linenum) override
    {
      auto [input_aps, output_aps] =
        filter_list_of_aps(f, filename, linenum);
      int res = solve_formula(f, input_aps, output_aps);
      if (opt_csv)
        {
          if (!filename || linenum <= 0)
            {
              print_csv(f, filename, false);
            }
          else
            {
              std::ostringstream os;
              os << filename << ':' << linenum;
              print_csv(f, os.str().c_str(), false);
            }
        }
      return res;
    }

    int
    process_tlsf_file(const char* filename) override
    {
      static char arg0[] = "syfco";
      static char arg1[] = "-f";
      static char arg2[] = "ltlxba";
      static char arg3[] = "-m";
      static char arg4[] = "fully";
      char* command[] = { arg0, arg1, arg2, arg3, arg4,
                          const_cast<char*>(filename), nullptr };
      std::string tlsf_string = read_stdout_of_command(command);

      // The set of atomic proposition will be temporary set to those
      // given by syfco, unless they were forced from the command-line.
      bool reset_aps = false;
      if (!all_input_aps.has_value() && !all_output_aps.has_value())
        {
          reset_aps = true;
          static char arg5[] = "--print-output-signals";
          char* command[] = { arg0, arg5,
                              const_cast<char*>(filename), nullptr };
          std::string res = read_stdout_of_command(command);

          all_output_aps.emplace(std::vector<std::string>{});
          split_aps(res, *all_output_aps);
          for (const std::string& a: *all_output_aps)
            identifier_map.emplace(a, true);
        }
      int res = process_string(tlsf_string, filename);
      if (reset_aps)
        {
          all_output_aps.reset();
          identifier_map.clear();
        }
      return res;
    }

    int process_pgame(spot::twa_graph_ptr arena,
                      const std::string& location)
    {
      if (opt_csv)              // reset benchmark data
        {
          gi->bv = spot::synthesis_info::bench_var();
          gi->bv->sub_specs = 1;  // We do not know how to split a game
        }
      spot::stopwatch sw_global;
      spot::stopwatch sw_local;
      if (gi->bv)
        {
          sw_global.start();
          sw_local.start();
        }
      if (!arena->get_named_prop<bdd>("synthesis-outputs"))
        {
          std::cerr << location << ": controllable-AP is not specified\n";
          return 2;
        }
      if (!arena->get_named_prop<std::vector<bool>>("state-player"))
        arena = spot::split_2step(arena, gi);
      else
        {
          // Check if the game is alternating and fix trivial cases
          const unsigned N = arena->num_states();
          // Can not use get_state_players because we need a non-const version
          auto spptr =
            arena->get_named_prop<std::vector<bool>>("state-player");
          assert(spptr);
          const bdd& outs = get_synthesis_outputs(arena);
          for (unsigned n = 0; n < N; ++n)
            {
              const bool p = (*spptr)[n];
              for (auto& e : arena->out(n))
                {
                  if (p != (*spptr)[e.dst])
                    continue; // All good
                  // Check if the condition is a simply conjunction of input and
                  // output. If so insert an intermediate state
                  // This also covers trivial self-loops
                  bdd cond = e.cond;
                  bdd i_cond = bdd_exist(cond, outs);
                  bdd o_cond = bdd_existcomp(cond, outs);
                  if ((i_cond & o_cond) == cond)
                    {
                      unsigned inter = arena->new_state();
                      spptr->push_back(!p);
                      e.cond = p ? o_cond : i_cond;
                      e.dst = inter;
                      arena->new_edge(inter, e.dst, !p ? o_cond : i_cond);
                    }
                  else
                    throw std::runtime_error("ltlsynt: given parity game is not"
                      "alternating and not trivially fixable!");
                }
            }
        }
      if (gi->bv)
        {
          gi->bv->sum_split_time += sw_local.stop();
          gi->bv->max_game_states = arena->num_states();
          gi->bv->max_game_colors = arena->num_sets();
        }
      if (opt_print_pg || opt_print_hoa)
        {
          dispatch_print_hoa(arena);
          return 0;
        }
      auto safe_tot_time = [&]() {
        if (gi->bv)
          gi->bv->total_time = sw_global.stop();
      };
      if (!spot::solve_game(arena, *gi))
        {
          if (show_status)
            std::cout << "UNREALIZABLE" << std::endl;
          safe_tot_time();
          return 1;
        }
      if (gi->bv)
        gi->bv->realizable = true;
      if (show_status)
        std::cout << "REALIZABLE" << std::endl;
      if (opt_real)
        {
          safe_tot_time();
          return 0;
        }
      sw_local.start();
      spot::twa_graph_ptr mealy_like =
        spot::solved_game_to_mealy(arena, *gi);
      // Keep the machine split for aiger otherwise, separate it.
      spot::simplify_mealy_here(mealy_like, *gi, opt_aiger);

      automaton_printer printer;
      spot::process_timer timer_printer_dummy;
      if (opt_aiger)
        {
          if (gi->bv)
            sw_local.start();
          spot::aig_ptr saig =
            spot::mealy_machine_to_aig(mealy_like, opt_aiger);
          if (gi->bv)
            {
              gi->bv->aig_time = sw_local.stop();
              gi->bv->aig_latches = saig->num_latches();
              gi->bv->aig_gates = saig->num_gates();
            }
          if (gi->verbose_stream)
            {
              *gi->verbose_stream << "AIG circuit was created in "
                                  << gi->bv->aig_time
                                  << " seconds and has " << gi->bv->aig_latches
                                  << " latches and "
                                  << gi->bv->aig_gates << " gates\n";
            }
          if (automaton_format != Quiet)
            spot::print_aiger(std::cout, saig) << '\n';
        }
      else
        {
          printer.print(mealy_like, timer_printer_dummy);
        }
      safe_tot_time();
      return 0;
    }

    int
    process_aut_file(const char* filename) override
    {
      spot::automaton_stream_parser hp(filename);
      int err = 0;
      while (!abort_run)
        {
          spot::parsed_aut_ptr haut = hp.parse(spot::make_bdd_dict());
          if (!haut->aut && haut->errors.empty())
            break;
          if (haut->format_errors(std::cerr))
            err = 2;
          if (!haut->aut /*|| (err && abort_on_error_)*/)
            {
              error(2, 0, "failed to read automaton from %s",
                    haut->filename.c_str());
            }
          else if (haut->aborted)
            {
              std::cerr << haut->filename << ':' << haut->loc
                        << ": aborted input automaton\n";
              err = std::max(err, 2);
            }
          else
            {
              std::ostringstream os;
              os << haut->filename << ':' << haut->loc;
              std::string loc = os.str();
              int res = process_pgame(haut->aut, loc);
              if (res < 2 && opt_csv)
                print_csv(nullptr, loc.c_str(), true);
              err = std::max(err, res);
            }
        }
      return err;
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
      gi->s = XARGMATCH("--algo", arg, algo_args, algo_types);
      break;
    case OPT_BYPASS:
      opt_bypass = XARGMATCH("--bypass", arg, bypass_args, bypass_values);
      break;
    case OPT_CSV_WITH_FORMULA:
      opt_csv = arg ? arg : "-";
      opt_csv_with_formula = true;
      break;
    case OPT_CSV_WITHOUT_FORMULA:
      opt_csv = arg ? arg : "-";
      opt_csv_with_formula = false;
      break;
    case OPT_DECOMPOSE:
      opt_decompose_ltl = XARGMATCH("--decompose", arg,
                                    decompose_args, decompose_values);
      break;
    case OPT_DOT:
      opt_dot = true;
      automaton_format_opt = opt_dot_arg = arg;
      automaton_format = Dot;
      break;
    case OPT_FROM_PGAME:
      jobs.emplace_back(arg, job_type::AUT_FILENAME);
      break;
    case OPT_GEQUIV:
      opt_gequiv = XARGMATCH("--global-equivalence", arg,
                               polarity_args, polarity_values);
      break;
    case OPT_HIDE:
      show_status = false;
      break;
    case OPT_INPUT:
      all_input_aps.emplace();
      split_aps(arg, *all_input_aps);
      break;
    case OPT_OUTPUT:
      all_output_aps.emplace();
      split_aps(arg, *all_output_aps);
      break;
    case OPT_PART_FILE:
      read_part_file(arg);
      break;
    case OPT_POLARITY:
      opt_polarity = XARGMATCH("--polarity", arg,
                               polarity_args, polarity_values);
      break;
    case OPT_PRINT:
      opt_print_pg = true;
      gi->force_sbacc = true;
      break;
    case OPT_PRINT_HOA:
      opt_print_hoa = true;
      opt_print_hoa_args = arg;
      break;
    case OPT_AIGER:
      opt_aiger = arg ? arg : "ite";
      break;
    case OPT_REAL:
      opt_real = true;
      break;
    case OPT_SIMPLIFY:
      gi->minimize_lvl = XARGMATCH("--simplify", arg,
                                   simplify_args, simplify_values);
      break;
    case OPT_SPLITTYPE:
      gi->sp = XARGMATCH("--splittype", arg,
                         splittype_args, splittype_values);
      break;
    case OPT_TLSF:
      jobs.emplace_back(arg, job_type::TLSF_FILENAME);
      break;
    case OPT_VERBOSE:
      gi->verbose_stream = &std::cerr;
      if (not gi->bv)
        gi->bv = spot::synthesis_info::bench_var();
      break;
    case OPT_VERIFY:
      opt_do_verify = true;
      break;
    case 'x':
      {
        const char* opt = gi->opt.parse_options(arg);
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
    // Create gi_ as a local variable, so make sure it is destroyed
    // before all global variables.
    spot::synthesis_info gi_;
    gi = &gi_;
    //gi_.opt.set("simul", 0);     // no simulation, except...
    //gi_.opt.set("dpa-simul", 1); // ... after determinization
    gi_.opt.set("tls-impl", 1);  // no automata-based implication check
    gi_.opt.set("wdba-minimize", 2); // minimize only syntactic oblig
    const argp ap = { options, parse_opt, nullptr,
                      argp_program_doc, children, nullptr, nullptr };
    if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
      exit(err);

    check_no_formula();
    process_io_options();

    // -q implies --hide-status
    if (automaton_format == Quiet)
      show_status = false;

    ltl_processor processor;
    if (int res = processor.run(); res == 0 || res == 1)
      {
        // Diagnose unused -x options
        gi_.opt.report_unused_options();
        return res;
      }
    return 2;
  });
}
