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


#include "common_sys.hh"
#include <argp.h>
#include "error.h"

#include "common_setup.hh"
#include "common_finput.hh"
#include "common_output.hh"
#include "common_ioap.hh"
#include "common_conv.hh"
#include "common_cout.hh"
#include "common_range.hh"

#include <spot/tl/defaultenv.hh>
#include <spot/tl/randomltl.hh>
#include <spot/misc/random.hh>

enum {
  OPT_BOOLEAN_PRIORITIES = 256,
  OPT_DUMP_PRIORITIES,
  OPT_DUPS,
  OPT_INS,
  OPT_LTL_PRIORITIES,
  OPT_OUTS,
  OPT_SEED,
  OPT_TREE_SIZE,
};

static const char * argp_program_doc =
  "Combine formulas taken randomly from an input set.\n\n\
The input set is specified using FILENAME, -F FILENAME, or -f formula.\n\
By default this generates a Boolean pattern of size 5, for instance\n\
\"(φ₁ & φ₂) | φ₃\", where each φᵢ is randomly taken from the input set.\n\
The size and nature of the pattern can be changed using generation\n\
parameters.  Additionally, it is possible to rename the atomic propositions\n\
in each φᵢ using -A or -P.\v\
Example:\n\
\n\
Generates 10 random Boolean combinations of terms of the form GFa, with\n\
'a' picked from a set of 5 atomic propositions:\n\
  % ltlmix -f GFa -n10 -A5\n\
\n\
Build a single LTL formula over subformulas taken randomly from the list of\n\
55 patterns by Dwyer et al., using a choice of 10 atomic propositions to\n\
relabel subformulas:\n\
  % genltl --dac | ltlmix -L -A10\n\
\n\
Build 5 random positive Boolean combination of GFa and GFb:\n"
  // next line is in its own double-quote to please sanity.test
  "  % ltlmix -f GFa -f GFb --boolean-prio=not=0,xor=0,implies=0,equiv=0 -n5";

static const argp_option options[] = {
    // Keep this alphabetically sorted (expect for aliases).
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Generation parameters:", 2 },
    { "allow-dups", OPT_DUPS, nullptr, 0,
      "allow duplicate formulas to be output", 0 },
    { "ap-count", 'A', "N[,M]", 0,
      "rename the atomic propositions in each selected formula by drawing "
      "randomly from N atomic propositions (the rewriting is bijective "
      "if N is larger than the original set).  If M is specified, two sets "
      "of atomic propositions are used to represent inputs and outputs, and "
      "options --ins/--outs can be used to classify the original propositions.",
      0 },
    { "boolean", 'B', nullptr, 0,
      "generate Boolean combinations of formulas (default)", 0 },
    { "formulas", 'n', "INT", 0,
      "number of formulas to generate (default: 1);\n"
      "use a negative value for unbounded generation", 0 },
    { "ltl", 'L', nullptr, 0, "generate LTL combinations of subformulas", 0 },
    { "polarized-ap", 'P', "N[,M]", 0,
      "similar to -A, but randomize the polarity of the new atomic "
      "propositions", 0 },
    { "random-conjuncts", 'C', "N", 0,
      "generate random-conjunctions of N conjuncts; "
      "shorthand for --tree-size {2N-1} -B "
      "--boolean-priorities=[disable everything but 'and']", 0 },
    { "seed", OPT_SEED, "INT", 0,
      "seed for the random number generator (default: 0)", 0 },
    { "tree-size", OPT_TREE_SIZE, "RANGE", 0,
      "tree size of main pattern generated (default: 5);\n"
      "input formulas count as size 1.", 0 },
    { "ins", OPT_INS, "PROPS", 0,
      "comma-separated list of atomic propositions to consider as input, "
      "interpreted as a regex if enclosed in slashes", 0 },
    { "outs", OPT_OUTS, "PROPS", 0,
      "comma-separated list of atomic propositions to consider as putput, "
      "interpreted as a regex if enclosed in slashes", 0 },
    RANGE_DOC,
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Adjusting probabilities:", 4 },
    { "dump-priorities", OPT_DUMP_PRIORITIES, nullptr, 0,
      "show current priorities, do not generate any formula", 0 },
    { "ltl-priorities", OPT_LTL_PRIORITIES, "STRING", 0,
      "set priorities for LTL formulas", 0 },
    { "boolean-priorities", OPT_BOOLEAN_PRIORITIES, "STRING", 0,
      "set priorities for Boolean formulas", 0 },
    { nullptr, 0, nullptr, 0, "STRING should be a comma-separated list of "
      "assignments, assigning integer priorities to the tokens "
      "listed by --dump-priorities.", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Output options:", -20 },
    { nullptr, 0, nullptr, 0, "The FORMAT string passed to --format may use "
      "the following interpreted sequences:", -19 },
    { "%f", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the formula (in the selected syntax)", 0 },
    { "%l", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the (serial) number of the formula (0-based)", 0 },
    { "%L", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the (serial) number of the formula (1-based)", 0 },
    { "%%", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "a single %", 0 },
    COMMON_LTL_OUTPUT_SPECS,
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Miscellaneous options:", -1 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
};

static const argp_child children[] = {
  { &finput_argp, 0, nullptr, 0 },
  { &output_argp, 0, nullptr, 0 },
  { &misc_argp, 0, nullptr, 0 },
  { nullptr, 0, nullptr, 0 }
};

static int opt_formulas = 1;
static spot::randltlgenerator::output_type output =
  spot::randltlgenerator::Bool;
static char* opt_pL = nullptr;
static char* opt_pB = nullptr;
static char random_conj[] = "not=0,implies=0,equiv=0,xor=0,or=0";
static bool opt_dump_priorities = false;
static int opt_seed = 0;
static range opt_tree_size = { 5, 5 };
static bool opt_unique = true;
static int opt_ap_count = 0;
static int opt_out_ap_count = 0;
static bool opt_literal = false;
static bool opt_io = false;

namespace
{
  // We want all these variables to be destroyed when we exit main, to
  // make sure it happens before all other global variables (like the
  // atomic propositions maps) are destroyed.  Otherwise we risk
  // accessing deleted stuff.
  static struct opt_t
  {
    spot::atomic_prop_set sub;
  }* opt = nullptr;

  class sub_processor final: public job_processor
  {
  public:
    int
    process_formula(spot::formula f, const char* filename = nullptr,
                    int linenum = 0) override
    {
      if (opt_io)
        // Filter the atomic propositions of each formula in order to
        // report those that are not classifiable.  Throw the result
        // of that filtering away, as we only care about the potential
        // diagnostics.
        (void) filter_list_of_aps(f, filename, linenum);
      opt->sub.insert(f);
      return 0;
    }
  };
}

static sub_processor subreader;

std::pair<int, int> to_int_pair(const char* arg, const char* opt)
{
  const char* comma = strchr(arg, ',');
  if (!comma)
    {
      int res = to_int(arg, opt);
      return {res, 0};
    }
  else
    {
      std::string arg1(arg, comma);
      int res1 = to_int(arg1.c_str(), opt);
      int res2 = to_int(comma + 1, opt);
      return {res1, res2};
    }
}


static int
parse_opt(int key, char* arg, struct argp_state*)
{
  // Called from C code, so should not raise any exception.
  BEGIN_EXCEPTION_PROTECT;
  switch (key)
    {
    case 'A':
      std::tie(opt_ap_count, opt_out_ap_count) =
        to_int_pair(arg, "-A/--ap-count");
      opt_literal = false;
      break;
    case 'B':
      output = spot::randltlgenerator::Bool;
      break;
    case 'C':
      {
        int s = 2 * to_int(arg, "-C/--random-conjuncs") - 1;
        opt_tree_size = {s, s};
        output = spot::randltlgenerator::Bool;
        opt_pB = random_conj;
        break;
      }
    case 'L':
      output = spot::randltlgenerator::LTL;
      break;
    case 'n':
      opt_formulas = to_int(arg, "-n/--formulas");
      break;
    case 'P':
      std::tie(opt_ap_count, opt_out_ap_count) =
        to_int_pair(arg, "-P/--polarized-ap");
      opt_literal = true;
      break;
    case OPT_BOOLEAN_PRIORITIES:
      opt_pB = arg;
      break;
    case OPT_LTL_PRIORITIES:
      opt_pL = arg;
      break;
    case OPT_DUMP_PRIORITIES:
      opt_dump_priorities = true;
      break;
    case OPT_DUPS:
      opt_unique = false;
      break;
    case OPT_INS:
      {
        all_input_aps.emplace(std::vector<std::string>{});
        split_aps(arg, *all_input_aps);
        opt_io = true;
        break;
      }
    case OPT_OUTS:
      {
        all_output_aps.emplace(std::vector<std::string>{});
        split_aps(arg, *all_output_aps);
        opt_io = true;
        break;
      }
    case OPT_SEED:
      opt_seed = to_int(arg, "--seed");
      break;
    case OPT_TREE_SIZE:
      opt_tree_size = parse_range(arg);
      if (opt_tree_size.min > opt_tree_size.max)
        std::swap(opt_tree_size.min, opt_tree_size.max);
      break;
    case ARGP_KEY_ARG:
      jobs.emplace_back(arg, job_type::LTL_FILENAME);
      break;
    default:
      return ARGP_ERR_UNKNOWN;
    }
  END_EXCEPTION_PROTECT;
  return 0;
}

int
main(int argc, char* argv[])
{
  return protected_main(argv, [&] {
      const argp ap = { options, parse_opt, "[FILENAME[/COL]...]",
                        argp_program_doc, children, nullptr, nullptr };

      // This will ensure that all objects stored in this struct are
      // destroyed before global variables.
      opt_t o;
      opt = &o;

      if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
        exit(err);

      check_no_formula("combine");

      if (opt_io && !opt_out_ap_count)
        error(2, 0,
              "options --ins and --outs only make sense when the "
              "two-argument version of '-A N,M' or '-P N,M' is used.");
      if (opt_out_ap_count > 0)
        // Do not require --ins/--outs to be used, as the input
        // pattern may use atomic propositions starting with i/o
        // already.  Setting opt_io will cause the subreader to
        // complain about unclassifible atomic propositions.
        opt_io = true;
      if (opt_io)
        process_io_options();

      if (subreader.run())
        return 2;

      if (opt->sub.empty())
        error(2, 0, "the set of subformulas to build from is empty");

      spot::srand(opt_seed);

      std::function<bool(spot::formula)> output_p = nullptr;
      if (opt_out_ap_count)
        output_p = [&](spot::formula f) { return is_output(f.ap_name()); };

      spot::randltlgenerator rg
        (opt_ap_count,
         [&] (){
          spot::option_map opts;
          opts.set("output", output);
          opts.set("out_ap_size", opt_out_ap_count);
          opts.set("tree_size_min", opt_tree_size.min);
          opts.set("tree_size_max", opt_tree_size.max);
          opts.set("seed", opt_seed);
          opts.set("simplification_level", 0);
          opts.set("unique", opt_unique);
          opts.set("literals", opt_literal);
          return opts;
         }(), opt_pL, nullptr, opt_pB, &opt->sub, output_p);

      if (opt_dump_priorities)
        {
          switch (output)
            {
            case spot::randltlgenerator::LTL:
              std::cout <<
                "Use --ltl-priorities to set the following LTL priorities:\n";
              rg.dump_ltl_priorities(std::cout);
              break;
            case spot::randltlgenerator::Bool:
              std::cout <<
                "Use --boolean-priorities to set the following Boolean "
                "formula priorities:\n";
              rg.dump_bool_priorities(std::cout);
              break;
            case spot::randltlgenerator::PSL:
            case spot::randltlgenerator::SERE:
              error(2, 0, "PSL/SERE output is unsupported");
              break;
            }
          exit(0);
        }

      int count = 0;
      while (opt_formulas < 0 || opt_formulas--)
        {
          spot::formula f = rg.next();
          if (!f)
            {
              error(2, 0, "failed to generate a new unique formula after %d " \
                    "trials", spot::randltlgenerator::MAX_TRIALS);
            }
          else
            {
              output_formula_checked(f, nullptr, nullptr, count + 1, count);
              ++count;
            }
        };

      flush_cout();
      return 0;
    });
}
