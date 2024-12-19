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
#include <error.h>
#include <argmatch.h>

#include "common_aoutput.hh"
#include "common_finput.hh"
#include "common_setup.hh"
#include "common_trans.hh"
#include <spot/tl/formula.hh>
#include <spot/tl/print.hh>
#include <spot/twaalgos/ltlf2dfa.hh>

enum
{
  OPT_NEGATE = 256,
  OPT_KEEP_NAMES,
  OPT_MTDFA_DOT,
  OPT_MTDFA_STATS,
  OPT_TLSF,
  OPT_TRANS,
  OPT_MINIMIZE,
};


static const argp_option options[] =
  {
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Input options:", 1 },
    { "tlsf", OPT_TLSF, "FILENAME", 0,
      "Read a TLSF specification from FILENAME, and call syfco to "
      "convert it into LTL", 0 },
    { "negate", OPT_NEGATE, nullptr, 0, "negate each formula", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Processing options:", 10 },
    { "translation", OPT_TRANS, "direct|compositional", 0,
      "Whether to translate the formula directly as a whole, or to "
      "assemble translations from subformulas.  Default is compositional.",
      0 },
    { "keep-names", OPT_KEEP_NAMES, nullptr, 0,
      "Keep the names of formulas that label states in the output automaton.",
      0 },
    { "minimize", OPT_MINIMIZE, "yes|no", 0,
      "Minimize the automaton (enabled by default).", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Output options:", 20 },
    { "hoaf", 'H', "1.1|b|i|k|l|m|s|t|v", OPTION_ARG_OPTIONAL,
      "Output the automaton in HOA format (default).  Add letters to select "
      "(1.1) version 1.1 of the format, "
      "(b) create an alias basis if >=2 AP are used, "
      "(i) use implicit labels for complete deterministic automata, "
      "(s) prefer state-based acceptance when possible [default], "
      "(t) force transition-based acceptance, "
      "(m) mix state and transition-based acceptance, "
      "(k) use state labels when possible, "
      "(l) single-line output, "
      "(v) verbose properties", 0 },
    { "dot", 'd', "options", OPTION_ARG_OPTIONAL,
      "print the automaton in DOT format", 0 },
    { "mtdfa-dot", OPT_MTDFA_DOT, nullptr, 0,
      "print the MTDFA in DOT format", 0 },
    { "mtdfa-stats", OPT_MTDFA_STATS, nullptr, 0,
      "print statistics about the MTDFA", 0 },
    { "quiet", 'q', nullptr, 0, "suppress all normal output", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Miscellaneous options:", -1 },
    { nullptr, 0, nullptr, 0, nullptr, 0 },
  };

static const struct argp_child children[] =
  {
    { &finput_argp_headless, 0, nullptr, 0 },
    { &misc_argp, 0, nullptr, 0 },
    { nullptr, 0, nullptr, 0 }
  };

static const char argp_program_doc[] = "\
Convert LTLf formulas to transition-based deterministic finite automata.\n\n\
If multiple formulas are supplied, several automata will be output.";

enum translation_type { translation_direct, translation_compositional };

static const char* const translation_args[] =
  {
    "direct", "compositional", "compose", nullptr
  };
static translation_type translation_values[] =
  {
    translation_direct, translation_compositional, translation_compositional,
  };
ARGMATCH_VERIFY(translation_args, translation_values);
static translation_type opt_trans = translation_compositional;

static const char* const minimize_args[] =
  {
    "yes", "true", "enabled", "1",
    "no", "false", "disabled", "0",
    nullptr
  };
static bool minimize_values[] =
  {
    true, true, true, true,
    false, false, false, false,
  };
ARGMATCH_VERIFY(minimize_args, minimize_values);
static bool opt_minimize = true;

static bool opt_keep_names = false;


enum mtdfa_output_type { mtdfa_none, mtdfa_dot, mtdfa_stats };
static mtdfa_output_type mtdfa_output = mtdfa_none;

static bool negate = false;

static int
parse_opt(int key, char *arg, struct argp_state *)
{
  // Called from C code, so should not raise any exception.
  BEGIN_EXCEPTION_PROTECT;
  switch (key)
    {
    case OPT_NEGATE:
      negate = true;
      break;
    case OPT_KEEP_NAMES:
      opt_keep_names = true;
      break;
    case OPT_TLSF:
      jobs.emplace_back(arg, job_type::TLSF_FILENAME);
      break;
    case OPT_TRANS:
      opt_trans = XARGMATCH("--translation", arg,
                            translation_args, translation_values);
      break;
    case OPT_MINIMIZE:
      opt_minimize = XARGMATCH("--minimize", arg,
                               minimize_args, minimize_values);
      break;
    case 'd':
      automaton_format = Dot;
      automaton_format_opt = arg;
      mtdfa_output = mtdfa_none;
      break;
    case 'H':
      automaton_format = Hoa;
      automaton_format_opt = arg;
      mtdfa_output = mtdfa_none;
      break;
    case 'q':
      automaton_format = Quiet;
      mtdfa_output = mtdfa_none;
      break;
    case OPT_MTDFA_DOT:
      mtdfa_output = mtdfa_dot;
      break;
    case OPT_MTDFA_STATS:
      mtdfa_output = mtdfa_stats;
      break;
    case ARGP_KEY_ARG:
      // FIXME: use stat() to distinguish filename from string?
      jobs.emplace_back(arg, ((*arg == '-' && !arg[1])
                              ? job_type::LTL_FILENAME
                              : job_type::LTL_STRING));
      break;

    default:
      return ARGP_ERR_UNKNOWN;
    }
  END_EXCEPTION_PROTECT;
  return 0;
}


namespace
{
  class trans_processor final: public job_processor
  {
  public:
    automaton_printer printer{ltl_input};
    spot::bdd_dict_ptr& dict;

    explicit trans_processor(spot::bdd_dict_ptr& dict)
      : dict(dict)
    {
    }

    int
    process_formula(spot::formula f,
                    const char* filename = nullptr, int linenum = 0) override
    {
      if (!f.is_ltl_formula())
        {
          std::string s = spot::str_psl(f);
          error_at_line(2, 0, filename, linenum,
                        "formula '%s' is not an LTLf formula",
                        s.c_str());
        }

      if (negate)
        f = spot::formula::Not(f);

      spot::process_timer timer;
      timer.start();

      spot::mtdfa_ptr a;
      if (opt_trans == translation_direct)
        {
          a = spot::ltlf_to_mtdfa(f, dict);
          if (!opt_keep_names)
            a->names.clear();
          if (opt_minimize)
            a = spot::minimize_mtdfa(a);
        }
      else
        {
          a = spot::ltlf_to_mtdfa_compose(f, dict,
                                          opt_minimize,
                                          opt_keep_names);
        }

      timer.stop();

      if (mtdfa_output == mtdfa_none && automaton_format == Quiet)
        {
          return 0;
        }
      else if (mtdfa_output == mtdfa_dot)
        {
          a->print_dot(std::cout);
        }
      else if (mtdfa_output == mtdfa_stats)
        {
          spot::mtdfa_stats s = a->get_stats();
          std::cout << "states: " << s.states << '\n'
                    << "leaves: " << s.leaves << '\n'
                    << "nodes: " << s.nodes << '\n'
                    << "paths: " << s.paths << '\n'
                    << "edges: " << s.edges << '\n'
                    << "has_true: " << s.has_true << '\n'
                    << "has_false: " << s.has_false << '\n';
        }
      else
        {
          spot::twa_graph_ptr aut = a->as_twa();
          static unsigned index = 0;
          printer.print(aut, timer, f, filename, linenum, index++,
                        nullptr, prefix, suffix);
        }
      return 0;
    }

    int
    process_tlsf_file(const char* filename) override
    {
      static char arg0[] = "syfco";
      static char arg1[] = "-f";
      static char arg2[] = "ltlxba-fin";
      static char arg3[] = "-m";
      static char arg4[] = "fully";
      char* command[] = { arg0, arg1, arg2, arg3, arg4,
                          const_cast<char*>(filename), nullptr };
      std::string tlsf_string = read_stdout_of_command(command);
      int res = process_string(tlsf_string, filename);
      return res;
    }

  };
}

int
main(int argc, char** argv)
{
  return protected_main(argv, [&] {
      // By default we name automata using the formula.
      opt_name = "%f";

      const argp ap = { options, parse_opt, "[FORMULA...]",
                        argp_program_doc, children, nullptr, nullptr };

      if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
        exit(err);

      check_no_formula();

      spot::bdd_dict_ptr dict = spot::make_bdd_dict();
      trans_processor processor(dict);
      if (processor.run())
        return 2;
      return 0;
  });
}
