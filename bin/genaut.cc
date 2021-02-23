// -*- coding: utf-8 -*-
// Copyright (C) 2017-2019 Laboratoire de Recherche et Développement
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

#include "common_sys.hh"

#include <iostream>
#include <fstream>
#include <argp.h>
#include <cstdlib>
#include "error.h"
#include <vector>

#include "common_setup.hh"
#include "common_aoutput.hh"
#include "common_range.hh"
#include "common_cout.hh"

#include <cassert>
#include <iostream>
#include <sstream>
#include <set>
#include <string>
#include <cmath>
#include <cstdlib>
#include <cstring>
#include <spot/gen/automata.hh>

using namespace spot;

const char argp_program_doc[] ="Generate ω-automata from predefined patterns.";

static const argp_option options[] =
  {
    /**************************************************/
    // Keep this alphabetically sorted (expect for aliases).
    { nullptr, 0, nullptr, 0, "Pattern selection:", 1},
    { "iar-dsa-2n", gen::AUT_IAR_DSA_2N, "RANGE[,RANGE]", 0,
      "A deterministic Streett automaton with 2N states and K pairs such that "
      "any equivalent parity automaton has at least 2N⋅K! states.", 0},
    { "ks-nca", gen::AUT_KS_NCA, "RANGE", 0,
      "A co-Büchi automaton with 2N+1 states for which any equivalent "
      "deterministic co-Büchi automaton has at least 2^N/(2N+1) states.", 0},
    { "l-nba", gen::AUT_L_NBA, "RANGE", 0,
      "A Büchi automaton with 3N+1 states whose complementary Streett "
      "automaton needs at least N! states.", 0},
    { "l-dsa", gen::AUT_L_DSA, "RANGE", 0,
      "A deterministic Streett automaton with 4N states with no "
      "equivalent deterministic Rabin automaton of less than N! states.", 0},
    { "m-nba", gen::AUT_M_NBA, "RANGE", 0,
      "An NBA with N+1 states whose determinization needs at least "
      "N! states", 0},
    RANGE_DOC,
  /**************************************************/
    { nullptr, 0, nullptr, 0, "Miscellaneous options:", -1 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
  };

struct job
{
  gen::aut_pattern_id pattern;
  struct range range_states;
  struct range range_colors;
};

typedef std::vector<job> jobs_t;
static jobs_t jobs;

const struct argp_child children[] =
  {
    { &aoutput_argp, 0, nullptr, 3 },
    { &aoutput_o_format_argp, 0, nullptr, 4 },
    { &misc_argp, 0, nullptr, -1 },
    { nullptr, 0, nullptr, 0 }
  };

static void
enqueue_job(int pattern, const char* range_str)
{
  job j;
  j.pattern = static_cast<gen::aut_pattern_id>(pattern);
  j.range_colors.min = -1;
  j.range_colors.max = -1;
  if (range_str)
  {
    if (gen::aut_pattern_argc(j.pattern) == 2)
    {
      const char *comma = strchr(range_str, ',');
      if (!comma)
      {
        j.range_states = j.range_colors = parse_range(range_str);
        j.range_colors.min = std::max(j.range_colors.min, 2);
        j.range_colors.max = std::max(j.range_colors.min, 2);
      }
      else
      {
        std::string range(range_str, comma);
        j.range_states = parse_range(range.c_str());
        j.range_colors = parse_range(comma + 1);
      }
    }
    else
      j.range_states = parse_range(range_str);
  }
  else
  {
    j.range_states.min = 1;
    j.range_states.max = 20;
    j.range_colors.min = 2;
    j.range_colors.max = MAX_ACCSETS / 2 - 1;
  }
  jobs.push_back(j);
}

static int
parse_opt(int key, char* arg, struct argp_state*)
{
  // Called from C code, so should not raise any exception.
  BEGIN_EXCEPTION_PROTECT;
  if (key >= gen::AUT_BEGIN && key < gen::AUT_END)
    {
      enqueue_job(key, arg);
      return 0;
    }
  END_EXCEPTION_PROTECT;
  return ARGP_ERR_UNKNOWN;
}

static void
output_pattern(gen::aut_pattern_id pattern, int n, int k)
{
  process_timer timer;
  timer.start();
  twa_graph_ptr aut = spot::gen::aut_pattern(pattern, n, k);
  timer.stop();
  automaton_printer printer;
  printer.print(aut, timer, nullptr, aut_pattern_name(pattern), n);
}

static void
run_jobs()
{
  for (auto& j: jobs)
    {
      int inc = (j.range_states.max < j.range_states.min) ? -1 : 1;
      int inc_k = (j.range_colors.max < j.range_colors.min) ? -1 : 1;
      int n = j.range_states.min;
      int k = j.range_colors.min;
      for (;;)
        {
          output_pattern(j.pattern, n, k);
          if (n == j.range_states.max && k == j.range_colors.max)
            break;
          if (k == j.range_colors.max)
          {
            n += inc;
            k = j.range_colors.min;
          }
          else
            k += inc_k;
        }
    }
}


int
main(int argc, char** argv)
{
  return protected_main(argv, [&] {
      strcpy(F_doc, "the name of the pattern");
      strcpy(L_doc, "the argument of the pattern");

      const argp ap = { options, parse_opt, nullptr, argp_program_doc,
                        children, nullptr, nullptr };

      if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
        exit(err);

      if (jobs.empty())
        error(1, 0, "Nothing to do.  Try '%s --help' for more information.",
              program_name);

      run_jobs();
      flush_cout();
      return 0;
    });
}
