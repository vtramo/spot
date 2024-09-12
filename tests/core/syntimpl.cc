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

#include "config.h"
#include <iostream>
#include <fstream>
#include <sstream>
#include <cassert>
#include <cstdlib>
#include <cstring>
#include <spot/tl/parse.hh>
#include <spot/tl/nenoform.hh>
#include <spot/tl/simplify.hh>
#include <spot/tl/print.hh>

static void
syntax(char* prog)
{
  std::cerr << prog << " file\n";
  exit(2);
}

int
main(int argc, char** argv)
{
  if (argc != 2)
    syntax(argv[0]);
  std::ifstream input(argv[1]);
  if (!input)
    {
      std::cerr << "failed to open " << argv[1] << '\n';
      return 2;
    }

  spot::tl_simplifier* c = new spot::tl_simplifier;
  std::string s;
  unsigned line = 0;
  while (std::getline(input, s))
    {
      ++line;
      std::cerr << line << ": " << s << '\n';
      if (s[0] == '#')                // Skip comments
        continue;

      spot::formula f[2];
      std::istringstream ss(s);
      for (unsigned i = 0; i < 2; ++i)
        {
          std::string form;
          if (!std::getline(ss, form, ','))
            {
              std::cerr << "missing first formula\n";
              exit(2);
            }
          std::string tmp;
          while (form.size() > 0 && form.back() == '\\'
                 && std::getline(ss, tmp, ','))
            {
              form.back() = ',';
              form += tmp;
            }
          auto pf = spot::parse_infix_psl(form);
          if (pf.format_errors(std::cerr))
            return 2;
          f[i] = spot::negative_normal_form(pf.f);
        }
      // ignore the rest of the line
      std::cout << spot::str_psl(f[0]) << ',' << spot::str_psl(f[1]) << ','
                << c->syntactic_implication(f[0], f[1]) << ','
                << c->syntactic_implication_neg(f[0], f[1], false) << ','
                << c->syntactic_implication_neg(f[0], f[1], true) << '\n';
    }
  delete c;
  assert(spot::fnode::instances_check());
  return 0;
}
