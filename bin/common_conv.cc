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

#include "common_conv.hh"
#include <cstdlib>
#include "error.h"

int
to_int(const char* s, const char* where)
{
  char* endptr;
  errno = 0;
  long int lres = strtol(s, &endptr, 10);
  if (*endptr)
    error(2, 0, "failed to parse '%s' as an integer (in argument of %s).",
          s, where);
  int res = lres;
  if (res != lres || errno == ERANGE)
    error(2, 0, "value '%s' is too large for an int (in argument of %s).",
          s, where);
  return res;
}

int
to_pos_int(const char* s, const char* where)
{
  int res = to_int(s, where);
  if (res < 0)
    error(2, 0, "%d is not positive (in argument of %s)", res, where);
  return res;
}

unsigned
to_unsigned (const char *s, const char* where)
{
  char* endptr;
  errno = 0;
  unsigned long lres = strtoul(s, &endptr, 10);
  if (*endptr)
    error(2, 0,
          "failed to parse '%s' as an unsigned integer (in argument of %s).",
          s, where);
  unsigned res = lres;
  if (res != lres || errno == ERANGE)
    error(2, 0,
          "value '%s' is too large for a unsigned int (in argument of %s).",
          s, where);
  return res;
}

float
to_float(const char* s, const char* where)
{
  char* endptr;
  errno = 0;
  float res = strtof(s, &endptr);
  if (*endptr || errno == ERANGE)
    error(2, 0, "failed to parse '%s' as a float (in argument of %s)",
          s, where);
  return res;
}

float
to_probability(const char* s, const char* where)
{
  float res = to_float(s, where);
  if (res < 0.0 || res > 1.0)
    error(2, 0, "%f is not between 0 and 1 (in argument of %s).", res, where);
  return res;
}

std::vector<long>
to_longs(const char* arg)
{
  std::vector<long> res;
  while (*arg)
    {
      char* endptr;
      errno = 0;
      long value = strtol(arg, &endptr, 10);
      if (endptr == arg || errno)
        error(2, 0, "failed to parse '%s' as an integer.", arg);
      res.push_back(value);
      while (*endptr == ' ' || *endptr == ',')
        ++endptr;
      arg = endptr;
    }
  return res;
}
