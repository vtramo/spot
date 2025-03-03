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
#include <spot/misc/memusage.hh>
#include <cstdio>

namespace spot
{
  int
  memusage()
  {
    int size;

    FILE* file = fopen("/proc/self/statm", "r");
    if (!file)
      return -1;
    int res = fscanf(file, "%d", &size);
    (void) fclose(file);
    if (res != 1)
      return -1;
    return size;
  }

}
