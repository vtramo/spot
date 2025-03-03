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

#pragma once

#include "common_sys.hh"
#include <iosfwd>
#include <memory>
#include <fstream>

class output_file
{
  std::ostream* os_;
  std::unique_ptr<std::ofstream> of_;
  bool append_ = false;
public:
  // Open a file for output.  "-" is interpreted as stdout.
  // Names that start with ">>" are opened for append.
  // The function calls error() on... error.
  output_file(const char* name, bool force_append = false);

  void close(const std::string& name);

  void reopen_for_append(const std::string& name);

  bool append() const
  {
    return append_;
  }

  std::ostream& ostream()
  {
    return *os_;
  }
};
