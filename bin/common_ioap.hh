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
#include <optional>
#include <regex>
#include <string>
#include <vector>
#include <unordered_map>
#include <spot/tl/formula.hh>
#include <spot/tl/relabel.hh>

// --ins and --outs, as supplied on the command-line
extern std::optional<std::vector<std::string>> all_output_aps;
extern std::optional<std::vector<std::string>> all_input_aps;

// Comma-separated list of strings, such as those passed to --ins/--outs
void split_aps(const std::string& arg, std::vector<std::string>& where);

// process the all_output_aps and all_input_aps above to
// fill regex_in, regex_out, and identifier_map.
void process_io_options();

// Store refirst, separate the filters that are regular expressions from
// the others.  Compile the regular expressions while we are at it.
extern std::vector<std::regex> regex_in;
extern std::vector<std::regex> regex_out;
// map identifier to input/output (false=input, true=output)
extern std::unordered_map<std::string, bool> identifier_map;


// Given an atomic proposition AP and the above
// regex_in/regex_out/identifier_map, decide if this AP is an output
// (true) or input (false.
bool
is_output(const std::string& ap,
          const char* filename = nullptr, int linenum = 0);


// Separate the set of the atomic propositions appearing in f, into
// two vectors: input APs and output APs, becased on regex_in,
// regex_out, and identifier_map.
std::pair<std::vector<std::string>, std::vector<std::string>>
filter_list_of_aps(spot::formula f, const char* filename, int linenum);


// Relabel APs incrementally, based on i/o class.
spot::formula relabel_io(spot::formula f, spot::relabeling_map& fro,
                         const char* filename, int linenum);

// Read a .part file.
void read_part_file(const char* filename);
