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

#include "common_ioap.hh"
#include "error.h"
#include <fstream>
#include <unordered_set>

// --ins and --outs, as supplied on the command-line
std::optional<std::vector<std::string>> all_output_aps;
std::optional<std::vector<std::string>> all_input_aps;

// Store refirst, separate the filters that are regular expressions from
// the others.  Compile the regular expressions while we are at it.
std::vector<std::regex> regex_in;
std::vector<std::regex> regex_out;
// map identifier to input/output (false=input, true=output)
std::unordered_map<std::string, bool> identifier_map;

static bool a_part_file_was_read = false;

static std::string
str_tolower(std::string s)
{
  std::transform(s.begin(), s.end(), s.begin(),
                 [](unsigned char c){ return std::tolower(c); });
  return s;
}

void
split_aps(const std::string& arg, std::vector<std::string>& where)
{
  std::istringstream aps(arg);
  std::string ap;
  while (std::getline(aps, ap, ','))
    {
      ap.erase(remove_if(ap.begin(), ap.end(), isspace), ap.end());
      where.push_back(str_tolower(ap));
    }
}

void process_io_options()
{
  // Filter identifiers from regexes.
  if (all_input_aps.has_value())
    for (const std::string& f: *all_input_aps)
      {
        unsigned sz = f.size();
        if (f[0] == '/' && f[sz - 1] == '/')
          regex_in.push_back(std::regex(f.substr(1, sz - 2)));
        else
          identifier_map.emplace(f, false);
      }
  if (all_output_aps.has_value())
    for (const std::string& f: *all_output_aps)
      {
        unsigned sz = f.size();
        if (f[0] == '/' && f[sz - 1] == '/')
          regex_out.push_back(std::regex(f.substr(1, sz - 2)));
        else if (auto [it, is_new] = identifier_map.try_emplace(f, true);
                 !is_new && !it->second)
          error(2, 0,
                a_part_file_was_read ?
                "'%s' appears in both inputs and outputs" :
                "'%s' appears in both --ins and --outs",
                f.c_str());
      }
}

static std::unordered_set<std::string>
list_aps_in_formula(spot::formula f)
{
  std::unordered_set<std::string> aps;
  f.traverse([&aps](spot::formula s) {
    if (s.is(spot::op::ap))
      aps.emplace(s.ap_name());
    return false;
  });
  return aps;
}


bool
is_output(const std::string& a, const char* filename, int linenum)
{
  if (auto it = identifier_map.find(a); it != identifier_map.end())
    return it->second;

  bool found_in = false;
  for (const std::regex& r: regex_in)
    if (std::regex_search(a, r))
      {
        found_in = true;
        break;
      }
  bool found_out = false;
  for (const std::regex& r: regex_out)
    if (std::regex_search(a, r))
      {
        found_out = true;
        break;
      }
  if (all_input_aps.has_value() == all_output_aps.has_value())
    {
      if (!all_input_aps.has_value())
        {
          // If the atomic proposition hasn't been classified
          // because neither --ins nor --out were specified,
          // attempt to classify automatically using the first
          // letter.
          int fl = a[0];
          if (fl == 'i' || fl == 'I')
            found_in = true;
          else if (fl == 'o' || fl == 'O')
            found_out = true;
        }
      if (found_in && found_out)
        error_at_line(2, 0, filename, linenum,
                      a_part_file_was_read ?
                      "'%s' matches both inputs and outputs" :
                      "'%s' matches both --ins and --outs",
                      a.c_str());
      if (!found_in && !found_out)
        {
          if (all_input_aps.has_value() || all_output_aps.has_value())
            error_at_line(2, 0, filename, linenum,
                          a_part_file_was_read ?
                          "'%s' does not match any input or output" :
                          "one of --ins or --outs should match '%s'",
                          a.c_str());
          else
            error_at_line(2, 0, filename, linenum,
                          "since '%s' does not start with 'i' or 'o', "
                          "it is unclear if it is an input or "
                          "an output;\n    use --ins, --outs, or --part-file",
                          a.c_str());
        }
    }
  else
    {
      // if we had only --ins or only --outs, anything not
      // matching that was given is assumed to belong to the
      // other one.
      if (!all_input_aps.has_value() && !found_out)
        found_in = true;
      else if (!all_output_aps.has_value() && !found_in)
        found_out = true;
    }
  return found_out;
}

// Takes a set of the atomic propositions appearing in the formula,
// and separate them into two vectors: input APs and output APs.
std::pair<std::vector<std::string>, std::vector<std::string>>
filter_list_of_aps(spot::formula f, const char* filename, int linenum)
{
  std::unordered_set<std::string> aps = list_aps_in_formula(f);
  // now iterate over the list of atomic propositions to filter them
  std::vector<std::string> matched[2]; // 0 = input, 1 = output
  for (const std::string& a: aps)
    matched[is_output(a, filename, linenum)].push_back(a);
  return {matched[0], matched[1]};
}


spot::formula relabel_io(spot::formula f, spot::relabeling_map& fro,
                         const char* filename, int linenum)
{
  auto [ins, outs] = filter_list_of_aps(f, filename, linenum);
  // Different implementation of unordered_set, usinged in
  // filter_list_of_aps can cause aps to be output in different order.
  // Let's sort everything for the sake of determinism.
  std::sort(ins.begin(), ins.end());
  std::sort(outs.begin(), outs.end());
  spot::relabeling_map to;
  unsigned ni = 0;
  for (std::string& i: ins)
    {
      std::ostringstream s;
      s << 'i' << ni++;
      spot::formula a1 = spot::formula::ap(i);
      spot::formula a2 = spot::formula::ap(s.str());
      fro[a2] = a1;
      to[a1] = a2;
    }
  unsigned no = 0;
  for (std::string& o: outs)
    {
      std::ostringstream s;
      s << 'o' << no++;
      spot::formula a1 = spot::formula::ap(o);
      spot::formula a2 = spot::formula::ap(s.str());
      fro[a2] = a1;
      to[a1] = a2;
    }
  return spot::relabel_apply(f, &to);
}

// Read FILENAME as a ".part" file.   It should
// contains lines of text of the following form:
//
//    .inputs IN1 IN2 IN3...
//    .outputs OUT1 OUT2 OUT3...
void read_part_file(const char* filename)
{
  std::ifstream in(filename);
  if (!in)
    error(2, errno, "cannot open '%s'", filename);

  // This parsing is inspired from Lily's parser for .part files.  We
  // read words one by one, and change the "mode" if we the word is
  // ".inputs" or ".outputs".  A '#' introduce a comment until the end
  // of the line.
  std::string word;
  enum { Unknown, Input, Output } mode = Unknown;
  while (in >> word)
    {
      // The benchmarks for Syft use ".inputs:" instead of ".inputs".
      if (word == ".inputs" || word == ".inputs:")
        {
          mode = Input;
          if (!all_input_aps.has_value())
            all_input_aps.emplace();
        }
      // The benchmarks for Syft use ".outputs:" instead of ".outputs".
      else if (word == ".outputs"  || word == ".outputs:")
        {
          mode = Output;
          if (!all_output_aps.has_value())
            all_output_aps.emplace();
        }
      else if (word[0] == '#')
        {
          // Skip the rest of the line.
          in.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
        }
      else if (mode == Unknown)
        {
          error_at_line(2, 0, filename, 0,
                        "expected '.inputs' or '.outputs' instead of '%s'",
                        word.c_str());
        }
      else if (mode == Input)
        {
          all_input_aps->push_back(str_tolower(word));
        }
      else /* mode == Output */
        {
          all_output_aps->push_back(str_tolower(word));
        }
    }
  a_part_file_was_read = true;
}
