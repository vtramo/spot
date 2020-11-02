// -*- coding: utf-8 -*-
// Copyright (C) 2019 Laboratoire de Recherche et Développement de
// l'Epita (LRDE)
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
#include <spot/ltsmin/spins_interface.hh>
#include <ltdl.h>
#include <cstring>
#include <ctype.h>
#include <cstdlib>
#include <string.h>
#include <spot/mc/utils.hh>
#include <sys/stat.h>
#include <cstdio>
#include <stdio.h>
#include <fstream>
#include <regex>

// MinGW does not define this.
#ifndef WEXITSTATUS
# define WEXITSTATUS(x) ((x) & 0xff)
#endif

namespace spot
{
  namespace
  {
    using namespace std::string_literals;

    //////////////////////////////////////////////////////////////////////////
    // LOADER

    // Call spins to compile "foo.prom" as "foo.prom.spins" if the latter
    // does not exist already or is older.
    static void
    compile_model(std::string& filename, const std::string& ext)
    {
      std::string command;
      std::string compiled_ext;

      if (ext == ".gal")
        {
          command = "gal2c " + filename;
          compiled_ext = "2C";
        }
      else if (ext == ".prom" || ext == ".pm" || ext == ".pml")
        {
          command = "spins " + filename;
          compiled_ext = ".spins";
        }
      else if (ext == ".dve")
        {
          command = "divine compile --ltsmin " + filename;
          command += " 2> /dev/null"; // FIXME needed for Clang on MacOSX
          compiled_ext = "2C";
        }
      else
        {
          throw std::runtime_error("Unknown extension '"s + ext +
                                   "'.  Use '.prom', '.pm', '.pml', "
                                   "'.dve', '.dve2C', '.gal', '.gal2C' or "
                                   "'.prom.spins'.");
        }

      struct stat s;
      if (stat(filename.c_str(), &s) != 0)
        throw std::runtime_error("Cannot open "s + filename);

      filename += compiled_ext;

      // Remove any directory, because the new file will
      // be compiled in the current directory.
      size_t pos = filename.find_last_of("/\\");
      if (pos != std::string::npos)
        filename = "./" + filename.substr(pos + 1);

      struct stat d;
      if (stat(filename.c_str(), &d) == 0)
        if (s.st_mtime < d.st_mtime)
          // The .spins or .dve2C or .gal2C is up-to-date, no need to compile.
          return;

      int res = system(command.c_str());
      if (res)
        throw std::runtime_error("Execution of '"s
                                 + command.c_str() + "' returned exit code "
                                 + std::to_string(WEXITSTATUS(res)));
    }
  }

  spins_interface::spins_interface(const std::string& file_arg)
  {
    std::string file;
    if (file_arg.find_first_of("/\\") != std::string::npos)
      file = file_arg;
    else
      file = "./" + file_arg;

    std::string ext = file.substr(file.find_last_of("."));
    if (ext != ".spins" && ext != ".dve2C" && ext != ".gal2C")
      {
        compile_model(file, ext);
        ext = file.substr(file.find_last_of("."));
      }

    if (lt_dlinit())
      throw std::runtime_error("Failed to initialize libltldl.");

    lt_dlhandle h = lt_dlopen(file.c_str());
    if (!h)
      {
        std::string lt_error = lt_dlerror();
        lt_dlexit();
        throw std::runtime_error("Failed to load '"s
                                 + file + "'.\n" + lt_error);
      }

    handle = h;

    auto sym = [&](auto* dst, const char* name)
    {
      // Work around -Wpendantic complaining that pointer-to-objects
      // should not be converted to pointer-to-functions (we have to
      // assume they can for POSIX).
      *reinterpret_cast<void**>(dst) = lt_dlsym(h, name);
      if (dst == nullptr)
        throw std::runtime_error("Failed to resolve symbol '"s
                                 + name + "' in '" + file + "'.");
    };

    // SpinS interface.
    if (ext == ".spins")
      {
        sym(&get_initial_state, "spins_get_initial_state");
        have_property = nullptr;
        sym(&get_successors, "spins_get_successor_all");
        sym(&get_state_size, "spins_get_state_size");
        sym(&get_state_variable_name, "spins_get_state_variable_name");
        sym(&get_state_variable_type, "spins_get_state_variable_type");
        sym(&get_type_count, "spins_get_type_count");
        sym(&get_type_name, "spins_get_type_name");
        sym(&get_type_value_count, "spins_get_type_value_count");
        sym(&get_type_value_name, "spins_get_type_value_name");
      }
    // dve2 and gal2C interfaces.
    else
      {
        sym(&get_initial_state, "get_initial_state");
        *reinterpret_cast<void**>(&have_property) =
          lt_dlsym(h, "have_property");
        sym(&get_successors, "get_successors");
        sym(&get_state_size, "get_state_variable_count");
        sym(&get_state_variable_name, "get_state_variable_name");
        sym(&get_state_variable_type, "get_state_variable_type");
        sym(&get_type_count, "get_state_variable_type_count");
        sym(&get_type_name, "get_state_variable_type_name");
        sym(&get_type_value_count, "get_state_variable_type_value_count");
        sym(&get_type_value_name, "get_state_variable_type_value");
      }

    if (have_property && have_property())
      throw std::runtime_error("Models with embedded properties "
                               "are not supported.");
  }

  // FIXME : the use of a trie may simplify the following computation
  void spins_interface::generate_compute_aps(std::vector<std::string> aps)
  {
    unsigned state_size = get_state_size();

    std::unordered_map<std::string, unsigned> matcher_var_index;
    std::unordered_map<int,                             // Process index
                       std::unordered_map< std::string, // process'state name
                                           int>         // corresponding id
                       > matcher_typeid_index;

    // Fill previous structures
    for (unsigned i = 0; i < state_size; ++i)
      {
        std::string k_var = get_state_variable_name(i);
        matcher_var_index.insert({k_var, i});
        int type_id = get_state_variable_type(i);
        std::unordered_map<std::string, int> tmp;
        int enum_count = get_type_value_count(type_id);
        for (int j = 0; j < enum_count; ++j)
          tmp[get_type_value_name(type_id, j)] = j;
        matcher_typeid_index[i] = tmp;
      }

    std::vector<std::string> new_aps;

    // Build new aps by matching variables positions inside of state structure
    for (auto str: aps)
      {
        unsigned pos = 0;
        unsigned last_letter, first_letter, last_pos = 0;
        std::string new_ap;

        // lookup function for a stable position and copy into new_ap
        // all intermediates
        auto next_stable = [&]()
        {
          while (pos < str.size() && !isalpha(str[pos]))
            ++pos;
          new_ap = new_ap + str.substr(last_pos, pos-last_pos);
          last_pos = pos;
        };

        // lookup function to find the start of the next variable
        auto find_next_variable = [&]()
        {
          while (pos < str.size() && !isalpha(str[pos]))
              ++pos;
          first_letter = pos;
        };

        // lookup function to find the eand of a variable
        auto eat_variable_name = [&]()
        {
          while (pos < str.size() &&
                 (isalpha(str[pos])  || isdigit(str[pos])  ||
                  str[pos] == '_'    || str[pos] == '['    ||
                  str[pos] == ']'))
            ++pos;
          last_letter = pos;
        };

        auto eat_state_name = [&]()
        {
          while (pos < str.size() &&
                 (isalpha(str[pos]) || isdigit(str[pos]) || str[pos] == '_'))
            ++pos;
        };

        // lookup function to find the eand of a variable
        auto error = [](std::string err)
        {
          std::cerr << err;
          exit(1);
        };

        // Main loop
        while (pos < str.size())
          {
            find_next_variable();
            eat_variable_name();

            // Multiple cases can occur then
            //     (1) str[pos] is a '.' : this means that we are
            //         facing something like P_0.state1 or P_0.var1
            //     (2) str[pos] is whitespace, comparison operator,
            //         arith operator, closing parenthesis, ...: in
            //         this case str[first_letter..last_letter] must
            //         be viable variable.  Warning situation
            //         such 'P_0 == state1' may occur in this case
            //     (3) we are facing 'min(k, j)' : this is not yet
            //         supported and we may not want to support
            //         something like that
            if (str[pos] == '.') // (1)
              {
                std::string proc_name = str.substr(first_letter,
                                                   last_letter-first_letter);
                auto search_pn = matcher_var_index.find(proc_name);

                if (search_pn == matcher_var_index.end())
                  error(proc_name + ": unknown variable \n");

                // remember index corresponding to this proc name
                unsigned proc_index = search_pn-> second;

                // skip the '.'  and search for the state name
                ++pos;
                if (pos == str.size() || !isalpha(str[pos]))
                  error("State name must start with a letter "
                        "and cannot be empty\n");

                eat_state_name();

                // Check wether this is a valid state name
                std::string state_name = str.substr(last_letter+1,
                                                    pos-1-last_letter);

                auto search_sn =
                  matcher_typeid_index[proc_index].find(state_name);
                if (search_sn != matcher_typeid_index[proc_index].end())
                  {
                    int state_idx =
                      matcher_typeid_index[proc_index][state_name];

                    new_ap += str.substr(last_pos, first_letter-last_pos)
                      + "(s[" + std::to_string(proc_index) + "] == "
                      + std::to_string(state_idx) + ")";
                    last_pos = pos;
                    next_stable();
                  }
                else
                  {
                    // May be a variable of a process
                    std::string tmpname = proc_name + '.' + state_name;
                    search_pn = matcher_var_index.find(tmpname);
                    if (search_pn == matcher_var_index.end())
                      error(tmpname + ": unknown variable \n");

                    new_ap += str.substr(last_pos, first_letter-last_pos)
                      + "s[" + std::to_string(search_pn->second) + "]";
                    last_pos = pos;
                    next_stable();
                  }
              }
            else // (2) and  (3)
              {
                std::string proc_name = str.substr(first_letter,
                                                   last_letter-first_letter);
                auto search_pn = matcher_var_index.find(proc_name);
                if (search_pn == matcher_var_index.end())
                  error(proc_name + ": unknown variable \n");

                // check wether we are facing P_0 == state or if this
                // is directly variable state.
                unsigned tmppos = pos;

                while (tmppos < str.size() && (str[tmppos] == ' ' ||
                                               str[tmppos] == '\t'))
                  ++tmppos;

                if (str[tmppos] != '=')
                  {
                    // it was a variable name: compute (part of) the
                    // new aps
                    pos = tmppos;

                    // compute new aps
                    new_ap = new_ap +
                      str.substr(last_pos, first_letter-last_pos)
                      + "(s[" + std::to_string(search_pn->second) +"])";
                    last_pos = pos;
                    next_stable();
                    continue;
                  }
                else
                  {
                    std::string proc_name =
                      str.substr(first_letter, last_letter-first_letter);
                    auto search_pn = matcher_var_index.find(proc_name);
                    if (search_pn == matcher_var_index.end())
                      error(proc_name + ": unknown variable \n");

                    // remember index corresponding to this proc name
                    unsigned proc_index = search_pn-> second;
                    if (tmppos+1 < str.size() && str[tmppos+1] == '=')
                      {
                        ++tmppos;
                        pos = tmppos;

                        while (pos < str.size() && !(isalpha(str[pos]) ||
                                                     isdigit(str[pos])))
                          ++pos;

                        // We are Facing P_0 == statename
                        if (!isdigit(str[pos]))
                          {
                            first_letter = pos;

                            eat_state_name();

                            std::string state_name =
                              str.substr(first_letter, pos-first_letter);

                            auto search_sn =
                              matcher_typeid_index[proc_index].find(state_name);
                            if (search_sn !=
                                matcher_typeid_index[proc_index].end())
                              {
                                int state_idx =
                                  matcher_typeid_index[proc_index][state_name];

                                new_ap += "(s[" + std::to_string(proc_index)
                                  + "] == " + std::to_string(state_idx) + ")";
                                last_pos = pos;
                                next_stable();
                                continue;
                              }
                            else
                              error(state_name + ": unrecognized for " +
                                    proc_name + '\n');
                          }
                      }
                    else
                      error(proc_name + str.substr(pos, tmppos+2-pos) +
                            ": unrecognized sequence \n");
                  }
              }
          }
        new_aps.emplace_back(new_ap);
      }

    // ---------------------------------------------------------------
    // We build the function that will evaluate, for each
    // state which atomic propositions are true or false
    // To achieve this, a C function is built, compiled and loaded
    // using dlopen.
    // Consequently, any arithmetic operation supported in C would
    // then now be available in atomic proposition.
    //
    // FIXME: the drawback is that the syntax of the atomic proposition
    // is no longer checked, and a user can type abberations like "a#z".
    // The solution would be to have a parser per model type, that takes
    // an atomic proposition and verify its syntax.
    // ---------------------------------------------------------------

    // Treat specific case  P_0 == S (close to preivous treatment)

    // Build the file that contains the necessary definitions for the
    // computation of all atomic propositions.
    // FIXME: this should be adapted to produce a BDD when BDD-based
    // emptiness check are used.
    std::string gfilename = "/tmp/foo.cc"; // FIXME find a unique name
    std::ofstream gfile;
    std::string cs, bs;

    gfile.open(gfilename, std::ofstream::out);

    cs =  "#include <stddef.h>\n";
    cs += "using cube = unsigned*;\n";
    cs += "size_t nb_bits = " + std::to_string(cubeset::nb_bits()) + ";\n";
    cs += "size_t uint_size = "
      +  std::to_string(cubeset::uint_size(aps.size())) + ";\n";
    cs += "inline void set_var(cube c, unsigned int x, bool val)"
      "\n{\n"
      "    *(c+x/nb_bits) = "
      "(*(c+x/nb_bits) & ~(1UL << (x%nb_bits))) | (val << (x%nb_bits));\n"
      "    *(c+uint_size+x/nb_bits) = "
      "(*(c+uint_size+x/nb_bits) & ~(1UL << (x%nb_bits)))"
      "| (!val << (x%nb_bits));\n"
      "}\n\n"
      "extern \"C\" void compute_aps_cube(int* s, unsigned* c)\n{\n";
    cs += "    bool b;\n";


    bs = "\n\nextern \"C\" unsigned long long "
      "compute_aps_bdd(int* s)\n{\n"
      "    unsigned long long res;\n"
      "    bool b;\n";

    int i = 0;
    for (auto ap: new_aps)
      {
        cs += "    b = " + ap + ";\n";
        cs += "    set_var(c, " + std::to_string(i) +  ", b);\n";

        bs += "    b = " + ap + ";\n";
        bs += "    res = (res & ~(1UL << "+ std::to_string(i) + ")) |"
          "(b << " + std::to_string(i) + ");\n";

        ++i;
      }
    cs +=  "}\n";
    bs +=  "    return res;\n}\n";

    gfile << cs << bs;
    gfile.close();

    // Compile this file
    std::string gname  = gfilename + ".so";
    std::string command = "g++ --std=c++17 -O3 -shared -fPIC -m64  " + gfilename
      + " -o " + gname;
    int res = system(command.c_str());
    if (res)
      throw std::runtime_error("Execution of '"
                               + command + "' returned exit code "
                               + std::to_string(WEXITSTATUS(res)));


    if (lt_dlinit())
      throw std::runtime_error("Failed to initialize libltldl.");

    lt_dlhandle h1 = lt_dlopen(gname.c_str());
    if (!h1)
      {
        std::string lt_error = lt_dlerror();
        lt_dlexit();
        throw std::runtime_error("Failed to load '"s
                                 + gname + "'.\n" + lt_error);
      }

    compute_handle = h1;

    auto sym1 = [&](auto* dst, const char* name)
    {
      // Work around -Wpendantic complaining that pointer-to-objects
      // should not be converted to pointer-to-functions (we have to
      // assume they can for POSIX).
      *reinterpret_cast<void**>(dst) = lt_dlsym(h1, name);
      if (*dst == nullptr)
        throw std::runtime_error("Failed to resolve symbol '"s
                                 + name + "' in '" + gname + "'.");
    };

    sym1(&compute_aps_cube, "compute_aps_cube");
    sym1(&compute_aps_bdd, "compute_aps_bdd");
  }

  spins_interface::~spins_interface()
  {
    lt_dlhandle h = (lt_dlhandle) handle;
    if (h)
      lt_dlclose(h);
    lt_dlhandle h1 = (lt_dlhandle) compute_handle;
    if (h1)
      lt_dlclose(h1);
    lt_dlexit();
  }
}
