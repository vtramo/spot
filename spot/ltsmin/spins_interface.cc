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

  spins_interface::spins_interface(const std::string& file_arg,
                                   std::vector<std::string> aps)
  {
    (void) aps;
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

    // ---------------------------------------------------------------
    // Fom Here, we build the function that will evaluate, for each
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

    std::vector<std::string> k_vars;  // The name of each variable
    std::vector<int> k_types;         // The type of each variable

    // Binds variable names to their index inside of the state
    std::unordered_map<std::string, int> matcher_var_index;

    // Binds process'state name with id
    std::unordered_map<int,                             // Process index
                       std::unordered_map< std::string, // process'state name
                                           int>         // corresponding id
                       > matcher_typeid_index;

    // Fill the previous structures by walking all variables of a state
    unsigned state_size = get_state_size();
    for (unsigned i = 0; i < state_size; ++i) // walk all variables
      {
        // Find type and names
        std::string k_var = get_state_variable_name(i);
        k_vars.emplace_back(k_var);
        matcher_var_index[k_var] = i;

        int type_id = get_state_variable_type(i);
        k_types.emplace_back(type_id);

        // First time we see this type, insert it
        if (matcher_typeid_index.find(type_id) == matcher_typeid_index.end())
          {
            std::unordered_map<std::string, int> tmp;
            int enum_count = get_type_value_count(type_id);
            for (int j = 0; j < enum_count; ++j)
              tmp[get_type_value_name(type_id, j)] = j;
            matcher_typeid_index[type_id] = tmp;
          }
      }

    // Sorting is necessary, since we then use regular expressions
    // to convert " a < b " into "s[1] < s[2]". Without sorting
    // problems can occurs when some variable name is prefix of other
    // variable names
    std::sort(std::begin(k_vars), std::end(k_vars), std::greater<>());

    for (auto& ap: aps)
      for (auto& kv: k_vars)
        ap = std::regex_replace(ap, std::regex(kv), "s[" +
                                std::to_string(matcher_var_index[kv]) + "]");

    // Treat specific cases P_0.S since this is  not really a reference
    // to a variable
    for (auto& ap: aps)
      {
        std::vector<std::pair<std::string, std::string>> replace;
        std::regex re("s\\[[1-9]+\\]\\.[a-zA-Z0-9]+");
        std::sregex_iterator next(ap.begin(), ap.end(), re);
        std::sregex_iterator end;
        while (next != end)
          {
            std::string match = (*next).str();
            std::regex re_st_pos("[1-9]+");
            std::sregex_iterator tmp(match.begin(), match.end(), re_st_pos);
            int var_idx  = std::stoi((*tmp).str());
            std::regex re_proc_stname("\\.[a-zA-Z0-9]+");
            std::sregex_iterator tmp2(match.begin(), match.end(),
                                      re_proc_stname);
            std::string strtmp = (*tmp2).str();
            std::string proc_name(strtmp.begin()+1, strtmp.end());
            std::string tmatch  = "s\\[" + std::to_string(var_idx) + "\\]\\."
              + proc_name;
            std::string replacement = "(s[" + std::to_string(var_idx)
              + "] == "
              + std::to_string(matcher_typeid_index[k_types[var_idx]]
                               [proc_name])
              + ")";
            replace.emplace_back(tmatch, replacement);
            next++;
          }

        for (auto& p: replace)
          {
            ap = std::regex_replace(ap, std::regex(p.first), p.second);
          }
      }

    // Treat specific case  P_0 == S (close to preivous treatment)

    // Build the file that contains the necessary definitions for the
    // computation of all atomic propositions.
    // FIXME: this should be adapted to produce a BDD when BDD-based
    // emptiness check are used.
    std::string gfilename = "/tmp/foo.cc"; // FIXME find a unique name
    std::ofstream gfile;
    gfile.open(gfilename, std::ofstream::out);

    gfile << "#include <stddef.h>\n";
    gfile << "using cube = unsigned*;\n";
    gfile << "size_t nb_bits = " << cubeset::nb_bits() << ";\n";
    gfile << "size_t uint_size = " << cubeset::uint_size(aps.size()) << ";\n";
    gfile << "inline void set_var(cube c, unsigned int x, bool val)"
      "\n{\n"
      "    *(c+x/nb_bits) = "
      "(*(c+x/nb_bits) & ~(1UL << (x%nb_bits))) | (val << (x%nb_bits));\n"
      "    *(c+uint_size+x/nb_bits) = "
      "(*(c+uint_size+x/nb_bits) & ~(1UL << (x%nb_bits)))"
      "| (!val << (x%nb_bits));\n"
      "}\n\n";
    gfile << "extern \"C\" void compute_aps(int* s, unsigned* c)\n{\n";
    gfile <<  "    bool b;\n";
    int i = 0;


    for (auto ap: aps)
      {
        gfile << "    b = " + ap + ";\n";
        gfile << "    set_var(c, " + std::to_string(i) +  ", b);\n";
        ++i;
      }
    gfile << "}\n";
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

    handle = h1;

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

    sym1(&compute_aps, "compute_aps");
    int f[100];
    unsigned g[100];
    compute_aps(f,g);
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
