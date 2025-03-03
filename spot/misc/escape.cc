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
#include <sstream>
#include <ostream>
#include <cstring>
#include <spot/misc/escape.hh>

namespace spot
{
  std::ostream&
  escape_rfc4180(std::ostream& os, const std::string& str)
  {
    for (auto i: str)
      switch (i)
        {
        case '"':
          os << "\"\"";
          break;
        default:
          os << i;
          break;
        }
    return os;
  }

  std::ostream&
  escape_latex(std::ostream& os, const std::string& str)
  {
    for (auto i: str)
      switch (i)
        {
        case '~':
          os << "\\text{\\textasciitilde}";
          break;
        case '^':
          os << "\\text{\\textasciicircum}";
          break;
        case '\\':
          os << "\\text{\\textbackslash}";
          break;
        case '&':
        case '%':
        case '$':
        case '#':
        case '_':
        case '{':
        case '}':
          os << '\\';
          SPOT_FALLTHROUGH;
        default:
          os << i;
          break;
        }
    return os;
  }

  std::ostream&
  escape_html(std::ostream& os, const std::string& str)
  {
    for (auto i: str)
      switch (i)
        {
        case '&':
          os << "&amp;";
          break;
        case '"':
          os << "&quot;";
          break;
        case '<':
          os << "&lt;";
          break;
        case '>':
          os << "&gt;";
          break;
        case '\n':
          os << "<br/>";
          break;
        default:
          os << i;
          break;
        }
    return os;
  }

  std::ostream&
  escape_str(std::ostream& os, const std::string& str)
  {
    for (auto i: str)
      switch (i)
        {
        case '\\':
          os << "\\\\";
          break;
        case '"':
          os << "\\\"";
          break;
        case '\n':
          os << "\\n";
          break;
        default:
          os << i;
          break;
        }
    return os;
  }

  std::string
  escape_str(const std::string& str)
  {
    std::ostringstream os;
    escape_str(os, str);
    return os.str();
  }

  std::ostream&
  quote_shell_string(std::ostream& os, const char* str)
  {
    // Single quotes are best, unless the string to quote contains one.
    if (!strchr(str, '\''))
      {
        os << '\'' << str << '\'';
      }
    else
      {
        // In double quotes we have to escape $ ` " or \.
        os << '"';
        while (*str)
          switch (*str)
            {
            case '$':
            case '`':
            case '"':
            case '\\':
              os << '\\';
              SPOT_FALLTHROUGH;
            default:
              os << *str++;
              break;
            }
        os << '"';
      }
    return os;
  }

}
