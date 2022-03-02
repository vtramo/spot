// -*- coding: utf-8 -*-
// Copyright (C) 2015, 2016, 2018, 2022 Laboratoire de
// Recherche et Developpement de l'Epita (LRDE).
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

#include "spot/twacube/cube.hh"

namespace spot
{
  void cubeset::display(const cube c) const
  {
    for (unsigned int i = 0; i < 2*uint_size_; ++i)
      {
        if (i == uint_size_)
          std::cout << '\n';

        for (unsigned x = 0; x < nb_bits_; ++x)
          std::cout << ((*(c+i) >> x) & 1);
      }
    std::cout << '\n';
  }

  std::string
  cubeset::dump(cube c, const std::vector<std::string>& aps) const
  {
    std::ostringstream oss;
    bool all_free = true;
    unsigned int cpt = 0;
    for (unsigned int i = 0; i < uint_size_; ++i)
      {
        for (unsigned x = 0; x < nb_bits_ && cpt != size_; ++x)
          {
            bool true_var = (*(c+i) >> x) & 1;
            bool false_var = (*(c+i+uint_size_) >> x) & 1;
            if (true_var)
              {
                oss << aps[cpt]
                    << (cpt != (size_ - 1) ? "&": "");
                all_free = false;
              }
            else if (false_var)
              {
                oss << '!' << aps[cpt]
                    << (cpt != (size_ - 1) ? "&": "");
                all_free = false;
              }
            ++cpt;
          }
      }
    if (all_free)
      oss << '1';

    std::string res = oss.str();
    if (res.back() == '&')
      res.pop_back();
    if (res.front() == '&')
      res =  res.substr(1);
    return res;
  }
}