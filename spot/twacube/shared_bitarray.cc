// -*- coding: utf-8 -*-
// Copyright (C) 2022 Laboratoire de Recherche et Developpement de
// l'Epita (LRDE).
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

#include<spot/twacube/shared_bitarray.hh>

namespace spot
{
  namespace internal_bitarr
  {

    void
    dump(std::ostream& os, c_bit_data_ptr ptr, unsigned n,
         unsigned stop, bool full)
    {
      unsigned idx = 0;
      for (unsigned i = 0; i < n; ++i)
        {
          bit_data d = ptr[i];
          for (unsigned j = 0; j < NB_BITS; ++j)
            {
             os << ((d & one) ? '1' : '0');
             if (full && (((j+1)%CHAR_WIDTH) == 0))
              os << ' ';
             d >>= 1;
             if (idx == stop)
              return;
             ++idx;
            }
          os << ((full && (i != n-1)) ? "| " : "");
        }
    }

  } // namespace internal
} // namespace spot