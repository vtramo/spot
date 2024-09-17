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

#include <spot/misc/common.hh>
#include <vector>
#include <algorithm>

namespace spot
{

  // Reorder `data` according the permutation in `indices` by
  // following the cycles in the permutation.  Additionally, if an
  // index is -1, the corresponding value is moved to the end of the
  // data.
  //
  // After running this algorithm, data[i] should be moved to
  // data[indices[i]] or to the end of the data if indices[i] == -1U.
  //
  // If indices.size() != data.size(), the minimum of both size is
  // used, and indices are expected to stay in this range.
  template<typename values>
  void permute_vector(std::vector<values>& data,
                      const std::vector<unsigned>& indices)
  {
    unsigned n = std::min(data.size(), indices.size());
    if (n == 0)
      return;
    std::vector<bool> done(n, false);
    unsigned end_of_data = n - 1; // index for the first -1
    for (unsigned i = 0; i < n; ++i)
      {
        if (done[i] || indices[i] == i)
          continue;             // already done or identity
        unsigned next = indices[i];
        if (next == -1U)
          {
            next = end_of_data--;
            if (next == i)
              continue;
          }
        values tmp = std::move(data[i]);
        while (next != i)
          {
            SPOT_ASSERT(next < n);
            if (done[next])
              throw std::invalid_argument
                ("permute_vector: invalid permutation");
            // this is a swap, but std::swap will not work
            // when data[next] is a bool_reference.
            values tmp2 = std::move(data[next]);
            data[next] = std::move(tmp);
            tmp = std::move(tmp2);
            done[next] = true;

            next = indices[next];
            if (next == -1U)
              next = end_of_data--;
          }
        data[i] = std::move(tmp);
        done[i] = true;
      }
  }

}
