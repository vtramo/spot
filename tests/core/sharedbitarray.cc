// -*- coding: utf-8 -*-
// Copyright (C) 2022 Laboratoire de Recherche et
// Développement de l'Epita.
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

#include <array>
#include <iostream>
#include <sstream>
#include <vector>
#include <spot/twacube/shared_bitarray.hh>

#ifdef ENABLE_PTHREAD
#include <thread>
#include <atomic>
#endif

namespace{
  struct modNtrue
  {
    unsigned cur_;
    unsigned end_;
    unsigned step_;

    modNtrue(unsigned start, unsigned end, unsigned step)
      : cur_{start}
      , end_{end}
      , step_{step}
    {
    }

    modNtrue(const modNtrue& other) = default;

    void next()
    {
      cur_ += step_*(cur_ <= end_);
    }

    auto get() const
    {
      return std::make_pair(cur_, true);
    }

    bool done() const
    {
      return cur_ > end_;
    }
  };
}

static void test_n(unsigned nbits)
{
  spot::bitarr_handler bh(nbits, 1);

  std::cout << "Nbits " << nbits << "; Is small? " << bh.is_small() << std::endl;

  auto b0 = bh.generate(modNtrue(1, nbits, 3));
  auto b1 = bh.generate(modNtrue(2, nbits, 3));
  auto bfull = bh.generate(modNtrue(1, nbits, 1));

  std::cout << "b0\n";
  bh.dump(std::cout, b0, false);
  std::cout << "b1\n";
  bh.dump(std::cout, b1, false);
  std::cout << "bfull\n";
  bh.dump(std::cout, bfull, false);

  std::cout << "bh.cmp(bfull && b0, b0), expected 0: "
            << bh.cmp(bfull && b0, b0) << std::endl;

  auto b2 = b0 || b1;
  auto b3 = b0 && b1;

  std::cout << "b0 || b1\n";
  bh.dump(std::cout, b2, false);
  std::cout << "b0 && b1\n";
  bh.dump(std::cout, b3, false);


  std::cout << "Expected use_count is 1:\n";
  std::cout << b2.use_count() << '\n';
  std::cout << b3.use_count() << '\n';

  if (!bh.is_small())
    {
      auto b4 = b0 || b1;
      auto b5 = b0 && b1;
      std::cout << "Expected use_count is 2:\n";
      std::cout << b4.use_count() << '\n';
      std::cout << b5.use_count() << '\n';
    }

  b0 &= b1;
  std::cout << "b0 &= b1\n";
  bh.dump(std::cout, b0, false);
  b0 |= b1;
  std::cout << "b0 |= b1\n";
  bh.dump(std::cout, b0, false);
}

static void test_small()
{
  std::cout << "small 23 bits\n";
  test_n(23);
}

static void test_large()
{
  std::cout << "large 144 bits\n";
  test_n(144);
}

#ifdef ENABLE_PTHREAD

class onegen{
  unsigned idx_;
  bool done_;

public:

  onegen(unsigned idx)
    : idx_{idx}
    , done_{idx == -1u}
  {
  }

  auto get() const
  {
    return std::make_pair(idx_, true);
  }

  bool done() const
  {
    return done_;
  }

  void next()
  {
    done_ = true;
  }
};

static void or_all(spot::bitarr_handler& bh, spot::bitarr& b, unsigned nbits,
                   const std::atomic_int& go, const unsigned id)
{
  std::cout << "Create " << std::this_thread::get_id() << std::endl;
  while(go == 0)
    continue;
  std::cout << "Launch " << std::this_thread::get_id() << std::endl;
  if (id & 1)
    {
      for (unsigned i = 1; i <= nbits; ++i)
        {
          auto tmp = bh.generate(onegen(i));
          b |= tmp;
        }
    }
  else
    {
      for (unsigned i = nbits; i != 0; --i)
        {
          auto tmp = bh.generate(onegen(i));
          b |= tmp;
        }
    }
}

static void test_threaded(unsigned nthreads, unsigned nbits)
{
  std::cout << "Test thread " << nthreads << ", " << nbits << '\n';
  spot::bitarr_handler bh(nbits, nthreads);

  std::vector<spot::bitarr> bv;
  std::vector<std::thread> w;
  std::atomic_int go = 0;

  for (unsigned i = 0; i < nthreads; ++i)
    bv.push_back(bh.generate(onegen(-1u)));

  for (unsigned i = 0; i < nthreads; ++i)
    {
      std::cout << i << std::endl;
      w.emplace_back([&bh, &bv, nbits, &go, i]()
                      {
                        or_all(bh, bv.at(i), nbits, go, i);
                      }
                    );
    }
  go = 1;
  for (auto& t : w)
    t.join();
  // Check if all bits are set for all bitarr
  for (const auto& b : bv)
    for (unsigned i = 1; i <= nbits; ++i)
      if (!b.is_set(i))
        std::cout << "Mutlthreaded test failed\n";
}
#endif


int main(){
  test_small();
  test_large();
#ifdef ENABLE_PTHREAD
  std::cout << "Testing pthread" << std::endl;
  test_threaded(1, 12);
  test_threaded(2, 12);
  test_threaded(1, 244);
  test_threaded(2, 244);
#else
  std::cout << "No pthread" << std::endl;
#endif

  return 0;
}