// -*- coding: utf-8 -*-
// Copyright (C) 2016, 2018, 2020 Laboratoire de Recherche et Développement
// de l'Epita.
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

#include <spot/bricks/brick-assert>
#include <spot/bricks/brick-bitlevel>
#include <spot/bricks/brick-hash>
#include <spot/bricks/brick-hashset>
#include <spot/bricks/brick-shmem>
#include <spot/bricks/brick-types>

#include <chrono>

using namespace std::chrono_literals;

struct both
{
  int x;
  int y;

  inline bool operator==(const both rhs)
  {
    return x == rhs.x && y == rhs.y;
  }
};


static inline bool equals(const both* lhs, const both* rhs)
{
  return lhs->x == rhs->x && lhs->y == rhs->y;
}


/// \brief The haser for the previous state.
struct both_hasher : brq::hash_adaptor<both>
{
  both_hasher() = default;

  auto hash(const both lhs) const
  {
    return brq::hash(lhs.x);
  }
};

static int main_raw_element()
{
  // Declare concurrent hash table
  brq::concurrent_hash_set<both> ht;

  // Declare workers and provide them some jobs.
   std::vector<std::thread> workers;
  for (int i = 0; i < 4; i++)
    workers.
      push_back(std::thread([](int tid, brq::concurrent_hash_set<both> ht)
                  throw()
                    {
                        for (int i = 0; i < 1000; ++i)
                            ht.insert(both{i, tid}, both_hasher());
                    }, i, ht));

  //Wait the end of all threads.
  for (auto& t: workers)
    t.join();

  // Display the whole table.
  for (unsigned i = 0; i < ht.capacity(); ++ i)
    if (ht.valid(i))
      std::cout << i << ": {"
                << ht.valueAt(i).x << ','
                << ht.valueAt(i).y  << "}\n";
  return 0;
}

/// \brief The haser for the previous state.
struct both_ptr_hasher : brq::hash_adaptor<both*>
{
  both_ptr_hasher() = default;

  auto hash(const both* lhs) const
  {
    return brq::hash(lhs->x);
  }
};

static int main_ptr_element()
{
  // Declare concurrent hash table
  brq::concurrent_hash_set<both*> ht;

  // Declare workers and provide them some jobs.
   std::vector<std::thread> workers;
  for (int i = 0; i < 4; i++)
    workers.
      push_back(std::thread([](int tid, brq::concurrent_hash_set<both*> ht)
                  throw()
                    {
                        for (int i = 0; i < 1000; ++i)
                        {
                            // FIXME Dealloc new
                            ht.insert(new both{i, tid}, both_ptr_hasher());
                        }
                    }, i, ht));

  //Wait the end of all threads.
  for (auto& t: workers)
    t.join();

  // Display the whole table.
  for (unsigned i = 0; i < ht.capacity(); ++ i)
    if (ht.valid(i))
      std::cout << i << ": {"
                << ht.valueAt(i)->x << ','
                << ht.valueAt(i)->y  << "}\n";

  return 0;
}

template<class Functor, class...Objects>
void for_all(Functor&& f, Objects&&... objects)
{
    using expand = int[];
    (void) expand { 0, (f(std::forward<Objects>(objects)), 0)... };

}

static void test_brick_hashmap()
{
  t_brq::sequential< brq::hash_set > t1;
  t_brq::sequential< brq::concurrent_hash_set > t2;

  // In C++ 17, the for_all could be rewritten with fold expression
  // auto tester = [](auto&&... args) { (args.basic(), ...);  };
  // tester(t);
  for_all([](auto& e)
          {
            std::clog << "# " << typeid(e).name() << '\n';
            std::clog << "  [HM -- Sequential] Testing basic\n";
            e.insert_basic();
            std::clog << "  [HM -- Sequential] Testing stress\n";
            e.stress();
            std::clog << "  [HM -- Sequential] Testing set\n";
            e.set();
            std::clog << "  [HM -- Sequential] Testing erase_basic\n";
            e.erase_basic();
            std::clog << "  [HM -- Sequential] Testing erase_many\n";
            e.erase_many();
          }, t1, t2);

  t_brq::parallel< brq::concurrent_hash_set > t3;
  for_all([](auto& e)
          {
            std::clog << "# " << typeid(e).name() << '\n';
            std::clog << "  [HM -- Parallel] Testing insert\n";
            e.insert();
            std::clog << "  [HM -- Parallel] Testing multi\n";
            e.multi();
            std::clog << "  [HM -- Parallel] Testing stress\n";
            e.stress();
            std::clog << "  [HM -- Parallel] Testing empty\n";
            e.empty();
            std::clog << "  [HM -- Parallel] Testing set\n";
            e.set();
          }, t3);
}

static void test_brick_bitlevel()
{
  brick::t_bitlevel::BitTupleTest t1;
  std::clog << "# " << typeid(t1).name() << '\n';
  std::clog << "  [BL -- BitTupleTest] Testing mask\n";
  t1.mask();
  std::clog << "  [BL -- BitTupleTest] Testing bitcopy\n";
  t1.bitcopy();
  std::clog << "  [BL -- BitTupleTest] Testing field\n";
  t1.field();
  std::clog << "  [BL -- BitTupleTest] Testing basic\n";
  t1.basic();
  std::clog << "  [BL -- BitTupleTest] Testing big\n";
  t1.big();
  std::clog << "  [BL -- BitTupleTest] Testing structure\n";
  t1.structure();
  std::clog << "  [BL -- BitTupleTest] Testing nested\n";
  t1.nested();
  std::clog << "  [BL -- BitTupleTest] Testing locked\n";
  t1.locked();
  std::clog << "  [BL -- BitTupleTest] Testing assign\n";
  t1.assign();
  std::clog << "  [BL -- BitTupleTest] Testing operators\n";
  t1.operators();
  std::clog << "  [BL -- BitTupleTest] Testing ones\n";
  t1.ones();

  brick::t_bitlevel::BitVecTest t2;
  std::clog << "# " << typeid(t2).name() << '\n';
  std::clog << "  [BL -- BitVecTest] Testing bvpair_shiftl\n";
  t2.bvpair_shiftl();
  std::clog << "  [BL -- BitVecTest] Testing bvpair_shiftr\n";
  t2.bvpair_shiftr();
}

static void test_brick_shmem()
{
  brick::t_shmem::ThreadTest t1;
  std::clog << "# " << typeid(t1).name() << '\n';
  std::clog << "  [S -- ThreadTest] Testing async_loop\n";
  // t1.async_loop();  // Triggers an alarm that break in test-suite
  std::clog << "  [S -- ThreadTest] Testing thread\n";
  // t1.thread();  // Triggers an alarm that break in test-suite
}

static void test_brick_types()
{
  brick::t_types::Mixins t1;
  std::clog << "# " << typeid(t1).name() << '\n';
  std::clog << "  [T -- Mixins] Testing comparable\n";
  t1.comparable();
  std::clog << "  [T -- Mixins] Testing eq\n";
  t1.eq();
  std::clog << "  [T -- Mixins] Testing ord\n";
  t1.ord();
  std::clog << "  [T -- Mixins] Testing eqord\n";
  t1.eqord();

  brick::t_types::UnionTest t2;
  std::clog << "# " << typeid(t2).name() << '\n';
  std::clog << "  [T -- UnionTest] Testing basic\n";
  t2.basic();
  std::clog << "  [T -- UnionTest] Testing moveNoCopy\n";
  t2.moveNoCopy();
  std::clog << "  [T -- UnionTest] Testing ctorCast\n";
  t2.ctorCast();
  std::clog << "  [T -- UnionTest] Testing eq\n";
  t2.eq();
  std::clog << "  [T -- UnionTest] Testing ord\n";
  t2.ord();

  brick::t_types::StrongEnumFlagsTest t3;
  std::clog << "# " << typeid(t3).name() << '\n';
  std::clog << "  [T -- StrongEnumFlagsTest] Testing regression\n";
  t3.regression();
  std::clog << "  [T -- StrongEnumFlagsTest] Testing enum_uchar\n";
  t3.enum_uchar();
  std::clog << "  [T -- StrongEnumFlagsTest] Testing enum_ushort\n";
  t3.enum_ushort();
  std::clog << "  [T -- StrongEnumFlagsTest] Testing enum_uint\n";
  t3.enum_uint();
  std::clog << "  [T -- StrongEnumFlagsTest] Testing enum_ulong\n";
  t3.enum_ulong();
}

int main()
{
  main_raw_element();
  std::cout << "----------------------------------------------------\n";
  main_ptr_element();
  // Run tests that are already embedded inside of bricks
  test_brick_hashmap();
  test_brick_bitlevel();
  test_brick_shmem();
  test_brick_types();
  return 0;
}
