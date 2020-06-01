// -*- coding: utf-8 -*-
// Copyright (C) 2020 Laboratoire de Recherche et Developpement de
// l'Epita
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

#include <spot/kripke/kripke.hh>
#include <spot/mc/bloom_filter.hh>
#include <spot/misc/memusage.hh>
#include <spot/misc/timer.hh>

#include <string>
#include <vector>

using namespace spot;

template<typename State, typename SuccIterator,
         typename StateHash, typename StateEqual>
class bitstate_hashing_stats
{
public:
  bitstate_hashing_stats(kripkecube<State, SuccIterator>& sys, unsigned tid,
                         size_t mem_size):
    sys_(sys), tid_(tid), bloom_filter_(mem_size)
  {
    static_assert(spot::is_a_kripkecube_ptr<decltype(&sys),
        State, SuccIterator>::value,
        "error: does not match the kripkecube requirements");
  }

  void push(State s)
  {
    todo_.push_back({s, sys_.succ(s, tid_), state_number_});
    seen_.insert(s);
    ++state_number_;
  }

  void pop()
  {
    auto current = todo_.back();
    todo_.pop_back();
    seen_.erase(current.s);
    bloom_filter_.insert(state_hash_(current.s));

    sys_.recycle(current.it, tid_);
  }

  void run()
  {
    state_number_ = 1;
    State initial = sys_.initial(tid_);
    push(initial);

    while (!todo_.empty())
    {
      if (todo_.back().it->done())
      {
        pop();
      }
      else
      {
        State next = todo_.back().it->state();
        todo_.back().it->next();

        bool marked = seen_.find(next) != seen_.end() ||
                      bloom_filter_.contains(state_hash_(next));
        if (marked == false)
          push(next);
      }
    }
  }

  unsigned int get_nb_reached_states()
  {
    return state_number_;
  }

private:
  struct todo__element
  {
    State s;
    SuccIterator* it;
    unsigned int current_state;
  };

protected:
  kripkecube<State, SuccIterator>& sys_;
  unsigned int tid_;
  StateHash state_hash_;

  std::unordered_set<State, StateHash, StateEqual> seen_;
  std::vector<todo__element> todo_;
  unsigned int state_number_;
  concurrent_bloom_filter bloom_filter_;
};

template<typename kripke_ptr, typename State,
         typename Iterator, typename Hash, typename Equal>
void bench_bitstate(kripke_ptr sys, std::vector<size_t> mem_sizes)
{
  spot::timer_map timer;
  int mem_used;
  using algo_name = bitstate_hashing_stats<State, Iterator, Hash, Equal>;

  // TODO: print reference

  for (size_t mem_size : mem_sizes)
  {
    auto bh = new algo_name(*sys, 0, mem_size);

    const std::string round = "Using " + std::to_string(mem_size) + " bits";
    timer.start(round);
    mem_used = spot::memusage();

    bh->run();

    mem_used = spot::memusage() - mem_used;
    timer.stop(round);

    auto walltime = (float) timer.timer(round).walltime() / CLOCKS_PER_SEC;
    std::cout << "\n" << round << "\n"
              << "\tmem_size (nb bits): " << mem_size << "\n"
              << "\tmem_used (nb pages): " << mem_used << "\n"
              << "\twalltime (seconds): " << walltime << "\n";

    delete bh;
  }

  std::cout << "\n";
  timer.print(std::cout);
}
