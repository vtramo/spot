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
#include <spot/misc/hashfunc.hh>

using namespace spot;

template<typename State, typename SuccIterator,
         typename StateHash, typename StateEqual>
class bitstate_hashing_stats
{
public:
  bitstate_hashing_stats(kripkecube<State, SuccIterator>& sys, unsigned tid,
                         size_t mem_size):
    sys_(sys), tid_(tid)
  {
    static_assert(spot::is_a_kripkecube_ptr<decltype(&sys),
        State, SuccIterator>::value,
        "error: does not match the kripkecube requirements");

    seen_.reserve(2000000);
    todo_.reserve(100000);

    bloom_filter::hash_functions_t hash_functions = {lookup3_hash};
    bf_ = std::make_unique<bloom_filter>(mem_size, hash_functions);
  }

  ~bitstate_hashing_stats()
  {
    // States will be destroyed by the system, so just clear map
    seen_.clear();
  }

  void push(State s)
  {
    todo_.push_back({s, sys_.succ(s, tid_), state_number_});
    seen_.insert(s);
    ++state_number_;
  }

  void pop()
  {
    StateHash state_hash;

    auto current = todo_.back();
    bf_->insert(state_hash(current.s));
    seen_.erase(current.s);
    todo_.pop_back();
  }

  void run()
  {
    state_number_ = 1;
    State initial = sys_.initial(tid_);
    StateHash state_hash;
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
                      bf_->contains(state_hash(next));
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

  std::unordered_set<State, StateHash, StateEqual> seen_;
  std::vector<todo__element> todo_;
  unsigned int state_number_;
  // TODO: unique_ptr are not thread safe
  std::unique_ptr<bloom_filter> bf_;
};
