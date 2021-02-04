// -*- coding: utf-8 -*-
// Copyright (C) 2017, 2018, 2020 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#include <string>

#include <spot/twaalgos/game.hh>
#include <spot/misc/bddlt.hh>
#include <spot/twaalgos/sccinfo.hh>

namespace spot
{
  namespace
  {
    constexpr unsigned unseen_mark = std::numeric_limits<unsigned>::max();
    using par_t = int;
    constexpr par_t limit_par_even =
        std::numeric_limits<par_t>::max() & 1
        ? std::numeric_limits<par_t>::max()-3
        : std::numeric_limits<par_t>::max()-2;
    using strat_t = long long;
    constexpr strat_t no_strat_mark = std::numeric_limits<strat_t>::min();


    static const region_t*
    ensure_game(const const_twa_graph_ptr& arena, const char* fnname)
    {
      auto owner = arena->get_named_prop<region_t>("state-player");
      if (!owner)
        throw std::runtime_error
          (std::string(fnname) + ": automaton should define \"state-player\"");
      if (owner->size() != arena->num_states())
        throw std::runtime_error
          (std::string(fnname) + ": \"state-player\" should have "
           "as many states as the automaton");
      return owner;
    }

    static const std::vector<bool>*
    ensure_parity_game(const const_twa_graph_ptr& arena, const char* fnname)
    {
      bool max, odd;
      bool is_par = arena->acc().is_parity(max, odd, true);
      if (!is_par)
        throw std::runtime_error
          (std::string(fnname) +
           ": arena must have one of the four parity acceptance conditions");
      return ensure_game(arena, fnname);
    }

    // Internal structs
    // winning regions for env and player
    struct winner_t
    {
      std::vector<bool> has_winner_;
      std::vector<bool> winner_;

      inline bool operator()(unsigned v, bool p)
      {
        // returns true if player p wins v
        // false otherwise
        return has_winner_[v] && winner_[v] == p;
      }

      inline void set(unsigned v, bool p)
      {
        has_winner_[v] = true;
        winner_[v] = p;
      }

      inline void unset(unsigned v)
      {
        has_winner_[v] = false;
      }

      inline bool winner(unsigned v)
      {
        assert(has_winner_.at(v));
        return winner_[v];
      }
    }; // winner_t

    // Internal structs used by parity_game
    // Struct to change recursive calls to stack
    struct work_t
    {
      work_t(unsigned wstep_, unsigned rd_, par_t min_par_,
             par_t max_par_) noexcept
        : wstep(wstep_),
          rd(rd_),
          min_par(min_par_),
          max_par(max_par_)
      {
      }
      const unsigned wstep, rd;
      const par_t min_par, max_par;
    }; // work_t

    // Collects information about an scc
    // Used to detect special cases
    struct subgame_info_t
    {
      typedef std::set<par_t, std::greater<par_t>> all_parities_t;

      subgame_info_t() noexcept
      {
      }

      subgame_info_t(bool empty, bool one_parity, bool one_player0,
                     bool one_player1, all_parities_t parities) noexcept
        : is_empty(empty),
          is_one_parity(one_parity),
          is_one_player0(one_player0),
          is_one_player1(one_player1),
          all_parities(parities)
      {};
      bool is_empty; // empty subgame
      bool is_one_parity; // only one parity appears in the subgame
      // todo : Not used yet
      bool is_one_player0; // one player subgame for player0 <-> p==false
      bool is_one_player1; // one player subgame for player1 <-> p==true
      all_parities_t all_parities;
    }; // subgame_info_t


    // A class to solve parity games
    // The current implementation is inspired by
    // by oink however without multicore and adapted to transition based
    // acceptance
    class parity_game
    {
    public:

      bool solve(const twa_graph_ptr& arena)
      {
        // todo check if reordering states according to scc is worth it
        set_up(arena);
        // Start recursive zielonka in a bottom-up fashion on each scc
        subgame_info_t subgame_info;
        for (c_scc_idx_ = 0; c_scc_idx_ < info_->scc_count(); ++c_scc_idx_)
          {
            // Testing
            // Make sure that every state that has a winner also
            // belongs to a subgame
            assert([&]()
                    {
                      for (unsigned i = 0; i < arena_->num_states(); ++i)
                        if (w_.has_winner_[i]
                            && (subgame_[i] == unseen_mark))
                          return false;
                        return true;
                    }());
            // Useless SCCs are winning for player 0.
            if (!info_->is_useful_scc(c_scc_idx_))
              {
                // This scc also gets its own subgame
                ++rd_;
                for (unsigned v: c_states())
                  {
                    subgame_[v] = rd_;
                    w_.set(v, false);
                    // The strategy for player 0 is to take the first
                    // available edge.
                    if ((*owner_ptr_)[v] == false)
                      for (const auto &e : arena_->out(v))
                        {
                          s_[v] = arena_->edge_number(e);
                          break;
                        }
                  }
                continue;
              }
            // Convert transitions leaving edges to self-loops
            // and check if trivially solvable
            subgame_info = fix_scc();
            // If empty, the scc was trivially solved
            if (!subgame_info.is_empty)
              {
                // Check for special cases
                if (subgame_info.is_one_parity)
                  one_par_subgame_solver(subgame_info, max_abs_par_);
                else
                  {
                    // "Regular" solver
                    max_abs_par_ = *subgame_info.all_parities.begin();
                    w_stack_.emplace_back(0, 0,
                                          min_par_graph_, max_abs_par_);
                    zielonka();
                  }
              }
          }
        // Every state needs a winner
//        print_hoa(std::cout, arena);
        assert(std::all_of(w_.has_winner_.cbegin(), w_.has_winner_.cend(),
                           [](bool b)
                           { return b; }));
        // Only the states owned by the winner need a strategy
        assert([&]()
               {
                  for (unsigned v = 0; v < arena_->num_states(); ++v)
                    {
                      if (((*owner_ptr_)[v] == w_.winner(v))
                          && ((s_[v] <= 0) || (s_[v] > arena_->num_edges())))
                        return false;
                    }
                  return true;
               }());

        // Put the solution as named property
        region_t &w = *arena->get_or_set_named_prop<region_t>("state-winner");
        strategy_t &s = *arena->get_or_set_named_prop<strategy_t>("strategy");
        w.swap(w_.winner_);
        s.reserve(s_.size());
        for (auto as : s_)
          s.push_back(as == no_strat_mark ? 0 : (unsigned) as);

        clean_up();
        return w[arena->get_init_state_number()];
      }

    private:

      // Returns the vector of states currently considered
      // i.e. the states of the current scc
      // c_scc_idx_ is set in the 'main' loop
      inline const std::vector<unsigned> &c_states()
      {
        assert(info_);
        return info_->states_of(c_scc_idx_);
      }

      void set_up(const twa_graph_ptr& arena)
      {
        owner_ptr_ = ensure_parity_game(arena, "solve_parity_game()");
        arena_ = arena;
        unsigned n_states = arena_->num_states();
        // Resize data structures
        subgame_.clear();
        subgame_.resize(n_states, unseen_mark);
        w_.has_winner_.clear();
        w_.has_winner_.resize(n_states, 0);
        w_.winner_.clear();
        w_.winner_.resize(n_states, 0);
        s_.clear();
        s_.resize(n_states, no_strat_mark);
        // Init
        rd_ = 0;
        info_ = std::make_unique<scc_info>(arena_);
        // Create all the parities
        bool max, odd;
        arena_->acc().is_parity(max, odd, true);
        max_abs_par_ = arena_->acc().all_sets().max_set()-1;
        // Make it the next larger odd
        par_t next_max_par_odd = max_abs_par_&1 ? max_abs_par_+2
                                                : max_abs_par_+1;
        all_edge_par_.resize(arena_->num_edges()+1);
        std::function<par_t(spot::acc_cond::mark_t m)> to_par_;
        if (max && odd)
          {
            min_par_graph_ = -1;
            max_par_graph_ = max_abs_par_;
            to_par_ = [](spot::acc_cond::mark_t m)
                        {
                          return (par_t)m.max_set() - 1;
                        };
          }
        else if (max && !odd)
          {
            // "Add 1" so even becomes odd
            max_abs_par_ += 1;
            min_par_graph_ = 0;
            max_par_graph_ = max_abs_par_;
            to_par_ = [](spot::acc_cond::mark_t m)
                        {
                          return (par_t)m.max_set();
                        };
          }
        else if (!max && odd)
          {
            max_abs_par_ = 1;
            min_par_graph_ = -next_max_par_odd;
            max_par_graph_ = 0;
            // Make sure no-color is the weakest
            to_par_ = [next_max_par_odd](spot::acc_cond::mark_t m)
                        {
                          par_t p = (par_t)m.min_set() - 1;
                          return p == -1 ? -next_max_par_odd : -p;
                        };
          }
        else if (!max && !odd)
          {
            max_abs_par_ = 0;
            min_par_graph_ = -next_max_par_odd;
            max_par_graph_ = -1;
            // Make sure no-color is the weakest
            to_par_ = [next_max_par_odd](spot::acc_cond::mark_t m)
                        {
                          par_t p = (par_t)m.min_set();
                          return p == 0 ? -next_max_par_odd : -p;
                        };
          }
        else
          throw std::runtime_error("Unreachable!");
        for (unsigned i = 1; i < arena_->num_edges() + 1; ++i)
          {
            all_edge_par_[i] = to_par_(arena_->edge_storage(i).acc);
            assert((min_par_graph_ <= all_edge_par_[i])
                    && (all_edge_par_[i] <= max_par_graph_));
          }
      }

      // Checks if an scc is empty and reports the occurring parities
      // or special cases
      inline subgame_info_t
      inspect_scc(par_t max_par)
      {
        subgame_info_t info;
        info.is_empty = true;
        info.is_one_player0 = true;
        info.is_one_player1 = true;
        for (unsigned v : c_states())
          {
            if (subgame_[v] != unseen_mark)
              continue;

            bool multi_edge = false;
            for (const auto &e : arena_->out(v))
              if (subgame_[e.dst] == unseen_mark)
                {
                  info.is_empty = false;
                  par_t this_par = to_par(e);
                  if (this_par <= max_par)
                    {
                      info.all_parities.insert(this_par);
                      multi_edge = true;
                    }
                }
            if (multi_edge)
              {
                // This state has multiple edges, so it is not
                // a one player subgame for !owner
                if ((*owner_ptr_)[v])
                  info.is_one_player1 = false;
                else
                  info.is_one_player0 = false;
              }
          } // v
        // todo is this always true?
        assert(info.all_parities.size() || info.is_empty);
        info.is_one_parity = info.all_parities.size() == 1;
        // Done
        return info;
      }

      // Computes the trivially solvable part of the scc
      // That is the states that can be attracted to an
      // outgoing transition
      inline subgame_info_t
      fix_scc()
      {
        // Note that the winner of the transitions
        // leaving the scc are already determined
        // attr(...) will only modify the
        // states within the current scc
        // but we have to "trick" it into
        // not disregarding the transitions leaving the scc
        // dummy needed to pass asserts
        max_abs_par_ = limit_par_even+2;
        // The attractors should define their own subgame
        // but as we want to compute the attractors of the
        // leaving transitions, we need to make
        // sure that
        // a) no transition is excluded due to its parity
        // b) no transition is considered accepting/winning
        //    due to its parity
        // Final note: Attractors cannot intersect by definition
        //             therefore the order in which they are computed
        //             is irrelevant
        unsigned dummy_rd = 0;
        // Attractor of outgoing transitions winning for env
        attr(dummy_rd, false, limit_par_even, true, limit_par_even, false);
        // Attractor of outgoing transitions winning for player
        attr(dummy_rd, true, limit_par_even+1, true, limit_par_even+1, false);

        // No strategy fix need
        // assert if all winning states of the current scc have a valid strategy

        assert([&]()
               {
                 for (unsigned v : c_states())
                   {
                     if (!w_.has_winner_[v])
                       continue;
                     // We only need a strategy if the winner
                     // of the state is also the owner
                     if (w_.winner(v) != (*owner_ptr_)[v])
                       continue;
                     if (s_[v] <= 0)
                       {
                         std::cerr << "state " << v << " has a winner "
                                   << w_.winner(v) << " and owner "
                                   << (*owner_ptr_)[v]
                                   << " but no strategy "
                                   << s_[v] << '\n';
                         return false;
                       }
                     const auto& e = arena_->edge_storage(s_[v]);
                     if (!w_.has_winner_[e.dst]
                         || (w_.winner(e.src) != w_.winner(e.dst)))
                       {
                         std::cerr << "state " << v << " has a winner "
                                   << w_.winner(v)
                                   << " but no valid strategy\n";
                         return false;
                       }
                   }
                 return true;
               }());

        auto ins = inspect_scc(limit_par_even);
        max_abs_par_ = ins.is_empty ? max_par_graph_
                                    : *ins.all_parities.begin();
        return ins;
      } // fix_scc

      inline bool
      attr(unsigned &rd, bool p, par_t max_par,
           bool acc_par, par_t min_win_par, bool respect_sg=true)
      {
        // Computes the attractor of the winning set of player p within a
        // subgame given as rd.
        // If acc_par is true, max_par transitions are also accepting and
        // the subgame count will be increased
        // The attracted vertices are directly added to the set

        // Increase rd meaning we create a new subgame
        if (acc_par)
          rd = ++rd_;
        // todo replace with a variant of topo sort ?
        // As proposed in Oink! / PGSolver
        // Needs the transposed graph however

        assert((!acc_par) || (acc_par && to_player(max_par) == p));
        assert(!acc_par || (min_par_graph_ <= min_win_par));
        assert((min_win_par <= max_par) && (max_par <= max_abs_par_));

        bool grown = false;
        // We could also directly mark states as owned,
        // instead of adding them to to_add first,
        // possibly reducing the number of iterations.
        // However by making the algorithm complete a loop
        // before adding it is like a backward bfs and (generally) reduces
        // the size of the strategy
        static std::vector<unsigned> to_add;

        assert(to_add.empty());

        do
          {
            grown |= !to_add.empty();
            for (unsigned v : to_add)
              {
                // v is winning
                w_.set(v, p);
                // Mark if demanded
                if (acc_par)
                  {
                    assert(subgame_[v] == unseen_mark);
                    subgame_[v] = rd;
                  }
              }
            to_add.clear();

            for (unsigned v : c_states())
              {
                if ((subgame_[v] < rd) || (w_(v, p)))
                  // Not in subgame or winning for p
                  continue;

                bool is_owned = (*owner_ptr_)[v] == p;
                bool wins = !is_owned;
                // Loop over out-going

                // Optim: If given the choice,
                // we seek to go to the "oldest" subgame
                // That is the subgame with the lowest rd value
                unsigned min_subgame_idx = unseen_mark;
                for (const auto &e: arena_->out(v))
                  {
                    par_t this_par = to_par(e);
                    if ((!respect_sg || (subgame_[e.dst] >= rd))
                         && (this_par <= max_par))
                      {
                        // Check if winning
                        if (w_(e.dst, p)
                            || (acc_par && (min_win_par <= this_par)))
                          {
                            assert(!acc_par || (this_par < min_win_par) ||
                                   (acc_par && (min_win_par <= this_par) &&
                                    (to_player(this_par) == p)));
                            if (is_owned)
                              {
                                wins = true;
                                if (acc_par)
                                  {
                                    s_[v] = arena_->edge_number(e);
                                    if (min_win_par <= this_par)
                                      // max par edge
                                      // change sign -> mark as needs
                                      // to be possibly fixed
                                      s_[v] = -s_[v];
                                    break;
                                  }
                                else
                                  {
                                    //snapping
                                    if (subgame_[e.dst] < min_subgame_idx)
                                      {
                                        s_[v] = arena_->edge_number(e);
                                        min_subgame_idx = subgame_[e.dst];
                                        if (!p)
                                          // No optim for env
                                          break;
                                      }
                                  }
                              }// owned
                          }
                        else
                          {
                            if (!is_owned)
                              {
                                wins = false;
                                break;
                              }
                          } // winning
                      } // subgame
                  }// for edges
                if (wins)
                  to_add.push_back(v);
              } // for v
          } while (!to_add.empty());
        // done

        assert(to_add.empty());
        return grown;
      }

      // We need to check if transitions that are accepted due
      // to their parity remain in the winning region of p
      inline bool
      fix_strat_acc(unsigned rd, bool p, par_t min_win_par, par_t max_par)
      {
        for (unsigned v : c_states())
          {
            // Only current attractor and owned
            // and winning vertices are concerned
            if ((subgame_[v] != rd) || !w_(v, p)
                || ((*owner_ptr_)[v] != p) || (s_[v] > 0))
              continue;

            // owned winning vertex of attractor
            // Get the strategy edge
            s_[v] = -s_[v];
            const auto &e_s = arena_->edge_storage(s_[v]);
            // Optimization only for player
            if (!p && w_(e_s.dst, p))
              // If current strat is admissible ->
              // nothing to do for env
              continue;

            // This is an accepting edge that is no longer admissible
            // or we seek a more desirable edge (for player)
            assert(min_win_par <= to_par(e_s));
            assert(to_par(e_s) <= max_par);

            // Strategy heuristic : go to the oldest subgame
            unsigned min_subgame_idx = unseen_mark;

            s_[v] = no_strat_mark;
            for (const auto &e_fix : arena_->out(v))
              {
                if (subgame_[e_fix.dst] >= rd)
                  {
                    par_t this_par = to_par(e_fix);
                    // This edge must have less than max_par,
                    // otherwise it would have already been attracted
                    assert((this_par <= max_par)
                           || (to_player(this_par) != (max_par&1)));
                    // if it is accepting and leads to the winning region
                    // -> valid fix
                    if ((min_win_par <= this_par)
                        && (this_par <= max_par)
                        && w_(e_fix.dst, p)
                        && (subgame_[e_fix.dst] < min_subgame_idx))
                      {
                        // Max par edge to older subgame found
                        s_[v] = arena_->edge_number(e_fix);
                        min_subgame_idx = subgame_[e_fix.dst];
                      }
                  }
              }
            if (s_[v] == no_strat_mark)
              // NO fix found
              // This state is NOT won by p due to any accepting edges
              return true; // true -> grown
          }
        // Nothing to fix or all fixed
        return false; // false -> not grown == all good
      }

      inline void zielonka()
      {
        while (!w_stack_.empty())
          {
            auto this_work = w_stack_.back();
            w_stack_.pop_back();

            switch (this_work.wstep)
              {
              case (0):
                {
                  assert(this_work.rd == 0);
                  assert(this_work.min_par == min_par_graph_);

                  unsigned rd;
                  assert(this_work.max_par <= max_abs_par_);

                  // Check if empty and get parities
                  subgame_info_t subgame_info =
                    inspect_scc(this_work.max_par);

                  if (subgame_info.is_empty)
                    // Nothing to do
                    break;
                  if (subgame_info.is_one_parity)
                    {
                      // Can be trivially solved
                      one_par_subgame_solver(subgame_info, this_work.max_par);
                      break;
                    }

                  // Compute the winning parity boundaries
                  // -> Priority compression
                  // Optional, improves performance
                  // Highest actually occurring
                  // Attention in partially colored graphs
                  // the parity -1 and 0 appear
                  assert(subgame_info.all_parities.size());
                  par_t max_par = *subgame_info.all_parities.begin();
                  par_t min_win_par = max_par;
                  while ((min_win_par >= (min_par_graph_+2)) &&
                         (!subgame_info.all_parities.count(min_win_par - 1)))
                    min_win_par -= 2;
                  assert(min_win_par >= min_par_graph_);
                  assert(max_par >= min_win_par);
                  assert((max_par&1) == (min_win_par&1));
                  assert(!subgame_info.all_parities.empty());

                  // Get the player
                  bool p = to_player(min_win_par);
                  // Attraction to highest par
                  // This increases rd_ and passes it to rd
                  attr(rd, p, max_par, true, min_win_par);
                  // All those attracted get subgame_[v] <- rd

                  // Continuation
                  w_stack_.emplace_back(1, rd, min_win_par, max_par);
                  // Recursion
                  w_stack_.emplace_back(0, 0, min_par_graph_,
                                        min_win_par - 1);
                  // Others attracted will have higher counts in subgame
                  break;
                }
              case (1):
                {
                  unsigned rd = this_work.rd;
                  par_t min_win_par = this_work.min_par;
                  par_t max_par = this_work.max_par;
                  assert(to_player(min_win_par) == to_player(max_par));
                  bool p = to_player(min_win_par);
                  // Check if the attractor of w_[!p] is equal to w_[!p]
                  // if so, player wins if there remain accepting transitions
                  // for max_par (see fix_strat_acc)
                  // This does not increase but reuse rd
                  bool grown = attr(rd, !p, max_par, false, min_win_par);
                  // todo investigate: A is an attractor, so the only way that
                  // attr(w[!p]) != w[!p] is if the max par "exit" edges lead
                  // to a trap for player/ exit the winning region of the
                  // player so we can do a fast check instead of the
                  // generic attr computation which only needs to be done
                  // if the fast check is positive

                  // Check if strategy needs to be fixed / is fixable
                  if (!grown)
                    // this only concerns parity accepting edges
                    grown = fix_strat_acc(rd, p, min_win_par, max_par);
                  // If !grown we are done, and the partitions are valid

                  if (grown)
                    {
                      // Reset current game without !p attractor
                      for (unsigned v : c_states())
                        if (!w_(v, !p) && (subgame_[v] >= rd))
                          {
                            // delete ownership
                            w_.unset(v);
                            // Mark as unseen
                            subgame_[v] = unseen_mark;
                            // Unset strat for testing
                            s_[v] = no_strat_mark;
                          }
                      w_stack_.emplace_back(0, 0, min_par_graph_, max_par);
                      // No need to do anything else
                      // the attractor of !p of this level is not changed
                    }
                  break;
                }
              default:
                throw std::runtime_error("No valid workstep");
              } // switch
          } // while
      } // zielonka

      // Empty all internal variables
      inline void clean_up()
      {
        info_ = nullptr;
        subgame_.clear();
        w_.has_winner_.clear();
        w_.winner_.clear();
        s_.clear();
        rd_ = 0;
        max_abs_par_ = 0;
      }

      // Dedicated solver for special cases
      inline void one_par_subgame_solver(const subgame_info_t &info,
                                         par_t max_par)
      {
        assert(info.all_parities.size() == 1);
        // The entire subgame is won by the player of the only parity
        // Any edge will do
        // todo optim for smaller circuit
        // This subgame gets its own counter
        ++rd_;
        unsigned rd = rd_;
        par_t one_par = *info.all_parities.begin();
        bool winner = to_player(one_par);
        assert(one_par <= max_par);

        for (unsigned v : c_states())
          {
            if (subgame_[v] != unseen_mark)
              continue;
            // State of the subgame
            subgame_[v] = rd;
            w_.set(v, winner);
            // Get the strategy
            assert(s_[v] == no_strat_mark);
            for (const auto &e : arena_->out(v))
              {
                par_t this_par = to_par(e);
                if ((subgame_[e.dst] >= rd) && (this_par <= max_par))
                  {
                    assert(this_par == one_par);
                    // Ok for strat
                    s_[v] = arena_->edge_number(e);
                    break;
                  }
              }
            assert((0 < s_[v]) && (s_[v] < unseen_mark));
          }
        // Done
      }

      template <class EDGE>
      inline par_t
      to_par(const EDGE& e)
      {
        return all_edge_par_[arena_->edge_number(e)];
      }

      inline bool
      to_player(par_t par)
      {
        return par & 1;
      }

      twa_graph_ptr arena_;
      const std::vector<bool> *owner_ptr_;
      unsigned rd_;
      winner_t w_;
      // Subgame array similar to the one from oink!
      std::vector<unsigned> subgame_;
      // strategies for env and player; For synthesis only player is needed
      // We need a signed value here in order to "fix" the strategy
      // during construction
      std::vector<strat_t> s_;

      // Informations about sccs andthe current scc
      std::unique_ptr<scc_info> info_;
      par_t max_abs_par_; // Max parity occurring in the current scc
      // Minimal and maximal parity occurring in the entire graph
      par_t min_par_graph_, max_par_graph_;
      // Info on the current scc
      unsigned c_scc_idx_;
      // Change recursive calls to stack
      std::vector<work_t> w_stack_;
      // Directly store a vector of parities
      // This vector will be created such
      // that it takes care of the actual parity condition
      // and after that zielonka can be called as if max odd
      std::vector<par_t> all_edge_par_;
    };

    template<class ACCFUN>
    void add_transposed_here_impl(const twa_graph_ptr& arena,
                                  ACCFUN accfun)
    {

      auto* gt = new transposed_graph_t();
      gt->new_states(arena->num_states());
      for (unsigned e_idx = 1; e_idx < arena->num_edges()+1; ++e_idx)
      {
        const auto& e = arena->edge_storage(e_idx);
        gt->new_edge(e.dst, e.src, accfun(e.acc));
      }
      // This destroys old one
      arena->set_named_prop<transposed_graph_t>("transposed", gt);
    }

    twa_graph_ptr
    highlight_strategy_false_impl_(twa_graph_ptr& aut,
                       int player0_color,
                       int player1_color)
    {
      auto owner = ensure_game(aut, "highlight_strategy()");
      region_t* w = aut->get_named_prop<region_t>("state-winner");
      strategy_t* s = aut->get_named_prop<strategy_t>("strategy");
      if (!w)
        throw std::runtime_error
            ("highlight_strategy(): "
             "winning region unavailable, solve the game first");
      if (!s)
        throw std::runtime_error
            ("highlight_strategy(): strategy unavailable, "
             "solve the game first");

      unsigned ns = aut->num_states();
      auto* hl_edges =
          aut->get_or_set_named_prop<std::map<unsigned, unsigned>>
          ("highlight-edges");
      auto* hl_states =
          aut->get_or_set_named_prop<std::map<unsigned, unsigned>>
          ("highlight-states");

      if (unsigned sz = std::min(w->size(), s->size()); sz < ns)
        ns = sz;

      for (unsigned n = 0; n < ns; ++n)
      {
        int color = (*w)[n] ? player1_color : player0_color;
        if (color == -1)
          continue;
        (*hl_states)[n] = color;
        if ((*w)[n] == (*owner)[n])
          (*hl_edges)[(*s)[n]] = color;
      }

      return aut;
    }

    twa_graph_ptr
    highlight_strategy_true_impl_(twa_graph_ptr& aut,
                                  int player0_color,
                                  int player1_color)
    {
      auto owner = ensure_game(aut, "highlight_strategy()");
      region_t* w = aut->get_named_prop<region_t>("state-winner");
      attr_strategy_t* as =
          aut->get_named_prop<attr_strategy_t>("attr-strategy");
      if (!w)
        throw std::runtime_error
            ("highlight_strategy(): "
             "winning region unavailable, solve the game first");
      if (!as)
        throw std::runtime_error
            ("highlight_strategy(): "
             "attractor strategy unavailable");

      std::vector<std::string>* snames =
          aut->get_or_set_named_prop<std::vector<std::string>>("state-names");

      unsigned ns = aut->num_states();

      if (snames->empty())
        for (unsigned i = 0; i < ns; ++i)
          snames->emplace_back(std::to_string(i));

      // Note:
      // If env wins a state there has to be an edge to
      // another state won by env
      // If player wins a state there has to be an edge to a lower lvl
      // or if lvl == 0 then there has to be an edge to another winning state
      // independent of its lvl
      auto* hl_edges =
          aut->get_or_set_named_prop<std::map<unsigned, unsigned>>
          ("highlight-edges");
      auto* hl_states =
          aut->get_or_set_named_prop<std::map<unsigned, unsigned>>
          ("highlight-states");

      if (ns != w->size())
        throw std::runtime_error("Winning region does not "
                                 "have the correct size");
      if (ns != as->size())
        throw std::runtime_error("Attractor strat does not "
                                 "have the correct size");

      for (unsigned n = 0; n < ns; ++n)
        {
          int color = (*w)[n] ? player1_color : player0_color;
          if (color == -1)
            continue;
          (*hl_states)[n] = color;
          if ((*w)[n])
            (*snames)[n] += std::string("-") + std::to_string((*as)[n]);
          if ((*w)[n] != (*owner)[n])
            continue;
          if ((*w)[n])
            {
              for (const auto&e : aut->out(n))
                if (((*as)[e.src] > (*as)[e.dst])
                    or ((*as)[e.src] == 0 and (*w)[n]))
                  (*hl_edges)[aut->edge_number(e)] = color;
            }
          else
            for (const auto& e : aut->out(n))
              if (not (*w)[e.dst])
                (*hl_edges)[aut->edge_number(e)] = color;
        }

      return aut;
    }

    // fp0 are called with lvl src, lvl dst and edge
    template <class FP0, class FP1>
    void attractor_strat_to_concrete_(const twa_graph_ptr& arena,
                                      bool do_p0, FP0 fp0,
                                      bool do_p1, FP1 fp1)
    {
      // A strategy for "most" games can be derived the following way for both
      // players:
      // Player 1: Either lvl > best_lvl_p1, then take an edge leading you
      //           to a lower lvl. If at the lowest lvl: take an edge back
      //           to the winning region. All edges taken must verify fp1.
      // Player 0 : Either lvl < best_lvl_p1, then take an edge leading you
      //            to a higher lvl. If at the highest lvl (best_lvl_p0):
      //            take any edge WITHIN the best lvl.
      //            All edges must verify fp0
      //            This ensures that no "accepting edge" is taken
      //            infinitely often in the best_lvl_p0.

      // #todo parity games

      using lvl_t = decltype(best_lvl_p0());

      auto* sp_ptr =
          arena->get_named_prop<region_t>("state-player");
      if (!sp_ptr)
        throw std::runtime_error("Needs state-player");
      auto& sp = *sp_ptr;

      auto* as_ptr =
          arena->get_named_prop<attr_strategy_t>("attr-strategy");
      if (!as_ptr)
        throw std::runtime_error("Needs attr-strategy");
      auto& as = *as_ptr;
      // There should be no 0 in the attr strategy as the games are determined
      // so the arena has to be split between the two players

      auto* strat_ptr =
          arena->get_or_set_named_prop<strategy_t>("strategy");
      strat_ptr->resize(arena->num_states());
      std::fill(strat_ptr->begin(), strat_ptr->end(), -1u);
      auto& strat = *strat_ptr;

      auto* w_ptr =
          arena->get_or_set_named_prop<region_t>("state-winner");
      w_ptr->resize(arena->num_states());
      auto& w = *w_ptr;

      // We only need a strategy for states
      // that are won and owned by the same player
      auto ns = arena->num_states();
      for (unsigned s = 0; s < ns; ++s)
        {
          // Winning if attracted
          w[s] = best_lvl_p1() <= as[s];
          // Need strat?
          if (w[s] != sp[s])
            continue;
          if (not sp[s] and do_p0)
            {
              // Descend if not at best lvl
              lvl_t w_lvl = as[s] - (as[s] != best_lvl_p0());
              for (const auto&e : arena->out(s))
                if (w_lvl <= as[e.dst] and as[e.dst] <= best_lvl_p0()
                    and fp0(as[e.src], as[e.dst], e))
                {
                  w_lvl = as[e.dst];
                  strat[s] = arena->edge_number(e);
                }
            }
          if (sp[s] and do_p1)
            {
              lvl_t w_lvl = as[s] == best_lvl_p1()
                                ? std::numeric_limits<lvl_t>::max()
                                : as[s];
              for (const auto&e : arena->out(s))
                if (best_lvl_p1() <= as[e.dst] and as[e.dst] < w_lvl
                    and fp1(as[e.src], as[e.dst], e))
                  {
                    w_lvl = as[e.dst];
                    strat[s] = arena->edge_number(e);
                  }
            }

        }
    }

    bool solve_deadlock_game_detailed(const twa_graph_ptr& arena)
    {
      // A deadlock game is won for player 1 if it can
      // attract the initial state to any state without outgoing edges
      // Therefore it will only accept finite words
      // Note that this is abusing the attractor
      // computation as 'arena' is not a proper arena in the
      // case
      auto* as_ptr =
          arena->get_or_set_named_prop<attr_strategy_t>("attr-strategy");
      as_ptr->resize(arena->num_states());
      std::fill(as_ptr->begin(), as_ptr->end(), game_unseen_lvl());

      attractor(arena, *as_ptr, true);
      // The complement of an attractor is a trap
      // Therefore all states not in the attractor win for player 0
      std::for_each(as_ptr->begin(), as_ptr->end(),
                    [](auto& val)->void
                      {val = (val == game_unseen_lvl()) ? best_lvl_p0()
                                                        : val; });

      // Deduce the winning regions and an actual strategy
      // for both players, all edges are allowed
      auto nofilt = [](const auto&...)noexcept{return true; };
      attractor_strat_to_concrete_(arena, true, nofilt,
                                          true, nofilt);

      return (*as_ptr)[arena->get_init_state_number()] >= best_lvl_p1();
    }

    bool solve_liveliness_game_detailed(const twa_graph_ptr& arena)
    {
      dualize_arena_here(arena);
      bool dual_player_win =
          solve_deadlock_game_detailed(arena);
      dualize_arena_here(arena);
      return not dual_player_win;
    }

    bool solve_reach_detailed(const twa_graph_ptr& arena)
    {
      // Here we want to see a (0) at least once
      // Attention, to get valid results we need to have
      // a proper arena
      // todo add check?
      auto* sp_ptr =
          arena->get_named_prop<region_t>("state-player");
      if (!sp_ptr)
        throw std::runtime_error("Needs state-player");

      transposed_graph_t * gt =
          arena->get_named_prop<transposed_graph_t>("transposed");
      if (not gt)
        throw std::runtime_error("Needs transposed graph");

      attr_strategy_t* astrat_ptr =
          arena->get_or_set_named_prop<attr_strategy_t>("attr-strategy");
      astrat_ptr->resize(arena->num_states());
      std::fill(astrat_ptr->begin(), astrat_ptr->end(), game_unseen_lvl());

      auto ffa = [](const auto& e, const auto&...)
          {
            return e.acc == acc_cond::mark_t({0});
          };

      attractor_filt<true>(arena, *sp_ptr, *gt, *astrat_ptr,
                           [](const auto&...)noexcept{return true; },
                           ffa);
      // Again, all that have not been attracted form a trap
      std::transform(astrat_ptr->cbegin(), astrat_ptr->cend(),
                     astrat_ptr->begin(), [](const auto& lvl)
                     {
                       return lvl == game_unseen_lvl() ? best_lvl_p0()
                                                       : lvl;
                     });
      // Deduce the winning regions and an actual strategy
      // Note that here, the best level for player has to go
      // through an accepting edge
      // On the other hand, in order to enforce (0) free circles,
      // env is forbidden to take (0) transitions on best lvl
      // These functions will be called with lvl src, lvl dst and edge
      auto fp0_best =
          [sp_ptr, ffa](const auto& lvl_src,
                         const auto&,
                         const auto& e)
          {
            assert(lvl_src <= best_lvl_p0()
                   and not (*sp_ptr)[e.src]
                   && "P0 filter called on an invalid state");
            return (lvl_src < best_lvl_p0())
                   or not ffa(e);
          };
      auto fp1_best =
          [sp_ptr, ffa](const auto& lvl_src,
                        const auto&,
                        const auto& e)
          {
            assert(lvl_src >= best_lvl_p1()
                   && (*sp_ptr)[e.src]
                   && "P1 filter called on an invalid state");
            // Note all player states with accepting edge
            // are in the best lvl
            return (lvl_src > best_lvl_p1())
                   or ffa(e);
          };
      // we can deduce a strat for both players
      attractor_strat_to_concrete_(arena, true, fp0_best,
                                          true, fp1_best);

      return (*astrat_ptr)[arena->get_init_state_number()] >= best_lvl_p1();
    }

    bool solve_avoid_detailed(const twa_graph_ptr& arena)
    {
      // This is the dual of reach
      dualize_arena_here(arena);
      bool dual_player_win =
          solve_reach_detailed(arena);
      dualize_arena_here(arena);
      return not dual_player_win;
    }

    // Todo there are better ways to do this (I think), but they have to be
    // adapted for transition based acceptance
    // Like https://arxiv.org/pdf/1109.5018.pdf
    // Another idea is to initialize by computing the attractor
    // of (0) and then add the condition of leading back to winning.
    // caveat: Keep the lvls in order!
    bool solve_buechi_detailed(const twa_graph_ptr& arena)
    {
      // To compute buechi acceptance we do the following:
      // In the first round we declare all transitions
      // accepting which have (0).
      // In all further iterations we only accept transitions
      // that lead back to the winning region of the last iteration
      // This is repeated until a fix point is reached
      // Note that this only gives rise to a strategy for
      // player not env, env needs additional computation
      // that is not done by default
      auto* sp_ptr =
          arena->get_named_prop<region_t>("state-player");
      if (!sp_ptr)
        throw std::runtime_error("Needs state-player");

      transposed_graph_t * gt =
          arena->get_named_prop<transposed_graph_t>("transposed");
      if (not gt)
        throw std::runtime_error("Needs transposed graph");

      attr_strategy_t attr_lvl(arena->num_states(), game_unseen_lvl());

      auto finalize = [&attr_lvl]()
        {
          std::transform(attr_lvl.cbegin(), attr_lvl.cend(),
                         attr_lvl.begin(), [](const auto& lvl)
                         {
                           return lvl == game_unseen_lvl() ? best_lvl_p0()
                                                           : lvl;
                         });
        };

      // init
      unsigned n_attr_new, n_attr_old;
      {
        auto ffai = [](const auto& e, const auto&...)
          {
            return e.acc == acc_cond::mark_t({0});
          };
        n_attr_new =
            attractor_filt<true>(arena, *sp_ptr, *gt, attr_lvl,
                           [](const auto&...)noexcept{return true; },
                           ffai);
        if (n_attr_new == 0)
          // No additional vertices could be attracted ->
          // unseen vertices got to env
          {
            finalize();
            return 0;
          }
      }
      // We could attract at least one additional vertex
      // -> Iterate
      attr_strategy_t& attr_lvl_new = attr_lvl;
      attr_strategy_t attr_lvl_old(arena->num_states());
      // Define a new acceptance criteria
      auto ffa = [&attr_lvl_old](const auto& e, const auto&...)
        {
          return e.acc == acc_cond::mark_t({0})
                 and (best_lvl_p1() <= attr_lvl_old[e.dst]);
        };

      while (true)
        {
          n_attr_old = n_attr_new;
          std::swap(attr_lvl_new, attr_lvl_old);
          n_attr_new =
              attractor_filt<true>(arena, *sp_ptr, *gt, attr_lvl_new,
                             [](const auto&...)noexcept{return true; },
                             ffa);
          if (n_attr_new == n_attr_old)
            break;
        }

      // Solving done
      finalize();
      bool p1wins = best_lvl_p1()
                    <= attr_lvl_new[arena->get_init_state_number()];
      arena->set_named_prop<attr_strategy_t>("attr-strategy",
          new attr_strategy_t(std::move(attr_lvl)));
      // Deduce the winning regions and an actual strategy
      // Note that here, the best level for player has to go
      // through an accepting edge
      // On the other hand, in order to enforce (0) free circles,
      // env is forbidden to take (0) transitions on best lvl
      // These functions will be called with lvl src, lvl dst and edge
      auto fp0_best =
          [sp_ptr, ffa](const auto& lvl_src,
                         const auto&,
                         const auto& e)
          {
            assert(lvl_src <= best_lvl_p0()
                   and not (*sp_ptr)[e.src]
                   && "P0 filter called on an invalid state");
            return (lvl_src < best_lvl_p0())
                   or not ffa(e);
          };
      auto fp1_best =
          [sp_ptr, &ffa](const auto& lvl_src,
                         const auto&,
                         const auto& e)
          {
            assert(lvl_src >= best_lvl_p1()
                   && (*sp_ptr)[e.src]
                   && "P1 filter called on an invalid state");
            // Note all player states with accepting edge
            // are in the best lvl
            return (lvl_src > best_lvl_p1())
                   or ffa(e);
          };
      // we can deduce a strat for both players
      attractor_strat_to_concrete_(arena, true, fp0_best,
                                          true, fp1_best);
      return p1wins;
    }

    bool solve_co_buechi_detailed(const twa_graph_ptr& arena)
    {
      // This is the dual of reach
      dualize_arena_here(arena);
      bool dual_player_win =
          solve_buechi_detailed(arena);
      dualize_arena_here(arena);
      return not dual_player_win;
    }

  } // anonymous

  void add_transposed_here(const twa_graph_ptr& arena)
  {

    if (arena->acc().is_f())
      {
        auto facc = [](acc_cond::mark_t)
          {
            return std::make_pair(acc_cond::mark_t({}), 0);
          };
        return add_transposed_here_impl(arena, facc);
      }
    else if (arena->acc().is_t() or
             arena->acc().is_buchi())
      return add_transposed_here_impl(arena,
                                      [](acc_cond::mark_t acc)
                                        {
                                           return std::make_pair(acc, 0);
                                        });
    else if (arena->acc().is_parity())
      {
        bool max, odd;
        arena->acc().is_parity(max, odd, true);
        int max_abs_par = arena->acc().all_sets().max_set()-1;
        // Make it the next larger odd
        par_t next_max_par_odd = max_abs_par&1 ? max_abs_par+2
                                                : max_abs_par+1;

        if (max && odd)
          {
            auto facc = [](acc_cond::mark_t m)
              {
                return std::make_pair(m, (par_t)m.max_set() - 1);
              };
            return add_transposed_here_impl(arena, facc);
          }
        else if (max && !odd)
          {
            // "Add 1" so even becomes odd
            auto facc = [](acc_cond::mark_t m)
              {
                return std::make_pair(m, (par_t)m.max_set());
              };
            return add_transposed_here_impl(arena, facc);
          }
        else if (!max && odd)
          {
            // Make sure no-color is the weakest
            auto facc = [next_max_par_odd](acc_cond::mark_t m)
              {
                par_t p = (par_t)m.min_set() - 1;
                return std::make_pair(m, p == -1 ? -next_max_par_odd : -p);
              };
            return add_transposed_here_impl(arena, facc);
          }
        else if (!max && !odd)
          {
            // Make sure no-color is the weakest
            auto facc = [next_max_par_odd](spot::acc_cond::mark_t m)
              {
                par_t p = (par_t)m.min_set();
                return std::make_pair(m, p == 0 ? -next_max_par_odd : -p);
              };
            return add_transposed_here_impl(arena, facc);
          }
        else
          throw std::runtime_error("Unreachable!");
      }
    throw std::runtime_error("Acceptance cond is not implemented yet");
  }

  void dualize_arena_here(const twa_graph_ptr& arena)
  {
    if (auto* owner_ptr =
        arena->get_named_prop<std::vector<bool>>("state-player"))
      owner_ptr->flip();
    else
      throw std::runtime_error("Arena has no \"state-player\"");

    // We also need to flip winners and and attractor strategies
    // if given to keep results consistent
    // Note that flipping attractors might then not be compatible with
    //attractor_strat_to_concrete_!
    if (auto* w_ptr =
        arena->get_named_prop<region_t>("state-winner"))
      w_ptr->flip();
    if (auto* as_ptr =
        arena->get_named_prop<attr_strategy_t>("attr-strategy"))
      std::transform(as_ptr->cbegin(),
                     as_ptr->cend(),
                     as_ptr->begin(),
                     std::negate<attr_strategy_t::value_type>());
  }

  unsigned cpre(const const_twa_graph_ptr& arena, const region_t& s_player,
                const transposed_graph_t& gt, attr_strategy_t& attr_strat,
                bool player,
                attr_strategy_t::value_type new_num)
  {
    // This is the "basic" version with no filters applies
    auto ffe = [](const auto&...){return true; };
    auto ffa = [](const auto&...){return false; };
    if (player)
      return cpre_filt<true>(arena, s_player, gt, attr_strat,
                             new_num, ffe, ffa);
    else
      return cpre_filt<false>(arena, s_player, gt, attr_strat,
                              new_num, ffe, ffa);
  }

  unsigned cpre(const const_twa_graph_ptr& arena, attr_strategy_t& attr_strat,
                bool player, attr_strategy_t::value_type new_num)
  {
    const region_t* const s_player =
        arena->get_named_prop<region_t>("state-player");
    if (!s_player)
      throw std::runtime_error("Arena does not have state-player!");
    const transposed_graph_t* gt =
        arena->get_named_prop<transposed_graph_t>("transposed");
    if (!gt)
      throw std::runtime_error("Arena has no transposed graph!");
    return cpre(arena, *s_player, *gt, attr_strat, player, new_num);
  }

  unsigned attractor(const const_twa_graph_ptr& arena,
                     const region_t& s_player,
                     transposed_graph_t& gt,
                     attr_strategy_t& attr_strat, bool player)
  {
    auto ffe = [](const auto&...)noexcept{return true; };
    auto ffa = [](const auto&...)noexcept{return false; };
    if (player)
      return attractor_filt<true>(arena, s_player, gt, attr_strat,
                                  ffe, ffa);
    else
      return attractor_filt<false>(arena, s_player, gt, attr_strat,
                                   ffe, ffa);
  }

  unsigned attractor(const const_twa_graph_ptr& arena,
                     attr_strategy_t& attr_strat, bool player)
  {
    const region_t* const s_player =
        arena->get_named_prop<region_t>("state-player");
    if (!s_player)
      throw std::runtime_error("Arena does not have state-player!");
    transposed_graph_t* gt =
        arena->get_named_prop<transposed_graph_t>("transposed");
    if (!gt)
      throw std::runtime_error("Arena has no transposed graph!");
    return attractor(arena, *s_player, *gt, attr_strat, player);
  }


  bool solve_parity_game(const twa_graph_ptr& arena)
  {
    parity_game pg;
    return pg.solve(arena);
  }

  void pg_print(std::ostream& os, const const_twa_graph_ptr& arena)
  {
    auto owner = ensure_parity_game(arena, "pg_print");

    auto arena_ = reduce_parity(arena, true);
    change_parity_here(arena_, parity_kind_max, parity_style_odd);

    unsigned ns = arena_->num_states();
    unsigned init = arena_->get_init_state_number();
    os << "parity " << ns - 1 << ";\n";
    std::vector<bool> seen(ns, false);
    std::vector<unsigned> todo({init});
    while (!todo.empty())
      {
        unsigned src = todo.back();
        todo.pop_back();
        if (seen[src])
          continue;
        seen[src] = true;
        os << src << ' ';
        os << arena_->out(src).begin()->acc.max_set() - 1 << ' ';
        os << (*owner)[src] << ' ';
        bool first = true;
        for (auto& e: arena_->out(src))
          {
            if (!first)
              os << ',';
            first = false;
            os << e.dst;
            if (!seen[e.dst])
              todo.push_back(e.dst);
          }
        if (src == init)
          os << " \"INIT\"";
        os << ";\n";
      }
  }

  void alternate_players(spot::twa_graph_ptr& arena,
                         bool first_player, bool complete0)
  {
    auto um = arena->acc().unsat_mark();
    if (!um.first)
      throw std::runtime_error
        ("alternate_players(): game winning condition is a tautology");

    unsigned sink_env = 0;
    unsigned sink_con = 0;

    std::vector<bool> seen(arena->num_states(), false);
    unsigned init = arena->get_init_state_number();
    std::vector<unsigned> todo({init});
    auto owner = new std::vector<bool>(arena->num_states(), false);
    (*owner)[init] = first_player;
    while (!todo.empty())
      {
        unsigned src = todo.back();
        todo.pop_back();
        seen[src] = true;
        bdd missing = bddtrue;
        for (const auto& e: arena->out(src))
          {
            bool osrc = (*owner)[src];
            if (complete0 && !osrc)
              missing -= e.cond;

            if (!seen[e.dst])
              {
                (*owner)[e.dst] = !osrc;
                todo.push_back(e.dst);
              }
            else if ((*owner)[e.dst] == osrc)
              {
                delete owner;
                throw
                  std::runtime_error("alternate_players(): odd cycle detected");
              }
          }
        if (complete0 && !(*owner)[src] && missing != bddfalse)
          {
            if (sink_env == 0)
              {
                sink_env = arena->new_state();
                sink_con = arena->new_state();
                owner->push_back(true);
                owner->push_back(false);
                arena->new_edge(sink_con, sink_env, bddtrue, um.second);
                arena->new_edge(sink_env, sink_con, bddtrue, um.second);
              }
            arena->new_edge(src, sink_con, missing, um.second);
          }
      }

    arena->set_named_prop("state-player", owner);
  }

  twa_graph_ptr
  highlight_strategy(twa_graph_ptr& aut,
                     int player0_color,
                     int player1_color,
                     bool use_attractor)
  {
    if (use_attractor)
      return highlight_strategy_true_impl_(aut, player0_color, player1_color);
    else
      return highlight_strategy_false_impl_(aut, player0_color, player1_color);
  }

  void set_state_players(twa_graph_ptr arena, region_t owners)
  {
    std::vector<bool>* owners_ptr = new std::vector<bool>(std::move(owners));
    set_state_players(arena, owners_ptr);
  }

  void set_state_players(twa_graph_ptr arena, region_t* owners)
  {
    if (owners->size() != arena->num_states())
      throw std::runtime_error
        ("set_state_players(): There must be as many owners as states");

    arena->set_named_prop<region_t>("state-player", owners);
  }

  void set_state_player(twa_graph_ptr arena, unsigned state,
                        region_t::value_type owner)
  {
    if (state >= arena->num_states())
      throw std::runtime_error("set_state_player(): invalid state number");

    std::vector<bool> *owners = arena->get_named_prop<region_t>
      ("state-player");
    if (!owners)
      {
        owners = new region_t(arena->num_states(), p0_val());
        arena->set_named_prop<region_t>("state-player", owners);
      }

    (*owners)[state] = owner;
  }

  const std::vector<bool>& get_state_players(const_twa_graph_ptr arena)
  {
    std::vector<bool> *owners = arena->get_named_prop<std::vector<bool>>
      ("state-player");
    if (!owners)
      throw std::runtime_error
        ("get_state_players(): state-player property not defined, not a game");

    return *owners;
  }

  region_t::value_type
  get_state_player(const_twa_graph_ptr arena, unsigned state)
  {
    if (state >= arena->num_states())
      throw std::runtime_error("get_state_player(): invalid state number");

    std::vector<bool>* owners = arena->get_named_prop<std::vector<bool>>
      ("state-player");
    if (!owners)
      throw std::runtime_error
        ("get_state_player(): state-player property not defined, not a game");

    return (*owners)[state];
  }

  const strategy_t& get_strategy(const_twa_graph_ptr arena)
  {
    auto* strat = arena->get_named_prop<strategy_t>("strategy");
    if (not strat)
      throw std::runtime_error
          ("get_strategy(): strategy property not defined, not solved?");

    return *strat;
  }

  auto get_strategy_of(const_twa_graph_ptr arena,
                       unsigned state) -> strategy_t::value_type
  {
    if (state >= arena->num_states())
      throw std::runtime_error("get_strategy_of(): invalid state number");
    return get_strategy(arena)[state];
  }

  const attr_strategy_t& get_attractor_strategy(const_twa_graph_ptr arena)
  {
    auto* astrat = arena->get_named_prop<attr_strategy_t>("attr-strategy");
    if (not astrat)
      throw std::runtime_error
          ("get_attractor_strategy(): "
           "strategy property not defined, not solved?");

    return *astrat;
  }

  attr_strategy_t::value_type
  get_attractor_strategy_of(const_twa_graph_ptr arena, unsigned state)
  {
    if (state >= arena->num_states())
      throw std::runtime_error("get_attractor_strategy_of(): "
                               "invalid state number");
    return get_attractor_strategy(arena)[state];
  }

  const region_t& get_state_winner(const const_twa_graph_ptr& arena)
  {
    if (const region_t* reg =
        arena->get_named_prop<region_t>("state-winner"))
      return *reg;
    else
      throw std::runtime_error("get_state_winner: state-winner"
                               " property not defined! Game not solved?");
  }

  region_t::value_type
  get_state_winner_of(const const_twa_graph_ptr& arena, unsigned state)
  {
    return get_state_winner(arena).at(state);
  }

  bool solve_safety_game(twa_graph_ptr game)
  {
    if (!game->acc().is_t())
      throw std::runtime_error
        ("solve_safety_game(): arena should have true acceptance");

    auto owners = get_state_players(game);

    unsigned ns = game->num_states();
    auto winners = new region_t(ns, true);
    game->set_named_prop("state-winner", winners);
    auto strategy = new strategy_t(ns, 0);
    game->set_named_prop("strategy", strategy);

    // transposed is a reversed copy of game to compute predecessors
    // more easily.  It also keep track of the original edge iindex.
    struct edge_data {
      unsigned edgeidx;
    };
    digraph<void, edge_data> transposed;
    // Reverse the automaton, compute the out degree of
    // each state, and save dead-states in queue.
    transposed.new_states(ns);
    std::vector<unsigned> out_degree;
    out_degree.reserve(ns);
    std::vector<unsigned> queue;
    for (unsigned s = 0; s < ns; ++s)
      {
        unsigned deg = 0;
        for (auto& e: game->out(s))
          {
            transposed.new_edge(e.dst, e.src, game->edge_number(e));
            ++deg;
          }
        out_degree.push_back(deg);
        if (deg == 0)
          {
            (*winners)[s] = false;
            queue.push_back(s);
          }
      }
    // queue is initially filled with dead-states, which are winning
    // for player 0.  Any predecessor owned by player 0 is therefore
    // winning as well (check 1), and any predecessor owned by player
    // 1 that has all its successors winning for player 0 (check 2) is
    // also winning.  Use queue to propagate everything.
    // For the second check, we decrease out_degree by each edge leading
    // to a state winning for player 0, so if out_degree reaches 0,
    // we have ensured that all outgoing transitions are winning for 0.
    //
    // We use queue as a stack, to propagate bad states in DFS.
    // However it would be ok to replace the vector by a std::deque
    // to implement a BFS and build shorter strategies for player 0.
    // Right no we are assuming that strategies for player 0 have
    // limited uses, so we just avoid the overhead of std::deque in
    // favor of the simpler std::vector.
    while (!queue.empty())
      {
        unsigned s = queue.back();
        queue.pop_back();
        for (auto& e: transposed.out(s))
          {
            unsigned pred = e.dst;
            if (!(*winners)[pred])
              continue;
            // check 1 || check 2
            bool check1 = owners[pred] == false;
            if (check1 || --out_degree[pred] == 0)
              {
                (*winners)[pred] = false;
                queue.push_back(pred);
                if (check1)
                  (*strategy)[pred] = e.edgeidx;
              }
          }
      }
    // Let's fill in the strategy for Player 1.
    for (unsigned s = 0; s < ns; ++s)
      if (owners[s] && (*winners)[s])
        for (auto& e: game->out(s))
          if ((*winners)[e.dst])
            {
              (*strategy)[s] = game->edge_number(e);
              break;
            }

    return (*winners)[game->get_init_state_number()];
  }

  bool solve(const twa_graph_ptr& arena,
             bool use_buechi_as_reach)
  {
    // Check if transposed graph is given
    if (not arena->get_named_prop<transposed_graph_t>("transposed"))
        add_transposed_here(arena);
    assert((arena->num_edges()
               == arena->get_named_prop<transposed_graph_t>("transposed")
                   ->num_edges())
           && (arena->num_states()
                  == arena->get_named_prop<transposed_graph_t>("transposed")
                      ->num_states())
           && "Original and transposed graph are not consistent."
              "Called add_transpose_here()?");

    if (arena->acc().is_f())
      return solve_deadlock_game_detailed(arena);
    else if (arena->acc().is_t())
      return solve_liveliness_game_detailed(arena);
    else if (arena->acc().is_buchi())
      {
        if (use_buechi_as_reach)
          return solve_reach_detailed(arena);
        else
          return solve_buechi_detailed(arena);
      }
    else if (arena->acc().is_co_buchi())
      {
        if (use_buechi_as_reach)
          return solve_avoid_detailed(arena);
        else
          return solve_co_buechi_detailed(arena);
      }

    throw std::runtime_error("Not implemented!");
  }
}
