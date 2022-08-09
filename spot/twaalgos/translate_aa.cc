// -*- coding: utf-8 -*-
// Copyright (C) 2013-2018, 2020-2021 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
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
#include <spot/twaalgos/alternation.hh>
#include <spot/twaalgos/translate_aa.hh>
#include <spot/tl/derive.hh>
#include <spot/tl/nenoform.hh>

#include <iostream>

namespace spot
{
  namespace
  {
    struct ltl_to_aa_builder
    {
      ltl_to_aa_builder(twa_graph_ptr aut, unsigned accepting_sink)
        : aut_(aut)
        , accepting_sink_(accepting_sink)
        , uniq_(aut_->get_graph(), accepting_sink)
        , oe_(aut_, accepting_sink)
      {
      }

      twa_graph_ptr aut_;
      unsigned accepting_sink_;
      internal::univ_dest_mapper<twa_graph::graph_t> uniq_;
      outedge_combiner oe_;

      void add_self_loop(twa_graph::edge_storage_t const& e,
                         unsigned init_state,
                         acc_cond::mark_t acc)
      {
        if (e.dst == accepting_sink_)
          {
            // avoid creating a univ_dests vector if the only dest is an
            // accepting sink, which can be simplified, only keeping the self
            // loop
            aut_->new_edge(init_state, init_state, e.cond, acc);
            return;
          }

        auto dests = aut_->univ_dests(e);
        std::vector<unsigned> new_dests(dests.begin(), dests.end());
        new_dests.push_back(init_state);

        unsigned dst = uniq_.new_univ_dests(new_dests.begin(),
                                            new_dests.end());
        aut_->new_edge(init_state, dst, e.cond, acc);
      }


      unsigned recurse(formula f)
      {
        switch (f.kind())
        {
          case op::ff:
            return aut_->new_state();

          case op::tt:
          {
            unsigned init_state = aut_->new_state();
            aut_->new_edge(init_state, accepting_sink_, bddtrue, {});
            return init_state;
          }

          case op::ap:
          case op::Not:
          {
            unsigned init_state = aut_->new_state();

            bdd ap;
            if (f.kind() == op::ap)
              ap = bdd_ithvar(aut_->register_ap(f.ap_name()));
            else
              ap = bdd_nithvar(aut_->register_ap(f[0].ap_name()));

            aut_->new_edge(init_state, accepting_sink_, ap, {});
            return init_state;
          }

          // FIXME: is this right for LTLf?
          case op::strong_X:
          case op::X:
          {
            unsigned sub_init_state = recurse(f[0]);
            unsigned new_init_state = aut_->new_state();
            aut_->new_edge(new_init_state, sub_init_state, bddtrue, {});
            return new_init_state;
          }

          case op::Or:
          {
            unsigned init_state = aut_->new_state();

            for (const auto& sub_formula : f)
              {
                unsigned sub_init = recurse(sub_formula);
                for (auto& e : aut_->out(sub_init))
                  {
                    unsigned dst = e.dst;
                    if (aut_->is_univ_dest(e.dst))
                      {
                        auto dests = aut_->univ_dests(e);
                        dst = uniq_.new_univ_dests(dests.begin(), dests.end());
                      }
                    aut_->new_edge(init_state, dst, e.cond, {});
                  }
              }

            return init_state;
          }

          case op::And:
          {
            unsigned init_state = aut_->new_state();

            outedge_combiner oe(aut_, accepting_sink_);
            bdd comb = bddtrue;
            for (const auto& sub_formula : f)
              {
                unsigned sub_init = recurse(sub_formula);
                comb &= oe_(sub_init);
              }
            oe_.new_dests(init_state, comb);

            return init_state;
          }

          case op::U:
          case op::W:
          {
            auto acc = f.kind() == op::U
              ? acc_cond::mark_t{0}
              : acc_cond::mark_t{};

            unsigned init_state = aut_->new_state();

            unsigned lhs_init = recurse(f[0]);
            unsigned rhs_init = recurse(f[1]);

            std::vector<unsigned> new_dests;
            for (auto& e : aut_->out(lhs_init))
              add_self_loop(e, init_state, acc);

            for (auto& e : aut_->out(rhs_init))
              {
                unsigned dst = e.dst;
                if (aut_->is_univ_dest(e.dst))
                  {
                    auto dests = aut_->univ_dests(e);
                    dst = uniq_.new_univ_dests(dests.begin(), dests.end());
                  }
                aut_->new_edge(init_state, dst, e.cond, {});
              }

            return init_state;
          }

          case op::R:
          case op::M:
          {
            auto acc = f.kind() == op::M
              ? acc_cond::mark_t{0}
              : acc_cond::mark_t{};

            unsigned init_state = aut_->new_state();

            unsigned lhs_init = recurse(f[0]);
            unsigned rhs_init = recurse(f[1]);

            for (auto& e : aut_->out(rhs_init))
              add_self_loop(e, init_state, acc);

            bdd comb = oe_(lhs_init);
            comb &= oe_(rhs_init);
            oe_.new_dests(init_state, comb);

            return init_state;
          }

          // F(phi) = tt U phi
          case op::F:
          {
            auto acc = acc_cond::mark_t{0};

            // if phi is boolean then we can reuse its initial state (otherwise
            // we can't because of potential self loops)
            if (f[0].is_boolean())
              {
                unsigned init_state = recurse(f[0]);
                aut_->new_edge(init_state, init_state, bddtrue, acc);
                return init_state;
              }

            unsigned init_state = aut_->new_state();
            unsigned sub_init = recurse(f[0]);

            aut_->new_edge(init_state, init_state, bddtrue, acc);

            for (auto& e : aut_->out(sub_init))
              aut_->new_edge(init_state, e.dst, e.cond, {});

            return init_state;
          }

          // G phi = ff R phi
          case op::G:
          {
            unsigned init_state = aut_->new_state();

            unsigned sub_init = recurse(f[0]);

            // translate like R, but only the self loop part; `ff` cancels out
            // the product of edges
            std::vector<unsigned> new_dests;
            for (auto& e : aut_->out(sub_init))
              add_self_loop(e, init_state, {});

            return init_state;
          }

          case op::UConcat:
          {
            // FIXME: combine out edges with rhs !
            //unsigned rhs_init = recurse(f[1]);
            twa_graph_ptr sere_aut = derive_finite_automaton_with_first(f[0]);

            const auto& dict = sere_aut->get_dict();

            std::map<unsigned, unsigned> old_to_new;
            std::map<unsigned, int> state_to_var;
            std::map<int, unsigned> var_to_state;
            bdd vars = bddtrue;
            bdd aps = sere_aut->ap_vars();
            std::vector<unsigned> univ_dest;

            // registers a state in various maps and returns the index of the
            // anonymous bdd var representing that state
            auto register_state = [&](unsigned st) -> int {
              auto p = state_to_var.emplace(st, 0);
              if (p.second)
              {
                int v = dict->register_anonymous_variables(1, this);
                p.first->second = v;
                var_to_state.emplace(v, st);

                unsigned new_st = aut_->new_state();
                old_to_new.emplace(st, new_st);

                vars &= bdd_ithvar(v);
              }

              return p.first->second;
            };

            unsigned ns = sere_aut->num_states();
            for (unsigned st = 0; st < ns; ++st)
              {
                register_state(st);

                bdd sig = bddfalse;
                for (const auto& e : sere_aut->out(st))
                  {
                    int st_bddi = register_state(e.dst);
                    sig |= e.cond & bdd_ithvar(st_bddi);
                  }

                for (bdd cond : minterms_of(bddtrue, aps))
                  {
                    bdd dest = bdd_appex(sig, cond, bddop_and, aps);
                    while (dest != bddtrue)
                      {
                        assert(bdd_low(dest) == bddfalse);
                        auto it = var_to_state.find(bdd_var(dest));
                        assert(it != var_to_state.end());
                        auto it2 = old_to_new.find(it->second);
                        assert(it2 != old_to_new.end());
                        univ_dest.push_back(it2->second);
                        dest = bdd_high(dest);
                      }

                    auto it = old_to_new.find(st);
                    assert(it != old_to_new.end());
                    unsigned src = it->second;
                    unsigned dst = uniq_.new_univ_dests(univ_dest.begin(),
                                                        univ_dest.end());
                    aut_->new_edge(src, dst, cond, {});
                  }
              }

            auto it = old_to_new.find(sere_aut->get_init_state_number());
            assert(it != old_to_new.end());

            return it->second;
          }

          case op::eword:
          case op::Xor:
          case op::Implies:
          case op::Equiv:
          case op::Closure:
          case op::NegClosure:
          case op::NegClosureMarked:
          case op::EConcat:
          case op::EConcatMarked:
          case op::OrRat:
          case op::AndRat:
          case op::AndNLM:
          case op::Concat:
          case op::Fusion:
          case op::Star:
          case op::FStar:
          case op::first_match:
            SPOT_UNREACHABLE();
            return -1;
        }

        SPOT_UNREACHABLE();
      }
    };
  }

  twa_graph_ptr
  ltl_to_aa(formula f, bdd_dict_ptr& dict, bool purge_dead_states)
  {
    f = negative_normal_form(f);

    auto aut = make_twa_graph(dict);
    aut->set_co_buchi();

    unsigned accepting_sink = aut->new_state();
    aut->new_edge(accepting_sink, accepting_sink, bddtrue, {});
    auto builder = ltl_to_aa_builder(aut, accepting_sink);

    unsigned init_state = builder.recurse(f);
    aut->set_init_state(init_state);

    if (purge_dead_states)
      aut->purge_dead_states();

    return aut;
  }
}
