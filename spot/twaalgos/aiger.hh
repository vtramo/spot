// -*- coding: utf-8 -*-
// Copyright (C) 2020 Laboratoire de Recherche et Développement
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

#pragma once

#include <spot/misc/bddlt.hh>
#include <spot/misc/common.hh>
#include <stack>
#include <spot/twa/fwd.hh>
#include <unordered_map>
#include <vector>
#include <set>
#include <memory>
#include <sstream>

#include <spot/twa/bdddict.hh>
#include <spot/tl/formula.hh>

namespace spot
{
  namespace
  {
    static std::set<std::string>
    name_vector(unsigned n, const std::string &prefix)
    {
      std::set<std::string> res;
      for (unsigned i = 0; i != n; ++i)
        res.emplace(prefix + std::to_string(i));
      return res;
    }
  }

  class aig;

  using aig_ptr = std::shared_ptr<aig>;
  using const_aig_ptr = std::shared_ptr<const aig>;


  // A class to represent an AIGER circuit
  class SPOT_API aig
  {
  protected:
    const unsigned num_inputs_;
    const unsigned num_outputs_;
    const unsigned num_latches_;
    const std::set<std::string> input_names_;
    const std::set<std::string> output_names_;
    unsigned max_var_;

    std::vector<unsigned> next_latches_;
    std::vector<unsigned> outputs_;
    std::vector<std::pair<unsigned, unsigned>> and_gates_;
    // Cache the function computed by each variable as a bdd.
    bdd_dict_ptr dict_;
    std::unordered_map<unsigned, bdd> var2bdd_;
    std::unordered_map<bdd, unsigned, bdd_hash> bdd2var_;
    int l0_;

    bdd all_ins_;
    bdd all_latches_;

    bool split_off_ = true;

  public:

    using safe_point = std::pair<unsigned, unsigned>;
    using safe_stash =
            std::pair<std::vector<std::pair<unsigned, unsigned>>,
                      std::vector<std::pair<unsigned, bdd>>>;


//    const bool use_and_split_ = true;
//    std::map<unsigned, std::set<unsigned>> left_gate_map_;

    aig(const std::set<std::string>& inputs,
        const std::set<std::string>& outputs,
        unsigned num_latches,
        bdd_dict_ptr dict = make_bdd_dict())
        : num_inputs_(inputs.size()),
          num_outputs_(outputs.size()),
          num_latches_(num_latches),
          input_names_(inputs),
          output_names_(outputs),
          max_var_((inputs.size() + num_latches) * 2),
          next_latches_(num_latches),
          outputs_(outputs.size()),
          dict_{dict}
    {
      bdd2var_[bddtrue] = aig_true();
      var2bdd_[aig_true()] = bddtrue;
      bdd2var_[bddfalse] = aig_false();
      var2bdd_[aig_false()] = bddfalse;

      all_ins_ = bddtrue;
      all_latches_ = bddtrue;

      l0_ = dict_->register_anonymous_variables(num_latches_, this);
      for (size_t i = 0; i < num_latches_; ++i)
        {
          bdd b = bdd_ithvar(l0_+i);
          register_latch_(i, b);
          all_latches_ &= b;
        }

      size_t i = 0;
      for (auto&& in : input_names_)
      {
        bdd b = bdd_ithvar(dict_->register_proposition(formula::ap(in), this));
        register_input_(i, b);
        all_ins_ &= b;
        ++i;
      }
      for (auto&& out : output_names_)
        dict_->register_proposition(formula::ap(out), this);

      bdd2var_.reserve(4 * (num_inputs_ + num_outputs_ + num_latches_));
      var2bdd_.reserve(4 * (num_inputs_ + num_outputs_ + num_latches_));
    }

    aig(unsigned num_inputs, unsigned num_outputs,
        unsigned num_latches, bdd_dict_ptr dict = make_bdd_dict())
        : aig(name_vector(num_inputs, "in"),
          name_vector(num_outputs, "out"), num_latches, dict)
    {
    }


    ~aig()
    {
      dict_->unregister_all_my_variables(this);
    }

    // register the bdd corresponding the an
    // aig literal
  protected:
    void register_new_lit_(unsigned v, const bdd &b);
    void register_latch_(unsigned i, const bdd& b);
    void register_input_(unsigned i, const bdd& b);
    void unregister_lit_(unsigned v);

    bdd accum_commun_(const bdd& b) const;

    unsigned bdd2partitionedDNFvar_(bdd b);
    unsigned bdd2partitionedDNFvar_impl_(const bdd& b);
    unsigned prod2partitionedDNFvar_impl_(const bdd& prod);

    unsigned bdd2INFvar_impl_1_(const bdd& b);
    unsigned bdd2INFvar_impl_(const bdd& b, bool do_min);

  public:

    safe_point get_safe_point_() const;
    safe_stash roll_back_(safe_point sp,
                          bool do_stash = false);
    void reapply_(safe_point sp, const safe_stash& ss);

    void use_split_off(bool nv)
    {
      split_off_ = nv;
    }

    unsigned num_outputs() const
    {
      return num_outputs_;
    }
    const std::vector<unsigned>& outputs() const
    {
      return outputs_;
    }
    const std::set<std::string>& output_names() const
    {
      return output_names_;
    }

    unsigned num_inputs() const
    {
      return num_inputs_;
    }
    const std::set<std::string>& input_names() const
    {
      return input_names_;
    }

    unsigned num_latches() const
    {
      return num_latches_;
    }
    const std::vector<unsigned>& next_latches() const
    {
      return next_latches_;
    };

    unsigned num_gates() const
    {
      return and_gates_.size();
    };
    const std::vector<std::pair<unsigned, unsigned>>& gates() const
    {
      return and_gates_;
    };

    unsigned max_var() const
    {
      return max_var_;
    };

    unsigned input_var(unsigned i, bool neg = false) const
    {
      SPOT_ASSERT(i < num_inputs_);
      return (1 + i) * 2 + neg;
    }
    bdd input_bdd(unsigned i, bool neg = false) const
    {
      return aigvar2bdd(input_var(i, neg));
    }

    unsigned latch_var(unsigned i, bool neg = false) const
    {
      SPOT_ASSERT(i < num_latches_);
      return (1 + num_inputs_ + i) * 2 + neg;
    }
    bdd latch_bdd(unsigned i, bool neg = false) const
    {
      return aigvar2bdd(latch_var(i, neg));
    }

    unsigned gate_var(unsigned i, bool neg = false) const
    {
      SPOT_ASSERT(i < num_gates());
      return (1 + num_inputs_ + num_latches_ + i) * 2 + neg;
    }
    bdd gate_bdd(unsigned i, bool neg = false) const
    {
      return aigvar2bdd(gate_var(i, neg));
    }

    bdd aigvar2bdd(unsigned v, bool neg = false) const
    {
      return neg ? bdd_not(var2bdd_.at(v)) : var2bdd_.at(v);
    }

    unsigned bdd2aigvar(const bdd& b) const
    {
      return bdd2var_.at(b);
    }

    void set_output(unsigned i, unsigned v);

    void set_next_latch(unsigned i, unsigned v);

    static constexpr unsigned aig_true() noexcept
    {
      return 1;
    };

    static constexpr unsigned aig_false() noexcept
    {
      return 0;
    };

    unsigned aig_not(unsigned v);

    unsigned aig_and(unsigned v1, unsigned v2);

    unsigned aig_and(std::vector<unsigned> vs);

    unsigned aig_or(unsigned v1, unsigned v2);

    unsigned aig_or(std::vector<unsigned> vs);

    unsigned aig_pos(unsigned v);

    void remove_unused();

    // Takes a bdd, computes the corresponding literal
    // using its DNF
    unsigned bdd2DNFvar(bdd b);

    // Takes a bdd and computes the corresponding literal
    // using partitioned DNF
    // that means that input and latch conditions
    // are computed separately as a balanced tree
    unsigned bdd2partitionedDNFvar(bdd b);

    // Takes a bdd, computes the corresponding literal
    // using its INF
    unsigned bdd2INFvar(bdd b, bool do_min);

    // Tries to construct an optimal controller
    // by taking into account all conditions needed
    void build_all_bdds(const std::vector<bdd>& all_bdd);


  // Parser an aiger from an aig file.
    // However the syntax is restricted
    static aig_ptr parse_aag(const std::string& aig_txt,
                             bdd_dict_ptr dict = make_bdd_dict());

    // Transform an Aiger into an equivalent monitor/strategy
    twa_graph_ptr aig2aut(bool keepsplit = false) const;

  };

  /// \ingroup twa_io
  /// \brief Print an AIGER circuit.
  ///
  /// \param os           The output stream to print on.
  /// \param circuit      The circuit to output.
  SPOT_API std::ostream &
  print_aiger(std::ostream &os, const_aig_ptr circuit);

  SPOT_API aig_ptr
  strategy_to_aig(const const_twa_graph_ptr &aut, const char *mode);

  SPOT_API aig_ptr
  strategies_to_aig(const std::vector<const_twa_graph_ptr>& strat_vec,
                    const char *mode);

  SPOT_API aig_ptr
  strategy_to_aig(const twa_graph_ptr& aut, const char *mode,
                  const std::set<std::string>& ins,
                  const std::set<std::string>& outs);

  SPOT_API aig_ptr
  strategies_to_aig(const std::vector<twa_graph_ptr>& strat_vec,
                    const char *mode,
                    const std::set<std::string>& ins,
                    const std::vector<std::set<std::string>>& outs);

}
