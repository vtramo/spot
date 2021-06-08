// -*- coding: utf-8 -*-
// Copyright (C) 2020-21 Laboratoire de Recherche et Développement
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

#include <iosfwd>
#include <spot/misc/common.hh>
#include <spot/misc/bddlt.hh>
#include <spot/twa/fwd.hh>
#include <spot/twa/bdddict.hh>
#include <spot/tl/formula.hh>

#include <unordered_map>
#include <vector>
#include <set>
#include <memory>
#include <sstream>



namespace spot
{
  namespace
  {
    static std::set<std::string>
    name_vector(unsigned n, const std::string& prefix)
    {
      std::set<std::string> res;
      for (unsigned i = 0; i != n; ++i)
        res.emplace_hint(res.end(), prefix + std::to_string(i));
      return res;
    }
  }

  class aig;

  using aig_ptr = std::shared_ptr<aig>;
  using const_aig_ptr = std::shared_ptr<const aig>;

  /// \brief A class representing AIG circuits
  ///
  /// AIG circuits consist of (named) inputs, (named) outputs, latches which
  /// serve as memory, and gates and negations connecting them.
  /// AIG circuits can be used to represent controllers, which is currently
  /// their sole purpose within spot.
  /// AIGs produce a output sequence based on the following rules:
  /// 1) All latches are initialised to 0
  /// 2) The next input is read.
  /// 3) The output and the state of the latches for the next turn
  ///    are given by the gates as a function of the current latches and inputs
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
    bdd_dict_ptr dict_;
    // Cache the function computed by each variable as a bdd.
    // Bidirectional map
    std::unordered_map<unsigned, bdd> var2bdd_;
    std::unordered_map<bdd, unsigned, bdd_hash> bdd2var_;
    // First anonymous var marking the beginning of variables used
    // as latches
    int l0_;

    bdd all_ins_;
    bdd all_latches_;
    // Try to decompose bdds into common sub-parts before
    // translating them to gates
    bool split_off_ = true;

    // For simulation
    std::vector<bool> state_;

  public:

    /// \brief Mark the beginning of a test tranlation
    ///
    /// Sometimes different encodings produces more or less gates.
    /// To improve performances, one can "safe" the current status
    //  and revert changes afterwards if needed
    using safe_point = std::pair<unsigned, unsigned>;
    using safe_stash =
            std::pair<std::vector<std::pair<unsigned, unsigned>>,
                      std::vector<std::pair<unsigned, bdd>>>;
    /// \brief Constructing an "empty" aig, knowing only about the
    ///        necessary inputs, outputs and latches. A bdd_dict can
    ///        be handed to the circuit in order to allow for verification
    ///        against other automata after construction
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
          next_latches_(num_latches, -1u),
          outputs_(outputs.size(), -1u),
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

    /// \brief Constructing the circuit with generic names.
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

  protected:
    /// \brief Register a new literal in both maps
    void register_new_lit_(unsigned v, const bdd &b);
    void register_latch_(unsigned i, const bdd& b);
    void register_input_(unsigned i, const bdd& b);
    /// \brief Remove a literal from both maps
    void unregister_lit_(unsigned v);

    /// \brief Split-off common sub-expressions
    bdd accum_commun_(const bdd& b) const;

    /// \brief Translate a bdd into gates using the sum-of-products
    ///        decomposition
    unsigned bdd2partitionedDNFvar_(bdd b);
    unsigned bdd2partitionedDNFvar_impl_(const bdd& b);
    unsigned prod2partitionedDNFvar_impl_(const bdd& prod);

    /// \brief Translate a bdd into gates using the
    /// if-then-else normalform
    unsigned bdd2INFvar_impl_1_(const bdd& b);
    unsigned bdd2INFvar_impl_(const bdd& b, bool do_min);

  public:

    /// \brief Safe the current state of the circuit
    /// \note This does not make a copy, so rolling back to
    ///       an older safe point invalidates all newer safepoints.
    ///       Also only concerns the gates, output and next_latch variables
    ///       will not change
    safe_point get_safe_point_() const;
    /// \brief roll_back to the saved point.
    ///
    /// \param sp : The safe_point to revert back to
    /// \param do_stash : Whether or not to save the changes to be possibly
    ///                   reapplied later on
    safe_stash roll_back_(safe_point sp,
                          bool do_stash = false);
    /// \brief Reapply to stored changes on top of a safe_point
    /// \note : ss has to be obtained from roll_back_(sp, true)
    void reapply_(safe_point sp, const safe_stash& ss);

    /// \brief Use heuristic to reduce circuit size by computing
    ///        common sub-expressions
    void use_split_off(bool nv)
    {
      split_off_ = nv;
    }

    /// \brief Get the number of outputs
    unsigned num_outputs() const
    {
      return num_outputs_;
    }
    /// \brief Get the variables associated to the ouputs
    /// \note Only available after call to aig::set_output
    const std::vector<unsigned>& outputs() const
    {
      SPOT_ASSERT(std::none_of(outputs_.begin(), outputs_.end(),
                               [](unsigned o){return o == -1u; }));
      return outputs_;
    }
    /// \brief Get the set of output names
    const std::set<std::string>& output_names() const
    {
      return output_names_;
    }

    /// \brief Get the number of inputs
    unsigned num_inputs() const
    {
      return num_inputs_;
    }
    /// \brief Get the set of input names
    const std::set<std::string>& input_names() const
    {
      return input_names_;
    }

    /// \brief Get the number of latches in the circuit
    unsigned num_latches() const
    {
      return num_latches_;
    }
    /// \brief Get the variables associated to the state of the latches
    ///        in the next iteration
    /// \note Only available after call to aig::set_next_latch
    const std::vector<unsigned>& next_latches() const
    {
      SPOT_ASSERT(std::none_of(next_latches_.begin(), next_latches_.end(),
                               [](unsigned o){return o == -1u; }));
      return next_latches_;
    };

    /// \brief Get the total number of and gates
    unsigned num_gates() const
    {
      return and_gates_.size();
    };
    /// \brief Access the underlying container
    const std::vector<std::pair<unsigned, unsigned>>& gates() const
    {
      return and_gates_;
    };

    /// \brief Maximal variable index currently appearing in the circuit
    unsigned max_var() const
    {
      return max_var_;
    };

    /// \brief Get the variable associated to the ith input
    unsigned input_var(unsigned i, bool neg = false) const
    {
      SPOT_ASSERT(i < num_inputs_);
      return (1 + i) * 2 + neg;
    }
    /// \brief Get the bdd associated to the ith input
    bdd input_bdd(unsigned i, bool neg = false) const
    {
      return aigvar2bdd(input_var(i, neg));
    }

    /// \brief Get the variable associated to the ith latch
    unsigned latch_var(unsigned i, bool neg = false) const
    {
      SPOT_ASSERT(i < num_latches_);
      return (1 + num_inputs_ + i) * 2 + neg;
    }
    /// \brief Get the bdd associated to the ith latch
    bdd latch_bdd(unsigned i, bool neg = false) const
    {
      return aigvar2bdd(latch_var(i, neg));
    }

    /// \brief Get the variable associated to the ith gate
    unsigned gate_var(unsigned i, bool neg = false) const
    {
      SPOT_ASSERT(i < num_gates());
      return (1 + num_inputs_ + num_latches_ + i) * 2 + neg;
    }
    /// \brief Get the bdd associated to the ith gate
    bdd gate_bdd(unsigned i, bool neg = false) const
    {
      return aigvar2bdd(gate_var(i, neg));
    }

    /// \brief Get the bdd associated to a variable
    /// \note Throws if non-existent
    bdd aigvar2bdd(unsigned v, bool neg = false) const
    {
      return neg ? bdd_not(var2bdd_.at(v)) : var2bdd_.at(v);
    }
    /// \brief Get the variable associated to a bdd
    /// \note Throws if non-existent
    unsigned bdd2aigvar(const bdd& b) const
    {
      return bdd2var_.at(b);
    }

    /// \brief Associate the ith output to the variable v
    void set_output(unsigned i, unsigned v);

    /// \brief Associate the ith latch state after update to the variable v
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

    /// \brief Computes the and of all vars
    /// \note This function modifies the given vector to only contain the
    ///       result after call
    unsigned aig_and(std::vector<unsigned>& vs);

    unsigned aig_or(unsigned v1, unsigned v2);

    /// \brief Computes the or of all vars
    /// \note This function modifies the given vector to only contain the
    ///       result after call
    unsigned aig_or(std::vector<unsigned>& vs);

    unsigned aig_pos(unsigned v);

    /// \brief Sweep throught the currently existing gates
    ///        and keep only those connected to an output or a next_latch input
    void remove_unused();

    /// \brief Compute the necessary gates to represent the given within the
    ///        circuit by decomposing it into a sum of products
    unsigned bdd2DNFvar(bdd b);
    /// \brief Given two bdds, compute their representation as circuit and
    ///        only keep the smaller one
    unsigned bdd2DNFvar(bdd b1, bdd b2);

    /// \brief Much like aig::bdd2DNFvar, but uses seperate products for
    ///        the inputs and latches, which sometimes results in higher
    ///        reuseability and therefore reduced circuit size
    unsigned bdd2partitionedDNFvar(bdd b);
    unsigned bdd2partitionedDNFvar(bdd b1, bdd b2);

    /// \brief Rerpresent a bdd within the circuit by using the
    ///        if-then-else normal form
    unsigned bdd2INFvar(bdd b, bool do_min);
    unsigned bdd2INFvar(bdd b1, bdd b2, bool do_min);

    /// \brief Instead of successively adding bdds to the circuit,
    ///        one can also pass a vector of all bdds needed to the circuit.
    ///        In this case additional optimization steps are taken to minimize
    ///        the size of the circuit
    /// \note This can be costly and did not bring about any advantages
    ///       in the SYNTCOMP cases
    void build_all_bdds(const std::vector<bdd>& all_bdd);

    /// \brief Create a circuit from an aag file with restricted syntax.
    static aig_ptr parse_aag(const std::string& aig_txt,
                             bdd_dict_ptr dict = make_bdd_dict());

    /// \brief Transform the circuit onto an equivalent monitor
    /// \note This can be slow for large input numbers
    twa_graph_ptr aig2aut(bool keepsplit = false) const;

    /// \brief Gives access to the current state of the simulation.
    ///
    ///        Corresponds to a vector of booleans holding the truth value
    ///        for each literal. Note that within the vector we have the truth
    ///        value of a literal and its negation, so sim_state()[2*i+1] is
    ///        always the negation of sim_state()[2*i].
    ///        The variable index can be obtained using
    ///        input_var, latch_var or outputs
    const std::vector<bool>& sim_state() const
    {
      SPOT_ASSERT(state_.size() == max_var_ + 2
                  && "State vector does not have the correct size.\n"
                     "Forgot to initialize?");
      return state_;
    }

    /// \brief Access to the state of a specific variable
    bool sim_state_of(unsigned var) const
    {
      SPOT_ASSERT(var <= max_var_ + 1
                  && "Variable out of range");
      return sim_state()[var];
    }

    /// \brief (Re)initialize the simulation.
    ///        This sets all latches to 0 and clears the output
    void sim_init();

    /// \brief Advances the simulation by one step based on inputs.
    ///
    ///        Updates the state of the aig such that sim_state holds the
    ///        values of output and latches AFTER reading the given input
    /// \param inputs : Vector of booleans with size num_inputs()
    void sim_step(const std::vector<bool>& inputs);

  };

  /// \brief Convert a strategy into an aig relying on the transformation
  ///        described by mode.
  SPOT_API aig_ptr
  strategy_to_aig(const const_twa_graph_ptr &aut, const char *mode);

  /// \brief Represent multiple strategies into an aig relying on
  ///        the transformation described by mode.
  /// \note The states of each strategy are represented by a block of latches
  ///       not affected by the others. For this to work in a general setting,
  ///       the output properties must be disjoint.
  SPOT_API aig_ptr
  strategies_to_aig(const std::vector<const_twa_graph_ptr>& strat_vec,
                    const char *mode);
  /// \brief Like above, but explicitly handing over which propositions
  ///        are input and outputs and does therefore not rely on the
  ///        named property "synthesis-outputs"
  SPOT_API aig_ptr
  strategy_to_aig(const twa_graph_ptr& aut, const char *mode,
                  const std::set<std::string>& ins,
                  const std::set<std::string>& outs);

  /// \brief Like above, but explicitly handing over the propositions
  SPOT_API aig_ptr
  strategies_to_aig(const std::vector<twa_graph_ptr>& strat_vec,
                    const char *mode,
                    const std::set<std::string>& ins,
                    const std::vector<std::set<std::string>>& outs);

  /// \brief Print the aig to stream in AIGER format
  SPOT_API std::ostream&
  print_aiger(std::ostream& os, const_aig_ptr circuit);

  /// \ingroup twa_io
  /// \brief Encode and print an automaton as an AIGER circuit.
  ///
  /// The circuit actually encodes the transition relation of the automaton, not
  /// its acceptance condition. Therefore, this function will reject automata
  /// whose acceptance condition is not trivial (i.e. true).
  /// States are encoded by latches (or registers) in the circuit. Atomic
  /// propositions are encoded as inputs and outputs of the circuit. To know
  /// which AP should be encoded as outputs, print_aiger() relies on the named
  /// property "synthesis-outputs", which is a bdd containing the conjunction of
  /// such output propositions. All other AP are encoded as inputs. If the named
  /// property is not set, all AP are encoded as inputs, and the circuit has no
  /// output.
  ///
  /// \pre  In order to ensure correctness, edge conditions have
  /// to have the form (input cond) & (output cond). The output cond
  /// does not need to be a minterm.
  /// Correct graphs are generated by spot::unsplit_2step
  ///
  ///
  /// \param os           The output stream to print on.
  /// \param aut          The automaton to output.
  /// \param mode         Determines how the automaton is encoded.
  ///                     "ISOP" Uses DNF.
  ///                     "ITE" Uses the "if-then-else" normal-form
  SPOT_API std::ostream&
  print_aiger(std::ostream& os, const const_twa_graph_ptr& aut,
              const char* mode);
}
