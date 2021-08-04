// -*- coding: utf-8 -*-
// Copyright (C) 2021 Laboratoire de Recherche et Développement
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

#include <spot/twa/acc.hh>
#include <spot/misc/trival.hh>

namespace spot
{
  class SPOT_API automaton_properties
  {
  public:
    automaton_properties(const acc_cond& acc)
      : acc_(acc)
      , props(0U)
    {}

    /// \brief Whether the automaton uses state-based acceptance.
    ///
    /// From the point of view of Spot, this means that all
    /// transitions leaving a state belong to the same acceptance
    /// sets.  Then it is equivalent to pretend that the state is in
    /// the acceptance set.
    trival prop_state_acc() const
    {
      if (acc_.num_sets() == 0)
        return trival(true);
      return trival::from_repr_t(is.state_based_acc);
    }

    /// \brief Set the state-based-acceptance property.
    ///
    /// If this property is set to true, then all transitions leaving
    /// a state must belong to the same acceptance sets.
    void prop_state_acc(trival val)
    {
      is.state_based_acc = val.val();
    }

    /// \brief Whether this is a state-based Büchi automaton.
    ///
    /// An SBA has a Büchi acceptance, and should have its
    /// state-based acceptance property set.
    trival is_sba() const
    {
      return prop_state_acc() && acc_.is_buchi();
    }

    /// \brief Whether the automaton is inherently weak.
    ///
    /// An automaton is inherently weak if accepting cycles and
    /// rejecting cycles are never mixed in the same strongly
    /// connected component.
    ///
    /// \see prop_weak()
    /// \see prop_terminal()
    trival prop_inherently_weak() const
    {
      return trival::from_repr_t(is.inherently_weak);
    }

    /// \brief Set the "inherently weak" property.
    ///
    /// Setting "inherently weak" to false automatically
    /// disables "terminal", "very weak", and "weak".
    ///
    /// \see prop_weak()
    /// \see prop_terminal()
    void prop_inherently_weak(trival val)
    {
      is.inherently_weak = val.val();
      if (!val)
        is.very_weak = is.terminal = is.weak = val.val();
    }

    /// \brief Whether the automaton is terminal.
    ///
    /// An automaton is terminal if it is weak, its accepting strongly
    /// connected components are complete, and no accepting edge leads
    /// to a non-accepting SCC.
    ///
    /// This property ensures that a word can be accepted as soon as
    /// one of its prefixes moves through an accepting edge.
    ///
    /// \see prop_weak()
    /// \see prop_inherently_weak()
    trival prop_terminal() const
    {
      return trival::from_repr_t(is.terminal);
    }

    /// \brief Set the terminal property.
    ///
    /// Marking an automaton as "terminal" automatically marks it as
    /// "weak" and "inherently weak".
    ///
    /// \see prop_weak()
    /// \see prop_inherently_weak()
    void prop_terminal(trival val)
    {
      is.terminal = val.val();
      if (val)
        is.inherently_weak = is.weak = val.val();
    }

    /// \brief Whether the automaton is weak.
    ///
    /// An automaton is weak if inside each strongly connected
    /// component, all transitions belong to the same acceptance sets.
    ///
    /// \see prop_terminal()
    /// \see prop_inherently_weak()
    trival prop_weak() const
    {
      return trival::from_repr_t(is.weak);
    }

    /// \brief Set the weak property.
    ///
    /// Marking an automaton as "weak" automatically marks it as
    /// "inherently weak".  Marking an automaton as "not weak"
    /// automatically marks it as "not terminal".
    ///
    /// \see prop_terminal()
    /// \see prop_inherently_weak()
    void prop_weak(trival val)
    {
      is.weak = val.val();
      if (val)
        is.inherently_weak = val.val();
      if (!val)
        is.very_weak = is.terminal = val.val();
    }

    /// \brief Whether the automaton is very-weak.
    ///
    /// An automaton is very-weak if it is weak (inside each strongly connected
    /// component, all transitions belong to the same acceptance sets)
    /// and each SCC contains only one state.
    ///
    /// \see prop_terminal()
    /// \see prop_weak()
    trival prop_very_weak() const
    {
      return trival::from_repr_t(is.very_weak);
    }

    /// \brief Set the very-weak property.
    ///
    /// Marking an automaton as "very-weak" automatically marks it as
    /// "weak" and "inherently weak".
    ///
    /// \see prop_terminal()
    /// \see prop_weak()
    void prop_very_weak(trival val)
    {
      is.very_weak = val.val();
      if (val)
        is.weak = is.inherently_weak = val.val();
    }


    /// \brief Whether the automaton is complete.
    ///
    /// An automaton is complete if for each state the union of the
    /// labels of its outgoing transitions is always true.
    ///
    /// Note that this method may return trival::maybe() when it is
    /// unknown whether the automaton is complete or not.  If you
    /// need a true/false answer, prefer the is_complete() function.
    ///
    /// \see prop_complete()
    /// \see is_complete()
    trival prop_complete() const
    {
      return trival::from_repr_t(is.complete);
    }

    /// \brief Set the complete property.
    ///
    /// \see is_complete()
    void prop_complete(trival val)
    {
      is.complete = val.val();
    }

    /// \brief Whether the automaton is universal.
    ///
    /// An automaton is universal if the conjunction between the
    /// labels of two transitions leaving a state is always false.
    ///
    /// Note that this method may return trival::maybe() when it is
    /// unknown whether the automaton is universal or not.  If you
    /// need a true/false answer, prefer the is_universal() function.
    ///
    /// \see prop_unambiguous()
    /// \see is_universal()
    trival prop_universal() const
    {
      return trival::from_repr_t(is.universal);
    }

    /// \brief Set the universal property.
    ///
    /// Setting the "universal" property automatically sets the
    /// "unambiguous" and "semi-deterministic" properties.
    ///
    /// \see prop_unambiguous()
    /// \see prop_semi_deterministic()
    void prop_universal(trival val)
    {
      is.universal = val.val();
      if (val)
        // universal implies unambiguous and semi-deterministic
        is.unambiguous = is.semi_deterministic = val.val();
    }

    // Starting with Spot 2.4, an automaton is deterministic if it is
    // both universal and existential, but as we already have
    // twa::is_existential(), we only need to additionally record the
    // universal property.  Before that, the deterministic property
    // was just a synonym for universal, hence we keep the deprecated
    // function prop_deterministic() with this meaning.
    SPOT_DEPRECATED("use prop_universal() instead")
    void prop_deterministic(trival val)
    {
      prop_universal(val);
    }

    SPOT_DEPRECATED("use prop_universal() instead")
    trival prop_deterministic() const
    {
      return prop_universal();
    }

    /// \brief Whether the automaton is unambiguous
    ///
    /// An automaton is unambiguous if any accepted word is recognized
    /// by exactly one accepting path in the automaton.  Any word
    /// (accepted or not) may be recognized by several rejecting paths
    /// in the automaton.
    ///
    /// Note that this method may return trival::maybe() when it is
    /// unknown whether the automaton is unambiguous or not.  If you
    /// need a true/false answer, prefer the is_unambiguous() function.
    ///
    /// \see prop_universal()
    /// \see is_unambiguous()
    trival prop_unambiguous() const
    {
      return trival::from_repr_t(is.unambiguous);
    }

    /// \brief Set the unambiguous property
    ///
    /// Marking an automaton as "non unambiguous" automatically
    /// marks it as "non universal".
    ///
    /// \see prop_deterministic()
    void prop_unambiguous(trival val)
    {
      is.unambiguous = val.val();
      if (!val)
        is.universal = val.val();
    }

    /// \brief Whether the automaton is semi-deterministic
    ///
    /// An automaton is semi-deterministic if the sub-automaton
    /// reachable from any accepting SCC is universal.
    ///
    /// Note that this method may return trival::maybe() when it is
    /// unknown whether the automaton is semi-deterministic or not.
    /// If you need a true/false answer, prefer the
    /// is_semi_deterministic() function.
    ///
    /// \see prop_universal()
    /// \see is_semi_deterministic()
    trival prop_semi_deterministic() const
    {
      return trival::from_repr_t(is.semi_deterministic);
    }

    /// \brief Set the semi-deterministic property
    ///
    /// Marking an automaton as "non semi-deterministic" automatically
    /// marks it as "non universal".
    ///
    /// \see prop_universal()
    void prop_semi_deterministic(trival val)
    {
      is.semi_deterministic = val.val();
      if (!val)
        is.universal = val.val();
    }

    /// \brief Whether the automaton is stutter-invariant.
    ///
    /// An automaton is stutter-invariant iff any accepted word
    /// remains accepted after removing a finite number of duplicate
    /// letters, or after duplicating a finite number of letters.
    ///
    /// Note that this method may return trival::maybe() when it is
    /// unknown whether the automaton is stutter-invariant or not.  If
    /// you need a true/false answer, prefer the
    /// is_stutter_invariant() function.
    ///
    /// \see is_stutter_invariant
    trival prop_stutter_invariant() const
    {
      return trival::from_repr_t(is.stutter_invariant);
    }

    /// \brief Set the stutter-invariant property
    void prop_stutter_invariant(trival val)
    {
      is.stutter_invariant = val.val();
    }

    /// \brief A structure for selecting a set of automaton properties
    /// to copy.
    ///
    /// When an algorithm copies an automaton before making some
    /// modification on that automaton, it should use a \c prop_set
    /// structure to indicate which properties should be copied from
    /// the original automaton.
    ///
    /// This structure does not list all supported properties, because
    /// properties are copied by groups of related properties.  For
    /// instance if an algorithm breaks the "inherent_weak"
    /// properties, it usually also breaks the "weak" and "terminal"
    /// properties.
    ///
    /// Set the flags to true to copy the value of the original
    /// property, and to false to ignore the original property
    /// (leaving the property of the new automaton to its default
    /// value, which is trival::maybe()).
    ///
    /// This can be used for instance as:
    /// \code
    ///    aut->prop_copy(other_aut, {true, false, false, false, false, true});
    /// \endcode
    /// This would copy the "state-based acceptance" and
    /// "stutter invariant" properties from \c other_aut to \c code.
    ///
    /// There are two flags for the determinism.  If \code
    /// deterministic is set, the universal, semi-deterministic,
    /// and unambiguous properties are copied as-is.  If deterministic
    /// is unset but improve_det is set, then those properties are
    /// only copied if they are positive.
    ///
    /// The reason there is no default value for these flags is that
    /// whenever we add a new property that does not fall into any of
    /// these groups, we will be forced to review all algorithms to
    /// decide if the property should be preserved or not.
    ///
    /// \see make_twa_graph_ptr
    /// \see prop_copy
    struct prop_set
    {
      bool state_based;     ///< preserve state-based acceptance
      bool inherently_weak; ///< preserve inherently weak, weak, & terminal
      bool deterministic;   ///< preserve deterministic, semi-det, unambiguous
      bool improve_det;     ///< improve deterministic, semi-det, unambiguous
      bool complete;        ///< preserve completeness
      bool stutter_inv;     ///< preserve stutter invariance

      prop_set()
      : state_based(false),
        inherently_weak(false),
        deterministic(false),
        improve_det(false),
        complete(false),
        stutter_inv(false)
      {
      }

      prop_set(bool state_based,
               bool inherently_weak,
               bool deterministic,
               bool improve_det,
               bool complete,
               bool stutter_inv)
      : state_based(state_based),
        inherently_weak(inherently_weak),
        deterministic(deterministic),
        improve_det(improve_det),
        complete(complete),
        stutter_inv(stutter_inv)
      {
      }

#ifndef SWIG
      // The "complete" argument was added in Spot 2.4
      SPOT_DEPRECATED("prop_set() now takes 6 arguments")
      prop_set(bool state_based,
               bool inherently_weak,
               bool deterministic,
               bool improve_det,
               bool stutter_inv)
      : state_based(state_based),
        inherently_weak(inherently_weak),
        deterministic(deterministic),
        improve_det(improve_det),
        complete(false),
        stutter_inv(stutter_inv)
      {
      }
#endif

      /// \brief An all-true \c prop_set
      ///
      /// Use that only in algorithms that copy an automaton without
      /// performing any modification.
      ///
      /// If an algorithm X does modifications, but preserves all the
      /// properties currently implemented, use an explicit
      ///
      /// \code
      ///    {true, true, true, true, true, true}
      /// \endcode
      ///
      /// instead of calling \c all().  This way, the day a new
      /// property is added, we will still be forced to review
      /// algorithm X, in case that new property is not preserved.
      static prop_set all()
      {
        return { true, true, true, true, true, true };
      }
    };

    /// \brief Copy the properties of another automaton.
    ///
    /// Copy the property specified with \a p from \a other to the
    /// current automaton.
    ///
    /// There is no default value for \a p on purpose.  This way any
    /// time we add a new property we have to update every call to
    /// prop_copy().
    ///
    /// \see prop_set
    template <typename OtherAutPtr>
    void prop_copy(const OtherAutPtr& other, prop_set p)
    {
      if (p.state_based)
        prop_state_acc(other->prop_state_acc());
      if (p.inherently_weak)
        {
          prop_terminal(other->prop_terminal());
          prop_weak(other->prop_weak());
          prop_very_weak(other->prop_very_weak());
          prop_inherently_weak(other->prop_inherently_weak());
        }
      if (p.deterministic)
        {
          prop_universal(other->prop_universal());
          prop_semi_deterministic(other->prop_semi_deterministic());
          prop_unambiguous(other->prop_unambiguous());
        }
      else if (p.improve_det)
        {
          if (other->prop_universal().is_true())
            {
              prop_universal(true);
            }
          else
            {
              if (other->prop_semi_deterministic().is_true())
                prop_semi_deterministic(true);
              if (other->prop_unambiguous().is_true())
                prop_unambiguous(true);
            }
        }
      if (p.complete)
        prop_complete(other->prop_complete());
      if (p.stutter_inv)
        prop_stutter_invariant(other->prop_stutter_invariant());
    }

    /// \brief Keep only a subset of properties of the current
    /// automaton.
    ///
    /// All properties part of a group set to \c false in \a p are reset
    /// to their default value of trival::maybe().
    void prop_keep(prop_set p)
    {
      if (!p.state_based)
        prop_state_acc(trival::maybe());
      if (!p.inherently_weak)
        {
          prop_terminal(trival::maybe());
          prop_weak(trival::maybe());
          prop_very_weak(trival::maybe());
          prop_inherently_weak(trival::maybe());
        }
      if (!p.deterministic)
        {
          if (!(p.improve_det && prop_universal().is_true()))
            prop_universal(trival::maybe());
          if (!(p.improve_det && prop_semi_deterministic().is_true()))
            prop_semi_deterministic(trival::maybe());
          if (!(p.improve_det && prop_unambiguous().is_true()))
            prop_unambiguous(trival::maybe());
        }
      if (!p.complete)
        prop_complete(trival::maybe());
      if (!p.stutter_inv)
        prop_stutter_invariant(trival::maybe());
    }

    void prop_reset()
    {
      prop_keep({});
    }

  private:
    const acc_cond& acc_;

    /// Helper structure used to store property flags.
    struct bprop
    {
      trival::repr_t state_based_acc:2;     // State-based acceptance.
      trival::repr_t inherently_weak:2;     // Inherently Weak automaton.
      trival::repr_t weak:2;                // Weak automaton.
      trival::repr_t terminal:2;            // Terminal automaton.
      trival::repr_t universal:2;           // Universal automaton.
      trival::repr_t unambiguous:2;         // Unambiguous automaton.
      trival::repr_t stutter_invariant:2;   // Stutter invariant language.
      trival::repr_t very_weak:2;           // very-weak, or 1-weak
      trival::repr_t semi_deterministic:2;  // semi-deterministic automaton.
      trival::repr_t complete:2;            // Complete automaton.
    };
    union
    {
      unsigned props;
      bprop is;
    };
  };
}
