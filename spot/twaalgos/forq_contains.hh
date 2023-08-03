// -*- coding: utf-8 -*-
// Copyright (C) 2023 Laboratoire de Recherche et Développement
// de l'Epita. IMDEA Software Institute.
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
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/word.hh>

namespace spot
{
  /// \brief Returns a word accepted by \a left that is rejected by \a right,
  /// or nullptr.
  ///
  /// This implements the language containment algorithm from
  /// \cite{doveriFORQBasedLanguageInclusion2022}
  /// to check whether L(left)⊆L(right), in which case, it returns nullptr.
  /// Otherwise, it returns a counterexample, i.e., a word that is accepted
  /// by $L(left)\setminus L(right)$, hence the name of the function.
  ///
  /// \pre Automata \a left and \a right should be
  /// non-alternating state-based Büchi-automata.
  SPOT_API twa_word_ptr difference_word_forq(
    const_twa_graph_ptr left, spot::const_twa_graph_ptr right);

  /// \brief Returns a boolean value indicating
  /// whether \a left is included in the language of \a right.
  ///
  /// This implements the language containment algorithm from
  /// \cite{doveriFORQBasedLanguageInclusion2022}
  /// to check whether L(left)⊆L(right).
  ///
  /// \pre Automata \a left and \a right should be
  /// non-alternating state-based Büchi-automata.
  SPOT_API bool contains_forq(
    const_twa_graph_ptr left, const_twa_graph_ptr right);
}
