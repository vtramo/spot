// -*- coding: utf-8 -*-
// Copyright (C) by the Spot authors, see the AUTHORS file for details.
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

#include <spot/tl/formula.hh>
#include <spot/tl/simplify.hh>

namespace spot
{
  /// \ingroup tl_rewriting
  /// \brief Convert an LTL formula to Δ₂
  ///
  /// This implement LTL rewriting rules as given by
  /// \cite esparza.24.acm
  ///
  /// Only LTL operators are supported, PSL operators
  /// will be left untouched.
  ///
  /// If \a tls is given, it will be used to simplify formulas and
  /// puts formulas in negative normal form.  If \a tls is not
  /// given, a temporary simplifier will be created.
  ///
  /// No transformation is attempted if the input is already Δ₂.
  SPOT_API formula
  to_delta2(formula f, tl_simplifier* tls = nullptr);
}
