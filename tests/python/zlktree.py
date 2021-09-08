# -*- mode: python; coding: utf-8 -*-
# Copyright (C) 2021 Laboratoire de Recherche et Développement de l'Epita
# (LRDE).
#
# This file is part of Spot, a model checking library.
#
# Spot is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
#
# Spot is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
# License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

import spot

a = spot.automaton("""HOA: v1 States: 5 Start: 0 AP: 2 "p0" "p1"
Acceptance: 4 Inf(3) | Fin(3) properties: trans-labels explicit-labels
trans-acc --BODY-- State: 0 [!0&!1] 3 [!0&!1] 4 State: 1 [!0&!1] 4 {3}
[0&!1] 0 {2} [!0&1] 1 {2} State: 2 [!0&1] 0 {0 2} [!0&!1] 1 State: 3
[!0&1] 2 State: 4 [0&!1] 3 --END--""")
b = spot.zielonka_tree_transform(a)
assert spot.are_equivalent(a, b)
assert b.acc().is_buchi()
