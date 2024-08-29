#!/usr/bin/python3
# -*- mode: python; coding: utf-8 -*-
# Copyright (C) by the Spot authors, see the AUTHORS file for details.
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
from unittest import TestCase
tc = TestCase()

a = spot.automaton("""HOA: v1
States: 4
Start: 0
AP: 3 "a" "b" "c"
acc-name: all
Acceptance: 0 t
properties: trans-labels explicit-labels state-acc stutter-invariant
properties: very-weak
--BODY--
State: 0 "Ga | Gb | Gc"
[0] 1
[1] 2
[2] 3
State: 1 "Ga"
[0] 1
State: 2 "Gb"
[1] 2
State: 3 "Gc"
[2] 3
--END--""")

b = spot.automaton("""HOA: v1 States: 7 Start: 6 AP: 3 "a" "b" "c"
acc-name: all Acceptance: 0 t properties: trans-labels explicit-labels
state-acc deterministic properties: stutter-invariant very-weak
--BODY-- State: 0 [2] 0 State: 1 [!1&2] 0 [1&2] 1 [1&!2] 2 State: 2
[1] 2 State: 3 [0] 3 State: 4 [!0&2] 0 [0&!2] 3 [0&2] 4 State: 5
[!0&1] 2 [0&!1] 3 [0&1] 5 State: 6 [!0&!1&2] 0 [!0&1&2] 1 [!0&1&!2] 2
[0&!1&!2] 3 [0&!1&2] 4 [0&1&!2] 5 [0&1&2] 6 --END--""")

m1 = spot.match_states(a, b)
tc.assertEqual(m1, ((6,), (3, 4, 5, 6), (1, 2, 5, 6), (0, 1, 4, 6)))
m2 = spot.match_states(b, a)
tc.assertEqual(m2, ((3,), (2, 3), (2,), (1,), (1, 3), (1, 2), (0, 1, 2, 3)))

c = spot.translate('false')
m3 = spot.match_states(a, c)
tc.assertEqual(m3, ((), (), (), ()))
m4 = spot.match_states(c, a)
tc.assertEqual(m4, ((), ))

f = spot.formula("Ga | Gb | Gc")
m5 = spot.match_states(a, f)
tc.assertEqual(m5, (f, f, f, f))
m6 = spot.match_states(b, f)
tc.assertEqual(m6, (spot.formula("Gc"),
                    spot.formula("Gb | Gc"),
                    spot.formula("Gb"),
                    spot.formula("Ga"),
                    spot.formula("Ga | Gc"),
                    spot.formula("Ga | Gb"),
                    spot.formula("Ga | Gb | Gc")))

m7 = spot.match_states(c, f)  # Note that f is not the formula for c
tc.assertEqual(m7, (spot.formula("0"),))
