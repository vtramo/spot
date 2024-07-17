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

# Test that the spot.gen package works, in particular, we want
# to make sure that the objects created from spot.gen methods
# are usable with methods from the spot package.


import spot
from unittest import TestCase
tc = TestCase()

b = spot.translate('FGb')
a = spot.translate('GFa & GFc')
p = spot.product_susp(b, a)
q = spot.scc_filter(spot.simulation(p), True)
s = p.to_str()
spot.restrict_dead_end_edges_here(p)
s += p.to_str()
# Applying it twice should not change anything
spot.restrict_dead_end_edges_here(p)
s += p.to_str()

tc.assertEqual(s, """HOA: v1
States: 2
Start: 0
AP: 3 "a" "b" "c"
acc-name: generalized-Buchi 2
Acceptance: 2 Inf(0)&Inf(1)
properties: trans-labels explicit-labels trans-acc stutter-invariant
--BODY--
State: 0
[t] 0
[!0&1&!2] 1
[0&1&!2] 1 {0}
[!0&1&2] 1 {1}
[0&1&2] 1 {0 1}
State: 1
[!0&1&!2] 1
[0&1&!2] 1 {0}
[!0&1&2] 1 {1}
[0&1&2] 1 {0 1}
--END--HOA: v1
States: 2
Start: 0
AP: 3 "a" "b" "c"
acc-name: generalized-Buchi 2
Acceptance: 2 Inf(0)&Inf(1)
properties: trans-labels explicit-labels trans-acc stutter-invariant
--BODY--
State: 0
[t] 0
[0&1&!2] 1 {0}
[0&1&2] 1 {0 1}
State: 1
[!0&1&!2] 1
[0&1&!2] 1 {0}
[!0&1&2] 1 {1}
[0&1&2] 1 {0 1}
--END--HOA: v1
States: 2
Start: 0
AP: 3 "a" "b" "c"
acc-name: generalized-Buchi 2
Acceptance: 2 Inf(0)&Inf(1)
properties: trans-labels explicit-labels trans-acc stutter-invariant
--BODY--
State: 0
[t] 0
[0&1&!2] 1 {0}
[0&1&2] 1 {0 1}
State: 1
[!0&1&!2] 1
[0&1&!2] 1 {0}
[!0&1&2] 1 {1}
[0&1&2] 1 {0 1}
--END--""")

spot.restrict_dead_end_edges_here(q)
s = q.to_str()
tc.assertEqual(s, """HOA: v1
States: 2
Start: 0
AP: 3 "a" "b" "c"
acc-name: generalized-Buchi 2
Acceptance: 2 Inf(0)&Inf(1)
properties: trans-labels explicit-labels trans-acc stutter-invariant
--BODY--
State: 0
[t] 0
[0&1] 1
State: 1
[!0&1&!2] 1
[0&1&!2] 1 {0}
[!0&1&2] 1 {1}
[0&1&2] 1 {0 1}
--END--""")

a = spot.translate('GFa & (FGb | FGc) & GFc', xargs='rde=0')
s = a.to_str()
spot.restrict_dead_end_edges_here(a)
s += a.to_str()
tc.assertEqual(s, """HOA: v1
States: 3
Start: 0
AP: 3 "a" "b" "c"
acc-name: generalized-Buchi 2
Acceptance: 2 Inf(0)&Inf(1)
properties: trans-labels explicit-labels trans-acc stutter-invariant
--BODY--
State: 0
[t] 0
[0&1 | 1&2] 1
[2] 2
State: 1
[!0&1&!2] 1
[0&1&!2] 1 {0}
[!0&1&2] 1 {1}
[0&1&2] 1 {0 1}
State: 2
[!0&2] 2 {1}
[0&2] 2 {0 1}
--END--HOA: v1
States: 3
Start: 0
AP: 3 "a" "b" "c"
acc-name: generalized-Buchi 2
Acceptance: 2 Inf(0)&Inf(1)
properties: trans-labels explicit-labels trans-acc stutter-invariant
--BODY--
State: 0
[t] 0
[0&1] 1
[0&2] 2
State: 1
[!0&1&!2] 1
[0&1&!2] 1 {0}
[!0&1&2] 1 {1}
[0&1&2] 1 {0 1}
State: 2
[!0&2] 2 {1}
[0&2] 2 {0 1}
--END--""")
