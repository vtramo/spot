#!/usr/bin/python3
# -*- mode: python; coding: utf-8 -*-
# Copyright (C) 2020-2022 Laboratoire de Recherche et Développement de
# l'EPITA.
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


import spot, buddy
from unittest import TestCase
tc = TestCase()

def create_aps(aut):
    return [buddy.bdd_ithvar(aut.register_ap(ap.ap_name())) for ap in aut.ap()]

aut = spot.automaton("""
HOA: v1 
States: 1 
Start: 0 
AP: 1 "a" "b"
Acceptance: 1 Inf(0) 
--BODY-- 
State: 0 
[t] 0
--END--""")

aps = create_aps(aut)
tc.assertEqual(aut.num_edges(), 1)
aut.split_edges(aps)
tc.assertEqual(aut.num_edges(), 2)

aut = spot.automaton("""
HOA: v1 
States: 2
Start: 0 
AP: 1 "a" "b"
Acceptance: 1 Inf(0) 
--BODY-- 
State: 0 
[t] 0
State: 1
[0&1] 1
--END--""")

aps = create_aps(aut)
tc.assertEqual(aut.num_edges(), 2)
aut.split_edges(aps)
tc.assertEqual(aut.num_edges(), 3)

aut = spot.automaton("""
HOA: v1 
States: 1 
Start: 0 
AP: 1 "a"
Acceptance: 1 Inf(0) 
--BODY-- 
State: 0  
--END--""")

aps = create_aps(aut)
tc.assertEqual(aut.num_edges(), 1)
aut.split_edges(aps)
tc.assertEqual(aut.num_edges(), 0)

aut = spot.automaton("""
HOA: v1 
States: 3
Start: 0 
AP: 1 "a" "b"
Acceptance: 1 Inf(0) 
--BODY-- 
State: 0 
[t] 1
[!0&!1 | 0&!1] 2
State: 1
State: 2
--END--""")
# Before:
# State: 0
# {a, b, c, d}
# {a, b}
# After:
# State : 0
# {a, b, c}, {d}
# {a, b}

# a = 00
# b = 10
# c = 01
# d = 11

aps = create_aps(aut)
tc.assertEqual(aut.num_edges(), 2)
# [{a, b, c}]
aut.split_edges([buddy.bdd_not(aps[0]) | buddy.bdd_not(aps[1])])
tc.assertEqual(aut.num_edges(), 3)

aut = spot.automaton("""
HOA: v1 
States: 3
Start: 0 
AP: 1 "a" "b"
Acceptance: 1 Inf(0) 
--BODY-- 
State: 0 
[t] 1
[!0&!1 | 0&!1] 2
State: 1
State: 2
--END--""")
# Before:
# State: 0
# {a, b, c, d}
# {a, c}
# After:
# State : 0
# {a, b}, {c, d}
# {a}, {c}

# a = 00
# b = 10
# c = 01
# d = 11

aps = create_aps(aut)
tc.assertEqual(aut.num_edges(), 2)
# [{a, b}, {c, d}]
aut.split_edges([buddy.bdd_not(aps[1]), buddy.bdd_not(aps[0])])
tc.assertEqual(aut.num_edges(), 4)

aut = spot.automaton("""
HOA: v1 
States: 3
Start: 0 
AP: 1 "a" "b"
Acceptance: 1 Inf(0) 
--BODY-- 
State: 0 
[t] 1
[!0&!1 | 0&!1] 2
State: 1
State: 2
--END--""")
# Before:
# State: 0
# {a, b, c, d}
# {a, c}
# After:
# State : 0
# {a},{b},{c},{d}
# {a},{c}

# a = 00
# b = 10
# c = 01
# d = 11

aps = create_aps(aut)
neg_aps = [buddy.bdd_not(a) for a in aps]
tc.assertEqual(aut.num_edges(), 2)
# [{a},{b},{c},{d}]
aut.split_edges([
    neg_aps[0] & neg_aps[1],
    neg_aps[0] & aps[1],
    aps[0] & neg_aps[1],
    aps[0] & aps[1]
])
tc.assertEqual(aut.num_edges(), 6)

aut = spot.automaton("""
HOA: v1 
States: 3
Start: 0 
AP: 1 "a" "b"
Acceptance: 1 Inf(0) 
--BODY-- 
State: 0 
[t] 1
[!0&!1 | 0&!1] 2
State: 1
State: 2
--END--""")
# Before
# State: 0
# {a, b, c, d}
# {a, b}
# After:
# State : 0
# {a, b, c}, {d}
# {a, b}

# a = 00
# b = 10
# c = 01
# d = 11

aps = create_aps(aut)
neg_aps = [buddy.bdd_not(a) for a in aps]
tc.assertEqual(aut.num_edges(), 2)
# [{a, b, c}, {d}]
aut.split_edges([
    neg_aps[0] | neg_aps[1],
    aps[0] & aps[1]
])
tc.assertEqual(aut.num_edges(), 3)