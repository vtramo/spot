# -*- mode: python; coding: utf-8 -*-
# Copyright (C) 2021 Laboratoire de Recherche et
# Développement de l'Epita (LRDE).
# Copyright (C) 2003, 2004 Laboratoire d'Informatique de Paris 6 (LIP6),
# département Systemes Répartis Coopératifs (SRC), Université Pierre
# et Marie Curie.
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

aut = spot.automaton("""HOA: v1
States: 56
Start: 0
AP: 4 "i0" "i1" "i2" "o0"
acc-name: all
Acceptance: 0 t
properties: trans-labels explicit-labels state-acc deterministic
spot-state-player: 0 0 1 0 1 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1
                   0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1
--BODY--
State: 0
[0&!1&!2] 2
[!0&1&!2] 4
[!0&!1&!2] 5
State: 1
[0&!1&!2] 2
[!0&!1&!2] 5
[0&1&!2] 7
State: 2
[!3] 1
State: 3
[!0&1&!2] 4
[0&1&!2] 47
State: 4
[!3] 3
State: 5
[!3] 0
State: 6
[0&1&!2] 7
[!0&1&!2] 9
State: 7
[!3] 6
State: 8
[!0&1&!2] 9
[!0&1&2] 11
State: 9
[3] 8
State: 10
[!0&1&2] 11
[0&1&2] 13
[!0&!1&2] 15
State: 11
[3] 10
State: 12
[0&1&2] 13
[0&1&!2] 17
State: 13
[!3] 12
State: 14
[!0&!1&2] 15
[0&!1&2] 45
State: 15
[3] 14
State: 16
[0&1&!2] 17
[!0&1&!2] 19
[0&!1&!2] 21
State: 17
[!3] 16
State: 18
[0&1&!2] 17
[!0&1&!2] 19
[!0&!1&!2] 23
State: 19
[!3] 18
State: 20
[0&!1&!2] 21
[!0&!1&!2] 35
State: 21
[!3] 20
State: 22
[!0&!1&!2] 23
[0&!1&!2] 25
State: 23
[!3] 22
State: 24
[0&!1&!2] 25
[0&!1&2] 27
State: 25
[3] 24
State: 26
[0&!1&2] 27
[0&1&2] 29
[!0&!1&2] 31
State: 27
[3] 26
State: 28
[0&1&2] 29
[!0&1&2] 33
State: 29
[3] 28
State: 30
[!0&!1&!2] 5
[!0&!1&2] 31
State: 31
[!3] 30
State: 32
[!0&1&!2] 19
[!0&1&2] 33
State: 33
[!3] 32
State: 34
[!0&!1&!2] 35
[!0&!1&2] 37
State: 35
[3] 34
State: 36
[!0&!1&2] 37
[!0&1&2] 39
[0&!1&2] 41
State: 37
[3] 36
State: 38
[!0&1&2] 39
[0&1&2] 43
State: 39
[3] 38
State: 40
[0&!1&!2] 2
[0&!1&2] 41
State: 41
[!3] 40
State: 42
[0&1&!2] 17
[0&1&2] 43
State: 43
[!3] 42
State: 44
[0&!1&!2] 2
[0&!1&2] 45
State: 45
[!3] 44
State: 46
[0&1&!2] 47
[0&1&2] 49
State: 47
[3] 46
State: 48
[0&1&2] 49
[!0&1&2] 51
[0&!1&2] 53
State: 49
[3] 48
State: 50
[!0&1&!2] 19
[!0&1&2] 51
State: 51
[!3] 50
State: 52
[0&!1&2] 53
[!0&!1&2] 55
State: 53
[3] 52
State: 54
[!0&!1&!2] 5
[!0&!1&2] 55
State: 55
[!3] 54
--END--""")

autmin_str = """HOA: v1
States: 13
Start: 3
AP: 4 "i0" "i1" "i2" "o0"
acc-name: all
Acceptance: 0 t
properties: trans-labels explicit-labels state-acc deterministic
spot-state-player: 0 0 0 0 1 1 1 1 1 1 1 1 1
--BODY--
State: 0
[0&2] 4
[!0&!1&2 | 0&!2] 5
[!0&1&!2] 6
[!0&!1&!2] 7
[!0&1&2] 8
State: 1
[!0&!1&2] 5
[0&!1 | 0&2] 9
[!0&1 | !0&!2] 10
[0&1&!2] 11
State: 2
[0&!1&2] 4
[!0&!1&!2 | !0&1&2] 8
[!0&1&!2] 10
[0&1 | 0&!2] 11
[!0&!1&2] 12
State: 3
[0&!1&!2] 5
[!0&!2 | 0&!1&2] 7
[!0&1&2] 8
[0&1&2] 9
[!0&!1&2 | 0&1&!2] 12
State: 4
[t] 3
State: 5
[!3] 0
State: 6
[3] 0
State: 7
[!3] 3
State: 8
[3] 2
State: 9
[3] 1
State: 10
[!3] 1
State: 11
[!3] 2
State: 12
[3] 3
--END--"""

autmin = spot.minimize_mealy(aut)

assert(autmin.to_str("hoa") == autmin_str)