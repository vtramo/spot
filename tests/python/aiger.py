# -*- mode: python; coding: utf-8 -*-
# Copyright (C) 2021  Laboratoire de Recherche et Développement
# de l'Epita
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

# Test parsing
flipflop = spot.aig.parse_aag("""aag 7 2 1 2 4
2
4
6 14
6
7
8 2 6
10 3 7
12 9 11
14 4 12
i0 enable
i1 reset
o0 out
o1 outneg""")

# Basics
assert flipflop.num_inputs() == 2
assert flipflop.num_outputs() == 2
assert flipflop.num_gates() == 4

# Test sim
ins = spot.vectorbool(2, False)
flipflop.sim_init()
assert not flipflop.sim_state_of(0)
assert flipflop.sim_state_of(1)
assert not any(flipflop.sim_state()[2:])
# test disabled
for _ in range(10):
    flipflop.sim_step(ins)
    assert not flipflop.sim_state_of(flipflop.outputs()[0])
#test enabled
ins[0] = True
ins[1] = True
flipflop.sim_step(ins)

old_val = flipflop.sim_state_of(flipflop.outputs()[0])
for _ in range(10):
    flipflop.sim_step(ins)
    assert flipflop.sim_state_of(flipflop.outputs()[0]) != old_val
    old_val = flipflop.sim_state_of(flipflop.outputs()[0])

# Check reset on low
for i in range(100):
    if i%3 == 0:
        ins[1] = False
    else:
        ins[1] = True
    flipflop.sim_step(ins)
    if i%3 == 0:
        flipflop.sim_state_of(flipflop.outputs()[0])

