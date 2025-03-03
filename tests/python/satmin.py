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


aut = spot.translate('GFa & GFb', 'Buchi', 'SBAcc')
tc.assertEqual(aut.num_sets(), 1)
tc.assertEqual(aut.num_states(), 3)
tc.assertTrue(aut.is_deterministic())


min1 = spot.sat_minimize(aut, acc='Rabin 1')
tc.assertEqual(min1.num_sets(), 2)
tc.assertEqual(min1.num_states(), 2)
min1 = spot.sat_minimize(aut, acc='Rabin 1', sat_langmap=True)
tc.assertEqual(min1.num_sets(), 2)
tc.assertEqual(min1.num_states(), 2)
min1 = spot.sat_minimize(aut, acc='Rabin 1', sat_incr=1)
tc.assertEqual(min1.num_sets(), 2)
tc.assertEqual(min1.num_states(), 2)
min1 = spot.sat_minimize(aut, acc='Rabin 1', sat_incr=1, sat_incr_steps=0)
tc.assertEqual(min1.num_sets(), 2)
tc.assertEqual(min1.num_states(), 2)
min1 = spot.sat_minimize(aut, acc='Rabin 1', sat_incr=1, sat_incr_steps=1)
tc.assertEqual(min1.num_sets(), 2)
tc.assertEqual(min1.num_states(), 2)
min1 = spot.sat_minimize(aut, acc='Rabin 1', sat_incr=1, sat_incr_steps=2)
tc.assertEqual(min1.num_sets(), 2)
tc.assertEqual(min1.num_states(), 2)
min1 = spot.sat_minimize(aut, acc='Rabin 1', sat_incr=1, sat_incr_steps=50)
tc.assertEqual(min1.num_sets(), 2)
tc.assertEqual(min1.num_states(), 2)
min1 = spot.sat_minimize(aut, acc='Rabin 1', sat_incr=2)
tc.assertEqual(min1.num_sets(), 2)
tc.assertEqual(min1.num_states(), 2)
min1 = spot.sat_minimize(aut, acc='Rabin 1', sat_incr=2, sat_incr_steps=-1)
tc.assertEqual(min1.num_sets(), 2)
tc.assertEqual(min1.num_states(), 2)
min1 = spot.sat_minimize(aut, acc='Rabin 1', sat_incr=2, sat_incr_steps=0)
tc.assertEqual(min1.num_sets(), 2)
tc.assertEqual(min1.num_states(), 2)
min1 = spot.sat_minimize(aut, acc='Rabin 1', sat_incr=2, sat_incr_steps=1)
tc.assertEqual(min1.num_sets(), 2)
tc.assertEqual(min1.num_states(), 2)
min1 = spot.sat_minimize(aut, acc='Rabin 1', sat_incr=2, sat_incr_steps=2)
tc.assertEqual(min1.num_sets(), 2)
tc.assertEqual(min1.num_states(), 2)
min1 = spot.sat_minimize(aut, acc='Rabin 1', sat_incr=2, sat_incr_steps=50)
tc.assertEqual(min1.num_sets(), 2)
tc.assertEqual(min1.num_states(), 2)
min1 = spot.sat_minimize(aut, acc='Rabin 1', sat_naive=True)
tc.assertEqual(min1.num_sets(), 2)
tc.assertEqual(min1.num_states(), 2)


min2 = spot.sat_minimize(aut, acc='Streett 2')
tc.assertEqual(min2.num_sets(), 4)
tc.assertEqual(min2.num_states(), 1)
min2 = spot.sat_minimize(aut, acc='Streett 2', sat_langmap=True)
tc.assertEqual(min2.num_sets(), 4)
tc.assertEqual(min2.num_states(), 1)
min2 = spot.sat_minimize(aut, acc='Streett 2', sat_incr=1)
tc.assertEqual(min2.num_sets(), 4)
tc.assertEqual(min2.num_states(), 1)
min2 = spot.sat_minimize(aut, acc='Streett 2', sat_incr=1, sat_incr_steps=0)
tc.assertEqual(min2.num_sets(), 4)
tc.assertEqual(min2.num_states(), 1)
min2 = spot.sat_minimize(aut, acc='Streett 2', sat_incr=1, sat_incr_steps=1)
tc.assertEqual(min2.num_sets(), 4)
tc.assertEqual(min2.num_states(), 1)
min2 = spot.sat_minimize(aut, acc='Streett 2', sat_incr=1, sat_incr_steps=2)
tc.assertEqual(min2.num_sets(), 4)
tc.assertEqual(min2.num_states(), 1)
min2 = spot.sat_minimize(aut, acc='Streett 2', sat_incr=1, sat_incr_steps=50)
tc.assertEqual(min2.num_sets(), 4)
tc.assertEqual(min2.num_states(), 1)
min2 = spot.sat_minimize(aut, acc='Streett 2', sat_incr=2)
tc.assertEqual(min2.num_sets(), 4)
tc.assertEqual(min2.num_states(), 1)
min2 = spot.sat_minimize(aut, acc='Streett 2', sat_incr=2, sat_incr_steps=-1)
tc.assertEqual(min2.num_sets(), 4)
tc.assertEqual(min2.num_states(), 1)
min2 = spot.sat_minimize(aut, acc='Streett 2', sat_incr=2, sat_incr_steps=0)
tc.assertEqual(min2.num_sets(), 4)
tc.assertEqual(min2.num_states(), 1)
min2 = spot.sat_minimize(aut, acc='Streett 2', sat_incr=2, sat_incr_steps=1)
tc.assertEqual(min2.num_sets(), 4)
tc.assertEqual(min2.num_states(), 1)
min2 = spot.sat_minimize(aut, acc='Streett 2', sat_incr=2, sat_incr_steps=2)
tc.assertEqual(min2.num_sets(), 4)
tc.assertEqual(min2.num_states(), 1)
min2 = spot.sat_minimize(aut, acc='Streett 2', sat_incr=2, sat_incr_steps=50)
tc.assertEqual(min2.num_sets(), 4)
tc.assertEqual(min2.num_states(), 1)
min2 = spot.sat_minimize(aut, acc='Streett 2', sat_naive=True)
tc.assertEqual(min2.num_sets(), 4)
tc.assertEqual(min2.num_states(), 1)


min3 = spot.sat_minimize(aut, acc='Rabin 2',
                         state_based=True, max_states=5)
tc.assertEqual(min3.num_sets(), 4)
tc.assertEqual(min3.num_states(), 3)
min3 = spot.sat_minimize(aut, acc='Rabin 2',
                         state_based=True, max_states=5, sat_langmap=True)
tc.assertEqual(min3.num_sets(), 4)
tc.assertEqual(min3.num_states(), 3)
min3 = spot.sat_minimize(aut, acc='Rabin 2',
                         state_based=True, max_states=5, sat_incr=1)
tc.assertEqual(min3.num_sets(), 4)
tc.assertEqual(min3.num_states(), 3)
min3 = spot.sat_minimize(aut, acc='Rabin 2',
                         state_based=True, max_states=5, sat_incr=1,
                         sat_incr_steps=0)
tc.assertEqual(min3.num_sets(), 4)
tc.assertEqual(min3.num_states(), 3)
min3 = spot.sat_minimize(aut, acc='Rabin 2',
                         state_based=True, max_states=5, sat_incr=1,
                         sat_incr_steps=1)
tc.assertEqual(min3.num_sets(), 4)
tc.assertEqual(min3.num_states(), 3)
min3 = spot.sat_minimize(aut, acc='Rabin 2',
                         state_based=True, max_states=5, sat_incr=1,
                         sat_incr_steps=2)
tc.assertEqual(min3.num_sets(), 4)
tc.assertEqual(min3.num_states(), 3)
min3 = spot.sat_minimize(aut, acc='Rabin 2',
                         state_based=True, max_states=5, sat_incr=1,
                         sat_incr_steps=50)
tc.assertEqual(min3.num_sets(), 4)
tc.assertEqual(min3.num_states(), 3)
min3 = spot.sat_minimize(aut, acc='Rabin 2',
                         state_based=True, max_states=5, sat_incr=2)
tc.assertEqual(min3.num_sets(), 4)
tc.assertEqual(min3.num_states(), 3)
min3 = spot.sat_minimize(aut, acc='Rabin 2',
                         state_based=True, max_states=5, sat_incr=2,
                         sat_incr_steps=-1)
tc.assertEqual(min3.num_sets(), 4)
tc.assertEqual(min3.num_states(), 3)
min3 = spot.sat_minimize(aut, acc='Rabin 2',
                         state_based=True, max_states=5, sat_incr=2,
                         sat_incr_steps=0)
tc.assertEqual(min3.num_sets(), 4)
tc.assertEqual(min3.num_states(), 3)
min3 = spot.sat_minimize(aut, acc='Rabin 2',
                         state_based=True, max_states=5, sat_incr=2,
                         sat_incr_steps=1)
tc.assertEqual(min3.num_sets(), 4)
tc.assertEqual(min3.num_states(), 3)
min3 = spot.sat_minimize(aut, acc='Rabin 2',
                         state_based=True, max_states=5, sat_incr=2,
                         sat_incr_steps=2)
tc.assertEqual(min3.num_sets(), 4)
tc.assertEqual(min3.num_states(), 3)
min3 = spot.sat_minimize(aut, acc='Rabin 2',
                         state_based=True, max_states=5, sat_incr=2,
                         sat_incr_steps=50)
tc.assertEqual(min3.num_sets(), 4)
tc.assertEqual(min3.num_states(), 3)
min3 = spot.sat_minimize(aut, acc='Rabin 2',
                         state_based=True, max_states=5, sat_naive=True)
tc.assertEqual(min3.num_sets(), 4)
tc.assertEqual(min3.num_states(), 3)


min4 = spot.sat_minimize(aut, acc='parity max odd 3',
                         colored=True)
tc.assertEqual(min4.num_sets(), 3)
tc.assertEqual(min4.num_states(), 2)
min4 = spot.sat_minimize(aut, acc='parity max odd 3',
                         colored=True, sat_langmap=True)
tc.assertEqual(min4.num_sets(), 3)
tc.assertEqual(min4.num_states(), 2)
min4 = spot.sat_minimize(aut, acc='parity max odd 3',
                         colored=True, sat_incr=1)
tc.assertEqual(min4.num_sets(), 3)
tc.assertEqual(min4.num_states(), 2)
min4 = spot.sat_minimize(aut, acc='parity max odd 3',
                         colored=True, sat_incr=1, sat_incr_steps=0)
tc.assertEqual(min4.num_sets(), 3)
tc.assertEqual(min4.num_states(), 2)
min4 = spot.sat_minimize(aut, acc='parity max odd 3',
                         colored=True, sat_incr=1, sat_incr_steps=1)
tc.assertEqual(min4.num_sets(), 3)
tc.assertEqual(min4.num_states(), 2)
min4 = spot.sat_minimize(aut, acc='parity max odd 3',
                         colored=True, sat_incr=1, sat_incr_steps=2)
tc.assertEqual(min4.num_sets(), 3)
tc.assertEqual(min4.num_states(), 2)
min4 = spot.sat_minimize(aut, acc='parity max odd 3',
                         colored=True, sat_incr=1, sat_incr_steps=50)
tc.assertEqual(min4.num_sets(), 3)
tc.assertEqual(min4.num_states(), 2)
min4 = spot.sat_minimize(aut, acc='parity max odd 3',
                         colored=True, sat_incr=2)
tc.assertEqual(min4.num_sets(), 3)
tc.assertEqual(min4.num_states(), 2)
min4 = spot.sat_minimize(aut, acc='parity max odd 3',
                         colored=True, sat_incr=2, sat_incr_steps=-1)
tc.assertEqual(min4.num_sets(), 3)
tc.assertEqual(min4.num_states(), 2)
min4 = spot.sat_minimize(aut, acc='parity max odd 3',
                         colored=True, sat_incr=2, sat_incr_steps=0)
tc.assertEqual(min4.num_sets(), 3)
tc.assertEqual(min4.num_states(), 2)
min4 = spot.sat_minimize(aut, acc='parity max odd 3',
                         colored=True, sat_incr=2, sat_incr_steps=1)
tc.assertEqual(min4.num_sets(), 3)
tc.assertEqual(min4.num_states(), 2)
min4 = spot.sat_minimize(aut, acc='parity max odd 3',
                         colored=True, sat_incr=2, sat_incr_steps=2)
tc.assertEqual(min4.num_sets(), 3)
tc.assertEqual(min4.num_states(), 2)
min4 = spot.sat_minimize(aut, acc='parity max odd 3',
                         colored=True, sat_incr=2, sat_incr_steps=50)
tc.assertEqual(min4.num_sets(), 3)
tc.assertEqual(min4.num_states(), 2)
min4 = spot.sat_minimize(aut, acc='parity max odd 3',
                         colored=True, sat_naive=True)
tc.assertEqual(min4.num_sets(), 3)
tc.assertEqual(min4.num_states(), 2)


aut = spot.translate('GFa')
tc.assertEqual(aut.num_sets(), 1)
tc.assertEqual(aut.num_states(), 1)
tc.assertTrue(aut.is_deterministic())
out = spot.sat_minimize(aut, state_based=True)
tc.assertEqual(out.num_states(), 2)
out = spot.sat_minimize(aut, state_based=True, max_states=1)
tc.assertTrue(out is None)
