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
import buddy
from unittest import TestCase
tc = TestCase()


def complement(aut):
    return spot.dualize(aut.postprocess('det', 'gen'))


n = 10000

for aut in spot.automata(
        "randltl -n-1 a b "
        "| ltl2tgba "
        f"| autfilt --is-semi-deterministic --acceptance-is=Buchi -n{n} |"):

    comp = complement(aut)
    semidet_comp = spot.complement_semidet(aut, True)
    tc.assertTrue(comp.equivalent_to(semidet_comp))
