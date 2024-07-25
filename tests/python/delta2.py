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

def generate_formulas():
    for i in ['{} {} ({} {} {})', '({} {} {}) {} {}']:
        for k in "MWUR":
            for l in "MWUR":
                for a in ['a', 'false', 'true']:
                    for b in ['b', 'false', 'true']:
                        for c in ['c', 'false', 'true']:
                            inner = i.format(a,k,b,l,c);
                            for j in ['GF({})', 'FG({})',
                                      '({}) W d', '({}) U d',
                                      'd W ({})', 'd U ({})',
                                      '({}) R d', '({}) M d',
                                      'd R ({})', 'd M ({})']:
                                yield j.format(inner)

                            for j1 in ['G(F({}){}F(e {} f))',
                                       'F(G({}){}G(e {} f))']:
                                for j2 in "&|":
                                    for j3 in "MWUR":
                                        yield j1.format(inner,j2,j3)

seen = set()
for f in generate_formulas():
    ltl_in = spot.formula(f)
    if ltl_in in seen:
        continue
    seen.add(ltl_in)
    ltl_out = spot.to_delta2(ltl_in)
    ok = spot.are_equivalent(ltl_in, ltl_out)
    din = ltl_in.is_delta2()
    dout = ltl_out.is_delta2()
    print(f"{ok:1} {din:1}{dout:1}   {ltl_in::30} {ltl_out::30}")
    tc.assertTrue(ok)
    tc.assertTrue(dout)
