#!/usr/bin/python3
# -*- mode: python; coding: utf-8 -*-
# Copyright (C) 2020 Laboratoire de Recherche et Développement de
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

import spot
import buddy

g = spot.automaton("""HOA: v1 States: 9 Start: 0 AP: 2 "a" "b"
acc-name: Streett 1 Acceptance: 2 Fin(0) | Inf(1) properties:
trans-labels explicit-labels state-acc spot-state-player: 0 1 0 1 0 1
0 1 1 --BODY-- State: 0 {1} [1] 1 [1] 3 State: 1 {1} [1] 2 State: 2
{1} [0] 8 State: 3 {1} [1] 4 State: 4 {1} [0] 5 State: 5 {1} [0] 6
State: 6 {1} [1] 7 State: 7 State: 8 {1} [0] 2 --END--""")

assert spot.solve_parity_game(g) == False

s = spot.highlight_strategy(g).to_str("HOA", "1.1")
assert s == """HOA: v1.1
States: 9
Start: 0
AP: 2 "a" "b"
acc-name: Streett 1
Acceptance: 2 Fin(0) | Inf(1)
properties: trans-labels explicit-labels state-acc !complete
properties: !deterministic exist-branch
spot.highlight.states: 0 5 1 4 2 4 3 5 4 5 5 5 6 5 7 5 8 4
spot.highlight.edges: 2 5 3 4 6 5 8 5 9 4
spot.state-player: 0 1 0 1 0 1 0 1 1
--BODY--
State: 0 {1}
[1] 1
[1] 3
State: 1 {1}
[1] 2
State: 2 {1}
[0] 8
State: 3 {1}
[1] 4
State: 4 {1}
[0] 5
State: 5 {1}
[0] 6
State: 6 {1}
[1] 7
State: 7
State: 8 {1}
[0] 2
--END--"""

p0v = spot.p0_val()
p1v = spot.p1_val()
usv = spot.game_unseen_lvl()
blvl_p0 = spot.best_lvl_p0()
blvl_p1 = spot.best_lvl_p1()

#circular constraint 1
g = spot.make_twa_graph()
g.new_states(6)
g.new_edge(0,1,buddy.bddtrue)
g.new_edge(0,2,buddy.bddtrue)
g.new_edge(1,2,buddy.bddtrue)
g.new_edge(2,1,buddy.bddtrue)
g.new_edge(1,3,buddy.bddtrue)
g.new_edge(2,3,buddy.bddtrue)
g.new_edge(3,4,buddy.bddtrue)
g.new_edge(4,5,buddy.bddtrue)
p_list = [p1v for _ in range(6)]
p_list[0] = p0v
spot.set_state_players(g, p_list)
spot.add_transposed_here(g)
this_attr = spot.vectorint([usv for _ in range(6)])
spot.attractor(g, this_attr, p1v)
assert (list(this_attr) == [blvl_p1+i-1 for i in [6, 5, 4, 3, 2, 1]]
        or list(this_attr) == [6, 4, 5, 3, 2, 1])

g = spot.make_twa_graph()
g.new_states(8)
g.new_edge(0,1,buddy.bddtrue)
g.new_edge(0,2,buddy.bddtrue)
for i in range(1,5):
    for j in range(1,5):
        if i == j:
            continue
        g.new_edge(i,j,buddy.bddtrue)
g.new_edge(3,5,buddy.bddtrue)
g.new_edge(4,5,buddy.bddtrue)
g.new_edge(5,6,buddy.bddtrue)
g.new_edge(6,7,buddy.bddtrue)
p_list = [p1v for _ in range(8)]
p_list[0] = p0v
spot.set_state_players(g, p_list)
spot.add_transposed_here(g)
this_attr = spot.vectorint([usv for _ in range(8)])
spot.attractor(g, this_attr, p1v)
# Apply the strategy "go down"
orig_edges = [(e.src,e.dst) for e in g.edges()]
g_test = spot.make_twa_graph()
g_test.new_states(g.num_states())
for i,vi in enumerate(this_attr):
    for j,vj in enumerate(this_attr):
        if i == j:
            continue
        # Check if there is an edge between them in the original graph
        if (i,j) not in orig_edges:
            continue
        # make an edge in test if lvl[j] is smaller than lvl[i]
        # Note neighbouring vertices can not have the same attr lvl
        assert vi != vj, "Neghbouring vertices have same lvl!";
        if vi < vj:
            g_test.new_edge(i,j,buddy.bddtrue)
# All SCCs have to be trivial
scci = spot.scc_info(g_test)
for ascc in scci:
    assert ascc.is_trivial(), "This has to generate trivial sccs"


g = spot.make_twa_graph()
g.new_states(9)
g.new_edge(0,1,buddy.bddtrue)
g.new_edge(0,2,buddy.bddtrue)
g.new_edge(1,3,buddy.bddtrue)
g.new_edge(1,4,buddy.bddtrue)
g.new_edge(2,4,buddy.bddtrue)
g.new_edge(2,5,buddy.bddtrue)
g.new_edge(5,6,buddy.bddtrue)
g.new_edge(6,7,buddy.bddtrue)
g.new_edge(8,6,buddy.bddtrue)
g.new_edge(8,7,buddy.bddtrue)
spot.set_state_players(g, [p1v,p0v,p1v,p1v,p1v,p1v,p1v,p1v,p0v])
spot.add_transposed_here(g)


#CPRE test
this_attr = spot.vectorint([usv for _ in range(9)])
this_attr[3] = blvl_p1+1
this_attr[4] = blvl_p1+1
this_attr[7] = blvl_p1+1
p0v = spot.p0_val()
p1v = spot.p1_val()
g = spot.make_twa_graph()
g.new_states(9)
g.new_edge(0,1,buddy.bddtrue)
g.new_edge(0,2,buddy.bddtrue)
g.new_edge(1,3,buddy.bddtrue)
g.new_edge(1,4,buddy.bddtrue)
g.new_edge(2,4,buddy.bddtrue)
g.new_edge(2,5,buddy.bddtrue)
g.new_edge(5,6,buddy.bddtrue)
g.new_edge(6,7,buddy.bddtrue)
g.new_edge(8,6,buddy.bddtrue)
g.new_edge(8,7,buddy.bddtrue)
spot.set_state_players(g, [p1v,p0v,p1v,p1v,p1v,p1v,p1v,p1v,p0v])
spot.add_transposed_here(g)


#CPRE test
usv = spot.game_unseen_lvl()
blvl_p0 = spot.best_lvl_p0()
blvl_p1 = spot.best_lvl_p1()
this_attr = spot.vectorint([usv for _ in range(9)])
this_attr[3] = blvl_p1+1
this_attr[4] = blvl_p1+1
this_attr[7] = blvl_p1+1
spot.cpre(g, this_attr, p1v, blvl_p1+2)
res_sol = [usv for _ in range(9)]
res_sol[3] = blvl_p1+1
res_sol[4] = blvl_p1+1
res_sol[7] = blvl_p1+1
res_sol[1] = blvl_p1+2
res_sol[2] = blvl_p1+2
res_sol[6] = blvl_p1+2
assert(res_sol == list(this_attr))
spot.cpre(g, this_attr, p1v, blvl_p1+3)
res_sol[0] = blvl_p1+3
res_sol[5] = blvl_p1+3
res_sol[8] = blvl_p1+3
assert(res_sol == list(this_attr))

# Attractor test
# Make 4 not trivially accepting
g.new_edge(4,4,buddy.bddtrue)
spot.add_transposed_here(g)
this_attr = spot.vectorint([usv for _ in range(9)])
# Mark 3 and 7 as winning
this_attr[3] = blvl_p1
this_attr[7] = blvl_p1
spot.attractor(g, this_attr, p1v)
assert(list(this_attr)
       == [blvl_p1+4,usv,blvl_p1+3,blvl_p1,usv,blvl_p1+2,
           blvl_p1+1,blvl_p1,blvl_p1+2])

#Change graph with a deadlock
g.new_edge(3,4,buddy.bddtrue)
g.new_edge(4,3,buddy.bddtrue)
spot.add_transposed_here(g)
this_attr = spot.vectorint([usv for _ in range(9)])
spot.attractor(g, this_attr, p1v)
assert(list(this_attr) == [blvl_p1+4,usv,blvl_p1+3,usv,usv,blvl_p1+2,
                           blvl_p1+1,blvl_p1+0,blvl_p1+1])

# Check acceptance of all finite words
g.acc().set_acceptance(spot.acc_code_f())
spot.solve(g)
this_strat = spot.get_strategy(g)
this_attr_strat = spot.get_attractor_strategy(g)
this_winner = spot.get_state_winner(g)
this_owner = spot.get_state_players(g)
assert(this_winner ==
       (p1v,p0v,p1v,p0v,p0v,p1v,p1v,p1v,p1v))
assert(this_attr_strat ==
       (blvl_p1+4,blvl_p0,blvl_p1+3,blvl_p0,blvl_p0,blvl_p1+2,
        blvl_p1+1,blvl_p1+0,blvl_p1+1))
# Check if derived strategies are infact valid
for s in range(g.num_states()):
    if (this_winner != p1v
        or this_owner[s] == p0v):
        continue

    # Follow the strat then no_strat <-> dead end
    while (this_strat[s] != spot.no_strat()):
        s = g.edge_storage(this_strat[s]).dst
    assert (list(g.out(s)) == []), "Strategy did not lead to dead end"

# Check acceptance of all infinite words
g.acc().set_acceptance(spot.acc_code_t())
spot.solve(g)
this_strat = spot.get_strategy(g)
this_attr_strat = spot.get_attractor_strategy(g)
this_winner = spot.get_state_winner(g)
this_owner = spot.get_state_players(g)
assert(this_winner ==
       (p1v,p1v,p1v,p1v,p1v,p0v,p0v,p0v,p0v))
assert(spot.get_attractor_strategy(g) ==
       (blvl_p1,blvl_p1,blvl_p1,blvl_p1,blvl_p1,blvl_p0-2,blvl_p0-1,
        blvl_p0-0,blvl_p0-1))

#Buchi
new_mark = g.set_buchi()
e_acc1 = g.new_edge(1,1,buddy.bddtrue, new_mark)
e_acc2 = g.new_edge(7,0,buddy.bddtrue, new_mark)
spot.add_transposed_here(g)
spot.solve(g)
this_strat = spot.get_strategy(g)
this_attr_strat = spot.get_attractor_strategy(g)
this_winner = spot.get_state_winner(g)
this_owner = spot.get_state_players(g)

assert (this_winner
        == (p1v,p0v,p1v,p0v,p0v,p1v,p1v,p1v,p1v))
assert (this_attr_strat
        == (blvl_p1+4,-1,blvl_p1+3,blvl_p0,blvl_p0,blvl_p1+2,blvl_p1+1,
            blvl_p1+0,blvl_p1+1))
#todo additional strategy testing

# Büchi as reach
spot.solve(g, True)
this_strat = spot.get_strategy(g)
this_attr_strat = spot.get_attractor_strategy(g)
this_winner = spot.get_state_winner(g)
this_owner = spot.get_state_players(g)
assert (this_winner
        == (p1v,p0v,p1v,p0v,p0v,p1v,p1v,p1v,p1v))
assert (this_attr_strat
        == (blvl_p1+4,-1,blvl_p1+3,blvl_p0,blvl_p0,blvl_p1+2,blvl_p1+1,
            blvl_p1+0,blvl_p1+1))

#Co-Buchi
new_mark2 = g.set_co_buchi()
if (new_mark != new_mark2):
    g.edge_storage(e_acc1).acc = new_mark2
    g.edge_storage(e_acc2).acc = new_mark2

spot.solve(g)
this_strat = spot.get_strategy(g)
this_attr_strat = spot.get_attractor_strategy(g)
this_winner = spot.get_state_winner(g)
this_owner = spot.get_state_players(g)

assert(this_attr_strat
       == (blvl_p1,blvl_p0,blvl_p1,blvl_p1,blvl_p1,blvl_p1,blvl_p1,
           blvl_p1, blvl_p1))
assert(this_winner
       == (p1v, p0v, p1v, p1v, p1v, p1v, p1v, p1v, p1v))

# Co-Büchi as avoid
spot.solve(g, True)
this_strat = spot.get_strategy(g)
this_attr_strat = spot.get_attractor_strategy(g)
this_winner = spot.get_state_winner(g)
this_owner = spot.get_state_players(g)

assert(this_winner
       == (p1v, p0v, p1v, p1v, p1v, p0v, p0v, p0v, p0v))
assert(this_attr_strat
       == (blvl_p1+0,blvl_p0-0,blvl_p1+0,blvl_p1+0,blvl_p1+0,
           blvl_p0-2,blvl_p0-1,blvl_p0-0,blvl_p0-1))


