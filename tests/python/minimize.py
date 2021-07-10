import spot
spot.setup()

# Syntcomp: Alarm_2d1010f8.tlsf
aut = spot.automaton("""HOA: v1
States: 17
Start: 0
AP: 6 "u02alarm29control02alarm29control"
"u02alarm29control0f1d2alarm29turn2off1b"
"u02alarm29control0f1d2alarm29turn2on1b" "p0p0off02alarm29intent"
"p0p0on02alarm29intent" "p0b02alarm29alarm"
acc-name: all
Acceptance: 0 t
properties: trans-labels explicit-labels state-acc deterministic
--BODY--
State: 0
[!0&!1&2&!3&!4 | !0&!1&2&3&4 | !0&1&!2&!3&!4 | !0&1&!2&3&4 | 0&!1&!2&!3&!4
               | 0&!1&!2&3&4] 1
[!0&!1&2&!3&4&!5 | !0&!1&2&3&!4&5] 2
[!0&!1&2&!3&4&5 | !0&!1&2&3&!4&!5] 3
State: 1
[!0&!1&2 | !0&1&!2 | 0&!1&!2] 1
State: 2
[!0&!1&2&!3&!4 | !0&!1&2&3&4 | !0&1&!2&!3&!4 | !0&1&!2&3&4 | 0&!1&!2&!3&!4
               | 0&!1&!2&3&4] 4
[!0&!1&2&!3&4&!5] 5
[!0&!1&2&3&!4&!5] 6
[!0&!1&2&!3&4&5] 7
[!0&1&!2&3&!4&5] 8
State: 3
[!0&!1&2&3&!4&5] 2
[!0&!1&2&!3&!4 | !0&!1&2&3&4 | !0&1&!2&!3&!4 | !0&1&!2&3&4 | 0&!1&!2&!3&!4
               | 0&!1&!2&3&4] 4
[!0&!1&2&!3&4&!5] 5
[!0&!1&2&3&!4&!5] 6
[!0&!1&2&!3&4&5] 7
State: 4
[!0&!1&2&!3&!4 | !0&!1&2&3&4 | !0&!1&2&!4&5 | !0&1&!2&!3&!4 | !0&1&!2&3&4
               | !0&1&!2&!4&5 | 0&!1&!2&!3&!4 | 0&!1&!2&3&4 | 0&!1&!2&!4&5] 4
[!0&!1&2&!3&4 | !0&1&!2&!3&4 | 0&!1&!2&!3&4] 9
[!0&!1&2&3&!4&!5 | !0&1&!2&3&!4&!5 | 0&!1&!2&3&!4&!5] 10
State: 5
[!0&!1&2&!3&!4 | !0&1&!2&!3&!4 | 0&!1&!2&!3&!4] 4
[!0&!1&2&!3&4] 5
[!0&!1&2&3&4 | !0&1&!2&3&4 | 0&!1&!2&3&4] 9
[!0&!1&2&3&!4] 11
State: 6
[!0&!1&2&!3&!4 | !0&!1&2&3&4&5 | !0&1&!2&!3&!4 | !0&1&!2&3&4&5 | 0&!1&!2&!3&!4
               | 0&!1&!2&3&4&5] 4
[!0&!1&2&!3&4] 5
[!0&!1&2&3&!4&!5] 6
[!0&!1&2&3&!4&5] 11
[!0&!1&2&3&4&!5 | !0&1&!2&3&4&!5 | 0&!1&!2&3&4&!5] 10
State: 7
[!0&!1&2&3&!4&5] 2
[!0&!1&2&!3&!4 | !0&1&!2&!3&!4 | 0&!1&!2&!3&!4] 4
[!0&!1&2&!3&4&!5] 5
[!0&!1&2&!3&4&5] 7
[!0&!1&2&3&4&!5 | !0&1&!2&3&4&!5 | 0&!1&!2&3&4&!5] 9
[!0&!1&2&3&!4&!5] 11
[!0&!1&2&3&4&5 | !0&1&!2&3&4&5 | 0&!1&!2&3&4&5] 12
State: 8
[!0&!1&2&!3&!4 | !0&!1&2&3&4 | !0&1&!2&!3&!4 | !0&1&!2&3&4 | 0&!1&!2&!3&!4
               | 0&!1&!2&3&4] 4
[!0&!1&2&3&!4&5] 11
[!0&!1&2&!3&4&5] 13
[!0&!1&2&!3&4&!5] 14
[!0&1&!2&3&!4&!5] 15
State: 9
[!0&!1&2&!4 | !0&1&!2&!4 | 0&!1&!2&!4] 4
[!0&!1&2&4 | !0&1&!2&4 | 0&!1&!2&4] 9
State: 10
[!0&!1&2&!3&!4 | !0&!1&2&3&5 | !0&1&!2&!3&!4 | !0&1&!2&3&5 | 0&!1&!2&!3&!4
               | 0&!1&!2&3&5] 4
[!0&!1&2&!3&4 | !0&1&!2&!3&4 | 0&!1&!2&!3&4] 9
[!0&!1&2&3&!5 | !0&1&!2&3&!5 | 0&!1&!2&3&!5] 10
State: 11
[!0&!1&2&!3&!4 | !0&!1&2&3&4 | !0&1&!2&!3&!4 | !0&1&!2&3&4 | 0&!1&!2&!3&!4
               | 0&!1&!2&3&4] 4
[!0&!1&2&!3&4] 5
[!0&!1&2&3&!4&!5] 6
[!0&!1&2&3&!4&5] 11
State: 12
[!0&!1&2&!4 | !0&1&!2&!4 | 0&!1&!2&!4] 4
[!0&!1&2&4&!5 | !0&1&!2&4&!5 | 0&!1&!2&4&!5] 9
[!0&!1&2&4&5 | !0&1&!2&4&5 | 0&!1&!2&4&5] 12
State: 13
[!0&!1&2&!3&!4 | !0&1&!2&!3&!4 | 0&!1&!2&!3&!4] 4
[!0&!1&2&!3&4&!5] 5
[!0&!1&2&3&4&!5 | !0&1&!2&3&4&!5 | 0&!1&!2&3&4&!5] 9
[!0&!1&2&3&!4] 11
[!0&!1&2&3&4&5 | !0&1&!2&3&4&5 | 0&!1&!2&3&4&5] 12
[!0&!1&2&!3&4&5] 13
State: 14
[!0&!1&2&3&!4&5] 2
[!0&!1&2&!3&!4 | !0&1&!2&!3&!4 | 0&!1&!2&!3&!4] 4
[!0&!1&2&!3&4&!5] 5
[!0&!1&2&!3&4&5] 7
[!0&!1&2&3&4 | !0&1&!2&3&4 | 0&!1&!2&3&4] 9
[!0&!1&2&3&!4&!5] 11
State: 15
[!0&!1&2&!3&!4 | !0&!1&2&3&4&5 | !0&1&!2&!3&!4 | !0&1&!2&3&4&5 | 0&!1&!2&!3&!4
               | 0&!1&!2&3&4&5] 4
[!0&!1&2&!3&4&5] 5
[!0&!1&2&3&!4&5] 11
[!0&!1&2&!3&4&!5] 14
[!0&1&!2&3&!4&!5] 15
[!0&!1&2&3&4&!5 | !0&1&!2&3&4&!5 | 0&!1&!2&3&4&!5] 16
State: 16
[!0&!1&2&!3&!4 | !0&!1&2&3&5 | !0&1&!2&!3&!4 | !0&1&!2&3&5 | 0&!1&!2&!3&!4
               | 0&!1&!2&3&5] 4
[!0&!1&2&!3&4 | !0&1&!2&!3&4 | 0&!1&!2&!3&4] 9
[!0&!1&2&3&!5 | !0&1&!2&3&!5 | 0&!1&!2&3&!5] 16
--END--""")

# Build an equivalent deterministic monitor
min_equiv = spot.minimize_mealy_fast(aut, False)
assert min_equiv.num_states() == 6
assert spot.are_equivalent(min_equiv, aut)

# Build an automaton that recognizes a subset of the language of the original
# automaton
min_sub = spot.minimize_mealy_fast(aut, True)
assert min_sub.num_states() == 5
prod = spot.product(spot.complement(aut), min_sub)
assert spot.generic_emptiness_check(prod)

aut = spot.automaton("""
HOA: v1
States: 4
Start: 0
AP: 2 "a" "b"
acc-name: all
Acceptance: 0 t
properties: trans-labels explicit-labels state-acc deterministic
--BODY--
State: 0
[!0&!1] 1
[!0&1] 2
[0] 3
State: 1
[0] 1
State: 2
[1] 2
State: 3
[0&1] 3
--END--
""")

exp = """HOA: v1
States: 1
Start: 0
AP: 2 "a" "b"
acc-name: all
Acceptance: 0 t
properties: trans-labels explicit-labels state-acc deterministic
--BODY--
State: 0
[0&1] 0
--END--"""

# An example that shows that we should not build a tree when we use inclusion.
res = spot.minimize_mealy_fast(aut, True)
assert res.to_str() == exp

aut = spot.automaton("""
HOA: v1
States: 4
Start: 0
AP: 2 "a" "b"
acc-name: all
Acceptance: 0 t
properties: trans-labels explicit-labels state-acc
--BODY--
State: 0
[!0&!1] 1
[!0&1] 2
[0&!1] 3
State: 1
[0] 1
State: 2
[1] 2
State: 3
[0&1] 3
--END--
""")

exp = """HOA: v1
States: 2
Start: 0
AP: 2 "a" "b"
acc-name: all
Acceptance: 0 t
properties: trans-labels explicit-labels state-acc deterministic
--BODY--
State: 0
[!0&!1] 1
[!0&1] 1
[0&!1] 1
State: 1
[0&1] 1
--END--"""

res = spot.minimize_mealy_fast(aut, True)
assert res.to_str() == exp
