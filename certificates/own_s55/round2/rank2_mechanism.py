#!/usr/bin/env python3
"""rank2_mechanism.py — s55 own initiative, round 2, item 3.

The rank-2 half of the s55 conjecture says: the representations of R(a) by a binary form become
arbitrarily many as R(a) picks up split primes, while a fixed output leaves at most two points; so
output-uniqueness must fail even when every symmetry of the form is blocked by the lattice coset.

Test family: Q(x1, x2) = x1^2 + 2 x2^2  (Z[sqrt(-2)], class number 1), unknowns b, u with
    x1 = 3b - 1,  x2 = 3u - 1       (x1 = x2 = 2 mod 3),
so the centre is (1/3, 1/3): 2c is never integral, x1 -> -x1 and x2 -> -x2 leave the coset, and the form
has no other automorphisms.  The residual is chosen so that the graph is total:
    N(a) = X1(a)^2 + 2 X2(a)^2,  X1(a) = 3(al a + be) - 1,  X2(a) = 3(ga a + de) - 1.
For every a in [1, AMAX] we record the number of distinct outputs b and omega_split(a) = the number of
distinct primes p | N(a) with p = 1, 3 (mod 8) (the primes that split in Q(sqrt(-2))).
Prediction: distinct outputs are 1 exactly when omega_split is small, and grow like 2^(omega_split).
Reported: for each omega_split value, the number of inputs and the min / mean / max distinct outputs.
"""
import sys
from math import isqrt

def factor_primes(n):
    ps = []; d = 2
    while d * d <= n:
        if n % d == 0:
            ps.append(d)
            while n % d == 0: n //= d
        d += 1 if d == 2 else 2
    if n > 1: ps.append(n)
    return ps

def outputs(N):
    outs = set()
    X = isqrt(N)
    for x1 in range(-X, X + 1):
        if x1 % 3 != 2: continue
        r = N - x1 * x1
        if r % 2: continue
        y = r // 2; x2 = isqrt(y)
        if x2 * x2 != y: continue
        if x2 % 3 == 2 or (-x2) % 3 == 2:
            outs.add((x1 + 1) // 3)
    return outs

AMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 600
families = [(1, 0, 2, 0), (1, 1, 1, 0), (2, 0, 1, 1), (1, 0, 0, 1), (0, 1, 1, 0)]
table = {}
never_ou_family = 0
for al, be, ga, de in families:
    ou_everywhere = True
    for a in range(1, AMAX + 1):
        X1 = 3 * (al * a + be) - 1; X2 = 3 * (ga * a + de) - 1
        N = X1 * X1 + 2 * X2 * X2
        outs = outputs(N)
        assert outs, "totality is built in"
        w = sum(1 for p in factor_primes(N) if p % 8 in (1, 3))
        table.setdefault(w, []).append(len(outs))
        if len(outs) > 1: ou_everywhere = False
    never_ou_family += (not ou_everywhere)
print(f"FAMILIES={len(families)} INPUTS_PER_FAMILY={AMAX} FAMILIES_NOT_OUTPUT_UNIQUE={never_ou_family}")
for w in sorted(table):
    v = table[w]
    print(f"OMEGA_SPLIT={w} INPUTS={len(v)} DISTINCT_OUTPUTS min={min(v)} mean={sum(v)/len(v):.2f} max={max(v)} "
          f"SHARE_UNIQUE={sum(1 for x in v if x == 1)/len(v):.3f}")
print("RANK2_MECHANISM_DONE")
