#!/usr/bin/env python3
"""general_pd_census.py — s55 own initiative, round 2, item 2.

Robustness of the s55 conjecture (positive definite, polar rank k >= 2, total and output-unique  =>
constant residual) beyond diagonal forms.

Data: S = B^T B + I with B a random k x k matrix in {-1,0,1} (positive definite, generic cross terms);
centre c(a) = (e0 + E a) / Dn with Dn in {1,2,3}; an integer affine z(a) = alpha a + beta is chosen and the
residual is DEFINED by R(a) = Q(z(a) - c(a)), so the graph is total by construction.  In the scaled variable
y = Dn z - e0 - E a (an integer vector with y = -(e0 + E a) mod Dn) the fibre at a is
    { y : y^T S y = N(a),  y = -(e0 + E a) mod Dn },   N(a) = Dn^2 R(a),
and the output is the first m coordinates of z = (y + e0 + E a) / Dn.
Classes: CONST (alpha = E / Dn exactly, so N is constant) and NONCONST.
For each datum we scan a in 0, 1, -1, 2, -2, ... (|a| <= AMAX) and stop at the first input with two
distinct outputs.  Reported: TOTAL_OU (no such input found) per (k, m, class), and the distribution of the
first failing |a|.  CONST is the positive control (output-unique graphs exist there).
"""
import random, sys
from math import isqrt
from fractions import Fraction as F

def rand_S(k):
    B = [[random.choice((-1, 0, 1)) for _ in range(k)] for _ in range(k)]
    return [[sum(B[r][i] * B[r][j] for r in range(k)) + (1 if i == j else 0) for j in range(k)] for i in range(k)]

def inv_diag(S):
    k = len(S)
    M = [[F(S[i][j]) for j in range(k)] + [F(1 if i == j else 0) for j in range(k)] for i in range(k)]
    for c in range(k):
        piv = next(r for r in range(c, k) if M[r][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for r in range(k):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][k + i] for i in range(k)]

def fibre_outputs(S, idiag, N, res, Dn, shift, m, stop_at=2):
    """distinct output tuples; stops early once stop_at distinct outputs are found"""
    k = len(S)
    bounds = [isqrt(int(idiag[i] * N)) + 1 for i in range(k)]
    outs = set()
    def rec(i, y):
        if len(outs) >= stop_at: return
        if i == k - 1:
            # S_kk x^2 + 2 x L + Q0 = N
            L = sum(S[k - 1][j] * y[j] for j in range(k - 1))
            Q0 = sum(S[p][q] * y[p] * y[q] for p in range(k - 1) for q in range(k - 1))
            a2 = S[k - 1][k - 1]
            disc = L * L - a2 * (Q0 - N)
            if disc < 0: return
            sd = isqrt(disc)
            if sd * sd != disc: return
            for num in (-L + sd, -L - sd):
                if num % a2: continue
                x = num // a2
                if (x - res[k - 1]) % Dn: continue
                yy = y + [x]
                outs.add(tuple((yy[j] + shift[j]) // Dn for j in range(m)))
            return
        for v in range(-bounds[i], bounds[i] + 1):
            if (v - res[i]) % Dn: continue
            rec(i + 1, y + [v])
            if len(outs) >= stop_at: return
    rec(0, [])
    return outs

def run(k, m, cls, n, amax):
    tot_ou = 0; first_fail = {}
    for _ in range(n):
        S = rand_S(k); idiag = inv_diag(S)
        Dn = random.choice((1, 2, 3))
        E = [random.randint(-2, 2) for _ in range(k)]
        e0 = [random.randrange(Dn) for _ in range(k)]
        if cls == 'CONST':
            E = [Dn * random.randint(-1, 1) for _ in range(k)]
            alpha = [E[i] // Dn for i in range(k)]
        else:
            while True:
                alpha = [random.randint(-1, 1) for _ in range(k)]
                if any(Dn * alpha[i] - E[i] for i in range(k)): break
        beta = [random.randint(-1, 1) for _ in range(k)]
        ok = True
        for a in sorted(range(-amax, amax + 1), key=lambda x: (abs(x), x)):
            shift = [e0[i] + E[i] * a for i in range(k)]
            y0 = [Dn * (alpha[i] * a + beta[i]) - shift[i] for i in range(k)]
            N = sum(S[p][q] * y0[p] * y0[q] for p in range(k) for q in range(k))
            res = [(-shift[i]) % Dn for i in range(k)]
            outs = fibre_outputs(S, idiag, N, res, Dn, shift, m)
            assert outs, "totality is built in: empty fibre is a bug"
            if len(outs) > 1:
                ok = False; first_fail[abs(a)] = first_fail.get(abs(a), 0) + 1; break
        if ok: tot_ou += 1
    return tot_ou, first_fail

random.seed(20260917)
plan = [(3, 1, 200, 12), (3, 2, 200, 12), (4, 1, 80, 6), (4, 2, 80, 6), (4, 3, 80, 6)]
for k, m, n, amax in plan:
    for cls in ('CONST', 'NONCONST'):
        t, ff = run(k, m, cls, n, amax)
        print(f"RANK={k} OUTPUTS={m} CLASS={cls:8s} SAMPLED={n} ABS_A_MAX={amax} TOTAL_OU={t} "
              f"FIRST_FAIL_ABS_A={dict(sorted(ff.items()))}", flush=True)
print("GENERAL_CENSUS_DONE", flush=True)
