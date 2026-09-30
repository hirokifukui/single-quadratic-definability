#!/usr/bin/env python3
"""rank3_growth_census.py — s55 (own initiative).  Does a non-constant residual kill output-uniqueness in
polar rank 3?  Heuristic being tested (NOT a theorem here):

  for a positive definite ternary form, the number of integer solutions of Q(z - c(a)) = R(a) grows like
  R(a)^(1/2 - eps) along suitable a (Siegel / Duke-Schulze-Pillot type lower bounds), while the solutions
  with a FIXED output coordinate are representations by a binary form, R(a)^eps many.  So a total graph with
  non-constant residual should have many outputs at some inputs: output-uniqueness fails, whether or not
  the doubled centre is ever integral.

Same diagonal family as obstruction_census.py, totality built in.  Three classes are sampled separately:
  CONST  (residual constant: every z_i(a) chosen so that X_i does not depend on a),
  REFL   (non-constant residual, 2c(a) integral for some a),
  OBSTR  (non-constant residual, 2c(a) integral for no a).
Reported per class: data sampled, TOTAL_OU on |a| <= 25, and for the rest the largest number of distinct
outputs seen at one input together with the |a| where it occurs.  Positive control: rank 1 (one output, no
witness), where output-unique graphs with non-constant residual exist (the reflected root can be non-integral);
the census must find them.  Rank 2 is reported as a second data point, not as a control.
"""
import random, sys
from math import isqrt
A0 = 25
AS = sorted(range(-A0, A0 + 1), key=lambda a: (abs(a), a))

def outs3(d, s, p, q, R, a):
    t = [p[i] * a + q[i] for i in range(3)]
    bs = set()
    X1 = isqrt(R // d[0])
    for x1 in range(-X1, X1 + 1):
        if (x1 + t[0]) % s[0]: continue
        r1 = R - d[0] * x1 * x1
        X2 = isqrt(r1 // d[1])
        for x2 in range(-X2, X2 + 1):
            if (x2 + t[1]) % s[1]: continue
            r2 = r1 - d[1] * x2 * x2
            if r2 % d[2]: continue
            y = r2 // d[2]; x3 = isqrt(y)
            if x3 * x3 == y and ((x3 + t[2]) % s[2] == 0 or (-x3 + t[2]) % s[2] == 0):
                bs.add((x1 + t[0]) // s[0]); break
    return bs

def outs2(d, s, p, q, R, a):
    t = [p[i] * a + q[i] for i in range(2)]
    bs = set()
    X1 = isqrt(R // d[0])
    for x1 in range(-X1, X1 + 1):
        if (x1 + t[0]) % s[0]: continue
        r1 = R - d[0] * x1 * x1
        if r1 % d[1]: continue
        y = r1 // d[1]; x2 = isqrt(y)
        if x2 * x2 == y and ((x2 + t[1]) % s[1] == 0 or (-x2 + t[1]) % s[1] == 0):
            bs.add((x1 + t[0]) // s[0])
    return bs

def outs1(d, s, p, q, R, a):
    t = [p[0] * a + q[0]]
    if R % d[0]: return set()
    y = R // d[0]; x = isqrt(y)
    if x * x != y: return set()
    return {(z + t[0]) // s[0] for z in (x, -x) if (z + t[0]) % s[0] == 0}

def sample(k, cls):
    while True:
        s = [random.choice((1, 2, 3)) for _ in range(k)]
        d = [random.choice((1, 2, 3))] + [random.choice((1, 2)) for _ in range(k - 1)]
        p = [random.randint(-2, 2) for _ in range(k)]
        q = [random.randrange(si) for si in s]
        if cls == 'CONST':
            # X_i(a) = s_i z_i(a) - p_i a - q_i independent of a needs s_i | p_i; take al_i = p_i / s_i
            if any(p[i] % s[i] for i in range(k)): continue
            al = [p[i] // s[i] for i in range(k)]
        else:
            al = [random.randint(-2, 2) for _ in range(k)]
        be = [random.randint(-2, 2) for _ in range(k)]
        k1 = [s[i] * al[i] - p[i] for i in range(k)]; k0 = [s[i] * be[i] - q[i] for i in range(k)]
        e = (sum(d[i] * k1[i] ** 2 for i in range(k)), sum(2 * d[i] * k1[i] * k0[i] for i in range(k)),
             sum(d[i] * k0[i] ** 2 for i in range(k)))
        const = e[0] == 0 and e[1] == 0
        L = 1
        for x in s: L *= x
        refl = any(all((2 * (p[i] * a + q[i])) % s[i] == 0 for i in range(k)) for a in range(L))
        got = 'CONST' if const else ('REFL' if refl else 'OBSTR')
        if got == cls: return d, s, p, q, e

def run(k, cls, n):
    outs = {3: outs3, 2: outs2, 1: outs1}[k]
    tot_ou = 0; worst = []
    for _ in range(n):
        d, s, p, q, e = sample(k, cls)
        best = (1, 0); ok = True
        for a in AS:
            R = e[0] * a * a + e[1] * a + e[2]
            bs = outs(d, s, p, q, R, a)
            assert bs, (d, s, p, q, e, a)          # totality is built in: an empty set is a bug
            if len(bs) > best[0]: best = (len(bs), abs(a))
            if len(bs) > 1: ok = False
        if ok: tot_ou += 1
        else: worst.append(best)
    mx = max(worst) if worst else (1, 0)
    return tot_ou, len(worst), mx

random.seed(917)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
for k, cls in ((3, 'CONST'), (3, 'REFL'), (3, 'OBSTR'), (2, 'CONST'), (2, 'REFL'), (2, 'OBSTR'), (1, 'REFL'), (1, 'OBSTR')):
    t, f, mx = run(k, cls, N)
    print(f"RANK={k} CLASS={cls:5s} SAMPLED={N} TOTAL_OU={t} NOT_OU={f} MAX_DISTINCT_OUTPUTS={mx[0]} AT_ABS_A={mx[1]}")
