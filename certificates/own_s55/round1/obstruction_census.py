#!/usr/bin/env python3
"""obstruction_census.py — s55 (own initiative).  A finite map of the open case left by D2.

Family (n = m = 1, r = 2, positive definite, polar rank 3, diagonal):
    P(a,b,u,v) = d1 (s1 b - p1 a - q1)^2 + d2 (s2 u - p2 a - q2)^2 + d3 (s3 v - p3 a - q3)^2 - R(a),
    R(a) = e2 a^2 + e1 a + e0,   centre c(a) = ((p1 a+q1)/s1, (p2 a+q2)/s2, (p3 a+q3)/s3),  residual R(a).
Obstruction case of D2: R NOT constant and 2c(a) integral for NO integer a.
For each sampled datum in that case we test, on |a| <= 25 only (a FINITE check, not a proof):
    TOTAL_OU   every a has solutions and all of them share one output b;
and for the TOTAL_OU data:
    CERT       the output flip T = diag(-1,1,1) passes the D4 certificate on some coset
               ((I - T)c(rho) = (2c_b(rho),0,0) integral; M = s1 makes M(I - T)C integral; A = -1/2),
               so symmetry_certificate_NF gives f = c_b on that coset -- and we check f = c_b numerically there;
    AFFINE     f is affine on some coset rho + M Z (M <= 6) on the range.
Planted control: a datum outside the obstruction case (constant residual) must be classified as such.
Totality is built in (R(a) = Q(z(a) - c(a)) for an integer affine z); deterministic sampling (seeded).
"""
import random, sys
from fractions import Fraction as F
from math import isqrt, gcd

A0 = 25
AS = sorted(range(-A0, A0 + 1), key=lambda a: (abs(a), a))

def outputs_at(prm, a):
    d1, d2, d3, s1, s2, s3, p1, p2, p3, q1, q2, q3, e2, e1, e0 = prm
    R = e2 * a * a + e1 * a + e0
    if R < 0: return None
    bs = set()
    t1 = p1 * a + q1; t2 = p2 * a + q2; t3 = p3 * a + q3
    X1 = isqrt(R // d1) if d1 else 0
    for x1 in range(-X1, X1 + 1):
        if (x1 + t1) % s1: continue
        r1 = R - d1 * x1 * x1
        X2 = isqrt(r1 // d2)
        for x2 in range(-X2, X2 + 1):
            if (x2 + t2) % s2: continue
            r2 = r1 - d2 * x2 * x2
            if r2 % d3: continue
            y = r2 // d3
            x3 = isqrt(y)
            if x3 * x3 != y: continue
            if (x3 + t3) % s3 == 0 or (-x3 + t3) % s3 == 0:
                bs.add((x1 + t1) // s1)
                break
    return bs

def reflectable(prm):
    d1, d2, d3, s1, s2, s3, p1, p2, p3, q1, q2, q3, *_ = prm
    L = s1 * s2 * s3
    return any(all((2 * (p * a + q)) % s == 0 for p, q, s in ((p1, q1, s1), (p2, q2, s2), (p3, q3, s3)))
               for a in range(L))

def classify(prm):
    e2, e1 = prm[12], prm[13]
    if e2 == 0 and e1 == 0: return 'constant_residual'
    if reflectable(prm): return 'reflectable'
    return 'obstruction'

def total_ou(prm):
    f = {}
    for a in AS:
        bs = outputs_at(prm, a)
        if not bs or len(bs) != 1: return None
        f[a] = next(iter(bs))
    return f

def cert_and_check(prm, f):
    s1, p1, q1 = prm[3], prm[6], prm[9]
    for rho in range(s1):
        if (2 * (p1 * rho + q1)) % s1 == 0:
            ok = all(F(f[a]) == F(p1 * a + q1, s1) for a in f if (a - rho) % s1 == 0)
            return True, ok
    return False, None

def affine_coset(f):
    for M in range(1, 7):
        for rho in range(M):
            pts = sorted(a for a in f if (a - rho) % M == 0)
            if len(pts) < 3: continue
            d = f[pts[1]] - f[pts[0]]
            if all(f[pts[i + 1]] - f[pts[i]] == d for i in range(len(pts) - 1)): return M
    return None

random.seed(20260917)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
stats = {'constant_residual': 0, 'reflectable': 0, 'obstruction': 0}
hits = []
seen = set()
for _ in range(N):
    # totality BY CONSTRUCTION: pick integer affine z_i(a) = al_i a + be_i and set R(a) = sum d_i X_i(a)^2,
    # X_i(a) = s_i z_i(a) - p_i a - q_i; output-uniqueness is what the range test decides.
    s = [random.choice((1, 2, 3)) for _ in range(3)]
    d = (random.choice((1, 2, 3)), random.choice((1, 2)), random.choice((1, 2)))
    pp = [random.randint(-2, 2) for _ in range(3)]
    qq = [random.randrange(si) for si in s]
    al = [random.randint(-2, 2) for _ in range(3)]
    be = [random.randint(-2, 2) for _ in range(3)]
    e2 = e1 = e0 = 0
    for i in range(3):
        k1 = s[i] * al[i] - pp[i]; k0 = s[i] * be[i] - qq[i]
        e2 += d[i] * k1 * k1; e1 += 2 * d[i] * k1 * k0; e0 += d[i] * k0 * k0
    prm = (*d, *s, *pp, *qq, e2, e1, e0)
    cls = classify(prm)
    stats[cls] += 1
    if cls != 'obstruction' or prm in seen: continue
    seen.add(prm)
    f = total_ou(prm)
    if f is None: continue
    has_cert, cert_ok = cert_and_check(prm, f)
    hits.append((prm, has_cert, cert_ok, affine_coset(f)))

plant = (1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1)   # b^2+u^2+v^2 = 1: constant residual
plant_ok = classify(plant) == 'constant_residual'

print("SAMPLED=%d %s" % (N, " ".join(f"{k}={v}" for k, v in stats.items())))
print("OBSTRUCTION_DISTINCT=%d TOTAL_OU_ON_RANGE=%d" % (len(seen), len(hits)))
with_cert = [h for h in hits if h[1]]
print("WITH_OUTPUT_FLIP_CERT=%d CERT_PREDICTION_HELD=%d" % (len(with_cert), sum(1 for h in with_cert if h[2])))
no_cert = [h for h in hits if not h[1]]
print("WITHOUT_CERT=%d  of which AFFINE_ON_SOME_COSET=%d" % (len(no_cert), sum(1 for h in no_cert if h[3])))
print("PLANT_CONSTANT_RESIDUAL_CLASSIFIED=%s" % plant_ok)
names = "d1 d2 d3 s1 s2 s3 p1 p2 p3 q1 q2 q3 e2 e1 e0".split()
with open('obstruction_census_hits.tsv', 'w') as fh:
    fh.write("\t".join(names + ['cert', 'cert_prediction_held', 'affine_M']) + "\n")
    for prm, hc, ok, M in hits:
        fh.write("\t".join(map(str, list(prm) + [hc, ok, M])) + "\n")
for prm, hc, ok, M in (no_cert[:5] + with_cert[:5]):
    print("EXAMPLE", dict(zip(names, prm)), "cert=", hc, "held=", ok, "affine_M=", M)
bad = sum(1 for h in with_cert if not h[2])
print("CENSUS_EXIT=%d" % (0 if plant_ok and bad == 0 else 1))
