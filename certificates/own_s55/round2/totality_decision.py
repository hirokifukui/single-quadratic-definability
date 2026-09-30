#!/usr/bin/env python3
"""totality_decision.py — s55 (own initiative, round 2).  A certifying decision procedure.

Question: for integers A != 0, B, C and D > 0, is P(t) = A t^2 + B t + C a rational value of X^2 + D Y^2
for EVERY integer t?

Criterion (proved below in the docstring, tested here):
    TOTAL  <=>  (delta = B^2 - 4AC is 0, or -delta*D is a perfect square)  and  A is a norm from Q(sqrt(-D)).

Proof.  (=>) Lemma A.3 gives the discriminant condition.  Then 4A P(t) = (2At+B)^2 + D h^2 with
h^2 = -delta/D, a norm; P(t) is a nonzero norm for all but at most two t, and nonzero norms form a group,
so 4A, hence A, is a norm.  (<=) If A = a0^2 + D b0^2, then
    r(t) = ((2At+B) a0 + D h b0) / (2A),   s(t) = (h a0 - (2At+B) b0) / (2A)
satisfy r^2 + D s^2 = ((2At+B)^2 + D h^2)(a0^2 + D b0^2) / (4A^2) = P(t)   (Brahmagupta).

Certificates produced:
    TOTAL      (a0, b0, h) and the affine section (r, s); the identity is checked with exact rationals at
               5 points (a degree-2 identity) -- plus symbolically once per run in sympy.
    NOT TOTAL  either a prime certificate (p, t) as in nontotality_certificate.py (discriminant fails), or
               a Hilbert-symbol certificate (A not a norm: a place v with (A, -D)_v = -1) together with an
               integer t where P(t) != 0 (then P(t) = norm / (4A) is not a norm).

Independent leg (nontotality_decision_sage.sage): Sage's own norm test in a number field on every
certificate row.
"""
import sys
from fractions import Fraction as F
from math import isqrt, gcd
import sympy as sp

def is_sq(x): return x >= 0 and isqrt(x) ** 2 == x

def vp(n, p):
    if n == 0: return 10 ** 9      # v_p(0) = infinity (a missing guard here hung the first run)
    k = 0
    while n % p == 0: n //= p; k += 1
    return k

def legendre(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p - 1) // 2, p) == 1 else -1)

def hilbert(a, b, p):
    """Hilbert symbol (a,b)_p for nonzero integers; p = -1 is the real place."""
    if p == -1: return -1 if (a < 0 and b < 0) else 1
    al, be = vp(a, p), vp(b, p)
    u, v = a // p ** al, b // p ** be
    if p != 2:
        e = (p - 1) // 2
        s = (-1) ** (al * be * e)
        return s * (legendre(u, p) ** be) * (legendre(v, p) ** al)
    eps = lambda x: ((x - 1) // 2) % 2
    om = lambda x: ((x * x - 1) // 8) % 2
    return (-1) ** ((eps(u) * eps(v) + al * om(v) + be * om(u)) % 2)

def primes_of(n):
    n = abs(n); ps = []; d = 2
    while d * d <= n:
        if n % d == 0:
            ps.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: ps.append(n)
    return ps

def is_norm(q, D):
    """q nonzero integer: norm from Q(sqrt(-D)) iff all Hilbert symbols (q,-D)_v = 1 (Hasse)."""
    places = set(primes_of(2 * q * D)) | {-1}
    for v in places:
        if hilbert(q, -D, v) == -1: return False, v
    return True, None

def find_rep(A, D, bound=60):
    # A z^2 = x^2 + D y^2 with z != 0, small search
    for z in range(1, bound):
        for y in range(0, bound):
            x2 = A * z * z - D * y * y
            if x2 < 0: break
            if is_sq(x2): return F(isqrt(x2), z), F(y, z)
    return None

def prime_cert(A, B, C, D, pmax=20000):
    delta = B * B - 4 * A * C
    for p in range(3, pmax, 2):
        if any(p % q == 0 for q in range(3, isqrt(p) + 1, 2)): continue
        if (2 * A * D * delta) % p == 0: continue
        if legendre(-D, p) != -1 or legendre(delta, p) != 1: continue
        for t0 in range(p):
            if (A * t0 * t0 + B * t0 + C) % p == 0:
                for t in (t0, t0 + p):
                    if vp(A * t * t + B * t + C, p) == 1: return p, t
    return None

def decide(A, B, C, D):
    delta = B * B - 4 * A * C
    if not (delta == 0 or is_sq(-delta * D)):
        c = prime_cert(A, B, C, D)
        return ('NOT', 'prime', c)
    ok, v = is_norm(A, D)
    if not ok:
        t = next(t for t in range(0, 3) if A * t * t + B * t + C != 0)
        return ('NOT', 'hilbert', (v, t))
    rep = find_rep(A, D)
    if rep is None: return ('TOTAL', 'unfound', None)
    a0, b0 = rep
    h = F(isqrt(-delta * D), D) if delta != 0 else F(0)   # h^2 = -delta/D
    return ('TOTAL', 'section', (a0, b0, h))

def check_section(A, B, C, D, a0, b0, h):
    for t in range(-2, 3):
        w = 2 * A * t + B
        r = (w * a0 + D * h * b0) / (2 * A); s = (h * a0 - w * b0) / (2 * A)
        if r * r + D * s * s != A * t * t + B * t + C: return False
    return True

# symbolic identity once
t_, A_, B_, D_, a0_, b0_ = sp.symbols('t A B D a0 b0')
h_ = sp.Symbol('h')
w_ = 2 * A_ * t_ + B_
r_ = (w_ * a0_ + D_ * h_ * b0_) / (2 * A_); s_ = (h_ * a0_ - w_ * b0_) / (2 * A_)
C_ = (B_ ** 2 + D_ * h_ ** 2) / (4 * A_)          # delta = -D h^2
Aeq = a0_ ** 2 + D_ * b0_ ** 2
sym = sp.expand(sp.numer(sp.together((r_ ** 2 + D_ * s_ ** 2 - (A_ * t_ ** 2 + B_ * t_ + C_)).subs(A_, Aeq)))) == 0
print("SYMBOLIC_SECTION_IDENTITY=%s" % sym, flush=True)

rows = []; counts = {}
bad = 0
for D in (1, 2, 3, 5, 6, 7):
    print('D', D, 'start', flush=True)
    for A in range(-5, 6):
        if A == 0: continue
        for B in range(-5, 6):
            for C in range(-5, 6):
                verdict, kind, cert = decide(A, B, C, D)
                counts[(verdict, kind)] = counts.get((verdict, kind), 0) + 1
                if kind == 'section' and not check_section(A, B, C, D, *cert): bad += 1
                if kind == 'prime' and cert is None: bad += 1
                if kind == 'unfound': bad += 1
                rows.append((A, B, C, D, verdict, kind, cert))
print("CASES=%d " % len(rows) + " ".join(f"{v}_{k}={n}" for (v, k), n in sorted(counts.items())))
print("CERTIFICATE_FAILURES=%d" % bad)
with open('totality_decision_rows.tsv', 'w') as fh:
    fh.write("A\tB\tC\tD\tverdict\tkind\tcert\n")
    for r in rows: fh.write("\t".join(map(str, r[:6])) + "\t" + repr(r[6]) + "\n")
print("TOTALITY_DECISION_EXIT=%d" % (0 if bad == 0 and sym else 1))
