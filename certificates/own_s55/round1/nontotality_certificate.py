#!/usr/bin/env python3
"""nontotality_certificate.py — s55 (own initiative).  Executable form of the proof of Lemma A.3.

For integers A != 0, B, C, D > 0 with delta = B^2 - 4AC != 0 and delta != -D h^2 (h rational), Lemma A.3
says that P(t) = A t^2 + B t + C is NOT a value of X^2 + D Y^2 (X, Y rational) at some integer t.
This tool produces the witness the proof constructs:

    a prime p with p | 2 A D delta false, (-D / p) = -1, (delta / p) = +1, and an integer t with v_p(P(t)) = 1.

CHECK (independent of the search): p prime, p does not divide D, (-D/p) = -1 by Euler's criterion, and
v_p(P(t)) = 1.  Then P(t) is not a rational value of X^2 + D Y^2: such a value has even p-adic valuation
when -D is a non-residue mod p and p does not divide D.

Batch: every (A, B, C, D) with A in [-6,6]\\{0}, B, C in [-6,6], D in {1,2,3,5,6,7,10,11}.
Planted controls: a certificate with the residue condition broken, and one with v_p = 2, must be rejected.
Exit 0 iff every eligible tuple gets a certificate that CHECK accepts and both plants are rejected.
"""
import sys
from fractions import Fraction
from math import isqrt

def is_prime(n):
    if n < 2: return False
    for q in (2, 3, 5, 7, 11, 13):
        if n % q == 0: return n == q
    i = 17
    while i * i <= n:
        if n % i == 0: return False
        i += 2
    return True

def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

def vp(n, p):
    if n == 0: return 10 ** 9
    k = 0
    while n % p == 0: n //= p; k += 1
    return k

def is_minus_D_times_square(delta, D):
    # delta = -D h^2 with h rational  <=>  -delta*D is a perfect square (of an integer), since D is an integer
    x = -delta * D
    return x >= 0 and isqrt(x) ** 2 == x

def P(A, B, C, t): return A * t * t + B * t + C

def find(A, B, C, D, pmax=5000):
    delta = B * B - 4 * A * C
    for p in range(3, pmax, 2):
        if not is_prime(p) or (2 * A * D * delta) % p == 0: continue
        if legendre(-D, p) != -1 or legendre(delta, p) != 1: continue
        for t0 in range(p):
            if P(A, B, C, t0) % p == 0:
                for t in (t0, t0 + p):
                    if vp(P(A, B, C, t), p) == 1: return p, t
    return None

def check(A, B, C, D, p, t):
    return is_prime(p) and D % p != 0 and legendre(-D, p) == -1 and vp(P(A, B, C, t), p) == 1

eligible = found = rejected_ok = 0
fails = []
out = []
R = range(-6, 7)
for D in (1, 2, 3, 5, 6, 7, 10, 11):
    for A in R:
        if A == 0: continue
        for B in R:
            for C in R:
                delta = B * B - 4 * A * C
                if delta == 0 or is_minus_D_times_square(delta, D): continue
                eligible += 1
                c = find(A, B, C, D)
                if c and check(A, B, C, D, *c):
                    found += 1
                    if len(out) < 400: out.append((A, B, C, D, c[0], c[1], P(A, B, C, c[1])))
                else:
                    fails.append((A, B, C, D, c))
# planted controls
A, B, C, D = 1, 0, -2, 1          # delta = 8, not -h^2
p, t = find(A, B, C, D)
plant1 = check(A, B, C, D, p + 0, t) and not check(A, B, C, D, 5, t)   # p = 5: (-1/5) = +1, must be rejected
plant2 = not check(1, 0, -49, 3, 7, 0)                                  # P(0) = -49: v_7 = 2, must be rejected
print(f"ELIGIBLE={eligible} CERTIFIED={found} FAILED={len(fails)}")
print(f"PLANT_WRONG_RESIDUE_REJECTED={plant1} PLANT_VALUATION_TWO_REJECTED={plant2}")
with open('nontotality_certificates_sample.tsv', 'w') as fh:
    fh.write("A\tB\tC\tD\tp\tt\tP(t)\n")
    for row in out: fh.write("\t".join(map(str, row)) + "\n")
print("SAMPLE_ROWS=%d" % len(out))
ok = (found == eligible and not fails and plant1 and plant2)
print("NONTOTALITY_CERT_EXIT=%d" % (0 if ok else 1))
sys.exit(0 if ok else 1)
