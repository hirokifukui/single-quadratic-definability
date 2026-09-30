#!/usr/bin/env python3
"""least_certificate_prime.py — s55 own initiative, round 3, item 8.

How large must the certificate prime of Lemma A.3 be?  For a non-total tuple (discriminant condition
failing) the proof needs a prime p, p not dividing 2 A D delta, with (-D/p) = -1 and (delta/p) = +1; the
integer t then exists below 2p.  Under GRH, Chebotarev-type bounds (Lagarias-Odlyzko, Bach, Bach-Sorenson)
put the least such prime below c (log M)^2 for M ~ |D delta| (the biquadratic field Q(sqrt(-D), sqrt(delta))
has discriminant dividing a power of 2 D delta), so the certificate SEARCH is polynomial in the input length.
This script only MEASURES the least prime; no bound is proved here.

Sample: 60 000 random tuples A, B, C in [-10^6, 10^6], D in [1, 10^4], restricted to the non-total side.
Reported: the maximum of p / (log M)^2 with M = 4 |A D delta|, the largest p seen, and a histogram.
"""
import random, math, sys

def is_prime(n):
    if n < 2: return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for q in small:
        if n % q == 0: return n == q
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in small[:7]:
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True

def leg(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p - 1) // 2, p) == 1 else -1)

def isq(x):
    if x < 0: return False
    r = math.isqrt(x); return r * r == x

random.seed(8)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 60000
worst = (0.0, None); pmax = (0, None); hist = {}
done = 0
while done < N:
    A = random.randint(-10**6, 10**6)
    if A == 0: continue
    B = random.randint(-10**6, 10**6); C = random.randint(-10**6, 10**6)
    D = random.randint(1, 10**4)
    delta = B * B - 4 * A * C
    if delta == 0 or isq(-delta * D): continue
    bad = 2 * A * D * delta
    p = 3
    while True:
        if is_prime(p) and bad % p and leg(-D, p) == -1 and leg(delta, p) == 1: break
        p += 2
    M = 4 * abs(A * D * delta)
    ratio = p / math.log(M) ** 2
    if ratio > worst[0]: worst = (ratio, (A, B, C, D, p))
    if p > pmax[0]: pmax = (p, (A, B, C, D))
    b = 1 << (p.bit_length() - 1)
    hist[b] = hist.get(b, 0) + 1
    done += 1
print(f"TUPLES={N}")
print(f"MAX_RATIO_p_over_log2M={worst[0]:.4f} at {worst[1]}")
print(f"LARGEST_p={pmax[0]} at {pmax[1]}")
print("HISTOGRAM_p_by_power_of_two=" + str(dict(sorted(hist.items()))))
print("LEAST_PRIME_DONE")
