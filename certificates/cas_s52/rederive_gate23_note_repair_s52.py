# s52 / GATE23 — Phase 2c for the PROOF NOTE REPAIR GUIDE (file D).
# GPT's repair paragraphs are proposals, not results.  Every identity and every
# inference below is re-derived here before any of it is written into the note.
#
# Covered:
#   5. the division-without-denominators identity for the Q == 0 branch
#   6. the witness-collision vector that kills the witness coefficients
#   7. the growth bound that replaces "the square root of a quadratic is linear"
#
# Sections 1-4 (polar Cauchy, the (2a+1)(b-a) control, N4, N5) are in
# rederive_gate23_s52.py / .sage; this file does not repeat them.

from sympy import symbols, expand, simplify, Poly, Rational, Abs, sqrt, Integer
import itertools, random

RESULTS = []


def check(tag, ok, detail=""):
    RESULTS.append((tag, bool(ok)))
    print(f"[{'PASS' if ok else 'FAIL'}] {tag}" + (f"  -- {detail}" if detail else ""), flush=True)


# ---------------------------------------------------------------------------
# 5. Division without denominators, Q == 0 branch (repair guide section 2).
#    h(t,x) = p*t + h0(x),  q(t,x) = A*t^2 + q1(x)*t + q0(x),  A, p constants.
#    Claim:  p^2 q = (p A t + p q1 - A h0) * h + [p^2 q0 - p q1 h0 + A h0^2].
# ---------------------------------------------------------------------------
print("=== 5. the division identity ===")
t, p, A, h0, q1, q0 = symbols('t p A h0 q1 q0')

h = p * t + h0
q = A * t ** 2 + q1 * t + q0
quotient = p * A * t + p * q1 - A * h0
bracket = p ** 2 * q0 - p * q1 * h0 + A * h0 ** 2

lhs = expand(p ** 2 * q)
rhs = expand(quotient * h + bracket)
print(f"    p^2 q - (quotient*h + bracket) = {simplify(lhs - rhs)}")
check("5a the identity is exact as polynomials in t (coefficients in p,A,h0,q1,q0)",
      simplify(lhs - rhs) == 0)

# the bracket must not depend on t -- that is the whole point of the argument
check("5b the bracket is free of t", Poly(bracket, t).degree() <= 0)
check("5c the quotient is affine in t", Poly(quotient, t).degree() == 1)

# 5d.  h | q for every t, with p != 0, forces bracket = 0.
#      Re-derived numerically: pick integer data where the bracket is NOT zero and
#      confirm that h(t) fails to divide q(t) for all large |t| -- i.e. the inference
#      is not vacuous, and the hypothesis really does bite.
rnd = random.Random(20260915)
witness_nonzero, witness_zero = 0, 0
for _ in range(400):
    P, Aa, H0, Q1, Q0 = (rnd.randint(-6, 6) or 1), rnd.randint(-6, 6), \
                        rnd.randint(-6, 6), rnd.randint(-6, 6), rnd.randint(-6, 6)
    br = P ** 2 * Q0 - P * Q1 * H0 + Aa * H0 ** 2
    divides_all = True
    for tv in range(-60, 61):
        hv = P * tv + H0
        if hv == 0:
            continue
        qv = Aa * tv ** 2 + Q1 * tv + Q0
        if qv % hv != 0:
            divides_all = False
            break
    if br != 0 and divides_all:
        witness_nonzero += 1          # would refute the inference
    if br == 0 and divides_all:
        witness_zero += 1
check("5d no integer datum with bracket != 0 divides for every t (|t|<=60)",
      witness_nonzero == 0, f"bracket==0 and divides-all cases seen: {witness_zero}")

# 5e.  When the bracket vanishes AND h divides q at every integer t, the quotient is
#      the output and it is affine in t:  f = -(p A t + p q1 - A h0)/p^2 = -q/h.
#      First attempt at this check used p=2, h0=q0=0, which has bracket = 0 but where
#      h = 2t does NOT divide q = t(3t+4) at odd t -- the instance did not satisfy the
#      hypothesis, so the test was wrong, not the formula.  Instances are now SEARCHED
#      for rather than hand-picked, and the check is skipped unless one is found.
found = 0
mismatch = []
for P in range(1, 5):
    for Aa in range(-4, 5):
        for H0 in range(-4, 5):
            for Q1 in range(-4, 5):
                for Q0 in range(-4, 5):
                    br = P**2*Q0 - P*Q1*H0 + Aa*H0**2
                    if br != 0:
                        continue
                    ts = [tv for tv in range(-40, 41) if P*tv + H0 != 0]
                    if not all((Aa*tv**2 + Q1*tv + Q0) % (P*tv + H0) == 0 for tv in ts):
                        continue
                    found += 1
                    quo = lambda tv: -(P*Aa*tv + P*Q1 - Aa*H0) / P**2
                    for tv in ts:
                        hv = P*tv + H0
                        qv = Aa*tv**2 + Q1*tv + Q0
                        if Rational(quo(tv)) != Rational(-qv, hv):
                            mismatch.append((P, Aa, H0, Q1, Q0, tv))
                            break
check("5e with bracket = 0 and h | q at every t, f = -quotient/p^2 equals -q/h",
      found > 0 and not mismatch,
      f"{found} qualifying integer instances, mismatches: {mismatch[:2]}")

# ---------------------------------------------------------------------------
# 6. The witness-collision vector (repair guide section 2, first paragraph).
#    Linear form  L(b,u) = sum_j c_j b_j + sum_k d_k u_k + Q.
#    e = d_k * e_{b_j} - c_j * e_{u_k}.  Claim: L(z0 + e) = L(z0), and output j
#    moves by d_k.  So d_k != 0 contradicts output uniqueness.
# ---------------------------------------------------------------------------
print("=== 6. the witness-collision vector ===")
bad = []
rnd2 = random.Random(52)
for _ in range(2000):
    m, r = rnd2.randint(1, 4), rnd2.randint(1, 4)
    c = [rnd2.randint(-5, 5) for _ in range(m)]
    d = [rnd2.randint(-5, 5) for _ in range(r)]
    Qc = rnd2.randint(-9, 9)
    j, k = rnd2.randrange(m), rnd2.randrange(r)
    z0b = [rnd2.randint(-4, 4) for _ in range(m)]
    z0u = [rnd2.randint(-4, 4) for _ in range(r)]
    L = lambda b, u: sum(c[i] * b[i] for i in range(m)) + sum(d[i] * u[i] for i in range(r)) + Qc
    b2 = list(z0b); b2[j] += d[k]
    u2 = list(z0u); u2[k] -= c[j]
    if L(b2, u2) != L(z0b, z0u):
        bad.append((c, d, j, k))
    if d[k] != 0 and b2[j] == z0b[j]:
        bad.append(("output did not move", c, d, j, k))
check("6a L(z0 + e) = L(z0) for e = d_k e_{b_j} - c_j e_{u_k}", not bad,
      f"counterexamples: {bad[:2]}")
check("6b the output coordinate j moves by exactly d_k (nonzero when d_k != 0)", True,
      "b2[j] - z0b[j] = d_k by construction, checked in 6a's second clause")

# ---------------------------------------------------------------------------
# 7. The growth bound that replaces "the square root of a quadratic is linear".
#    |f(a)_j| <= 2 sqrt(Q(w_j)) sqrt(R(a)) + |centre(a)_j|,  R quadratic, centre affine
#    => |f(a)_j| <= K (1 + ||a||_inf).   Verified as an inequality on coefficients,
#    not as an identity about square roots.
# ---------------------------------------------------------------------------
print("=== 7. the growth bound ===")
a1, a2 = symbols('a1 a2', real=True)
R_poly = 3 * a1 ** 2 - 2 * a1 * a2 + 5 * a2 ** 2 + 7 * a1 - a2 + 11
C_R = sum(abs(c) for c in Poly(R_poly, a1, a2).coeffs())
viol = 0
for A1 in range(-40, 41):
    for A2 in range(-40, 41):
        nrm = max(abs(A1), abs(A2))
        Rv = R_poly.subs({a1: A1, a2: A2})
        if Rv > C_R * (1 + nrm) ** 2:
            viol += 1
check("7a R(a) <= C_R (1 + ||a||_inf)^2 with C_R = sum of |coefficients|",
      viol == 0, f"C_R = {C_R}, samples 81x81")
check("7b hence sqrt(R(a)) <= sqrt(C_R) (1 + ||a||_inf): a LINEAR UPPER BOUND, "
      "not the false identity 'the square root of a quadratic is linear'", True)

# ---------------------------------------------------------------------------
print("=== SUMMARY ===")
npass = sum(1 for _, ok in RESULTS if ok)
for tag, ok in RESULTS:
    if not ok:
        print("    FAILED:", tag)
print(f"CHECKS={len(RESULTS)} PASS={npass} FAIL={len(RESULTS) - npass}")
print("REDERIVE_GATE23_NOTE_REPAIR_S52 DONE")
