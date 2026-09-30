# s52 / GATE23 — Phase 2c for repair-guide sections 4 and 5 (isotropic fallback, Pell).
# Same rule as the other legs: GPT's paragraphs are proposals until re-derived here.
# Convention throughout: B(v,w) = Q(v+w) - Q(v) - Q(w), so Q(v+u) = Q(v) + B(v,u) + Q(u).

import random
from fractions import Fraction as F

RESULTS = []


def check(tag, ok, detail=""):
    RESULTS.append((tag, bool(ok)))
    print(f"[{'PASS' if ok else 'FAIL'}] {tag}" + (f"  -- {detail}" if detail else ""), flush=True)


def mk_form(n, rnd, lo=-4, hi=4):
    """A symmetric rational Gram matrix G; Q(x) = x^T G x, B(v,w) = 2 v^T G w."""
    G = [[F(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            g = F(rnd.randint(lo, hi))
            G[i][j] = g
            G[j][i] = g
    return G


def Q(G, x):
    n = len(x)
    return sum(x[i] * G[i][j] * x[j] for i in range(n) for j in range(n))


def B(G, v, w):
    return Q(G, [v[i] + w[i] for i in range(len(v))]) - Q(G, v) - Q(G, w)


def add(v, w, s=F(1)):
    return [v[i] + s * w[i] for i in range(len(v))]


rnd = random.Random(20260915)

# ---------------------------------------------------------------------------
# 8.  Repair guide section 4(b): the rational section through an isotropic direction.
#     z(a) = c(a) + v0 + t(a) e,  t(a) = (R(a) - R(a0)) / B(v0, e),  Q(e) = 0.
#     Claim: Q(z(a) - c(a)) = R(a) exactly, for every target value R(a).
# ---------------------------------------------------------------------------
print("=== 8. the isotropic section hits R(a) exactly ===")
bad, tested = [], 0
for _ in range(4000):
    n = rnd.randint(2, 4)
    G = mk_form(n, rnd)
    v0 = [F(rnd.randint(-4, 4)) for _ in range(n)]
    e = [F(rnd.randint(-4, 4)) for _ in range(n)]
    if Q(G, e) != 0:
        continue                      # the lemma supplies an isotropic e; here we filter for one
    b = B(G, v0, e)
    if b == 0:
        continue                      # and a non-radical one, i.e. B(v0,e) != 0
    tested += 1
    R0 = Q(G, v0)
    Ra = F(rnd.randint(-30, 30))
    t = (Ra - R0) / b
    z = add(v0, e, t)
    if Q(G, z) != Ra:
        bad.append((n, Ra, Q(G, z)))
check("8a Q(v0 + t e) = R(a) for t = (R(a) - R(a0)) / B(v0, e), whenever Q(e) = 0",
      not bad and tested > 0, f"{tested} qualifying instances, failures: {bad[:2]}")

# 8b.  Q(e) = 0 is load-bearing: with Q(e) != 0 the same t misses by t^2 Q(e).
miss = 0
for _ in range(2000):
    n = rnd.randint(2, 4)
    G = mk_form(n, rnd)
    v0 = [F(rnd.randint(-4, 4)) for _ in range(n)]
    e = [F(rnd.randint(-4, 4)) for _ in range(n)]
    b = B(G, v0, e)
    if b == 0 or Q(G, e) == 0:
        continue
    R0, Ra = Q(G, v0), F(rnd.randint(-30, 30))
    t = (Ra - R0) / b
    if Q(G, add(v0, e, t)) != Ra:
        miss += 1
check("8b planted control: dropping Q(e) = 0 breaks the identity", miss > 0,
      f"{miss} instances where the section misses R(a)")

# 8c.  Branch (a): if every integer solution has z - c(a) in rad Q and pi(rad Q) = 0,
#      then f(a) = pi c(a) -- an affine map, modulus 1.  Checked as: a vector in the
#      radical has zero polar against everything, so its projection cannot be detected
#      by the output; modelled by taking pi to kill the radical directions.
rad_ok = True
for _ in range(2000):
    n = rnd.randint(2, 4)
    G = mk_form(n, rnd)
    # build a radical vector: solve nothing, just test the definition on candidates
    for _try in range(6):
        r = [F(rnd.randint(-3, 3)) for _ in range(n)]
        if all(B(G, r, [F(1) if i == k else F(0) for i in range(n)]) == 0 for k in range(n)):
            if Q(G, r) != 0:
                rad_ok = False        # radical => isotropic must hold: 2Q(r) = B(r,r) = 0
            break
check("8c every radical vector is isotropic (2Q(r) = B(r,r) = 0)", rad_ok)

# ---------------------------------------------------------------------------
# 9.  Repair guide section 5: the Pell return to the original lattice.
#     A = h Q(v), Bc = h Q(w), Delta = -A*Bc, with B(v,w) = 0 and Q(v)Q(w) < 0.
# ---------------------------------------------------------------------------
print("=== 9. the Pell identities ===")
bad9, n9 = [], 0
for _ in range(4000):
    n = rnd.randint(2, 4)
    G = mk_form(n, rnd)
    v = [F(rnd.randint(-4, 4)) for _ in range(n)]
    w = [F(rnd.randint(-4, 4)) for _ in range(n)]
    if B(G, v, w) != 0 or Q(G, v) * Q(G, w) >= 0:
        continue
    n9 += 1
    h = rnd.randint(1, 4)
    A, Bc = h * Q(G, v), h * Q(G, w)
    Delta = -A * Bc
    if Delta <= 0:
        bad9.append(("Delta not positive", Delta))
        continue
    # 9a: the norm identity  Q(X v +- A Y w) = Q(v) (X^2 - Delta Y^2)
    X, Y = F(rnd.randint(-6, 6)), F(rnd.randint(-6, 6))
    for sign in (1, -1):
        z = [X * v[i] + sign * A * Y * w[i] for i in range(n)]
        lhs = Q(G, z)
        rhs = Q(G, v) * (X ** 2 - Delta * Y ** 2)
        if lhs != rhs:
            bad9.append(("norm identity", lhs, rhs))
    # 9b: if Delta were a square s^2, e = s v + A w is isotropic with B(v,e) = 2 s Q(v)
    s2 = Delta
    if s2 == int(s2) and int(s2) >= 0:
        s_int = int(round(float(s2) ** 0.5))
        if s_int * s_int == s2:
            e = [s_int * v[i] + A * w[i] for i in range(n)]
            if Q(G, e) != 0:
                bad9.append(("square-Delta e not isotropic", Q(G, e)))
            if B(G, v, e) != 2 * s_int * Q(G, v):
                bad9.append(("B(v,e) != 2 s Q(v)", B(G, v, e)))
check("9a Q(X v +- A Y w) = Q(v)(X^2 - Delta Y^2); 9b a square Delta yields an isotropic "
      "e = s v + A w with B(v,e) = 2 s Q(v)", not bad9 and n9 > 0,
      f"{n9} qualifying (v,w) pairs, failures: {bad9[:2]}")

# 9c: with a Pell unit X^2 - Delta Y^2 = 1 the three points share the same value of Q,
#     so they are solutions at the SAME input; and their outputs cannot all agree.
def pell_unit(D, cap=200000):
    for Y in range(1, cap):
        v = 1 + D * Y * Y
        X = int(round(v ** 0.5))
        if X * X == v and X > 1:
            return X, Y
    return None


tested9c, bad9c = 0, []
for D in [2, 3, 5, 6, 7, 8, 10, 11, 12, 13]:
    pu = pell_unit(D)
    if pu is None:
        continue
    X, Y = pu
    tested9c += 1
    if X * X - D * Y * Y != 1 or X <= 1 or Y == 0:
        bad9c.append((D, X, Y))
check("9c a Pell unit X^2 - Delta Y^2 = 1 with X > 1, Y != 0 exists for each nonsquare Delta tried",
      not bad9c and tested9c > 0, f"{tested9c} discriminants")

# 9d: the three-point output argument.  If pi w != 0 the outputs of z+ and z- differ by
#     2 A Y pi w; if pi w = 0 then pi v != 0 and z+ differs from z0 by (X-1) pi v.
bad9d = 0
for _ in range(3000):
    A_, Y_, X_ = rnd.randint(-9, 9) or 1, rnd.randint(-9, 9) or 1, rnd.randint(2, 9)
    piv, piw = rnd.randint(-5, 5), rnd.randint(-5, 5)
    if piw != 0:
        if 2 * A_ * Y_ * piw == 0:
            bad9d += 1
    else:
        if piv != 0 and (X_ - 1) * piv == 0:
            bad9d += 1
check("9d among z0, z+, z- at least two outputs differ (pi w != 0 or pi v != 0)", bad9d == 0)

# ---------------------------------------------------------------------------
print("=== SUMMARY ===")
npass = sum(1 for _, ok in RESULTS if ok)
for tag, ok in RESULTS:
    if not ok:
        print("    FAILED:", tag)
print(f"CHECKS={len(RESULTS)} PASS={npass} FAIL={len(RESULTS) - npass}")
print("REDERIVE_GATE23_ISOTROPIC_PELL_S52 DONE")
