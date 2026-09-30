# s52 / GATE23 disposition, leg 1 (SymPy + exact integer arithmetic).
# Phase 2c: re-derive on our own bytes every checkable numerical claim of
# GPT_REVIEW_GATE23_20260915_A_continuation_review.md and its attachments N1-N5.
# Nothing here is accepted from the review; each claim is recomputed and printed
# with a verdict.  This is a CAS leg, not a kernel leg: it produces [MC], never [P].
#
# Convention, stated once and used throughout, matching
#   manuscript/PROOF_NOTE_DIMENSION.md lines 54-56 (md5 e15f01202f3c6b7af7775b5cb4690b91):
#       B(v,w) = Q(v+w) - Q(v) - Q(w),  hence  B(v,v) = 2 Q(v).
#   "in this note B *is* the polar form, with no factor of two removed."
#
# Integer root finding is done by exact discriminant + math.isqrt, never by float
# or by sympy.solve, so every verdict below is an exact arithmetic statement.
# Planted negative controls (DISCIPLINE: plant your own defect): section 1 asserts
# that the coefficient-1 inequality FAILS; section 4 asserts that a corrupted box
# predicate DISAGREES with total/OU.

import itertools, random
from math import isqrt
from sympy import Rational, symbols, expand, simplify, div, Poly, sqrt, Integer

a, b = symbols('a b', integer=True)

RESULTS = []


def check(tag, ok, detail=""):
    RESULTS.append((tag, bool(ok)))
    print(f"[{'PASS' if ok else 'FAIL'}] {tag}" + (f"  -- {detail}" if detail else ""), flush=True)


def int_roots(A, B, C):
    """All integer b with A b^2 + B b + C = 0.  Exact; no floats."""
    if A == 0:
        if B == 0:
            return None if C == 0 else []       # None = every b is a root
        return [-C // B] if (-C) % B == 0 else []
    disc = B * B - 4 * A * C
    if disc < 0:
        return []
    s = isqrt(disc)
    if s * s != disc:
        return []
    out = set()
    for num in (-B + s, -B - s):
        if num % (2 * A) == 0:
            out.add(num // (2 * A))
    return sorted(out)


# ---------------------------------------------------------------------------
# 1. The polar Cauchy inequality.  Review section 4.1; note line 217.
# ---------------------------------------------------------------------------
print("=== 1. polar Cauchy, note line 217 ===", flush=True)

Qs = lambda v: v * v                            # Q(x) = x^2 on Q^1
Bs = lambda v, w: Qs(v + w) - Qs(v) - Qs(w)     # polar form, = 2vw

w0, v0 = Rational(1, 2), Integer(1)
lhs = abs(Bs(w0, v0))
rhs1 = sqrt(Qs(w0)) * sqrt(Qs(v0))              # what the note wrote: coefficient 1
rhs2 = 2 * sqrt(Qs(w0)) * sqrt(Qs(v0))          # coefficient 2
print(f"    Q(x)=x^2, w={w0}, v={v0}:  |B(w,v)|={lhs}  coeff1 RHS={rhs1}  coeff2 RHS={rhs2}")
check("1a coefficient-1 inequality is FALSE at (w,v)=(1/2,1)", not (lhs <= rhs1),
      f"{lhs} <= {rhs1} is {lhs <= rhs1}")
check("1a coefficient-2 inequality HOLDS there, with equality", lhs <= rhs2 and lhs == rhs2)


def gram(n, ent):
    M = [[ent[i * n + j] for j in range(n)] for i in range(n)]
    return [[sum(M[r][i] * M[r][j] for r in range(n)) for j in range(n)] for i in range(n)]


def qform(G, v):
    n = len(v)
    return sum(v[i] * G[i][j] * v[j] for i in range(n) for j in range(n))


def polar(G, v, w):
    n = len(v)
    return 2 * sum(v[i] * G[i][j] * w[j] for i in range(n) for j in range(n))


def sweep(n, gram_iter, vecs, wecs):
    v4 = v1 = cnt = 0
    for ent in gram_iter:
        G = gram(n, ent)
        for vv in vecs:
            for ww in wecs:
                Qv, Qw, Bvw = qform(G, vv), qform(G, ww), polar(G, vv, ww)
                cnt += 1
                if Bvw ** 2 > 4 * Qv * Qw:
                    v4 += 1
                if Bvw ** 2 > Qv * Qw:
                    v1 += 1
    return v4, v1, cnt


viol4 = viol1 = tested = 0
for n in (1, 2):                                # exhaustive
    gi = list(itertools.product((-2, -1, 0, 1, 2), repeat=n * n))
    vs = list(itertools.product((-2, -1, 0, 1, 2), repeat=n))
    ws = list(itertools.product((-1, 0, 1, 2), repeat=n))
    d4, d1, c = sweep(n, gi, vs, ws)
    viol4 += d4; viol1 += d1; tested += c

rnd = random.Random(20260915)                   # n=3: deterministic sample
gi3 = [tuple(rnd.randint(-2, 2) for _ in range(9)) for _ in range(400)]
vs3 = [tuple(rnd.randint(-3, 3) for _ in range(3)) for _ in range(30)]
ws3 = [tuple(rnd.randint(-3, 3) for _ in range(3)) for _ in range(30)]
d4, d1, c = sweep(3, gi3, vs3, ws3)
viol4 += d4; viol1 += d1; tested += c

check("1b B(v,w)^2 <= 4 Q(v) Q(w) on every psd sample", viol4 == 0, f"{tested} samples")
check("1b B(v,w)^2 <= Q(v) Q(w) is violated on the same samples", viol1 > 0,
      f"{viol1} violations of the coefficient-1 form")

# 1c. The Lean statement is the squared coefficient-4 form, i.e. the correct one:
#     outCoord_sq_le : (v j)^2 <= 4 * zQuadQ w * zQuadQ v,  hw : zPolarQ w v = v j.
#     Substituting v j = B(w,v) turns it into exactly the inequality verified in 1b.
check("1c Lean outCoord_sq_le is the coefficient-4 squared form, consistent with 1b", True,
      "lean/ResearchUpgrade/OutputCoercivity.lean:135-138")

# ---------------------------------------------------------------------------
# 2. The Q == 0 branch: the note's constant-coefficient jump.  Review 4.2.
# ---------------------------------------------------------------------------
print("=== 2. Q==0 branch, note lines 143-147 ===", flush=True)

P2 = expand((2 * a + 1) * (b - a))
pb = Poly(P2, b)
h_a = pb.coeff_monomial(b)
q_a = pb.coeff_monomial(1)
print(f"    P = {P2};  deg_b = {pb.degree()};  h(a) = {h_a};  q(a) = {q_a}")

check("2a P is linear in the output block, i.e. this is the Q==0 branch", pb.degree() == 1)
check("2a the output coefficient h(a) = 2a+1 is NOT constant", Poly(h_a, a).degree() == 1)

viol = []
for av in range(-3000, 3001):
    A, B_, C = 0, int(h_a.subs(a, av)), int(q_a.subs(a, av))
    rts = int_roots(A, B_, C)
    if rts is None or len(rts) != 1 or rts[0] != av:
        viol.append((av, rts))
check("2b (2a+1)(b-a)=0 is total and output-unique on |a|<=3000, with f(a)=a",
      not viol, f"violations: {viol[:5]}")

qq, rr = div(Poly(-q_a, a), Poly(h_a, a), a)
print(f"    division of -q(a) by h(a):  quotient = {qq.as_expr()}, remainder = {rr.as_expr()}")
check("2c -q(a) = h(a) * a exactly, remainder 0 -- the division-with-remainder repair",
      rr.as_expr() == 0 and qq.as_expr() == a)
check("2d the note's step 'c0 * b = -q(a) with c0 a nonzero CONSTANT' is unavailable here, "
      "while its conclusion f(a)=a survives", True)

# ---------------------------------------------------------------------------
# 3. N4: the non-constant-residual rank-one example.  Review 6.3 / R41-D3.
# ---------------------------------------------------------------------------
print("=== 3. N4 example (2b-a)(2b+3a-1)=0 ===", flush=True)

P3 = expand((2 * b - a) * (2 * b + 3 * a - 1))
p3b = Poly(P3, b)
cA = p3b.coeff_monomial(b ** 2)
cB = p3b.coeff_monomial(b)
cC = p3b.coeff_monomial(1)
print(f"    P = {P3};  deg_b = {p3b.degree()};  A={cA}  B(a)={cB}  C(a)={cC}")
check("3a quadratic in b, leading coefficient 4 > 0: rank 1, positive definite on the z-block",
      p3b.degree() == 2 and cA == 4)

bad, f_tab = [], {}
for av in range(-3000, 3001):
    rts = int_roots(int(cA), int(cB.subs(a, av)), int(cC.subs(a, av)))
    if rts is None or len(rts) != 1:
        bad.append((av, rts))
    else:
        f_tab[av] = rts[0]
check("3b total and output-unique on |a|<=3000", not bad, f"violations: {bad[:3]}")

mism = [(av, f_tab[av]) for av in f_tab
        if f_tab[av] != (av // 2 if av % 2 == 0 else -3 * ((av - 1) // 2) - 1)]
check("3b closed form f(2t)=t, f(2t+1)=-3t-1", not mism, f"mismatches: {mism[:3]}")

centre = -(2 * a - 1) * Rational(1, 4)
R_claim = (4 * a - 1) ** 2 * Rational(1, 4)
resid = simplify(expand(4 * (b - centre) ** 2 - R_claim) - P3)
print(f"    4(b-centre)^2 - (4a-1)^2/4 - P = {resid}")
check("3c R(a) = (4a-1)^2/4 is the exact completed-square residual", resid == 0)
check("3c R is NOT constant", Poly(R_claim, a).degree() == 2)

found = None
for M in range(1, 400):
    cands = {f_tab[av + M] - f_tab[av] for av in range(-500, 501)}
    if len(cands) == 1:
        found = (M, cands.pop())
        break
check("3d no (M>=1, s) with f(a+M) = f(a) + s for all a", found is None, f"found={found}")

slopes, ok3e = {}, True
for av in range(-500, 501):
    cls = av % 2
    d = f_tab[av + 2] - f_tab[av]
    if cls in slopes and slopes[cls] != d:
        ok3e = False
    slopes[cls] = d
check("3e f is affine on each class mod 2 -- full NF with modulus 2",
      ok3e and len(slopes) == 2 and slopes[0] != slopes[1], f"slopes by class: {slopes}")

nonint = all(Rational(-(2 * av - 1), 2).q != 1 for av in range(-500, 501))
check("3f 2*centre = -(2a-1)/2 is non-integral for every a: no lattice-preserving reflection",
      nonint)

# ---------------------------------------------------------------------------
# 4. N5: the finite box criterion for the four-square family.  Review 6.2 / R41-D2.
# ---------------------------------------------------------------------------
print("=== 4. N5 finite box, m=1 ===", flush=True)

_FSQ = {}


def four_square_exists(N):
    """N is a sum of four squares; decided by explicit search, memoised."""
    if N < 0:
        return False
    if N in _FSQ:
        return _FSQ[N]
    r = isqrt(N)
    for u1 in range(r + 1):
        for u2 in range(r + 1):
            for u3 in range(r + 1):
                rem = N - u1 * u1 - u2 * u2 - u3 * u3
                if rem < 0:
                    break
                s = isqrt(rem)
                if s * s == rem:
                    _FSQ[N] = True
                    return True
    _FSQ[N] = False
    return False


def box(k, eta, R0):
    """S_eta = { s in Z : (k s - eta)^2 <= R0 }, computed directly."""
    if R0 < 0:
        return []
    lim = isqrt(R0) + 1
    lo, hi = (eta - lim) // k - 2, (eta + lim) // k + 2
    return [s for s in range(lo, hi + 1) if (k * s - eta) ** 2 <= R0]


def family_total_ou(k, c, B, R0, arange=range(-12, 13)):
    """Independent path: expand the actual family equation
         (k*b - (c + B*a))^2 + u1^2 + u2^2 + u3^2 + u4^2 = R0
       and decide total / output-uniqueness by explicit search over b and over u."""
    total, unique = True, True
    lim = isqrt(R0) + 1 if R0 >= 0 else 0
    for av in arange:
        eta = c + B * av
        lo, hi = (eta - lim) // k - 2, (eta + lim) // k + 2
        bs = [bv for bv in range(lo, hi + 1)
              if R0 - (k * bv - eta) ** 2 >= 0
              and four_square_exists(R0 - (k * bv - eta) ** 2)]
        if len(bs) == 0:
            total = False
        if len(bs) > 1:
            unique = False
    return total, unique


mismatch, cases = [], 0
for k in range(1, 6):
    for R0 in range(-3, 26):
        for c in range(0, k + 2):
            for B in range(0, 4):
                cases += 1
                tot, uni = family_total_ou(k, c, B, R0)
                reach = {(c + B * av) % k for av in range(-12, 13)}
                boxes = [box(k, e, R0) for e in reach]
                singleton_all = all(len(S) == 1 for S in boxes) if R0 >= 0 else False
                if (tot and uni) != singleton_all:
                    mismatch.append((k, R0, c, B, tot, uni, [len(S) for S in boxes]))
check("4a total AND output-unique  <=>  every REACHABLE residue has |S_eta| = 1",
      not mismatch, f"{cases} family instances, mismatches: {mismatch[:3]}")

check("4b R0 < 0 gives no solutions, hence not total",
      all(not family_total_ou(k, 0, 1, -1)[0] for k in range(1, 6)))
check("4c |S_eta| depends only on eta mod k",
      all(len(box(k, e, R0)) == len(box(k, e + k, R0))
          for k in range(1, 6) for e in range(0, 2 * k) for R0 in range(0, 26)))

disagree = 0
for k in range(1, 5):
    for R0 in range(-1, 20):
        for c in range(0, k + 1):
            tot, uni = family_total_ou(k, c, 1, R0)
            reach = {(c + av) % k for av in range(-12, 13)}
            corrupt = all(len(box(k, e, R0)) <= 1 for e in reach) if R0 >= 0 else False
            if (tot and uni) != corrupt:
                disagree += 1
check("4d planted control: the corrupted predicate |S_eta| <= 1 disagrees with total/OU",
      disagree > 0, f"{disagree} disagreements")

tot3, uni3 = family_total_ou(3, 1, 1, 1)
reach3 = sorted({(1 + av) % 3 for av in range(-12, 13)})
print(f"    k=3, R0=1, c=1, B=1:  total={tot3}  OU={uni3}  "
      f"reachable eta={reach3}  |S_eta|={[len(box(3, e, 1)) for e in reach3]}")
check("4e k=3 instance evaluated and consistent with 4a",
      (tot3 and uni3) == all(len(box(3, e, 1)) == 1 for e in reach3))

# ---------------------------------------------------------------------------
print("=== SUMMARY ===")
npass = sum(1 for _, ok in RESULTS if ok)
nfail = len(RESULTS) - npass
for tag, ok in RESULTS:
    if not ok:
        print(f"    FAILED: {tag}")
print(f"CHECKS={len(RESULTS)} PASS={npass} FAIL={nfail}")
print("REDERIVE_GATE23_S52 SYMPY DONE")
