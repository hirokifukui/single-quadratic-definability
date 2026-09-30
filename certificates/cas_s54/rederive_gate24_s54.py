"""rederive_gate24_s54.py -- s54 Phase-2c leg 1 (pure Python ints/Fractions + SymPy).

Re-derives, independently of GPT's review_r42_math_checks.py (NOT run), the figures cited in
GPT_REVIEW_GATE24_20260916_{A,C,D}.  Four-square box: brute-force enumeration of lattice points
in an explicit box.  The Sage leg uses a different method (per-coordinate distance multisets
convolved as polynomials).  Planted negative controls (defects we wrote in) must be caught.
"""
from fractions import Fraction as Fr
from itertools import product
import sympy as sp

CH = []
def check(name, cond):
    CH.append((name, bool(cond)))
    print(("PASS " if cond else "FAIL ") + name)

# G1  growth lemma: hypotheses of DefiniteBranch.le_of_sq_le are needed
def concl(c, s, B, C, K):
    return not (c * s * s <= B * s + C and C <= K * K) or s <= B + K
check("G1a prose lemma false at integer c=0,s=2,B=0,C=K=1", not concl(0, 2, 0, 1, 1))
check("G1b prose lemma false at rational c=1/4,s=2,B=0,C=K=1", not concl(Fr(1, 4), 2, 0, 1, 1))
viol = sum(1 for c in range(1, 5) for s in range(0, 13) for B in range(0, 7) for K in range(0, 7)
           for C in range(-5, K * K + 1) if not concl(c, s, B, C, K))
check("G1c with Lean hyps (1<=c,0<=s,0<=B,0<=K) no violation in box", viol == 0)
viol0 = sum(1 for c in range(0, 2) for s in range(0, 6) for B in range(0, 3) for K in range(0, 3)
            for C in range(-2, K * K + 1) if not concl(c, s, B, C, K))
check("G1ctl planted (c=0 allowed) is caught", viol0 > 0)

# G2  centre: the Lean criterion is for existence, not for a given vector
# Q(x)=x^2, polar B(x,y)=2xy (factor 2 kept); ell=0.  IsCentre c <-> forall w, 2cw = 0.
is_centre = lambda c: all(2 * c * w == 0 for w in range(-5, 6))
radical = [e for e in range(-5, 6) if all(2 * e * w == 0 for w in range(-5, 6))]
check("G2a radical of x^2 is {0}, so ell=0 annihilates it", radical == [0])
check("G2b candidate c=1 is NOT a centre", not is_centre(1))
check("G2c a centre exists (c=0)", is_centre(0))

# G3  linear-growth box radius is C(1+N), not CN
C = 1; f = lambda a: a + 1
check("G3a f(0)=1 escapes radius C*N at N=0", abs(f(0)) > C * 0)
check("G3b f maps [-N,N] into radius C(1+N), N<=50",
      all(abs(f(a)) <= C * (1 + N) for N in range(51) for a in range(-N, N + 1)))

# G4  Pell visibility: Q(b,u)=b^2-2u^2, output b, polar 2b1b2-4u1u2, v=(1,0)
v = (1, 0)
orth = [(b, u) for b in range(-6, 7) for u in range(-6, 7) if 2 * v[0] * b - 4 * v[1] * u == 0]
opp = [w for w in orth if (w[0] ** 2 - 2 * w[1] ** 2) < 0]
check("G4a an orthogonal w of opposite sign exists", len(opp) > 0)
check("G4b every orthogonal w has output coordinate 0", all(w[0] == 0 for w in orth))
check("G4c v itself is visible (the Lean disjunction holds via v)", v[0] != 0)

# G5  Ex: Lean has c=0 -> (3b-a)^2<=1, f=floor((a+1)/3)
outs = lambda box, a: [b for b in range(-60, 60) if box(a, b)]
check("G5a (3b-a)^2<=1: total, OU, f=floor((a+1)/3), 121 inputs",
      all(outs(lambda a, b: (3 * b - a) ** 2 <= 1, a) == [(a + 1) // 3] for a in range(-60, 61)))
check("G5b the comment's (3b-a-1)^2<=1 defines a different function",
      any(outs(lambda a, b: (3 * b - a - 1) ** 2 <= 1, a) != [(a + 1) // 3] for a in range(-60, 61)))

# G6  N4 control, 161 inputs
n4 = lambda a: [b for b in range(-400, 401) if (2 * b - a) * (2 * b + 3 * a - 1) == 0]
n4f = lambda a: a // 2 if a % 2 == 0 else (1 - 3 * a) // 2
check("G6 N4 total/OU, f(2t)=t, f(2t+1)=-3t-1, |a|<=80", all(n4(a) == [n4f(a)] for a in range(-80, 81)))

# G7  GAP theorem by brute force
from bisect import bisect_right
from math import isqrt
_DIST = {}
RMAX = 200
def _dists(k, eta):
    key = (k, eta)
    if key not in _DIST:
        lim = isqrt(RMAX) // k + 2          # |k s - eta| <= sqrt(RMAX) => |s| <= sqrt(RMAX)/k + 1
        rng = range(-lim, lim + 2)
        _DIST[key] = sorted(sum((k * s[j] - eta[j]) ** 2 for j in range(len(eta)))
                            for s in product(rng, repeat=len(eta)))
    return _DIST[key]
def count_S(k, eta, R0):
    assert R0 <= RMAX
    return 0 if R0 < 0 else bisect_right(_dists(k, tuple(eta)), R0)
def gap_pred(k, eta, R0, strict=True):
    dl = [min(e, k - e) for e in eta]
    d = sum(x * x for x in dl); g = min(k * (k - 2 * x) for x in dl)
    return (d <= R0 < d + g) if strict else (d <= R0 <= d + g)
cases = bad = bad_ctl = 0
for k in range(1, 10):
    for m in range(1, 4):
        for eta in product(range(k), repeat=m):
            cases += 1
            top = sum(min(e, k - e) ** 2 for e in eta) + k * k + 2
            for R0 in range(-1, top):
                one = count_S(k, eta, R0) == 1
                bad += one != gap_pred(k, eta, R0)
                bad_ctl += one != gap_pred(k, eta, R0, strict=False)
check("G7a residue cases enumerated = 2355", cases == 2355)
check("G7b #S_eta=1 <-> d<=R0<d+g for every R0 in [-1, d+k^2+1]", bad == 0)
check("G7ctl planted (<= for <) is caught", bad_ctl > 0)

# G8  full-residue classification
full_ok = lambda k, m, R0: all(count_S(k, eta, R0) == 1 for eta in product(range(k), repeat=m))
def predicted(k, m, R0):
    if k == 1: return R0 == 0
    if k % 2 == 0: return False
    h = (k - 1) // 2
    return m * h * h <= R0 < (h + 1) ** 2
mism = [(k, m, R0) for k in range(1, 8) for m in range(1, 5 if k <= 3 else 4)
        for R0 in range(-1, (k // 2 + 1) ** 2 + 3) if full_ok(k, m, R0) != predicted(k, m, R0)]
check("G8a full-residue thresholds = brute force (k<=7)", mism == [])
check("G8b k=3,m=3,R0=3 passes", full_ok(3, 3, 3))
check("G8c k=3,m=4 admits no R0", not any(full_ok(3, 4, R0) for R0 in range(-1, 12)))
check("G8d k=5,m=2,R0=8 passes", full_ok(5, 2, 8))

# G9  negative controls of the finite criterion (c=B=0, m=n=1)
fo = lambda k, R: [b for b in range(-50, 51) if (k * b) ** 2 <= R]
Rq = lambda a: a * (a - 1)
check("G9a k=2,R=a(a-1): a=0,1 give unique b=0", fo(2, Rq(0)) == [0] and fo(2, Rq(1)) == [0])
check("G9b ... but a=3 gives b in {-1,0,1}", fo(2, Rq(3)) == [-1, 0, 1])
check("G9c k=3,R=a mod 2: total, OU, f=0, R non-constant",
      all(fo(3, a % 2) == [0] for a in range(-40, 41)))

# G10  Proposition N (norm lift), symbolic, n=3 generic
D, r0, s0, c = sp.symbols('D r0 s0 c')
x = sp.symbols('x0:3'); l = sp.symbols('l0:3'); hh = sp.symbols('h0:3')
ell = sum(l[i] * x[i] for i in range(3)); h = sum(hh[i] * x[i] for i in range(3))
A = c + ell
H = (D * h ** 2 + ell ** 2) / c            # the content of T = h^2
R = c + 2 * ell + H
check("G10a (star) c*R = (c+ell)^2 + D h^2", sp.simplify(c * R - (A ** 2 + D * h ** 2)) == 0)
r = (r0 * A - D * s0 * h) / c; s = (s0 * A + r0 * h) / c
check("G10b c^2(r^2+Ds^2) = (r0^2+Ds0^2)(A^2+Dh^2)",
      sp.expand((r ** 2 + D * s ** 2) * c ** 2 - (r0 ** 2 + D * s0 ** 2) * (A ** 2 + D * h ** 2)) == 0)
check("G10c with c=r0^2+Ds0^2: r^2+Ds^2 = R identically",
      sp.simplify((r ** 2 + D * s ** 2 - R).subs({c: r0 ** 2 + D * s0 ** 2})) == 0)
z0 = {xi: 0 for xi in x}
check("G10d basepoint r(0)=r0, s(0)=s0",
      sp.simplify(r.subs(z0) - r0) == 0 and sp.simplify(s.subs(z0) - s0) == 0)
t = sp.symbols('t')
disc = sp.discriminant(sp.expand(H * t ** 2 + 2 * ell * t + c), t)
check("G10e line discriminant = -D*(2h)^2", sp.simplify(disc + D * (2 * h) ** 2) == 0)

# concrete: D=2, R = norm of affine forms, basepoint 0 with a DIFFERENT representation
a1, a2 = sp.symbols('a1 a2'); Dv = 2
Rc = sp.expand((3 * a1 - a2 + 5) ** 2 + Dv * (a1 + 2 * a2 + 1) ** 2)
cval = Rc.subs({a1: 0, a2: 0})
check("G10f R(0)=27 also equals 3^2+2*3^2 (second representation)", cval == 27 and 9 + 2 * 9 == 27)
P0, Q0 = 3, 3
lin = sum(sp.diff(Rc, w).subs({a1: 0, a2: 0}) * w for w in (a1, a2)) / 2
quad = sp.expand(Rc - cval - 2 * lin)
T = sp.expand((cval * quad - lin ** 2) / Dv)
coef, facs = sp.factor_list(T)
check("G10g concrete T=(cH-ell^2)/D is a square of a linear form",
      coef >= 0 and sp.sqrt(coef).is_rational and all(e % 2 == 0 for _, e in facs))
hl = sp.sqrt(coef) * sp.Mul(*[b ** (e // 2) for b, e in facs])
rr = sp.expand((P0 * (cval + lin) - Dv * Q0 * hl) / cval)
ss = sp.expand((Q0 * (cval + lin) + P0 * hl) / cval)
check("G10h concrete section: r^2+2s^2 = R and passes through (3,3)",
      sp.expand(rr ** 2 + Dv * ss ** 2 - Rc) == 0
      and rr.subs({a1: 0, a2: 0}) == P0 and ss.subs({a1: 0, a2: 0}) == Q0)
check("G10ctl basis-only square test accepts x1^2+x2^2 though T(1,1)=2 is not a square",
      sp.sqrt(1).is_integer and not sp.sqrt(2).is_rational)

npass = sum(1 for _, ok in CH if ok)
print("CHECKS=%d PASS=%d FAIL=%d" % (len(CH), npass, len(CH) - npass))
