#!/usr/bin/env python3
"""s58 GATE28 leg 1 v2 (SymPy/exact integers; G3 omission-control box widened to +-12 after v1 MISSED it). Checks the figures and claims of GPT's R46 review.
Written independently of GPT's vector_encoder_checks.py (which is NOT run). Each block has a planted
control that must be CAUGHT. Exit 0 iff every PASS holds and every control is caught."""
import sys, itertools, random
from fractions import Fraction as Fr
import sympy as sp

res = []; ctl = []
def ok(name, cond): res.append((name, bool(cond))); print(("PASS " if cond else "FAIL ") + name)
def plant(name, wrong_holds):  # a control is CAUGHT when the planted (false) statement fails
    ctl.append((name, not wrong_holds)); print(("CAUGHT " if not wrong_holds else "MISSED ") + "control " + name)

# ---- G1 exponent comparison (TCER_ADAPTER §1): eps = 1/56 against KK p.5 bounds n^(1/2-eps), n^(3/7+eps)
eps = sp.Rational(1, 56)
lo = sp.Rational(1, 2) - eps; hi = sp.Rational(3, 7) + eps
ok("G1 lower exponent 1/2-1/56 = 27/56", lo == sp.Rational(27, 56))
ok("G1 upper exponent 3/7+1/56 = 25/56", hi == sp.Rational(25, 56))
ok("G1 gap = 1/28", lo - hi == sp.Rational(1, 28))
N, c, C = sp.symbols('N c C', positive=True)
expr = sp.factor(c*N**lo - C*N**hi)
ok("G1 c N^(27/56) - C N^(25/56) = N^(25/56) (c N^(1/28) - C)", sp.simplify(expr - N**hi*(c*N**sp.Rational(1, 28) - C)) == 0)
# numeric: N0 = (2C/c)^28 gives positivity just above N0 for sample constants
good = all(float(cc*(1.0001*(2*CC/cc)**28)**(27/56) - CC*(1.0001*(2*CC/cc)**28)**(25/56)) > 0
           for cc, CC in [(1, 1), (0.3, 5), (2, 0.1), (1e-2, 7)])
ok("G1 threshold (2C/c)^28 suffices on samples", good)
plant("G1 eps=1/28 would leave no gap (27/56 claimed)", sp.Rational(1, 2) - sp.Rational(1, 28) - (sp.Rational(3, 7) + sp.Rational(1, 28)) > 0)

# ---- G2 counterexample P(a,b) = b - a to PROOF_NOTE_NF §0 (Q=0, radical everything, linear part 1)
a, b = sp.symbols('a b')
P = b - a
Qpart = sp.Poly(P, b).coeff_monomial(b**2)
ok("G2 Q (quadratic part in unknown b) = 0", Qpart == 0)
lin = sp.Poly(P, b).coeff_monomial(b)
ok("G2 linear part at radical vector 1 is 1 (not 0)", lin == 1)
tot = all(len([bb for bb in range(-60, 61) if P.subs({a: aa, b: bb}) == 0]) == 1 for aa in range(-40, 41))
ok("G2 total and output-unique on a in [-40,40]", tot)
plant("G2 'output uniqueness forces linear part 0 on Rad' holds for b-a", lin == 0)

# ---- G3 reverse compiler (V1): exact enumeration on two instances, own implementation
def reps(M, n): return list(itertools.product(range(M), repeat=n))
def V1(M, B, beta, a, b, u, e, boolean=True):
    n, m = len(a), len(b); R = reps(M, n)
    s = (sum(e) - 1)**2 + (sum(x*(x-1) for x in e) if boolean else 0)
    for i in range(n):
        s += (a[i] - M*u[i] - sum(R[k][i]*e[k] for k in range(len(R))))**2
    for j in range(m):
        dj = [M*beta[R[k]][j] - sum(B[j][i]*R[k][i] for i in range(n)) for k in range(len(R))]
        s += (M*b[j] - sum(B[j][i]*a[i] for i in range(n)) - sum(dj[k]*e[k] for k in range(len(R))))**2
    return s
def f_of(M, B, beta, a):
    r = tuple(x % M for x in a); u = tuple((x - y)//M for x, y in zip(a, r))
    return tuple(beta[r][j] + sum(B[j][i]*u[i] for i in range(len(a))) for j in range(len(B)))
# instance I1: n=1, m=2, M=3, B=[[2],[-1]], random beta
rng = random.Random(58)
inst = []
for (n, m, M) in [(1, 2, 3), (2, 2, 2)]:
    B = [[rng.randrange(-2, 3) for _ in range(n)] for _ in range(m)]
    beta = {r: tuple(rng.randrange(-3, 4) for _ in range(m)) for r in reps(M, n)}
    inst.append((n, m, M, B, beta))
# CommonSlope of the tabulated f
for (n, m, M, B, beta) in inst:
    cs = all(f_of(M, B, beta, tuple(x + M*t for x, t in zip(aa, tt))) ==
             tuple(f_of(M, B, beta, aa)[j] + sum(B[j][i]*tt[i] for i in range(n)) for j in range(m))
             for aa in itertools.product(range(-5, 6), repeat=n) for tt in itertools.product(range(-3, 4), repeat=n))
    ok(f"G3 table f has CommonSlope (n={n},M={M})", cs)
# exhaustive search: zeros of V1 over a box of (b,u,e) are exactly b=f(a); nonnegativity everywhere
for (n, m, M, B, beta) in inst:
    R = reps(M, n); nonneg = True; iff = True
    ar, ur, er, br = ((range(-4, 5), range(-3, 3), range(-1, 3), 2) if n == 1 else (range(-2, 3), range(-2, 2), range(-1, 2), 1))
    for aa in itertools.product(ar, repeat=n):
        fa = f_of(M, B, beta, aa); zeros_b = set()
        for uu in itertools.product(ur, repeat=n):
            for ee in itertools.product(er, repeat=len(R)):
                for bb in itertools.product(*[range(fa[j]-br, fa[j]+br+1) for j in range(m)]):
                    v = V1(M, B, beta, aa, bb, uu, ee)
                    if v < 0: nonneg = False
                    if v == 0: zeros_b.add(bb)
        if zeros_b != {fa}: iff = False
    ok(f"G3 V1 >= 0 on box (n={n},M={M})", nonneg)
    ok(f"G3 V1 = 0 exactly at b = f(a) on box (n={n},M={M})", iff)
# symbolic degree and positive definiteness of the unknown part for I1
(n, m, M, B, beta) = inst[0]; R = reps(M, n)
As = sp.symbols('a0:%d' % n); Bs = sp.symbols('b0:%d' % m); Us = sp.symbols('u0:%d' % n); Es = sp.symbols('e0:%d' % len(R))
Psym = sp.expand(V1(M, B, beta, As, Bs, Us, Es))
ok("G3 total degree of V1 is 2", sp.Poly(Psym, *As, *Bs, *Us, *Es).total_degree() == 2)
unk = list(Bs) + list(Us) + list(Es)
H = sp.hessian(Psym, unk) / 2
ok("G3 unknown quadratic part positive definite (Sylvester)", all(H[:k, :k].det() > 0 for k in range(1, len(unk)+1)))
# planted: drop the Boolean term -> a non-graph zero must appear (search)
(n, m, M, B, beta) = inst[0]; R = reps(M, n); found = False
for aa in range(-3, 4):
    fa = f_of(M, B, beta, (aa,))
    for uu in range(-3, 3):
        for ee in itertools.product(range(-2, 3), repeat=len(R)):
            for bb in itertools.product(*[range(fa[j]-12, fa[j]+13) for j in range(m)]):
                if bb != fa and V1(M, B, beta, (aa,), bb, (uu,), ee, boolean=False) == 0: found = True; break
            if found: break
        if found: break
    if found: break
plant("G3 V1 without e(e-1) still defines the graph", not found)
# GPT's own omission example, recomputed independently: M=2,B=[[1],[0]],beta={0:(0,0),1:(0,1)}
g = V1(2, [[1], [0]], {(0,): (0, 0), (1,): (0, 1)}, (0,), (-1, 2), (-1,), (-1, 2))
g0 = V1(2, [[1], [0]], {(0,): (0, 0), (1,): (0, 1)}, (0,), (-1, 2), (-1,), (-1, 2), boolean=False)
ok("G3 GPT example: correct V1 = 4, omitted = 0", g == 4 and g0 == 0)

# ---- G4 padding obstruction a -> (a^2, 0)
aa_, MM = sp.symbols('a M')
d = sp.expand((aa_ + MM)**2 - aa_**2)
ok("G4 (a+M)^2 - a^2 = 2Ma + M^2", d == 2*MM*aa_ + MM**2)
ok("G4 no M in 1..50 gives constant difference of a^2", all(len({(x+M)**2 - x**2 for x in range(-10, 11)}) > 1 for M in range(1, 51)))
plant("G4 difference constant in a", sp.diff(d, aa_) == 0)

# ---- G5 scalar control (2b-a)(2b+3a-1)=0
vals = {}
tu = True
for x in range(-60, 61):
    rts = [y for y in range(-200, 201) if (2*y - x)*(2*y + 3*x - 1) == 0]
    tu &= len(rts) == 1; vals[x] = rts[0] if rts else None
ok("G5 total and unique on [-60,60]", tu)
ok("G5 f(2t)=t, f(2t+1)=-3t-1", all(vals[2*t] == t for t in range(-30, 31)) and all(vals[2*t+1] == -3*t-1 for t in range(-30, 30)))
ok("G5 affine on each class mod 2 (full coset NF with M=2)", True and all(vals[2*t+2]-vals[2*t] == 1 for t in range(-30, 29)))
def has_cs(M): return len({vals[x+M]-vals[x] for x in range(-50, 50-M+1) if x+M <= 60}) == 1
ok("G5 no CommonSlope for M in 1..20", not any(has_cs(M) for M in range(1, 21)))
plant("G5 CommonSlope with M=2", has_cs(2))

# ---- G6 divisor lemma (split rank 2)
bad = 0; cnt = 0
for al, be, ga in itertools.product(range(-3, 4), repeat=3):
    if al == 0 and be == 0: continue
    F = lambda k: al*k*k + be*k + ga
    for K in range(1, 7):
        k1 = next(k for k in (0, 1, 2) if F(k) != 0)
        done = False
        for s in range(1, 6):
            k0 = k1 + K*F(k1)*s
            if F(k0) % F(k1): continue
            lam = F(k0)//F(k1)
            if lam in (0, 1): continue
            if (lam - 1) % K: continue
            if all(F(k0 + lam*j) % lam == 0 for j in range(-5, 6)): done = True; break
        cnt += 1; bad += (not done)
ok(f"G6 lambda lemma holds on {cnt} (F,K) instances", bad == 0)
# planted: require lambda ≡ 1 mod (K+1) -> must fail somewhere
fails = 0
for al, be, ga in itertools.product(range(-3, 4), repeat=3):
    if al == 0 and be == 0: continue
    F = lambda k: al*k*k + be*k + ga
    K = 2; k1 = next(k for k in (0, 1, 2) if F(k) != 0)
    lam = F(k1 + K*F(k1))//F(k1)
    if (lam - 1) % (K+1): fails += 1
plant("G6 lambda ≡ 1 mod (K+1) always", fails == 0)

# ---- G7 A4 step: x radical, e isotropic non-radical, Q(x+Ne)=Q(x); x+Ne non-radical
x1, x2, x3, x4 = sp.symbols('x1:5')
Gm = sp.Matrix([[0, 1, 0, 0], [1, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]])  # degenerate: radical = span(e4)
Qf = lambda v: (v.T*Gm*v)[0]
pol = lambda v, w: Qf(v+w) - Qf(v) - Qf(w)
e = sp.Matrix([sp.Rational(1, 3), 0, 0, 0]); xr = sp.Matrix([0, 0, 0, x4]); Nn = 3
ok("G7 e isotropic, non-radical", Qf(e) == 0 and pol(e, sp.Matrix([0, 1, 0, 0])) != 0)
ok("G7 x radical: polar(x, .) = 0", all(sp.simplify(pol(xr, sp.eye(4)[:, i])) == 0 for i in range(4)))
ok("G7 Q(x+Ne) = Q(x)", sp.simplify(Qf(xr + Nn*e) - Qf(xr)) == 0)
ok("G7 N e integral", all(v.is_integer for v in Nn*e))
ok("G7 x+Ne non-radical", pol(xr + Nn*e, sp.Matrix([0, 1, 0, 0])) != 0)
ebad = sp.Matrix([0, 0, 1, 0])  # non-isotropic
plant("G7 with non-isotropic e, Q(x+Ne)=Q(x)", sp.simplify(Qf(xr + Nn*ebad) - Qf(xr)) == 0)

# ---- G8 D3 injectivity criterion, n=1
def inj_box(M, B, beta):
    seen = {}
    for x in range(-40, 41):
        y = f_of(M, B, beta, (x,))
        if y in seen: return False
        seen[y] = x
    return True
def crit(M, B, beta):
    m = len(B); Bv = [B[j][0] for j in range(m)]
    if all(v == 0 for v in Bv): return M == 1 and False  # kernel nonzero
    R = reps(M, 1)
    for r, s in itertools.combinations(R, 2):
        dvec = [beta[r][j] - beta[s][j] for j in range(m)]
        # dvec in B Z ?  exists t integer with dvec = t*Bv
        ts = {Fr(dvec[j], Bv[j]) for j in range(m) if Bv[j] != 0}
        if all(dvec[j] == 0 for j in range(m) if Bv[j] == 0) and len(ts) == 1 and list(ts)[0].denominator == 1:
            return False
    return True
agree = 0; tot = 0
for _ in range(400):
    M = rng.randrange(1, 4); m = rng.randrange(1, 3)
    B = [[rng.randrange(-2, 3)] for _ in range(m)]
    beta = {r: tuple(rng.randrange(-3, 4) for _ in range(m)) for r in reps(M, 1)}
    tot += 1; agree += (inj_box(M, B, beta) == crit(M, B, beta))
ok(f"G8 injectivity iff (B injective and residue cosets disjoint): {agree}/{tot}", agree == tot)
plant("G8 criterion without the coset-disjointness clause", all(
    inj_box(M, B, beta) == any(B[j][0] != 0 for j in range(len(B)))
    for (M, B, beta) in [(2, [[2]], {(0,): (0,), (1,): (2,)})]))

np_ = sum(1 for _, v in res if v); nc = sum(1 for _, v in ctl if v)
print(f"LEG1_SUMMARY {np_}/{len(res)}  CONTROLS_CAUGHT {nc}/{len(ctl)}")
sys.exit(0 if np_ == len(res) and nc == len(ctl) else 1)
