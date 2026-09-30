#!/usr/bin/env python3
"""s59 GATE29 CAS leg 1 (SymPy). Independent of GPT's scripts (not run).
Every PASS line is a claim from GPT's R47 review; every control is a planted false claim that must be CAUGHT."""
import itertools, random
from fractions import Fraction as F
import sympy as sp
random.seed(59)
res = []; ctl = []
def P(name, ok): res.append((name, ok)); print(("PASS " if ok else "FAIL ") + name)
def C(name, holds):  # holds = planted false claim evaluates true?  must be False
    ctl.append((name, not holds)); print(("CAUGHT " if not holds else "MISSED ") + "control " + name)

# ---- K1  A.8 imprimitive coset: S=I3, d=2, rho=0, N=4 ----
def rep_mod(S, d, rho, N, p, e, primitive):
    q = p ** e
    for x in itertools.product(range(q), repeat=3):
        v = [rho[i] + d * x[i] for i in range(3)]
        val = sum(S[i][j] * v[i] * v[j] for i in range(3) for j in range(3))
        if (val - N) % q == 0 and (not primitive or any(vi % p for vi in v)):
            return True
    return False
I3 = [[1,0,0],[0,1,0],[0,0,1]]
ordinary = all(rep_mod(I3, 2, [0,0,0], 4, p, e, False) for p, E in [(2,5),(3,3),(5,2),(7,2)] for e in range(1, E+1))
prim2 = any(rep_mod(I3, 2, [0,0,0], 4, 2, e, True) for e in range(1, 5))
P("K1 N=4 ordinarily represented by 2Z^3 mod p^e (p<=7, box)", ordinary)
P("K1 global solution (2,0,0): 4 = 2^2", 2**2 == 4)
P("K1 N=4 NOT primitively represented by 2Z^3 mod 2^e (e=1..4)", not prim2)
# control: a primitive coset rho=(1,0,0), d=2, N=1: claim 'not primitively represented mod 2' must fail
C("K1 rho=(1,0,0),d=2,N=1 not primitive mod 2^e", not any(rep_mod(I3, 2, [1,0,0], 1, 2, e, True) for e in range(1, 5)))

# ---- K2  encoder unknown Gram: det = M^(2(n+m)) (1+M^n), positive definite ----
def gram(n, m, M, rnd):
    R = list(itertools.product(range(M), repeat=n))
    k = len(R)
    b = sp.symbols('b0:%d' % m); u = sp.symbols('u0:%d' % n); e = sp.symbols('e0:%d' % k)
    delta = [[rnd() for _ in range(m)] for _ in range(k)]
    Qu = sum(e) ** 2 + sum(x ** 2 for x in e)
    Qu += sum((M * u[i] + sum(R[r][i] * e[r] for r in range(k))) ** 2 for i in range(n))
    Qu += sum((M * b[j] - sum(delta[r][j] * e[r] for r in range(k))) ** 2 for j in range(m))
    X = list(b) + list(u) + list(e)
    H = sp.hessian(sp.expand(Qu), X) / 2
    return H, k
for (n, m, M) in [(1,1,2),(1,2,2),(1,1,3),(2,1,2),(1,3,3),(2,2,2)]:
    H, k = gram(n, m, M, lambda: random.randint(-7, 7))
    det = H.det()
    P(f"K2 det Gram (n,m,M)=({n},{m},{M}) = M^(2(n+m))(1+M^n) = {M**(2*(n+m))*(1+M**n)}", det == M ** (2 * (n + m)) * (1 + M ** n))
    minors_pos = all(H[:i, :i].det() > 0 for i in range(1, H.shape[0] + 1))
    P(f"K2 Sylvester positive definite (n,m,M)=({n},{m},{M})", minors_pos)
H, k = gram(1, 2, 2, lambda: random.randint(-7, 7))
C("K2 det = M^(2(n+m)) * M^n (wrong factor)", H.det() == 2 ** 6 * 2)
P("K2 GPT's instance n=1,m=2,M=2 gives 192", H.det() == 192)

# ---- K3  two affine integrality domains covering Z^n (n=1: denominators<=12; n=2: <=4) ----
def domains_n1(D):
    out = {}
    for den in range(1, D + 1):
        for p in range(den):
            for c in range(den):
                if sp.gcd(sp.gcd(p, c), den) != 1 and not (p == 0 and c == 0 and den == 1):
                    continue
                dom = frozenset(a for a in range(den * 2 * 12) if (p * a + c) % den == 0)
                out[(p, c, den)] = dom
    return out
Lp = 2 * 12 * 12 * 11 * 10 * 7  # period covering all denominators <= 12
bad = covers = 0
dens = {}
for den in range(1, 13):
    for p in range(den):
        for c in range(den):
            if sp.gcd(sp.gcd(p, c), den) != 1: continue
            dens[(p, c, den)] = den
keys = list(dens)
for k0, k1 in itertools.combinations(keys, 2):
    p0, c0, d0 = k0; p1, c1, d1 = k1
    L = sp.ilcm(d0, d1)
    I0 = {a for a in range(L) if (p0 * a + c0) % d0 == 0}
    I1 = {a for a in range(L) if (p1 * a + c1) % d1 == 0}
    if I0 and I1 and not (I0 & I1) and (I0 | I1) == set(range(L)):
        covers += 1
        # GPT: reduced denominators are 2 (index 2) and domains are the two parity classes
        if not (d0 == 2 and d1 == 2 and I0 in ({a for a in range(L) if a % 2 == 0}, {a for a in range(L) if a % 2 == 1})):
            bad += 1
P(f"K3 n=1, reduced denominators<=12: every disjoint nonempty 2-cover is the parity split (covers={covers})", covers > 0 and bad == 0)
# n=2, denominators <= 4 (residue vectors mod den)
bad2 = cov2 = 0
aff2 = []
for den in range(1, 5):
    for p in itertools.product(range(den), repeat=2):
        for c in range(den):
            if sp.gcd(sp.gcd(sp.gcd(p[0], p[1]), c), den) != 1: continue
            aff2.append((p, c, den))
for (pa, ca, da), (pb, cb, db) in itertools.combinations(aff2, 2):
    L = sp.ilcm(da, db)
    pts = list(itertools.product(range(L), repeat=2))
    I0 = {x for x in pts if (pa[0]*x[0] + pa[1]*x[1] + ca) % da == 0}
    I1 = {x for x in pts if (pb[0]*x[0] + pb[1]*x[1] + cb) % db == 0}
    if I0 and I1 and not (I0 & I1) and len(I0) + len(I1) == len(pts):
        cov2 += 1
        ok = da == 2 and db == 2 and (pa[0] - pb[0]) % 2 == 0 and (pa[1] - pb[1]) % 2 == 0 and (ca - cb) % 2 == 1 and (pa[0] % 2 or pa[1] % 2)
        bad2 += (not ok)
P(f"K3 n=2, reduced denominators<=4: every 2-cover has den 2, p0=p1 mod 2, p0!=0 mod 2, c0-c1 odd (covers={cov2})", cov2 > 0 and bad2 == 0)
# control: 'some 2-cover with a reduced denominator 3 exists' must be false
C("K3 a 2-cover with denominator 3 exists (n=1)", any(True for k0, k1 in itertools.combinations([k for k in keys if k[2] == 3], 2)
    if (lambda I0, I1: I0 and I1 and not (I0 & I1) and (I0 | I1) == set(range(3)))(
        {a for a in range(3) if (k0[0]*a + k0[1]) % 3 == 0}, {a for a in range(3) if (k1[0]*a + k1[1]) % 3 == 0})))

# ---- K4  H-type examples and negative controls ----
def graph_ok(h0, h1, rng=range(-60, 61)):
    for a in rng:
        roots = [F(h(a), 2) for h in (h0, h1)]
        ints = {r for r in roots if r.denominator == 1}
        if len(ints) != 1: return False
    return True
parity = lambda a: a // 2 if a % 2 == 0 else -3 * (a // 2) - 1
P("K4 (2b-a)(2b+3a-1): total and output-unique on [-60,60]", graph_ok(lambda a: a, lambda a: 1 - 3 * a))
P("K4 the unique root equals parityFn: f(2t)=t, f(2t+1)=-3t-1", all((F(a,2) if a % 2 == 0 else F(1-3*a,2)) == parity(a) for a in range(-60, 61)))
P("K4 p0=1,p1=-3: p0=p1 mod 2, p0 odd, c0-c1=-1 odd", (1 - (-3)) % 2 == 0 and 1 % 2 == 1 and (0 - 1) % 2 == 1)
C("K4 h0=a, h1=a+2 (same parity) defines a function", graph_ok(lambda a: a, lambda a: a + 2))
C("K4 roots a/3,(a-1)/3 total", all(any(F(x, 3).denominator == 1 for x in (a, a - 1)) for a in range(-30, 31)))
C("K4 roots +a,-a output-unique", graph_ok(lambda a: 2 * a, lambda a: -2 * a))
x = sp.symbols('x')
q = x * (x - 1) / 2
P("K4 a(a-1)/2 integer-valued on [-50,50] with non-integer coefficients", all(q.subs(x, a).is_integer for a in range(-50, 51)) and not all(c.is_integer for c in sp.Poly(q, x).coeffs()))

# ---- K5  composition of common slopes: (g o f)(a+MNt) = (g o f)(a) + CBt ----
fails = 0; cases = 0
for trial in range(60):
    n, m, k = random.randint(1, 2), random.randint(1, 2), random.randint(1, 2)
    M, N = random.randint(1, 3), random.randint(1, 3)
    B = sp.Matrix(m, n, lambda i, j: random.randint(-3, 3)); Cm = sp.Matrix(k, m, lambda i, j: random.randint(-3, 3))
    tf = {r: sp.Matrix([random.randint(-5, 5) for _ in range(m)]) for r in itertools.product(range(M), repeat=n)}
    tg = {r: sp.Matrix([random.randint(-5, 5) for _ in range(k)]) for r in itertools.product(range(N), repeat=m)}
    def f(a):
        r = tuple(ai % M for ai in a); t = sp.Matrix([(ai - ri) // M for ai, ri in zip(a, r)]); return tf[r] + B * t
    def g(y):
        r = tuple(int(yi) % N for yi in y); s = sp.Matrix([(int(yi) - ri) // N for yi, ri in zip(y, r)]); return tg[r] + Cm * s
    for _ in range(8):
        a = [random.randint(-9, 9) for _ in range(n)]; t = [random.randint(-4, 4) for _ in range(n)]
        lhs = g(f([ai + M * N * ti for ai, ti in zip(a, t)])); rhs = g(f(a)) + Cm * B * sp.Matrix(t)
        cases += 1; fails += (lhs != rhs)
P(f"K5 composition identity on {cases} random cases", fails == 0)
# control: period M+N instead of MN
wrong = 0
M, N = 2, 3; B = sp.Matrix([[1]]); Cm = sp.Matrix([[2]])
tf = {(0,): sp.Matrix([0]), (1,): sp.Matrix([5])}; tg = {(0,): sp.Matrix([0]), (1,): sp.Matrix([7]), (2,): sp.Matrix([1])}
f = lambda a: tf[(a[0] % 2,)] + B * sp.Matrix([(a[0] - a[0] % 2) // 2])
g = lambda y: tg[(int(y[0]) % 3,)] + Cm * sp.Matrix([(int(y[0]) - int(y[0]) % 3) // 3])
C("K5 period M+N works", all(g(f([a + (M + N) * t])) == g(f([a])) + Cm * B * sp.Matrix([t]) for a in range(-6, 7) for t in range(-3, 4)))

# ---- K6  score arithmetic ----
P("K6 25+20+14+8+17 = 84", 25 + 20 + 14 + 8 + 17 == 84)
P("K6 13/16 = 81.25%", F(13, 16) * 100 == F(8125, 100))
C("K6 13/16 = 82%", F(13, 16) * 100 == 82)

np_ = sum(ok for _, ok in res); nc = sum(ok for _, ok in ctl)
print(f"LEG1_SUMMARY {np_}/{len(res)}  CONTROLS_CAUGHT {nc}/{len(ctl)}")
