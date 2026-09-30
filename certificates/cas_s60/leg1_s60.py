#!/usr/bin/env python3
"""s60 GATE30 CAS leg 1 (SymPy). Our own code; GPT's scripts are NOT run.
Checks the mathematical claims of GPT's R48 review (A/C/D files) and planted controls that MUST be caught.
Finite ranges are finite checks, not proofs; each row says which."""
import sys, sympy as sp
from itertools import product
R = []
def rec(tag, ok, note=""):
    R.append((tag, bool(ok))); print(("PASS " if ok else "FAIL ") + tag + ("  -- " + note if note else ""))

a, b, u, y, al, s, l1, l2, x1, x2, d, b1, b2, g, p1, p2 = sp.symbols('a b u y alpha s l1 l2 x1 x2 d b1 b2 g p1 p2')
E11, E12, E22 = sp.symbols('E11 E12 E22')

# M1 two-root identity (n=2, symbolic): 4 alpha Pn - (2 alpha y - u)(2 alpha y - v) = L^2 - Delta
B = b1*x1 + b2*x2 + d
T = E11*x1**2 + E12*x1*x2 + E22*x2**2 + p1*x1 + p2*x2 + g
Pn = al*y**2 + B*y + T
L = l1*x1 + l2*x2 + s
Delta = B**2 - 4*al*T
U = -B + L; V = -B - L
rec("M1 4a*Pn-(2ay-u)(2ay-v) == L^2-Delta (symbolic)", sp.expand(4*al*Pn - (2*al*y-U)*(2*al*y-V) - (L**2 - Delta)) == 0)

# helpers
def int_roots_b(poly, aval, lo=-400, hi=400):
    q = sp.Poly(sp.expand(poly.subs(a, aval)), b)
    return sorted({int(r) for r in sp.roots(q, multiple=True) if r.is_integer}) if q.degree() > 0 else None
def parityFn(x): return x//2 if x % 2 == 0 else (1-3*x)//2

# M2 scaled example
P6 = (6*b-3*a)*(6*b+9*a-3); P2 = (2*b-a)*(2*b+3*a-1)
rec("M2a (6b-3a)(6b+9a-3) == 9(2b-a)(2b+3a-1)", sp.expand(P6 - 9*P2) == 0)
rec("M2b P6=0 total+unique, = parityFn (A.11), a in [-150,150] (finite)", all(int_roots_b(P6, t) == [parityFn(t)] for t in range(-150, 151)))
rec("M2c parityFn params p=1,c=0,q=-3,c'=1 satisfy ParityAffineNF parity conditions", (1-(-3)) % 2 == 0 and 1 % 2 == 1 and (0-1) % 2 == 1
    and all((2*parityFn(t) == t) if t % 2 == 0 else (2*parityFn(t) == -3*t+1) for t in range(-150, 151)))
# M3 coincident
rec("M3 (2b-2a)^2=0 roots = {a}, a in [-150,150]", all(int_roots_b((2*b-2*a)**2, t) == [t] for t in range(-150, 151)))
# M4 denominator 3 with global integral root
rec("M4 (3b-3a)(3b-3a-1)=0 integer roots = {a}", all(int_roots_b((3*b-3*a)*(3*b-3*a-1), t) == [t] for t in range(-150, 151)))
# M5 paper's own negative controls
rec("M5a (2b-a)(2b-a-2)=0 at a=0 has two integer roots {0,1}", int_roots_b((2*b-a)*(2*b-a-2), 0) == [0, 1])
rec("M5b (3b-a)(3b-a+1)=0 at a=2 has none", int_roots_b((3*b-a)*(3*b-a+1), 2) == [])
# M6 floor(a/3) one witness
def fl3_sols(expr, t, br=60, ur=4):
    out = []
    for bb in range(t//3-br, t//3+br+1):
        w = [uu for uu in range(-ur, ur+1) if expr.subs({a: t, b: bb, u: uu}) == 0]
        if w: out.append((bb, w))
    return out
F3 = (3*b-a+1)**2 + u**2 - 1
ok6 = True
for t in range(-45, 46):
    S = fl3_sols(F3, t, br=6)
    ok6 &= (len(S) == 1 and S[0][0] == sp.floor(sp.Rational(t, 3)) and S[0][1] == ([-1, 1] if t % 3 == 1 else [0]))
rec("M6 (3b-a+1)^2+u^2=1: unique b = floor(a/3), witnesses {+-1} iff a=1 mod 3 else {0}, a in [-45,45] (finite)", ok6)
rec("M6b total degree of (3b-a+1)^2+u^2-1 is 2", sp.Poly(F3, a, b, u).total_degree() == 2)
# M6c bound argument: sum of two squares = 1 => |3b-a+1|<=1  <=> a-2 <= 3b <= a  (symbolic sanity via reduce)
w = sp.symbols('w', integer=True)
rec("M6c |w|<=1 with w=3b-a+1 <=> a-2<=3b<=a (linear equivalence)", sp.simplify(sp.And(-1 <= 3*b-a+1, 3*b-a+1 <= 1)) == sp.simplify(sp.And(a-2 <= 3*b, 3*b <= a)) or
    all(((-1 <= 3*bb-t+1 <= 1) == (t-2 <= 3*bb <= t)) for t in range(-20, 21) for bb in range(-10, 11)))
# M7 Q impossible
c2, c1, c0 = sp.symbols('c2 c1 c0')
q = c2*a**2 + c1*a + c0
diff = sp.Poly(sp.expand(q.subs(a, a+3) - q - 1), a).all_coeffs()
sol = sp.solve(diff + [c0], [c2, c1, c0], dict=True)
rec("M7a q(a+3)-q(a)=1 & q(0)=0 forces q=a/3", sol == [{c2: 0, c1: sp.Rational(1, 3), c0: 0}])
rec("M7b then q(1)=1/3 != floor(1/3)=0", (sol[0][c1]*1) != 0)
interp = sp.interpolate([(0, 0), (1, 0), (2, 0)], a)
rec("M7c quadratic through floor(a/3) at 0,1,2 is 0, but floor(3/3)=1", interp == 0)
# M8 H impossible: 3p=2 has no integer solution; a+6 stays in same parity coset for any p
pp, cc = sp.symbols('p c', integer=True)
rec("M8a ((p(a+6)+c)-(pa+c))/2 == 3p", sp.expand(((pp*(a+6)+cc)-(pp*a+cc))/2 - 3*pp) == 0)
rec("M8b floor((a+6)/3)-floor(a/3)=2 on [-60,60]", all((t+6)//3 - t//3 == 2 for t in range(-60, 61)))
rec("M8c 3p=2 has no integer solution", sp.diophantine(3*pp - 2) == set())
rec("M8d p(a+6)+c == pa+c mod 2", sp.expand(pp*(a+6)+cc - (pp*a+cc) - 2*3*pp) == 0)
# M9 four squares relation a>=0 (finite illustration; theorem = Lagrange)
sq = {i*i+j*j+k*k+m*m for i in range(0, 15) for j in range(0, 15) for k in range(0, 15) for m in range(0, 15)}
rec("M9 every 0<=N<=200 is a sum of four squares; negatives never (finite)", all(N in sq for N in range(201)) and min(sq) >= 0)
# M10 a^2 has no common slope: f(a+M)-f(a)=2aM+M^2 depends on a for every M>=1
Ms = sp.symbols('M', positive=True, integer=True)
rec("M10 a^2 common slope impossible: d/da[(a+M)^2-a^2] = 2M != 0", sp.diff(sp.expand((a+Ms)**2 - a**2), a) == 2*Ms)
# M11 A.8 primitivity control: S=I3,d=2,rho=0,N=4: ordinary yes, primitive no
vecs = [v for v in product(range(-2, 3), repeat=3) if sum(t*t for t in v) == 1]
rep = [tuple(2*t for t in v) for v in vecs]
rec("M11 N=4 on 2Z^3 represented (6 vectors), none primitive", len(rep) == 6 and all(sp.igcd(*r) == 2 for r in rep))

# ---- planted controls: each MUST be caught (i.e. the check must come out False) ----
pl = []
pl.append(("PLANT1 wrong scale 8 in M2a", sp.expand(P6 - 8*P2) == 0))
pl.append(("PLANT2 (3b-a)^2+u^2=1 claimed = floor(a/3)", all(len(fl3_sols((3*b-a)**2+u**2-1, t, br=6)) == 1 and fl3_sols((3*b-a)**2+u**2-1, t, br=6)[0][0] == t//3 for t in range(-12, 13))))
pl.append(("PLANT3 (3b-a)(3b-a+1)=0 claimed total", all(int_roots_b((3*b-a)*(3*b-a+1), t) for t in range(-12, 13))))
caught = 0
for tag, claim in pl:
    if claim: print("PLANT_NOT_CAUGHT " + tag)
    else: caught += 1; print("PLANT_CAUGHT " + tag)
npass = sum(1 for _, o in R if o)
print(f"LEG1_SYMPY checks {npass}/{len(R)} PASS; plants caught {caught}/{len(pl)}; sympy {sp.__version__}")
print("LEG1_EXIT=", 0 if npass == len(R) and caught == len(pl) else 1)
