#!/usr/bin/env python3
"""s61 GATE31 CAS leg 1 (SymPy). Clone of s60 leg1_sympy_s60.py (2d470152): same harness (rec / plants / exit line),
checks replaced by the mathematical claims of GPT's R49 review (A §3–§4, C §7, verification/check_witness_count_examples).
Our own code; GPT's scripts are NOT run. Finite ranges are finite checks, not proofs; each row says which."""
import sys, sympy as sp
from fractions import Fraction
from itertools import product
R = []
def rec(tag, ok, note=""):
    R.append((tag, bool(ok))); print(("PASS " if ok else "FAIL ") + tag + ("  -- " + note if note else ""))

a, b, u, x = sp.symbols('a b u x')
F3 = (3*b - a + 1)**2 + u**2 - 1

def sols(expr, t, bw=3, uw=2):
    """all (b,u) with b in floor(t/3)±bw, u in [-uw,uw] and expr=0; returns (triples_scanned, solutions)"""
    out, n = [], 0
    for bb in range(t//3 - bw, t//3 + bw + 1):
        for uu in range(-uw, uw + 1):
            n += 1
            if expr.subs({a: t, b: bb, u: uu}) == 0: out.append((bb, uu))
    return n, out

# N1 (A §3.3, review §7) floor formula on a in [-300,300], same window as GPT's claim, OUR code
tot = 0; ok1 = True
for t in range(-300, 301):
    n, S = sols(F3, t)
    tot += n
    ok1 &= ({s[0] for s in S} == {t//3}) and ({s[1] for s in S} == ({-1, 1} if t % 3 == 1 else {0}))
rec("N1 (3b-a+1)^2+u^2=1: b=floor(a/3) only; u-set {+-1} iff a=1 mod 3 else {0}; a in [-300,300] (finite)", ok1)
rec("N1b triples scanned = 21035 (GPT's count: 601 inputs x 7 b x 5 u)", tot == 21035 == 601*7*5)
rec("N1c a=1,b=0: u=+1 and u=-1 both solve (two witnesses)", F3.subs({a: 1, b: 0, u: 1}) == 0 and F3.subs({a: 1, b: 0, u: -1}) == 0)
rec("N1d total degree 2", sp.Poly(F3, a, b, u).total_degree() == 2)
# N2 sum of two squares = 1 => |3b-a+1|<=1 <=> a-2<=3b<=a  (symbolic: solve linear ineq in b)
rec("N2 |3b-a+1|<=1 <=> a-2<=3b<=a (grid a in [-40,40], b in [-20,20])",
    all(((-1 <= 3*B_ - A_ + 1 <= 1) == (A_ - 2 <= 3*B_ <= A_)) for A_ in range(-40, 41) for B_ in range(-20, 21)))
rec("N2b a-2<=3b<=a has exactly one integer b, = floor(a/3), a in [-300,300]",
    all([B_ for B_ in range(t//3 - 5, t//3 + 6) if t - 2 <= 3*B_ <= t] == [t//3] for t in range(-300, 301)))
# N3 residues: a=3q+r -> u = 1 if r==1 else 0 (paper) / GPT "u=0,1,0"
rec("N3 residue r=0,1,2 -> u=0,1,0 solves with b=q", all(F3.subs({a: 3*q + r, b: q, u: (1 if r == 1 else 0)}) == 0 for q in range(-30, 31) for r in range(3)))
# N4 quadratic part of lower bound (A §3.3): quadratic vanishing at 0,1,2 is 0, so value at 3 is 0 != floor(3/3)=1
c0, c1, c2 = sp.symbols('c0 c1 c2')
qq = c0 + c1*x + c2*x**2
sol = sp.solve([qq.subs(x, 0), qq.subs(x, 1), qq.subs(x, 2)], [c0, c1, c2], dict=True)
rec("N4 rational quadratic with q(0)=q(1)=q(2)=0 is identically 0; q(3)=0 != 1", sol == [{c0: 0, c1: 0, c2: 0}] and 3//3 == 1)
# N5 parity part (A §3.3 "6p=4"; paper 10.18 proof): 2f = p x + c on {p x + c even}
pp, cc = sp.symbols('p c', integer=True)
rec("N5a (p(x+6)+c) - (p x + c) = 6p  (so 2(f(x+6)-f(x)) = 6p on the same class)", sp.expand(pp*(x+6)+cc - (pp*x+cc) - 6*pp) == 0)
rec("N5b x and x+6 give the same parity of p x + c (difference 6p = 2*3p)", all(((P*(X+6)+C) - (P*X+C)) % 2 == 0 for P in range(-9, 10) for C in range(-5, 6) for X in range(-5, 6)))
rec("N5c p odd: exactly one of x=0,1 has p x + c even (all odd p in [-21,21], c in [-10,10])",
    all(sum(1 for X in (0, 1) if (P*X + C) % 2 == 0) == 1 for P in range(-21, 22, 2) for C in range(-10, 11)))
rec("N5d 2(floor((x+6)/3)-floor(x/3)) = 4 on [-300,300]", all(2*((t+6)//3 - t//3) == 4 for t in range(-300, 301)))
rec("N5e 6p = 4 has no integer solution", sp.diophantine(6*pp - 4) == set())
# N6 (A §4) c21 integrality: rational affine L integer on Z^n => L(0), L(e_i)-L(0) integers; control of the converse direction
ok6 = True
for s_, l1_, l2_ in product([Fraction(k, 6) for k in range(-6, 7)], repeat=3):
    Lint = all((s_ + l1_*X + l2_*Y).denominator == 1 for X in range(-3, 4) for Y in range(-3, 4))
    ok6 &= (Lint == (s_.denominator == 1 and l1_.denominator == 1 and l2_.denominator == 1))
rec("N6 affine L(x,y)=s+l1 x+l2 y with coeffs in (1/6)Z: integer on Z^2 grid <=> s,l1,l2 integers (finite)", ok6)
# N7 floor(a/3) common slope M=3, B=1 (paper 10.18 remark)
rec("N7 floor((a+3t)/3) = floor(a/3)+t, a in [-60,60], t in [-10,10]", all((A_+3*T)//3 == A_//3 + T for A_ in range(-60, 61) for T in range(-10, 11)))
# N8 regression of R48-era paper examples still quoted in §10 (A §4 bullet 2)
P6 = (6*b-3*a)*(6*b+9*a-3); P2 = (2*b-a)*(2*b+3*a-1)
rec("N8a (6b-3a)(6b+9a-3) == 9(2b-a)(2b+3a-1)", sp.expand(P6 - 9*P2) == 0)
rec("N8b (2b-2a)^2 = 0 iff b = a (repeated root)", sp.factor((2*b-2*a)**2) == 4*(a-b)**2 or sp.factor((2*b-2*a)**2) == 4*(b-a)**2)

# ---- planted controls: each MUST be caught (the claim must come out False) ----
pl = []
Fbad = (3*b - a)**2 + u**2 - 1
pl.append(("PLANT1 (3b-a)^2+u^2=1 (no +1) claimed to define floor(a/3) on [-12,12]", all({s[0] for s in sols(Fbad, t)[1]} == {t//3} for t in range(-12, 13))))
pl.append(("PLANT2 a=1 mod 3 claimed to have witness set {0}", all({s[1] for s in sols(F3, t)[1]} == {0} for t in range(-11, 12, 3))))
pl.append(("PLANT3 6p = 4 claimed solvable in integers", sp.diophantine(6*pp - 4) != set()))
pl.append(("PLANT4 quadratic through (0,0),(1,0),(2,0),(3,1) claimed", len(sp.solve([qq.subs(x, 0), qq.subs(x, 1), qq.subs(x, 2), qq.subs(x, 3) - 1], [c0, c1, c2], dict=True)) > 0))
pl.append(("PLANT5 triple count claimed 21036", tot == 21036))
pl.append(("PLANT6 L=(x+1)/2 claimed integer-valued on Z", all((Fraction(X + 1, 2)).denominator == 1 for X in range(-5, 6))))
caught = 0
for tag, claim in pl:
    if claim: print("PLANT_NOT_CAUGHT " + tag)
    else: caught += 1; print("PLANT_CAUGHT " + tag)
npass = sum(1 for _, o in R if o)
print(f"LEG1_SYMPY checks {npass}/{len(R)} PASS; plants caught {caught}/{len(pl)}; sympy {sp.__version__}")
print("LEG1_EXIT=", 0 if npass == len(R) and caught == len(pl) else 1)
