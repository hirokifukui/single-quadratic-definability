#!/usr/bin/env python3
"""s57 leg1 (SymPy, exact rationals). Independent re-derivation of GATE27 (GPT R45) figures/identities.
Each block has a planted control that must be caught (reported as CAUGHT)."""
import itertools, random
import sympy as sp
res = []
def rec(tag, ok): res.append((tag, ok)); print(("PASS " if ok else "FAIL ") + tag)
def ctl(tag, bad):  # planted control: 'bad' must be False (the wrong statement must not hold)
    res.append(("CONTROL " + tag, not bad)); print(("CAUGHT " if not bad else "MISSED ") + "control " + tag)

# N1 three-square figures (review §7)
N = 1 + 24*45**2
rec("N1 48601 == 1+24*45^2", N == 48601)
s = lambda v: sum(x*x for x in v)
rec("N1 wrong ex1 (-219,15,20) sums to 48586", s((-219,15,20)) == 48586)
rec("N1 wrong ex2 (-210,-19,64) sums to 48557", s((-210,-19,64)) == 48557)
rec("N1 (-199,-90,30) sums to 48601", s((-199,-90,30)) == N)
rec("N1 (-195,-24,100) sums to 48601", s((-195,-24,100)) == N)
rec("N1 first coords differ mod 5", (-199) % 5 != (-195) % 5)
ctl("N1 perturbed (-199,-90,31) sums to 48601", s((-199,-90,31)) == N)

# N2 transvections E_v, F_v on Q = alpha*beta + q(w), q generic on W (dim 1,2,3)
t = sp.Symbol('t')
for dW in (1, 2, 3):
    Ws = sp.symbols(f'w0:{dW}'); Vs = sp.symbols(f'v0:{dW}')
    al, be = sp.symbols('alpha beta')
    G = sp.Matrix(dW, dW, lambda i, j: sp.Symbol(f'g{min(i,j)}{max(i,j)}'))  # generic symmetric Gram
    w = sp.Matrix(Ws); v = sp.Matrix(Vs)
    q = lambda x: (x.T*G*x)[0]
    bq = lambda x, y: (x.T*G*y)[0]           # half-polar: q(x+y)-q(x)-q(y) = 2 bq
    rec(f"N2 dW={dW} half-polar identity", sp.expand(q(w+v)-q(w)-q(v)-2*bq(w,v)) == 0)
    Q = lambda a, b, x: a*b + q(x)
    Ea = al - 2*t*bq(w,v) - t**2*be*q(v); Eb = be; Ew = w + t*be*v
    Fa = al; Fb = be - 2*t*bq(w,v) - t**2*al*q(v); Fw = w + t*al*v
    rec(f"N2 dW={dW} E_v preserves Q", sp.expand(Q(Ea,Eb,Ew) - Q(al,be,w)) == 0)
    rec(f"N2 dW={dW} F_v preserves Q", sp.expand(Q(Fa,Fb,Fw) - Q(al,be,w)) == 0)
    rec(f"N2 dW={dW} E_v,F_v identity at t=0",
        all(sp.simplify(e.subs(t,0) - o) == 0 for e, o in [(Ea,al),(Fb,be)]) and (Ew.subs(t,0)-w) == sp.zeros(dW,1))
    # (★): output p = A*alpha + B*beta + ell.w ; coefficients of t, t^2 of p(E(t)) - p(x)
    A, B = sp.symbols('A B'); ell = sp.Matrix(sp.symbols(f'l0:{dW}'))
    p = lambda a, b, x: A*a + B*b + (ell.T*x)[0]
    dE = sp.Poly(sp.expand(p(Ea,Eb,Ew) - p(al,be,w)), t); dF = sp.Poly(sp.expand(p(Fa,Fb,Fw) - p(al,be,w)), t)
    star = [(dE.coeff_monomial(t**2), -A*be*q(v)), (dE.coeff_monomial(t), -2*A*bq(w,v) + be*(ell.T*v)[0]),
            (dF.coeff_monomial(t**2), -B*al*q(v)), (dF.coeff_monomial(t), -2*B*bq(w,v) + al*(ell.T*v)[0])]
    rec(f"N2 dW={dW} (★) four coefficient equations", all(sp.expand(a-b) == 0 for a, b in star)
        and dE.degree() <= 2 and dF.degree() <= 2)
    Ebad = al + 2*t*bq(w,v) - t**2*be*q(v)   # planted: wrong sign of the linear term
    ctl(f"N2 dW={dW} sign-flipped E_v preserves Q", sp.expand(Q(Ebad,Eb,Ew) - Q(al,be,w)) == 0)

# N3 factor scaling in split rank 2: Q(XU+YV)=XY; Z=c+p+F v, Z'=c+lam p+(F/lam) v
X0, lam, Fk, K = sp.symbols('X0 lam F K', nonzero=True)
U = sp.Matrix(sp.symbols('u0 u1')); V = sp.Matrix(sp.symbols('V0 V1'))
Dd = sp.Symbol('D', nonzero=True)
pvec = X0*U; vvec = V/Dd
Z = pvec + Fk*vvec; Zp = lam*pvec + (Fk/lam)*vvec
# coordinates wrt (U,V): X = coefficient on U, Y on V
XY = lambda cU, cV: cU*cV
rec("N3 factor scaling preserves XY", sp.simplify(XY(lam*X0, Fk/(lam*Dd)) - XY(X0, Fk/Dd)) == 0)
diff = Zp - Z; claimed = ((lam-1)/K)*(K*pvec - (Fk/lam)*(K*vvec))
rec("N3 Z'-Z = ((lam-1)/K)[K p - (F/lam) K v]", sp.simplify(diff - claimed) == sp.zeros(2,1))
claimed_bad = ((lam+1)/K)*(K*pvec - (Fk/lam)*(K*vvec))
ctl("N3 (lam+1) variant equals Z'-Z", sp.simplify(diff - claimed_bad) == sp.zeros(2,1))
# integrality on a concrete instance: lam=q^h ≡ 1 mod K, K p, K v integral, lam | F  -> Z'-Z integral
Kc = 3; qc = 5; h = 2; lamc = qc**h   # 25 ≡ 1 mod 3
pc = sp.Matrix([sp.Rational(2,3), sp.Rational(-1,3)]); vc = sp.Matrix([sp.Rational(1,3), sp.Rational(5,3)])
ok = True
for Fv in range(-5*lamc, 5*lamc+1, lamc):
    d = (lamc-1)*pc - sp.Rational(Fv*(lamc-1), lamc)*vc
    ok &= all(x.is_integer for x in d)
rec("N3 concrete instance: Z'-Z integral for all F in lam*Z (K=3, lam=25)", ok)
lamb = 5  # planted: 5 ≢ 1 mod 3
d = (lamb-1)*pc - 0*vc
ctl("N3 lam=5 (not ≡1 mod K) keeps integrality", all(x.is_integer for x in d))

# N4 D3 controls
box = range(-60, 61)
sol1 = [(b,u) for b in box for u in box if b*(2*u+1) == 0]
rec("N4 b(2u+1)=0: every solution in box has b=0 (output unique)", all(b == 0 for b,u in sol1) and len(sol1) == len(box))
b_, u_ = sp.symbols('b u')
rec("N4 b(2u+1): Q=2bu, centre (0,-1/2), R=0", sp.expand(b_*(2*u_+1) - 2*b_*(u_+sp.Rational(1,2))) == 0)
sol2 = [(b,u) for b in box for u in box if (4*b+1)*(4*u+1) == 1]
rec("N4 (4b+1)(4u+1)=1: only (0,0) in box", sol2 == [(0,0)])
rec("N4 (4b+1)(4u+1)-1 = 16(b+1/4)(u+1/4) - 1 (Q=16bu, R=1)",
    sp.expand((4*b_+1)*(4*u_+1) - 1 - (16*(b_+sp.Rational(1,4))*(u_+sp.Rational(1,4)) - 1)) == 0)
sol3 = [(b,u) for b in box for u in box if (2*b+1)*(2*u+1) == 1]
ctl("N4 (2b+1)(2u+1)=1 has only (0,0)", sol3 == [(0,0)])

# N5 prime-power roots for nonconstant F, deg<=2 (examples of the three cases), lam=q^h ≡ 1 mod K
def roots_mod(Fp, m): return [x for x in range(m) if Fp(x) % m == 0]
cases = [("deg1 F=6t+4, K=4 (q=5)", lambda x: 6*x+4, 5, 4),
         ("deg2 disc!=0 F=t^2+1, K=3 (q=5)", lambda x: x*x+1, 5, 3),
         ("deg2 disc=0 F=(2t+1)^2, K=7 (q=3)", lambda x: (2*x+1)**2, 3, 7)]
for name, Fp, qc, Kc in cases:
    ok = all(len(roots_mod(Fp, qc**hh)) > 0 for hh in range(1, 6))
    hK = next(hh for hh in range(1, 50) if pow(qc, hh, Kc) == 1)
    rec(f"N5 {name}: roots mod q^h for h=1..5; q^{hK} ≡ 1 mod K", ok and qc**hK > 1)
ctl("N5 F=t^2+1 has a root mod 3", len(roots_mod(lambda x: x*x+1, 3)) > 0)

# N6 Conclusion I sanity (NOT a proof): isotropic nondegenerate rank 3 fibers are not output-unique.
# Q = alpha*beta + w^2 with output = alpha: fiber alpha*beta + w^2 = r, integer solutions with >=2 alpha values.
multi = all(len({a for a in range(-30,31) for b_i in range(-30,31) for w_i in range(-30,31) if a*b_i + w_i*w_i == r}) >= 2
            for r in range(-10, 11))
rec("N6 finite sanity: alpha*beta+w^2=r (|r|<=10) has >=2 outputs alpha in box", multi)
ctl("N6 anisotropic alpha^2+beta^2+w^2 = 0 has >=2 outputs", len({a for a in range(-5,6) for b_i in range(-5,6)
    for w_i in range(-5,6) if a*a+b_i*b_i+w_i*w_i == 0}) >= 2)

npass = sum(1 for _, ok in res if ok)
print(f"LEG1_SUMMARY {npass}/{len(res)}  CONTROLS_CAUGHT {sum(1 for tg, ok in res if tg.startswith('CONTROL') and ok)}/{sum(1 for tg, _ in res if tg.startswith('CONTROL'))}")
