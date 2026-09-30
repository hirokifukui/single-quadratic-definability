# s61 GATE31 CAS leg 2 (Sage). Clone of s60 leg2_sage_s60.sage (c5e3f80f): same harness, checks replaced.
# Independent of leg 1: polynomial rings over QQ/ZZ, lagrange_polynomial, explicit enumeration by norm,
# integer-valued-polynomial criteria; tuples compared (s59 trap 4). Plants MUST be caught.
R_ = []
def rec(tag, ok):
    R_.append((tag, bool(ok))); print(("PASS " if ok else "FAIL ") + tag)
S.<A,Bv,Uv> = PolynomialRing(ZZ)
F3 = (3*Bv - A + 1)^2 + Uv^2 - 1
# N1: enumerate ALL integer solutions (b,u) for each a by bounding: (3b-a+1)^2<=1 and u^2<=1 are forced,
# so search b over the whole interval |3b-a+1|<=1 derived independently, u in {-1,0,1} -- then compare tuples.
def all_sols(P, t):
    out = []
    for bb in range(floor((t-2)/3) - 2, ceil(t/3) + 3):
        for uu in range(-3, 4):
            if P(t, bb, uu) == 0: out.append((bb, uu))
    return tuple(sorted(out))
ok = True
for t in range(-300, 301):
    q, r = t // 3, t % 3
    exp = ((q, -1), (q, 1)) if r == 1 else ((q, 0),)
    ok = ok and all_sols(F3, t) == exp
rec("N1 full solution tuples of (3b-a+1)^2+u^2=1 = ((q,+-1)) if r=1 else ((q,0)); a in [-300,300]", ok)
rec("N1c a=1: solutions ((0,-1),(0,1)) -> two witnesses", all_sols(F3, 1) == ((0, -1), (0, 1)))
rec("N1d total degree 2", F3.total_degree() == 2)
# N1e bounding argument used by N1 is sound: u^2<=1 and (3b-a+1)^2<=1 for any real zero (sum of squares = 1)
Rq.<w,z> = PolynomialRing(QQ)
rec("N1e w^2+z^2=1 over ZZ has exactly the 4 solutions (+-1,0),(0,+-1)",
    tuple(sorted((W, Z) for W in range(-5, 6) for Z in range(-5, 6) if W^2 + Z^2 == 1)) == ((-1, 0), (0, -1), (0, 1), (1, 0)))
# N4: Lagrange interpolation through floor at 0,1,2 is zero; value at 3 is 0 != 1
Px.<X> = PolynomialRing(QQ)
Lp = Px.lagrange_polynomial([(0, 0), (1, 0), (2, 0)])
rec("N4 Lagrange poly through (0,0),(1,0),(2,0) is 0 (degree<=2 uniqueness), so value 0 at 3 != 1", Lp == 0)
rec("N4b no degree<=2 poly through (0,0),(1,0),(2,0),(3,1): Lagrange of 4 points has degree 3",
    Px.lagrange_polynomial([(0, 0), (1, 0), (2, 0), (3, 1)]).degree() == 3)
# N5: parity family. For every odd p, c and x in {0,1} with p x + c even: 2(floor((x+6)/3)-floor(x/3)) = 4 vs 6p
ok5 = True
for p in range(-31, 32, 2):
    for c in range(-8, 9):
        xs = tuple(X0 for X0 in (0, 1) if (p*X0 + c) % 2 == 0)
        ok5 = ok5 and len(xs) == 1 and ((p*(xs[0]+6) + c) - (p*xs[0] + c)) == 6*p and 2*(floor((xs[0]+6)/3) - floor(xs[0]/3)) == 4 and 6*p != 4
rec("N5 odd p: unique even point in {0,1}; 6p vs 4 never equal (p in [-31,31] odd)", ok5)
rec("N5e 6p=4: gcd(6) does not divide 4", gcd(6, 4) == 2 and (4 % 6 != 0))
# N6 integrality (A §4): integer-valued affine on Z^2 <=> integer coefficients (binomial basis criterion)
ok6 = True
for s_ in [QQ(k)/6 for k in range(-6, 7)]:
    for l1 in [QQ(k)/6 for k in range(-6, 7)]:
        iv = all((s_ + l1*Xv) in ZZ for Xv in range(-3, 4))
        ok6 = ok6 and iv == (s_ in ZZ and l1 in ZZ)
rec("N6 affine s + l x integer-valued on Z <=> s,l in ZZ (s,l in (1/6)Z grid)", ok6)
# N7 common slope of floor(a/3)
rec("N7 floor((a+3t)/3) = floor(a/3)+t", all(floor((a0+3*t0)/3) == floor(a0/3) + t0 for a0 in range(-60, 61) for t0 in range(-10, 11)))
# N8 regression: scaled identity by factorisation
P6 = (6*Bv - 3*A)*(6*Bv + 9*A - 3); P2 = (2*Bv - A)*(2*Bv + 3*A - 1)
rec("N8a P6 == 9*P2 and content(P6)=9", P6 == 9*P2 and P6.content() == 9)
Rt.<At,Bt> = PolynomialRing(ZZ)
rec("N8b (2b-2a)^2 factors as 4*(a-b)^2", ((2*Bt - 2*At)^2).factor() == (4*(At - Bt)^2).factor())
# ---- planted controls ----
pl = []
Fbad = (3*Bv - A)^2 + Uv^2 - 1
pl.append(("PLANT1 (3b-a)^2+u^2=1 claimed = floor(a/3)", all(tuple(sorted(set(s[0] for s in all_sols(Fbad, t)))) == (t//3,) for t in range(-12, 13))))
pl.append(("PLANT2 a=1 witness tuple claimed ((0,0),)", all_sols(F3, 1) == ((0, 0),)))
pl.append(("PLANT3 Lagrange through (0,0),(1,0),(2,0),(3,1) claimed degree <= 2", Px.lagrange_polynomial([(0, 0), (1, 0), (2, 0), (3, 1)]).degree() <= 2))
pl.append(("PLANT4 6p=4 claimed solvable (p=2/3 claimed integer)", QQ(4)/6 in ZZ))
pl.append(("PLANT5 affine (x+1)/2 claimed integer-valued", all((QQ(Xv) + 1)/2 in ZZ for Xv in range(-5, 6))))
caught = 0
for tag, claim in pl:
    if claim: print("PLANT_NOT_CAUGHT " + tag)
    else:
        caught += 1; print("PLANT_CAUGHT " + tag)
npass = sum(1 for _, o in R_ if o)
print("LEG2_SAGE checks %d/%d PASS; plants caught %d/%d; sage %s" % (npass, len(R_), caught, len(pl), version()))
print("LEG2_EXIT=", 0 if npass == len(R_) and caught == len(pl) else 1)
