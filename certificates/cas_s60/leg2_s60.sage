# s60 GATE30 CAS leg 2 (Sage). Independent of leg 1: polynomial rings over QQ/ZZ, factorisation,
# explicit lattice enumeration; tuples compared (s59 trap 4). Plants MUST be caught.
R_ = []
def rec(tag, ok):
    R_.append((tag, bool(ok))); print(("PASS " if ok else "FAIL ") + tag)
Rg.<a,b,u,y,al,s,l1,l2,x1,x2,d,b1,b2,g,p1,p2,E11,E12,E22> = PolynomialRing(QQ)
B = b1*x1+b2*x2+d; T = E11*x1^2+E12*x1*x2+E22*x2^2+p1*x1+p2*x2+g
Pn = al*y^2+B*y+T; L = l1*x1+l2*x2+s; Delta = B^2-4*al*T
rec("M1 two-root identity", 4*al*Pn-(2*al*y-(-B+L))*(2*al*y-(-B-L)) == L^2-Delta)
S.<A,Bv,Uv> = PolynomialRing(ZZ)
def roots_b(P, t):
    Q = P.subs(A=t).univariate_polynomial() if P.subs(A=t).degree() > 0 else None
    if Q is None: return None
    return tuple(sorted(set(r for r, m in Q.change_ring(QQ).roots() if r in ZZ)))
def parityFn(x): return x//2 if x % 2 == 0 else (1-3*x)//2
P6 = (6*Bv-3*A)*(6*Bv+9*A-3); P2 = (2*Bv-A)*(2*Bv+3*A-1)
rec("M2a scaled identity (factor)", P6 == 9*P2 and P6.factor().unit()*prod(f^e for f, e in P6.factor()) == P6)
rec("M2b P6 total/unique = parityFn on [-150,150]", all(roots_b(P6, t) == (parityFn(t),) for t in range(-150, 151)))
rec("M3 (2b-2a)^2 -> (a,)", all(roots_b((2*Bv-2*A)^2, t) == (t,) for t in range(-150, 151)))
rec("M4 (3b-3a)(3b-3a-1) -> (a,)", all(roots_b((3*Bv-3*A)*(3*Bv-3*A-1), t) == (t,) for t in range(-150, 151)))
rec("M5a (2b-a)(2b-a-2) at 0 -> (0,1)", roots_b((2*Bv-A)*(2*Bv-A-2), 0) == (0, 1))
rec("M5b (3b-a)(3b-a+1) at 2 -> ()", roots_b((3*Bv-A)*(3*Bv-A+1), 2) == ())
F3 = (3*Bv-A+1)^2+Uv^2-1
ok = True
for t in range(-45, 46):
    sols = tuple((bb, uu) for bb in range(-25, 26) for uu in range(-3, 4) if F3(t, bb, uu) == 0)
    bs = tuple(sorted(set(p[0] for p in sols)))
    ws = tuple(sorted(p[1] for p in sols))
    ok = ok and bs == (floor(t/3),) and ws == ((-1, 1) if t % 3 == 1 else (0,))
rec("M6 floor(a/3) one-witness, witness sets", ok)
rec("M6b total degree 2", F3.degree() == 2)
Qr.<z> = QQ[]
q = Qr.lagrange_polynomial([(0, 0), (1, 0), (2, 0)])
rec("M7 unique quadratic through (0,0),(1,0),(2,0) is 0; floor(1)=1 at a=3", q == 0 and floor(3/3) == 1)
K.<c2,c1,c0> = QQ[]
Za.<w> = K[]
qq = c2*w^2+c1*w+c0
I = K.ideal(list((qq(w+3)-qq(w)-1).coefficients(sparse=False)) + [c0])
V = I.variety()
rec("M7a forces (c2,c1,c0)=(0,1/3,0)", len(V) == 1 and (V[0][c2], V[0][c1], V[0][c0]) == (0, 1/3, 0))
rec("M8 3p=2 unsolvable in ZZ; floor shift 6 = 2", (2 % 3 != 0) and all(floor((t+6)/3)-floor(t/3) == 2 for t in range(-60, 61)))
sq = set(i^2+j^2+k^2+m^2 for i in range(15) for j in range(15) for k in range(15) for m in range(15))
rec("M9 four squares 0..200", all(N in sq for N in range(201)))
Mv = var('Mv'); av = var('av')
rec("M10 (a+M)^2-a^2 not constant in a", diff(expand((av+Mv)^2-av^2), av) == 2*Mv)
reps = [tuple(2*c for c in v) for v in cartesian_product([range(-2, 3)]*3) if sum(c^2 for c in v) == 1]
rec("M11 N=4 on 2Z^3: 6 reps, gcd 2", len(reps) == 6 and all(gcd(list(r)) == 2 for r in reps))
# plants
pl = [("PLANT1 scale 8", P6 == 8*P2),
      ("PLANT2 (3b-a)^2+u^2=1 = floor", all(tuple(sorted(set(bb for bb in range(-25, 26) for uu in range(-3, 4) if ((3*Bv-A)^2+Uv^2-1)(t, bb, uu) == 0))) == (floor(t/3),) for t in range(-12, 13))),
      ("PLANT3 (3b-a)(3b-a+1) total", all(len(roots_b((3*Bv-A)*(3*Bv-A+1), t)) > 0 for t in range(-12, 13)))]
c = 0
for tag, claim in pl:
    if claim: print("PLANT_NOT_CAUGHT " + tag)
    else: c += 1; print("PLANT_CAUGHT " + tag)
n = sum(1 for _, o in R_ if o)
print("LEG2_SAGE checks %d/%d PASS; plants caught %d/%d; %s" % (n, len(R_), c, len(pl), version()))
print("LEG2_EXIT=", 0 if (n == len(R_) and c == len(pl)) else 1)
