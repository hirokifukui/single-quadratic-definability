# rederive_gate24_s54.sage -- s54 Phase-2c leg 2 (Sage).  Different methods from leg 1:
#  * box counts via generating polynomials: prod_j (sum_s X^{(k s - eta_j)^2}), coefficient sums
#  * centre / Pell via Sage matrices over QQ (kernel, polar Gram)
#  * norm lift in a multivariate polynomial ring over a fraction field; concrete case factored
#    by Sage's own factorisation, and a random family of instances
CH = []
def check(name, cond):
    CH.append((name, bool(cond)))
    print(("PASS " if cond else "FAIL ") + name)

# G1 growth lemma
def concl(c, s, B, C, K):
    return (not (c*s^2 <= B*s + C and C <= K^2)) or s <= B + K
check("G1a integer c=0,s=2,B=0,C=K=1 breaks the unhypothesised lemma", not concl(0,2,0,1,1))
check("G1b rational c=1/4 breaks it too", not concl(QQ(1)/4,2,0,1,1))
check("G1c Lean hypotheses: no violation, c<=6 s<=15 B,K<=8",
      all(concl(c,s,B,C,K) for c in [1..6] for s in [0..15] for B in [0..8] for K in [0..8]
          for C in [-3..K^2]))

# G2 centre via Gram matrix: Q=x^2, Gram of polar form = [2]
G = matrix(QQ, [[2]])
check("G2a radical = kernel of polar Gram = 0", G.right_kernel().dimension() == 0)
ell = vector(QQ, [0])
# IsCentre c  <=>  G*c + ell = 0
check("G2b c=1 is not a centre", G*vector(QQ,[1]) + ell != 0)
check("G2c the unique centre is 0", G.solve_right(-ell) == vector(QQ,[0]))

# G3 box radius
check("G3 f(a)=a+1 has |f(0)|=1 > C*0 with C=1, but <= C*(1+0)", abs(0+1) > 0 and abs(0+1) <= 1)

# G4 Pell: Gram of polar of b^2-2u^2 is diag(2,-4); output coordinate is index 0
Gp = diagonal_matrix(QQ, [2, -4]); v = vector(QQ, [1, 0])
W = matrix(QQ, [v*Gp]).right_kernel()          # vectors polar-orthogonal to v
check("G4a orthogonal complement of v is spanned by (0,1)", W.basis() == [vector(QQ,[0,1])])
w = W.basis()[0]
check("G4b it has opposite sign and zero output coordinate",
      (w*Gp*w/2)*(v*Gp*v/2) < 0 and w[0] == 0)
check("G4c v has nonzero output coordinate", v[0] != 0)

# G5 Ex
check("G5a (3b-a)^2<=1 -> unique b = floor((a+1)/3), |a|<=60",
      all([b for b in [-40..40] if (3*b-a)^2 <= 1] == [floor((a+1)/3)] for a in [-60..60]))
check("G5b comment version differs somewhere",
      any([b for b in [-40..40] if (3*b-a-1)^2 <= 1] != [floor((a+1)/3)] for a in [-60..60]))

# G6 N4 via Sage roots in b
Rb.<bb> = ZZ[]
def n4roots(a):
    return sorted(r for r, _ in ((2*bb - a)*(2*bb + 3*a - 1)).roots(ring=ZZ))
def n4f(a):
    return a//2 if a % 2 == 0 else (1 - 3*a)//2
check("G6 N4 total/OU with the two affine branches, |a|<=80",
      all(n4roots(a) == [n4f(a)] for a in [-80..80]))

# G7 GAP via generating polynomials
PX.<X> = ZZ[]
RMAX = 200
def coord_poly(k, e):
    lim = isqrt(RMAX)//k + 2
    return sum(X^((k*s - e)^2) for s in [-lim..lim+1] if (k*s - e)^2 <= RMAX)
def count_table(k, eta):
    p = prod(coord_poly(k, e) for e in eta)
    cs = p.list()
    out = []; acc = 0
    for R0 in range(RMAX+1):
        acc += cs[R0] if R0 < len(cs) else 0
        out.append(acc)
    return out
def pred(k, eta, R0):
    dl = [min(e, k-e) for e in eta]
    d = sum(t^2 for t in dl); g = min(k*(k-2*t) for t in dl)
    return d <= R0 < d + g
cases = 0; bad = 0
for k in [1..9]:
    for m in [1..3]:
        for eta in cartesian_product([range(k)]*m):
            eta = tuple(eta); cases += 1
            tab = count_table(k, eta)
            dl = [min(e, k-e) for e in eta]
            top = sum(t^2 for t in dl) + k^2 + 2
            for R0 in range(-1, top):
                one = (tab[R0] == 1) if R0 >= 0 else False
                bad += (one != pred(k, eta, R0))
check("G7a 2355 residue cases", cases == 2355)
check("G7b #S_eta=1 <-> d<=R0<d+g (generating-polynomial count)", bad == 0)
# planted control: the 'distinct distances' reading must disagree somewhere
ctl_bad = 0
for k in [2..5]:
    for eta in cartesian_product([range(k)]*2):
        eta = tuple(eta)
        cs = prod(coord_poly(k, e) for e in eta).list()
        distinct = [i for i, cf in enumerate(cs) if cf]
        d0 = distinct[0]; d1 = distinct[1]
        tab = count_table(k, eta)
        for R0 in range(0, d1 + 2):
            wrong = d0 <= R0 < d1              # ignores multiplicity at the nearest distance
            ctl_bad += (wrong != (tab[R0] == 1))
check("G7ctl planted 'distinct distance values' reading is caught", ctl_bad > 0)

# G8 full-residue thresholds
def full_ok(k, m, R0):
    return all(count_table(k, tuple(eta))[R0] == 1 for eta in cartesian_product([range(k)]*m)) if R0 >= 0 else False
def predicted(k, m, R0):
    if k == 1: return R0 == 0
    if k % 2 == 0: return False
    h = (k-1)//2
    return m*h^2 <= R0 < (h+1)^2
mism = [(k,m,R0) for k in [1..7] for m in ([1..4] if k <= 3 else [1..3])
        for R0 in range(-1, (k//2+1)^2 + 3) if full_ok(k,m,R0) != predicted(k,m,R0)]
check("G8a thresholds match (k<=7)", mism == [])
check("G8b k=3,m=3,R0=3", full_ok(3,3,3))
check("G8c k=3,m=4 none", not any(full_ok(3,4,R0) for R0 in [0..11]))
check("G8d k=5,m=2,R0=8", full_ok(5,2,8))

# G9 controls
def fo(k, R):
    return [b for b in [-50..50] if (k*b)^2 <= R]
check("G9a/b k=2, R=a(a-1): a=0,1 unique, a=3 triple",
      fo(2, 0*(0-1)) == [0] and fo(2, 1*(1-1)) == [0] and fo(2, 3*(3-1)) == [-1,0,1])
check("G9c k=3, R=a mod 2: f=0 total OU, R takes two values",
      all(fo(3, a % 2) == [0] for a in [-40..40]) and len(set(a % 2 for a in [0..3])) == 2)

# G10 norm lift in a polynomial ring over a fraction field
K = FractionField(PolynomialRing(QQ, 'D,r0,s0,l0,l1,l2,h0,h1,h2'))
D, r0, s0, l0, l1, l2, h0, h1, h2 = K.gens()
S.<x0,x1,x2> = K[]
ellp = l0*x0 + l1*x1 + l2*x2; hp = h0*x0 + h1*x1 + h2*x2
c = r0^2 + D*s0^2
A = c + ellp
Hp = (D*hp^2 + ellp^2)/c
Rp = c + 2*ellp + Hp
r = (r0*A - D*s0*hp)/c; s = (s0*A + r0*hp)/c
check("G10a c*R = (c+ell)^2 + D h^2", c*Rp == A^2 + D*hp^2)
check("G10b r^2 + D s^2 = R", r^2 + D*s^2 == Rp)
check("G10c basepoint", r(0,0,0) == r0 and s(0,0,0) == s0)
T.<tt> = K[]
lv = ellp(1,2,3); Hv = Hp(1,2,3); hv = hp(1,2,3)
check("G10d discriminant along v=(1,2,3) equals -D(2h(v))^2", (2*lv)^2 - 4*c*Hv == -D*(2*hv)^2)
# random concrete instances: R = norm of random affine forms, base 0, all representations of c
set_random_seed(54)
Z.<a1,a2,a3> = QQ[]
ok = True; tried = 0; multi = 0
for trial in range(40):
    Dv = ZZ.random_element(1, 6)
    rr0 = sum(ZZ.random_element(-3,4)*g for g in Z.gens()) + ZZ.random_element(1,6)
    ss0 = sum(ZZ.random_element(-3,4)*g for g in Z.gens()) + ZZ.random_element(0,4)
    Rz = rr0^2 + Dv*ss0^2
    cv = ZZ(Rz(0,0,0))
    if cv == 0: continue
    lin = sum(Rz.derivative(g)(0,0,0)*g for g in Z.gens())/2
    quad = Rz - cv - 2*lin
    Tz = (cv*quad - lin^2)/Dv
    F = Tz.factor()
    if Tz != 0:
        facs = list(F)
        if not (all(e % 2 == 0 for _, e in facs) and F.unit() > 0 and F.unit().is_square()):
            ok = False; break
        hz = F.unit().sqrt()*prod(b^(e//2) for b, e in facs)
    else:
        hz = Z(0)
    reps = [(p,q) for p in [-isqrt(cv)..isqrt(cv)] for q in [-isqrt(cv)..isqrt(cv)] if p^2 + Dv*q^2 == cv]
    multi += (len(reps) > 2)
    for (p,q) in reps:
        tried += 1
        rz = (p*(cv+lin) - Dv*q*hz)/cv; sz = (q*(cv+lin) + p*hz)/cv
        if rz^2 + Dv*sz^2 != Rz or rz(0,0,0) != p or sz(0,0,0) != q:
            ok = False
check("G10e random instances (40 seeds): T is a square, and the section passes through EVERY integer representation of R(0)", ok and tried > 0)
print("G10e_reps_tried=%d instances_with_extra_reps=%d" % (tried, multi))

npass = sum(1 for _, o in CH if o)
print("CHECKS=%d PASS=%d FAIL=%d" % (len(CH), npass, len(CH) - npass))
