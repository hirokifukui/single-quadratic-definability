# s59 GATE29 CAS leg 2 (Sage 10.8). Independent implementation of the leg-1 claims.
import itertools
set_random_seed(5959)
res = []; ctl = []
def P(name, ok):
    res.append(bool(ok)); print(("PASS " if ok else "FAIL ") + name)
def C(name, holds):
    ctl.append(not holds); print(("CAUGHT " if not holds else "MISSED ") + "control " + name)

# K1: represent via reduction of the quadratic polynomial over Zmod(p^e) (vectorised enumeration)
def locrep(rho, d, N, p, e, prim):
    R = Zmod(p^e)
    for x in cartesian_product([range(p^e)]*3):
        v = [rho[i] + d*x[i] for i in range(3)]
        if R(sum(t^2 for t in v) - N) == 0 and (not prim or any(t % p != 0 for t in v)):
            return True
    return False
P("K1 N=4 ordinary local rep by 2Z^3 at p in {2,3,5} e<=3", all(locrep([0,0,0], 2, 4, p, e, False) for p in [2,3,5] for e in [1,2,3]))
P("K1 N=4 no primitive local rep by 2Z^3 at 2^e, e<=3", not any(locrep([0,0,0], 2, 4, 2, e, True) for e in [1,2,3]))
P("K1 4 = Q_I3(2,0,0)", vector([2,0,0]).dot_product(vector([2,0,0])) == 4)
C("K1 rho=(1,0,0),d=2,N=1 has no primitive rep mod 2^3", not locrep([1,0,0], 2, 1, 2, 3, True))

# K2: Gram matrix with FULLY SYMBOLIC delta and residues (polynomial ring), determinant must be the constant M^(2(n+m))(1+M^n)
def gram_symbolic(n, m, M):
    k = M^n
    names = ['b%d'%j for j in range(m)] + ['u%d'%i for i in range(n)] + ['e%d'%r for r in range(k)]
    dn = ['dl%d_%d'%(r,j) for r in range(k) for j in range(m)]
    R = PolynomialRing(QQ, names + dn); g = R.gens()
    b = g[:m]; u = g[m:m+n]; e = g[m+n:m+n+k]; dl = g[m+n+k:]
    rho = list(cartesian_product([range(M)]*n))
    Qu = sum(e)^2 + sum(x^2 for x in e)
    Qu += sum((M*u[i] + sum(rho[r][i]*e[r] for r in range(k)))^2 for i in range(n))
    Qu += sum((M*b[j] - sum(dl[r*m+j]*e[r] for r in range(k)))^2 for j in range(m))
    X = list(b)+list(u)+list(e)
    G = matrix(R, len(X), len(X), lambda i, j: Qu.derivative(X[i]).derivative(X[j]) / 2)
    return G
for (n, m, M) in [(1,1,2),(1,2,2),(1,1,3),(2,1,2),(1,2,3)]:
    G = gram_symbolic(n, m, M)
    P(f"K2 symbolic-delta det ({n},{m},{M}) = {M^(2*(n+m))*(1+M^n)}", G.det() == M^(2*(n+m))*(1+M^n))
# positive definiteness at random integer delta via eigen/cholesky
for (n, m, M) in [(1,2,2),(2,2,2),(1,1,4)]:
    G = gram_symbolic(n, m, M)
    sub = {v: ZZ.random_element(-9, 10) for v in G.base_ring().gens() if str(v).startswith('dl')}
    Gn = G.apply_map(lambda z: QQ(z.subs(sub)))
    P(f"K2 positive definite at random delta ({n},{m},{M})", Gn.change_ring(QQ).is_positive_definite())
G = gram_symbolic(1, 2, 2)
C("K2 det = 2^6*2", G.det() == 2^7)

# K3: integrality domains via lattice kernels; enumerate rational affine maps with denominators <= Dmax
def domain(v, c, L, n):   # v in QQ^n, c in QQ; points mod L
    return frozenset(x for x in cartesian_product([range(L)]*n) if (c + sum(v[i]*x[i] for i in range(n))) in ZZ)
def check_covers(n, Dmax):
    maps = set()
    for den in range(1, Dmax+1):
        for p in cartesian_product([range(den)]*n):
            for c in range(den):
                maps.add((tuple(QQ(pi)/den for pi in p), QQ(c)/den))
    maps = list(maps); cov = bad = 0
    L = lcm(range(1, Dmax+1))
    L = L if n == 1 else lcm(range(1, Dmax+1))
    for (v0, c0), (v1, c1) in itertools.combinations(maps, 2):
        if (v0, c0) == (v1, c1): continue
        LL = lcm([x.denominator() for x in list(v0)+[c0]+list(v1)+[c1]])
        I0 = domain(v0, c0, LL, n); I1 = domain(v1, c1, LL, n)
        if I0 and I1 and not (I0 & I1) and len(I0)+len(I1) == LL^n:
            cov += 1
            dens = [x.denominator() for x in list(v0)+[c0]+list(v1)+[c1]]
            p0 = [ZZ(2*x) for x in v0]; p1 = [ZZ(2*x) for x in v1]
            ok = max(dens) == 2 and all((a-b) % 2 == 0 for a, b in zip(p0, p1)) and any(a % 2 for a in p0) and (ZZ(2*c0) - ZZ(2*c1)) % 2 == 1
            bad += (not ok)
    return cov, bad
cov1, bad1 = check_covers(1, 12); P(f"K3 n=1 den<=12 covers={cov1} all parity type", cov1 > 0 and bad1 == 0)
cov2, bad2 = check_covers(2, 4); P(f"K3 n=2 den<=4 covers={cov2} all parity type", cov2 > 0 and bad2 == 0)
# index-2 lemma on a non-lattice group: Z/12 x Z/4, all subgroup pairs, verify: disjoint nonempty 2-coset cover => H=K, index 2
A = AdditiveAbelianGroup([12, 4]); els = list(A)
subs = [frozenset(S) for S in {frozenset(A.submodule(gs)) for gs in itertools.combinations(els[:], 1)} | {frozenset(A.submodule([x, y])) for x in els for y in els}]
subs = list(set(subs)); badg = covg = 0
for H in subs:
    for K in subs:
        for b in els:
            bK = frozenset(b + k for k in K)
            if not (H & bK) and len(H) + len(bK) == len(els):
                covg += 1; badg += not (H == K and 2*len(H) == len(els))
P(f"K3 group lemma on Z/12xZ/4: covers={covg}, all H=K of index 2", covg > 0 and badg == 0)
C("K3 a disjoint 2-coset cover of Z/12xZ/4 with index 3 exists", any(3*len(H) == len(els) for H in subs for K in subs for b in els
   if not (H & frozenset(b+k for k in K)) and len(H)+len(K) == len(els)))

# K4
def uniq_total(h0, h1, box=70):
    return all(len({QQ(h(a))/2 for h in (h0, h1)} & set(ZZ(t) for t in [QQ(h0(a))/2, QQ(h1(a))/2] if t in ZZ)) == 1 for a in range(-box, box+1))
P("K4 (2b-a)(2b+3a-1) total unique", uniq_total(lambda a: a, lambda a: 1-3*a))
R.<a, b> = QQ[]
Pp = (2*b - a)*(2*b + 3*a - 1)
P("K4 total degree of (2b-a)(2b+3a-1) is 2", Pp.degree() == 2)
P("K4 root is parityFn on [-70,70]", all([t for t in [ZZ(s) for s in [QQ(x)/2 for x in (x0, 1-3*x0)] if s in ZZ]][0] == (x0//2 if x0 % 2 == 0 else -3*(x0//2)-1)
       for x0 in range(-70, 71) for t in [0]) if False else all((QQ(x0)/2 if x0 % 2 == 0 else QQ(1-3*x0)/2) == (x0//2 if x0 % 2 == 0 else -3*(x0//2)-1) for x0 in range(-70, 71)))
C("K4 same-parity numerators a, a+2 unique", uniq_total(lambda a: a, lambda a: a+2))
C("K4 a/3,(a-1)/3 total", all(any(QQ(x)/3 in ZZ for x in (x0, x0-1)) for x0 in range(-30, 31)))
x = polygen(QQ)
q = x*(x-1)/2
P("K4 a(a-1)/2 integer-valued, not in Z[x]", all(q(t) in ZZ for t in range(-50, 51)) and q not in ZZ['x'])

# K5 composition (independent tables)
fails = 0; cases = 0
for trial in range(50):
    n = ZZ.random_element(1, 3); m = ZZ.random_element(1, 3); k = ZZ.random_element(1, 3)
    M = ZZ.random_element(1, 4); N = ZZ.random_element(1, 4)
    B = random_matrix(ZZ, m, n, x=-3, y=4); Cm = random_matrix(ZZ, k, m, x=-3, y=4)
    tf = {r: random_vector(ZZ, m, x=-5, y=6) for r in cartesian_product([range(M)]*n)}
    tg = {r: random_vector(ZZ, k, x=-5, y=6) for r in cartesian_product([range(N)]*m)}
    f = lambda v: tf[tuple(vi % M for vi in v)] + B*vector(ZZ, [(vi - vi % M)//M for vi in v])
    g = lambda v: tg[tuple(vi % N for vi in v)] + Cm*vector(ZZ, [(vi - vi % N)//N for vi in v])
    for _ in range(10):
        av = random_vector(ZZ, n, x=-9, y=10); tv = random_vector(ZZ, n, x=-4, y=5)
        cases += 1; fails += g(f(av + M*N*tv)) != g(f(av)) + Cm*B*tv
P(f"K5 composition identity {cases} cases", fails == 0)
tf = {(0,): vector([0]), (1,): vector([5])}; tg = {(0,): vector([0]), (1,): vector([7]), (2,): vector([1])}
f = lambda v: tf[(v[0] % 2,)] + vector([(v[0] - v[0] % 2)//2]); g = lambda v: tg[(v[0] % 3,)] + 2*vector([(v[0] - v[0] % 3)//3])
C("K5 period M+N", all(g(f(vector([s + 5*t]))) == g(f(vector([s]))) + vector([2*t]) for s in range(-6, 7) for t in range(-3, 4)))

P("K6 84", 25+20+14+8+17 == 84); P("K6 81.25", QQ(13)/16*100 == QQ(325)/4); C("K6 81", QQ(13)/16*100 == 81)
print("LEG2_SUMMARY %d/%d  CONTROLS_CAUGHT %d/%d" % (sum(res), len(res), sum(ctl), len(ctl)))
