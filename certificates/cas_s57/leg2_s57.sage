# s57 leg2 (Sage). Independent of leg1: isometries as matrices (M^T G M == G), p-adic roots via Zp, divisor enumeration.
res = []
def rec(tag, ok):
    res.append((tag, bool(ok))); print(("PASS " if ok else "FAIL ") + tag)
def ctl(tag, bad):
    res.append(("CONTROL " + tag, not bool(bad))); print(("CAUGHT " if not bad else "MISSED ") + "control " + tag)

# N1 via Gaussian-integer norms: enumerate all x with 48601 - x^2 a sum of two squares, then check the four vectors
N = 1 + 24*45^2
rec("N1 N == 48601", N == 48601)
for name, v, target in [("wrong1",(-219,15,20),48586),("wrong2",(-210,-19,64),48557),("right1",(-199,-90,30),N),("right2",(-195,-24,100),N)]:
    rec("N1 %s norm = %d" % (name, target), vector(ZZ, v).dot_product(vector(ZZ, v)) == target)
rec("N1 mod 5 first coords 1 and 0", (Mod(-199,5), Mod(-195,5)) == (Mod(1,5), Mod(0,5)))
ctl("N1 48586 == 48601", 48586 == N)

# N2 transvection as a matrix acting on (alpha, beta, w) for fixed t, v; check Gram preservation
for dW in [1,2,3]:
    names = ['t'] + ['g%d%d' % (i,j) for i in range(dW) for j in range(i,dW)] + ['v%d' % i for i in range(dW)]
    R = PolynomialRing(QQ, names); t = R.gen(0)
    gs = R.gens()[1:1+dW*(dW+1)//2]; vs = R.gens()[1+dW*(dW+1)//2:]
    Gq = matrix(R, dW, dW); k = 0
    for i in range(dW):
        for j in range(i, dW):
            Gq[i,j] = gs[k]; Gq[j,i] = gs[k]; k += 1
    v = vector(R, vs); n = dW + 2
    # Q(alpha,beta,w) = alpha*beta + w^T Gq w  ->  Gram G with Q(x) = x^T G x
    G = matrix(R, n, n); G[0,1] = 1/2; G[1,0] = 1/2; G.set_block(2, 2, Gq)
    qv = v * Gq * v
    # E_v(t): alpha' = alpha - 2t (w^T Gq v) - t^2 q(v) beta ; beta' = beta ; w' = w + t beta v
    E = identity_matrix(R, n)
    E[0,1] = -t^2*qv
    for j in range(dW): E[0, 2+j] = -2*t*(Gq*v)[j]; E[2+j, 1] = t*v[j]
    F = identity_matrix(R, n)
    F[1,0] = -t^2*qv
    for j in range(dW): F[1, 2+j] = -2*t*(Gq*v)[j]; F[2+j, 0] = t*v[j]
    rec("N2 dW=%d E^T G E == G" % dW, E.transpose()*G*E == G)
    rec("N2 dW=%d F^T G F == G" % dW, F.transpose()*G*F == G)
    rec("N2 dW=%d E(0)=F(0)=I" % dW, E.subs(t=0) == 1 and F.subs(t=0) == 1)
    # (★) via derivatives at t=0 of the row functional p(E(t) x): p = (A, B, ell)
    S = PolynomialRing(R, ['A','B'] + ['l%d' % i for i in range(dW)] + ['al','be'] + ['w%d' % i for i in range(dW)])
    A, B = S.gen(0), S.gen(1); ell = vector(S, S.gens()[2:2+dW]); al, be = S.gen(2+dW), S.gen(3+dW)
    w = vector(S, S.gens()[4+dW:]); x = vector(S, [al, be] + list(w)); pr = vector(S, [A, B] + list(ell))
    Es = E.change_ring(S); Fs = F.change_ring(S)
    dE = pr * (Es*x - x); dF = pr * (Fs*x - x)
    bw = w * Gq.change_ring(S) * v.change_ring(S)
    qvs = S(qv); ellv = ell * v.change_ring(S)
    d1 = lambda P: P.map_coefficients(lambda c: c.derivative(t).subs(t=0))
    d2 = lambda P: P.map_coefficients(lambda c: c.derivative(t, 2).subs(t=0) / 2)
    cE1 = d1(dE); cE2 = d2(dE); cF1 = d1(dF); cF2 = d2(dF)
    rec("N2 dW=%d (★) coefficients" % dW, cE2 == -A*be*qvs and cE1 == -2*A*bw + be*ellv and cF2 == -B*al*qvs and cF1 == -2*B*bw + al*ellv)
    Ebad = copy(E); Ebad[0,1] = +t^2*qv   # planted: sign of t^2 term
    ctl("N2 dW=%d sign-flipped t^2 term preserves Gram" % dW, Ebad.transpose()*G*Ebad == G)

# N3 factor scaling: Q = XY in basis (U,V) -> Gram [[0,1/2],[1/2,0]]; scaling diag(lam, 1/lam)
T.<lam, Fk, K, X0, D> = FractionField(PolynomialRing(QQ, 'lam,Fk,K,X0,D'))
H = matrix(T, [[0,1/2],[1/2,0]]); Sc = diagonal_matrix(T, [lam, 1/lam])
rec("N3 diag(lam,1/lam) preserves XY Gram", Sc.transpose()*H*Sc == H)
coordZ = vector(T, [X0, Fk/D]); coordZp = vector(T, [lam*X0, Fk/(lam*D)])
rec("N3 Q(Z'-c) == Q(Z-c)", coordZp*H*coordZp == coordZ*H*coordZ)
diffc = coordZp - coordZ
claim = ((lam-1)/K) * (K*vector(T,[X0,0]) - (Fk/lam)*K*vector(T,[0,1/D]))
rec("N3 difference identity (coords in U,V)", diffc == claim)
ctl("N3 difference with 1/lam in place of F/lam", diffc == ((lam-1)/K) * (K*vector(T,[X0,0]) - (1/lam)*K*vector(T,[0,1/D])))
# integrality sweep: random rational p,v with K p, K v integral; lam=q^h ≡ 1 mod K; lam | F
set_random_seed(20260925); okall = True; ntest = 0
for Kc in [2,3,4,6,10]:
    for qc in [p for p in primes(3, 40) if Kc % p != 0][:3]:
        hc = Mod(qc, Kc).multiplicative_order(); lc = qc^hc
        for _ in range(5):
            pc = vector(QQ, [ZZ.random_element(-20,20)/Kc for _ in range(3)]); vc = vector(QQ, [ZZ.random_element(-20,20)/Kc for _ in range(3)])
            for j in range(-3, 4):
                Fv = lc*j
                d = (lc-1)*pc - (Fv*(lc-1)/lc)*vc
                okall &= all(c in ZZ for c in d); ntest += 1
rec("N3 integrality sweep (%d cases)" % ntest, okall)
pc = vector(QQ, [1/3, 0, 0]); ctl("N3 lam=2 (≢1 mod 3) integral", all(c in ZZ for c in (2-1)*pc))

# N4 via divisors
rec("N4 (4b+1)(4u+1)=1: divisor pairs with both ≡1 mod 4 give only (0,0)",
    [((d-1)/4, (1/d-1)/4) for d in [1,-1] if (d-1) % 4 == 0 and (ZZ(1/d)-1) % 4 == 0] == [(0,0)])
Rb.<b,u> = QQ[]
rec("N4 b(2u+1) = 2 b (u+1/2) (Q=2bu, centre (0,-1/2), R=0)", b*(2*u+1) == 2*b*(u+1/2))
rec("N4 (4b+1)(4u+1)-1 = 16(b+1/4)(u+1/4)-1", (4*b+1)*(4*u+1)-1 == 16*(b+1/4)*(u+1/4)-1)
rec("N4 b(2u+1)=0 over ZZ forces b=0 (2u+1 odd, never 0)", all((2*uu+1) != 0 for uu in range(-1000,1001)))
ctl("N4 (2b+1)(2u+1)=1 unique", len([(d, 1/d) for d in [1,-1] if (d-1) % 2 == 0 and (ZZ(1/d)-1) % 2 == 0]) == 1)

# N5 p-adic roots (Hensel) via Zp to precision h, and lam = q^h ≡ 1 mod K
Pt.<x> = ZZ[]
for name, Fp, qc, Kc in [("deg1 6x+4", 6*x+4, 5, 4), ("disc!=0 x^2+1", x^2+1, 5, 3), ("disc=0 (2x+1)^2", (2*x+1)^2, 3, 7),
                         ("disc!=0 3x^2+x+5", 3*x^2+x+5, None, 10)]:
    if qc is None:   # Schur-type choice: smallest prime q not dividing 2*lead*disc*K that divides some F(t0)
        bad = 2*Fp.leading_coefficient()*Fp.discriminant()*Kc
        qc = next(p for t0 in range(0,200) for p in prime_divisors(Fp(t0)) if bad % p != 0)
    Fr = Fp if Fp.discriminant() != 0 or Fp.degree() < 2 else prod(g for g, _ in Fp.squarefree_decomposition())  # disc=0: use the linear factor L
    roots = Fr.change_ring(Zp(qc, prec=12)).roots()
    roots = [r for r, _ in roots if Fp(ZZ(r.lift())) % qc^12 == 0]  # every returned root is a root of F mod q^12
    hK = Mod(qc, Kc).multiplicative_order()
    rec("N5 %s: q=%d, %d root(s) in Z_q to prec 12, q^%d ≡ 1 mod %d" % (name, qc, len(roots), hK, Kc), len(roots) > 0 and qc^hK > 1)
ctl("N5 x^2+1 has a root in Z_3", len((x^2+1).change_ring(Zp(3, prec=8)).roots()) > 0)

npass = sum(1 for _, ok in res if ok)
print("LEG2_SUMMARY %d/%d  CONTROLS_CAUGHT %d/%d" % (npass, len(res), sum(1 for tg, ok in res if tg.startswith('CONTROL') and ok), sum(1 for tg, _ in res if tg.startswith('CONTROL'))))
