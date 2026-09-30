# s55 CAS leg 2 (Sage, methods different from leg 1) for GPT R43 (our GATE25).
# T1/T2: counting by truncated generating-function convolution (not box enumeration).
# T4: GPT's own finite-shell proposition FS via Sage QuadraticForm short vectors.
# T5: Sage three_squares; T7: Smith-free lattice test via Sage matrices mod N;
# T9: Cholesky-free check with QQ matrices; each test has a planted control.
OUT = []
def rep(name, ok, detail=""):
    s = "%s %s %s" % (name, "PASS" if ok else "FAIL", detail)
    OUT.append(s.strip()); print(OUT[-1])

R = PolynomialRing(ZZ, 'X'); X = R.gen()
def count_gf(k, eta, R0):
    # number of s in Z^m with sum (k s_j - eta_j)^2 <= R0, via product of per-coordinate series
    if R0 < 0: return 0
    prod = R(1)
    for e in eta:
        p = R(0); r = isqrt(R0)
        for s in range(-(r + k) // k - 2, (r + k) // k + 3):
            v = (k*s - e)**2
            if v <= R0: p += X**v
        prod = (prod * p).truncate(R0 + 1)
    return sum(prod.list())

def dlt(k, e): return min(e, k - e)

n = bad = pl = 0
for k in range(1, 7):
    for m in range(1, 4):
        for eta in cartesian_product([range(k)]*m):
            d = sum(dlt(k, e)**2 for e in eta); g = min(k*(k - 2*dlt(k, e)) for e in eta)
            for R0 in range(-2, 3*k*k + 3):
                lhs = count_gf(k, eta, R0) == 1
                n += 1; bad += (lhs != (d <= R0 < d + g)); pl += (lhs != (d < R0 < d + g))
rep("S1_gap_criterion", bad == 0, "checks=%d mismatch=%d" % (n, bad))
rep("S1_planted_strict_lower", pl > 0, "caught=%d" % pl)

n = bad = pl = 0
for k in range(1, 8):
    for m in range(1, 4):
        etas = list(cartesian_product([range(k)]*m))
        for R0 in range(-1, 2*k*k):
            lhs = all(count_gf(k, e, R0) == 1 for e in etas)
            h = (k - 1) // 2
            n += 1; bad += (lhs != (k % 2 == 1 and m*h*h <= R0 < (h + 1)**2))
            pl += (lhs != (k % 2 == 1 and m*h*h <= R0 <= (h + 1)**2))
rep("S2_full_residue", bad == 0, "checks=%d mismatch=%d" % (n, bad))
rep("S2_planted_upper", pl > 0, "caught=%d" % pl)

# S4: FS proposition on (3b-a)^2+(u+b)^2+v^2=1, M=3, C(a)=M c(a)=(a,-a,0), shell Q(y)=M^2 R0=9
G = matrix(QQ, [[10, 1, 0], [1, 1, 0], [0, 0, 1]])
Qf = QuadraticForm(ZZ, 2*G)            # Q(y) = y^T G y, stored as even form 2G
shell = [vector(v) for v in Qf.short_vector_list_up_to_length(10)[9]]
ok = True; recovered_bad = 0; pl4 = 0
for rho in range(3):
    Crho = vector([rho, -rho, 0])
    S = [y for y in shell if all((y[i] + Crho[i]) % 3 == 0 for i in range(3))]
    img = set(y[0] for y in S)
    if len(img) != 1: ok = False
    if len(S) == 1: pl4 += 1
    e = list(img)[0]
    for t in range(-10, 11):
        a = rho + 3*t
        if (e + a) / 3 != floor((a + 1) / 3): recovered_bad += 1
rep("S4_FS_image_card1", ok, "shell size=%d" % len(shell))
rep("S4_FS_recovery", recovered_bad == 0, "f(a)=(e_rho+a)/3 == floor((a+1)/3), a in [-30,30]")
rep("S4_planted_card_shell", pl4 < 3, "card(S_rho)=1 criterion fails on %d of 3 residues" % (3 - pl4))

# S5: (5.1) totality via Sage three_squares; planted 7 mod 8
miss = 0
for a in cartesian_product([range(-3, 4)]*4):
    N = 1 + 8*sum(x*x for x in a)
    try:
        t = three_squares(N)
        if sum(x*x for x in t) != N: miss += 1
    except ValueError:
        miss += 1
try:
    three_squares(7); pl5 = False
except ValueError:
    pl5 = True
rep("S5_totality", miss == 0, "inputs=2401 miss=%d" % miss)
rep("S5_planted_7", pl5)
rk = max((Lr.T*Lr).rank() for Lr in [random_matrix(QQ, 3, 4, num_bound=9, den_bound=5) for _ in range(50)])
rep("S5_rank", rk == 3 and (8*identity_matrix(QQ, 4)).rank() == 4, "max rank(L^T L) over 50 random L = %d" % rk)

# S6: D4 example via polynomial ring identity and isometry check
PRq = PolynomialRing(QQ, ['a', 'b', 'u', 'v']); a, b, u, v = PRq.gens()
P6 = (2*b - 2*a)**2 + (3*u - 1)**2 + v**2 - 1
Q6 = diagonal_matrix(QQ, [4, 9, 1])
T6 = diagonal_matrix(QQ, [-1, 1, 1]); Tbad = diagonal_matrix(QQ, [1, -1, 1])
rep("S6_isometry", T6.T*Q6*T6 == Q6 and Tbad.T*Q6*Tbad == Q6)
c6 = vector(PRq, [a, 1/3, 0]); z = vector(PRq, [b, u, v])
zp = c6 + T6.change_ring(PRq)*(z - c6); zq = c6 + Tbad.change_ring(PRq)*(z - c6)
rep("S6_T_integral_map", all(all(cf in ZZ for cf in PRq(w).coefficients()) for w in zp) and
    P6(a, *zp) == P6, "z'=(2a-b,u,v) and P preserved")
rep("S6_planted_T", not all(all(cf in ZZ for cf in PRq(w).coefficients()) for w in zq), "u'=2/3-u non-integral")

# S7: doubled-centre finite criterion; solvability of H x = -H0 (mod N) via Smith normal form
def zsolvable(A, bvec):
    Dm, U, V = A.smith_form()          # Dm = U*A*V
    c = U*bvec
    for i in range(Dm.nrows()):
        d = Dm[i, i] if i < Dm.ncols() else 0
        if d == 0:
            if c[i] != 0: return False
        elif c[i] % d != 0: return False
    return True
set_random_seed(55)
bad7 = pl7 = pos = 0
for trial in range(120):
    c0 = vector(QQ, [QQ(randint(-9, 9))/choice([1, 2, 3, 4, 6]) for _ in range(3)])
    C = matrix(QQ, 3, 2, [QQ(randint(-9, 9))/choice([1, 2, 3, 4, 6]) for _ in range(6)])
    N = lcm([x.denominator() for x in list(2*c0) + (2*C).list()])
    H0 = (2*N*c0).change_ring(ZZ); H = (2*N*C).change_ring(ZZ)
    # brute over a in a full period box
    brute = any(all(x in ZZ for x in 2*(c0 + C*vector([p, q]))) for p in range(N) for q in range(N))
    # Sage: solvability of H x = -H0 over Z/N
    fin = zsolvable(H.augment(N*identity_matrix(ZZ, 3)), -H0)
    fpl = zsolvable(H.augment(N*identity_matrix(ZZ, 3)), -H0 + vector(ZZ, [1, 0, 0]))
    pos += brute; bad7 += (brute != fin); pl7 += (brute != fpl)
rep("S7_HC_finite", bad7 == 0, "trials=120 positives=%d mismatch=%d" % (pos, bad7))
rep("S7_planted_shift", pl7 > 0, "caught=%d" % pl7)

# S9: coercivity bound via Lagrange: max y_i^2/Q(y) = (A^-1)_ii attained at y = A^-1 e_i
bad9 = pl9 = 0
for trial in range(60):
    while True:
        L = matrix(QQ, 3, 3, lambda i, j: QQ(randint(-4, 4))/choice([1, 2, 3]) if i >= j else 0)
        A = L*L.T
        if A.det() != 0: break
    Ai = A.inverse()
    for i in range(3):
        y = Ai.column(i)
        val = y[i]**2 / (y*A*y)
        if val != Ai[i, i]: bad9 += 1          # equality case of the bound
        if val > 1/A[i, i]: pl9 += 1           # planted bound 1/A_ii is exceeded
rep("S9_coercivity_sharp", bad9 == 0, "equality at y=A^-1 e_i for 180 cases")
rep("S9_planted_diag", pl9 > 0, "1/A_ii exceeded %d times" % pl9)

# S10: Brahmagupta over a different ring (QQ[r0,s0,D,x,y]) plus section passes through (r0,s0) at x=1,y=0
PB = PolynomialRing(QQ, ['r0', 's0', 'D', 'x', 'y']); r0, s0, D, x, y = PB.gens()
rsec = r0*x - D*s0*y; ssec = r0*y + s0*x
rep("S10_brahmagupta", (r0**2 + D*s0**2)*(x**2 + D*y**2) == rsec**2 + D*ssec**2 and
    rsec(x=1, y=0) == r0 and ssec(x=1, y=0) == s0)

nf = len([o for o in OUT if " FAIL" in o])
print("LEG2_TESTS=%d LEG2_FAIL=%d" % (len(OUT), nf))
print("LEG2_DONE")
