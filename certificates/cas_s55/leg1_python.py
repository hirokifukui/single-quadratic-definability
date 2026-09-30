#!/usr/bin/env python3
"""s55 CAS leg 1 (python brute force + sympy) for GPT R43 (our GATE25) figures and claims.
Each test has a planted control that MUST be caught. Prints one line per test.
Written independently of GPT's review_r43_math_controls.py (not run, not read for code)."""
import itertools, math, random
from fractions import Fraction as Fr
import sympy as sp

random.seed(55)
OUT = []
def rep(name, ok, detail=""):
    OUT.append(f"{name} {'PASS' if ok else 'FAIL'} {detail}".rstrip()); print(OUT[-1])

# ---------- T1 lattice nearest/gap criterion (FourSquareFinite.existsUnique_iff_gap)
def dlt(k, e): return min(e, k - e)
def d_of(k, eta): return sum(dlt(k, e) ** 2 for e in eta)
def g_of(k, eta): return min(k * (k - 2 * dlt(k, e)) for e in eta)
def count_box(k, eta, R0):
    if R0 < 0: return 0
    r = math.isqrt(R0)
    rngs = [[s for s in range((-r - e) // k - 1, (r + e) // k + 2) if (k*s - e)**2 <= R0] for e in eta]
    return sum(1 for t in itertools.product(*rngs) if sum((k*s - e)**2 for s, e in zip(t, eta)) <= R0)

def t1(planted):
    n = bad = 0
    for k in range(1, 7):
        for m in range(1, 4):
            for eta in itertools.product(range(k), repeat=m):
                d, g = d_of(k, eta), g_of(k, eta)
                for R0 in range(-2, 3 * k * k + 3):
                    lhs = count_box(k, eta, R0) == 1
                    rhs = (d <= R0 <= d + g) if planted else (d <= R0 < d + g)
                    n += 1; bad += (lhs != rhs)
    return n, bad
n, bad = t1(False); rep("T1_gap_criterion", bad == 0, f"checks={n} mismatch={bad}")
n, bad = t1(True);  rep("T1_planted_nonstrict", bad > 0, f"caught={bad}")

# ---------- T2 all-residues criterion (full_residue_iff / ..._of_surjective)
def t2(planted):
    n = bad = 0
    for k in range(1, 8):
        for m in range(1, 4):
            for R0 in range(-1, 2 * k * k):
                lhs = all(count_box(k, eta, R0) == 1 for eta in itertools.product(range(k), repeat=m))
                h = (k - 1) // 2
                odd = True if planted else (k % 2 == 1)
                rhs = odd and m * h * h <= R0 < (h + 1) ** 2
                n += 1; bad += (lhs != rhs)
    return n, bad
n, bad = t2(False); rep("T2_full_residue", bad == 0, f"checks={n} mismatch={bad}")
n, bad = t2(True);  rep("T2_planted_drop_odd", bad > 0, f"caught={bad}")

def allres(k, m, R0): return all(count_box(k, e, R0) == 1 for e in itertools.product(range(k), repeat=m))
rep("T3_examples",
    allres(3, 3, 3) and not any(allres(3, 4, R) for R in range(-1, 40)) and allres(5, 2, 8)
    and [R for R in range(-3, 10) if allres(1, 2, R)] == [0]
    and not any(allres(k, 1, R) for k in (2, 4, 6) for R in range(-1, 60)),
    "k3m3R3 yes; k3m4 none(R0<40); k5m2R8 yes; k=1 -> R0=0 only; even k none(m=1,R0<60)")
rep("T3_planted", allres(3, 4, 4) is False, "k3m4R0=4 rejected")

# ---------- T4 rank-3 rounding example (3b-a)^2+(u+b)^2+v^2 = 1
def sols4(a):
    return [(b, u, v) for b in range(a//3 - 3, a//3 + 4) for u in range(-abs(a) - 6, abs(a) + 7)
            for v in (-1, 0, 1) if (3*b - a)**2 + (u + b)**2 + v*v == 1]
ok = True; outs_bad = 0
for a in range(-30, 31):
    S = sols4(a)
    if {s[0] for s in S} != {(a + 1) // 3}: outs_bad += 1
S0 = sorted(sols4(0))
rep("T4_rank3_outputs", outs_bad == 0, f"inputs=61 bad={outs_bad}")
rep("T4_rank3_a0_four", S0 == sorted([(0, -1, 0), (0, 1, 0), (0, 0, -1), (0, 0, 1)]), f"a0={S0}")
rep("T4_planted_card_solutions_eq1", len(S0) != 1, "witness-count criterion rejects a=0 wrongly")
a, b, u, v, t = sp.symbols('a b u v t', integer=True)
P4 = (3*b - a)**2 + (u + b)**2 + v**2 - 1
rep("T4_translation", sp.expand(P4.subs({a: a + 3*t, b: b + t, u: u - t}, simultaneous=True) - P4) == 0)
rep("T4_planted_translation", sp.expand(P4.subs({a: a + 3*t, b: b + t, u: u + t}, simultaneous=True) - P4) != 0)
Qm = sp.Matrix([[10, 1, 0], [1, 1, 0], [0, 0, 1]])  # 9b^2+(u+b)^2+v^2
rep("T4_pd_rank3", Qm.rank() == 3 and all(Qm[:i, :i].det() > 0 for i in (1, 2, 3)))
cen = {b: a/3, u: -a/3, v: 0}
rep("T4_centre_residual", sp.expand((9*(b - a/3)**2 + ((u + a/3) + (b - a/3))**2 + v**2) - (P4 + 1)) == 0)

# ---------- T5 (5.1) b^2+u^2+v^2 = 1 + 8 sum a_i^2
def three_sq(N):
    r = math.isqrt(N)
    for x in range(r + 1):
        for y in range(x, math.isqrt(N - x*x) + 1):
            z2 = N - x*x - y*y
            if z2 >= y*y and math.isqrt(z2)**2 == z2: return True
    return False
miss = [a4 for a4 in itertools.product(range(-3, 4), repeat=4) if not three_sq(1 + 8*sum(x*x for x in a4))]
rep("T5_totality_box", not miss, f"inputs=2401 miss={len(miss)}")
rep("T5_planted_7mod8", not three_sq(7), "7+8S never a sum of three squares")
rep("T5_a0_outputs", sorted({B for B in range(-2, 3) for U in range(-2, 3) for V in range(-2, 3) if B*B+U*U+V*V == 1}) == [-1, 0, 1])
H = sp.diag(8, 8, 8, 8)
L = sp.Matrix(3, 4, lambda i, j: sp.Symbol(f"L{i}{j}"))
rep("T5_rank_obstruction", H.rank() == 4 and (L.T * L).rank() <= 3, "rank(8M^2 I4)=4 > rank(L^T L)<=3")

# ---------- T6 D4 symmetry example (2b-2a)^2+(3u-1)^2+v^2 = 1
bad6 = 0
for A in range(-20, 21):
    S = [(B, U, V) for B in range(A - 3, A + 4) for U in range(-3, 4) for V in range(-2, 3)
         if (2*B - 2*A)**2 + (3*U - 1)**2 + V*V == 1]
    if S != [(A, 0, 0)]: bad6 += 1
    c = (Fr(A), Fr(1, 3), Fr(0))
    if all((2*x).denominator == 1 for x in c): bad6 += 1
    z = (A, 0, 0); zp = tuple(c[i] + [-1, 1, 1][i]*(z[i] - c[i]) for i in range(3))
    if any(x.denominator != 1 for x in zp): bad6 += 1
    zq = tuple(c[i] + [1, -1, 1][i]*(z[i] - c[i]) for i in range(3))
    if all(x.denominator == 1 for x in zq): bad6 += 1   # planted T must NOT return to lattice
rep("T6_D4_example", bad6 == 0, "unique sol b=a; 2c nonintegral; diag(-1,1,1) integral; planted diag(1,-1,1) nonintegral")

# ---------- T7 finite doubled-centre criterion, T8 constant-residual transport
def rq(): return Fr(random.randint(-9, 9), random.choice([1, 2, 3, 4, 6]))
bad7 = 0; planted7 = 0; trials = 0
for _ in range(150):
    n_, s_ = 2, 3
    c0 = [rq() for _ in range(s_)]; C = [[rq() for _ in range(n_)] for _ in range(s_)]
    N = math.lcm(*[(2*x).denominator for x in c0 + [y for r in C for y in r]])
    H0 = [int(2*N*x) for x in c0]; Hm = [[int(2*N*y) for y in r] for r in C]
    brute = any(all((2*(c0[i] + sum(C[i][j]*a_[j] for j in range(n_)))).denominator == 1 for i in range(s_))
                for a_ in itertools.product(range(-2*N, 2*N + 1), repeat=n_))
    fin = any(all((H0[i] + sum(Hm[i][j]*r[j] for j in range(n_))) % N == 0 for i in range(s_))
              for r in itertools.product(range(N), repeat=n_))
    pl = any(all((H0[i] + sum(Hm[i][j]*r[j] for j in range(n_))) % N == 1 % N for i in range(s_))
             for r in itertools.product(range(N), repeat=n_))
    trials += 1; bad7 += (brute != fin); planted7 += (brute != pl)
rep("T7_HC_finite", bad7 == 0, f"trials={trials} mismatch={bad7} positives={'n/a'}")
rep("T7_planted_residue1", planted7 > 0, f"caught={planted7}")

bad8 = 0; pl8 = 0
for _ in range(200):
    s_, n_ = 3, 2
    Qr = [[rq() for _ in range(s_)] for _ in range(s_)]
    c0 = [rq() for _ in range(s_)]; C = [[rq() for _ in range(n_)] for _ in range(s_)]
    R0 = rq()
    M = math.lcm(*[y.denominator for r in C for y in r]); G = [[M*y for y in r] for r in C]
    Mbad = max(1, M // 2) if M > 1 else None
    def P(a_, z):
        w = [z[i] - c0[i] - sum(C[i][j]*a_[j] for j in range(n_)) for i in range(s_)]
        return sum(w[i]*Qr[i][j]*w[j] for i in range(s_) for j in range(s_)) - R0
    a_ = [random.randint(-9, 9) for _ in range(n_)]; z = [random.randint(-9, 9) for _ in range(s_)]
    t_ = [random.randint(-5, 5) for _ in range(n_)]
    a2 = [a_[j] + M*t_[j] for j in range(n_)]; z2 = [z[i] + sum(G[i][j]*t_[j] for j in range(n_)) for i in range(s_)]
    if P(a2, z2) != P(a_, z) or any(y.denominator != 1 for r in G for y in r): bad8 += 1
    if Mbad is not None and any((Mbad*y).denominator != 1 for r in C for y in r): pl8 += 1
rep("T8_CR_transport", bad8 == 0, "P(a+Mt,z+Gt)=P(a,z), G integral, no PD assumed")
rep("T8_planted_halfM", pl8 > 0, f"caught={pl8}")

# ---------- T9 coercivity y_i^2 <= (A^-1)_ii Q(y)
def rand_pd():
    while True:
        Lm = sp.Matrix(3, 3, lambda i, j: sp.Rational(random.randint(-4, 4), random.choice([1, 2, 3])) if i >= j else 0)
        A = Lm * Lm.T
        if A.det() != 0: return A
bad9 = 0
for _ in range(60):
    A = rand_pd(); Ai = A.inv()
    for _ in range(40):
        y = sp.Matrix([random.randint(-7, 7) for _ in range(3)])
        q = (y.T * A * y)[0]
        if any(y[i]**2 > Ai[i, i]*q for i in range(3)): bad9 += 1
rep("T9_coercivity", bad9 == 0, "60 PD matrices x 40 vectors, exact")
A2 = sp.Matrix([[1, -2], [-2, 5]])   # (x-2y)^2+y^2
y2 = sp.Matrix([2, 1]); q2 = (y2.T*A2*y2)[0]
rep("T9_planted_diag", y2[0]**2 > q2 / A2[0, 0], f"1/A_ii bound fails at (2,1): 4 > {q2/A2[0,0]}")
rep("T9_sheared_ratio", q2 == 1 and min(((sp.Matrix([x, w]).T*A2*sp.Matrix([x, w]))[0] / max(x*x, w*w))
                                           for x in range(-6, 7) for w in range(-6, 7) if (x, w) != (0, 0)) == sp.Rational(1, 5),
    "note §4.3: Q(2,1)=1 and min ratio 1/5")

# ---------- T10 Brahmagupta anchored section
r0, s0, D, x, y = sp.symbols('r0 s0 D x y')
rep("T10_brahmagupta", sp.expand((r0**2 + D*s0**2)*(x**2 + D*y**2) - ((r0*x - D*s0*y)**2 + D*(r0*y + s0*x)**2)) == 0)
rep("T10_planted_sign", sp.expand((r0**2 + D*s0**2)*(x**2 + D*y**2) - ((r0*x + D*s0*y)**2 + D*(r0*y + s0*x)**2)) != 0)

# ---------- T11 square-values rigidity recipe h = B_A(w,x)/(2aN)
x1, x2 = sp.symbols('x1 x2')
def recipe(T, vars_):
    N = sp.ilcm(*[sp.Rational(cf).q for cf in sp.Poly(T, *vars_).coeffs()])
    A = sp.expand(N**2 * T)
    for w in itertools.product(range(-3, 4), repeat=len(vars_)):
        val = A.subs(dict(zip(vars_, w)))
        if val > 0:
            a_ = sp.sqrt(val)
            if not a_.is_integer: return None
            BA = sp.expand(A.subs({vv: vv + ww for vv, ww in zip(vars_, w)}) - A - val)
            return sp.expand(BA / (2*a_*N))
    return 0
T = sp.Rational(1, 4)*(2*x1 + 3*x2)**2
h = recipe(T, [x1, x2])
rep("T11_recipe", h is not None and sp.expand(h**2 - T) == 0, f"h={h}")
T_bad = x1**2 + x2**2
sq_all = all(sp.sqrt(T_bad.subs({x1: p, x2: q})).is_rational for p in range(-3, 4) for q in range(-3, 4))
rep("T11_planted_nonsquare", not sq_all, "x1^2+x2^2 not square at (1,1)")

# ---------- T12 le_of_sq_le hypotheses (note line 295): s>=0 is not needed; B>=0, K>=0 are
viol_neg_s = 0; ce_B = ce_K = 0; pl12 = 0
for c in range(1, 4):
    for s in range(-12, 13):
        for B in range(-6, 7):
            for K in range(-6, 7):
                for C in range(-4, K*K + 1):
                    if c*s*s <= B*s + C:
                        if s < 0 and B >= 0 and K >= 0 and not s <= B + K: viol_neg_s += 1
                        if s >= 0 and B < 0 and K >= 0 and not s <= B + K: ce_B += 1
                        if s >= 0 and B >= 0 and K < 0 and not s <= B + K: ce_K += 1
                        if s >= 0 and B >= 0 and K >= 0 and not s <= B: pl12 += 1
rep("T12_s_nonneg_droppable", viol_neg_s == 0, "no violation with s<0 (B,K>=0)")
rep("T12_B_K_needed", ce_B > 0 and ce_K > 0, f"counterexamples B<0:{ce_B} K<0:{ce_K}")
rep("T12_planted_drop_K_from_bound", pl12 > 0, f"s<=B alone fails {pl12} times")

nf = sum(1 for o in OUT if " FAIL" in o)
print(f"LEG1_TESTS={len(OUT)} LEG1_FAIL={nf}")
print("LEG1_DONE")
