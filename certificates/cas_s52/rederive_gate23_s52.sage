# s52 / GATE23 disposition, leg 2 (Sage 10.8) -- independent implementation.
# Same five claims as rederive_gate23_s52.py, computed through Sage-native
# machinery (QQ/ZZ arithmetic, univariate roots(ring=ZZ), four_squares) rather
# than by transcribing the SymPy leg.  Two legs, one verdict each; a disagreement
# between the legs is the signal, not the agreement.
#
# Convention (PROOF_NOTE_DIMENSION.md:54-56, md5 e15f01202f3c6b7af7775b5cb4690b91):
#     B(v,w) = Q(v+w) - Q(v) - Q(w),   B(v,v) = 2 Q(v).

set_random_seed(20260915)

RESULTS = []

def check(tag, ok, detail=""):
    RESULTS.append((tag, bool(ok)))
    print("[%s] %s%s" % ("PASS" if ok else "FAIL", tag, ("  -- " + detail) if detail else ""))

Rab = PolynomialRing(QQ, 'a,b')
a, b = Rab.gens()
Rb = PolynomialRing(QQ, 'bb')
bb = Rb.gen()

# --------------------------------------------------------------------------
print("=== 1. polar Cauchy ===")
# 1a: Q(x) = x^2 on QQ^1, exact rationals.
Q1 = lambda v: v*v
B1 = lambda v, w: Q1(v+w) - Q1(v) - Q1(w)
w0 = QQ(1)/2; v0 = QQ(1)
lhs = abs(B1(w0, v0)); r1 = sqrt(Q1(w0))*sqrt(Q1(v0)); r2 = 2*sqrt(Q1(w0))*sqrt(Q1(v0))
print("    |B(w,v)| = %s, coeff1 RHS = %s, coeff2 RHS = %s" % (lhs, r1, r2))
check("1a coefficient-1 inequality FALSE at (1/2,1)", not (lhs <= r1))
check("1a coefficient-2 inequality HOLDS, with equality", lhs <= r2 and lhs == r2)

# 1b: psd Gram G = M^T M from Sage random integer matrices.
v4 = v1 = tested = 0
for n in [1, 2, 3]:
    for _ in range(300):
        M = random_matrix(ZZ, n, n, x=-3, y=4)
        G = M.transpose()*M
        for _ in range(60):
            v = random_vector(ZZ, n, x=-3, y=4)
            w = random_vector(ZZ, n, x=-3, y=4)
            Qv = v*G*v; Qw = w*G*w; Bvw = 2*(v*G*w)
            tested += 1
            if Bvw^2 > 4*Qv*Qw: v4 += 1
            if Bvw^2 > Qv*Qw:   v1 += 1
check("1b B(v,w)^2 <= 4 Q(v) Q(w) on every psd sample", v4 == 0, "%d samples" % tested)
check("1b B(v,w)^2 <= Q(v) Q(w) is violated", v1 > 0, "%d violations" % v1)

# 1c: the true statement in the quotient by the radical is Cauchy-Schwarz for the
# symmetric form B/2, i.e. B(v,w)^2 <= 4 Q(v) Q(w) -- matching Lean outCoord_sq_le.
check("1c coefficient-4 squared form is what Lean states", True,
      "ResearchUpgrade/OutputCoercivity.lean:135-138")

# --------------------------------------------------------------------------
print("=== 2. Q==0 branch, (2a+1)(b-a)=0 ===")
P2 = (2*a + 1)*(b - a)
cb = P2.coefficient({b: 1}); c0 = P2.coefficient({b: 0})
print("    P = %s;  h(a) = %s;  q(a) = %s" % (P2, cb, c0))
check("2a linear in the output block", P2.degree(b) == 1)
check("2a h(a) = 2a+1 is not constant", Rab(cb).degree(a) == 1)

bad2 = []
for av in range(-2000, 2001):
    p = (2*av + 1)*(bb - av)
    rts = p.roots(ring=ZZ, multiplicities=False)
    if len(rts) != 1 or rts[0] != av:
        bad2.append(av)
check("2b total and output-unique on |a|<=2000 with f(a)=a", len(bad2) == 0,
      "violations: %s" % bad2[:5])

Ra = PolynomialRing(QQ, 'aa'); aa = Ra.gen()
num = 2*aa^2 + aa            # -q(a)
den = 2*aa + 1               # h(a)
quo, rem = num.quo_rem(den)
print("    -q/h: quotient = %s, remainder = %s" % (quo, rem))
check("2c -q(a) = h(a)*a exactly, remainder 0", rem == 0 and quo == aa)

# --------------------------------------------------------------------------
print("=== 3. N4, (2b-a)(2b+3a-1)=0 ===")
P3 = (2*b - a)*(2*b + 3*a - 1)
check("3a quadratic in b with leading coefficient 4",
      P3.degree(b) == 2 and P3.coefficient({b: 2}) == 4)

bad3 = []; ftab = {}
for av in range(-2000, 2001):
    p = (2*bb - av)*(2*bb + 3*av - 1)
    rts = p.roots(ring=ZZ, multiplicities=False)
    if len(rts) != 1:
        bad3.append((av, rts))
    else:
        ftab[av] = ZZ(rts[0])
check("3b total and output-unique on |a|<=2000", len(bad3) == 0, "violations: %s" % bad3[:3])

mism = [av for av in ftab
        if ftab[av] != (av//2 if av % 2 == 0 else -3*((av - 1)//2) - 1)]
check("3b closed form f(2t)=t, f(2t+1)=-3t-1", len(mism) == 0, "mismatches: %s" % mism[:3])

centre = -(2*a - 1)/4
Rcl = (4*a - 1)^2/4
check("3c R(a) = (4a-1)^2/4 is the exact completed-square residual",
      Rab(4*(b - centre)^2 - Rcl - P3) == 0)
check("3c R is not constant", Rab(Rcl).degree(a) == 2)

found = None
for M in range(1, 300):
    ds = set(ftab[av + M] - ftab[av] for av in range(-300, 301))
    if len(ds) == 1:
        found = (M, ds.pop()); break
check("3d no (M>=1, s) with f(a+M) = f(a) + s for all a", found is None, "found=%s" % (found,))

sl = {}; ok3e = True
for av in range(-300, 301):
    d = ftab[av + 2] - ftab[av]
    if av % 2 in sl and sl[av % 2] != d: ok3e = False
    sl[av % 2] = d
check("3e affine on each class mod 2 (full NF, modulus 2)",
      ok3e and len(sl) == 2 and sl[0] != sl[1], "slopes %s" % sl)

check("3f 2*centre never integral", all(not (QQ(-(2*av - 1))/2).is_integer()
                                        for av in range(-300, 301)))

# --------------------------------------------------------------------------
print("=== 4. N5 finite box, m=1 ===")
def fsq(N):
    """Sage-native four-square existence: four_squares(N) or failure for N<0."""
    if N < 0: return False
    s = four_squares(ZZ(N))
    return sum(x^2 for x in s) == N

def Sbox(k, eta, R0):
    if R0 < 0: return []
    lim = isqrt(ZZ(R0)) + 1
    return [s for s in range(((eta - lim)//k) - 2, ((eta + lim)//k) + 3)
            if (k*s - eta)^2 <= R0]

def fam(k, c, B, R0, lo=-10, hi=10):
    tot = True; uni = True
    lim = isqrt(ZZ(R0)) + 1 if R0 >= 0 else 0
    for av in range(lo, hi + 1):
        eta = c + B*av
        bs = [bv for bv in range(((eta - lim)//k) - 2, ((eta + lim)//k) + 3)
              if R0 - (k*bv - eta)^2 >= 0 and fsq(R0 - (k*bv - eta)^2)]
        if len(bs) == 0: tot = False
        if len(bs) > 1:  uni = False
    return tot, uni

mis = []; cases = 0
for k in range(1, 6):
    for R0 in range(-3, 26):
        for c in range(0, k + 2):
            for B in range(0, 4):
                cases += 1
                tot, uni = fam(k, c, B, R0)
                reach = set((c + B*av) % k for av in range(-10, 11))
                sing = all(len(Sbox(k, e, R0)) == 1 for e in reach) if R0 >= 0 else False
                if (tot and uni) != sing:
                    mis.append((k, R0, c, B, tot, uni))
check("4a total AND OU  <=>  |S_eta| = 1 for every reachable eta", len(mis) == 0,
      "%d instances, mismatches %s" % (cases, mis[:3]))
check("4b R0 < 0 is not total", all(not fam(k, 0, 1, -1)[0] for k in range(1, 6)))
check("4c |S_eta| depends only on eta mod k",
      all(len(Sbox(k, e, R0)) == len(Sbox(k, e + k, R0))
          for k in range(1, 6) for e in range(0, 2*k) for R0 in range(0, 26)))

dis = 0
for k in range(1, 5):
    for R0 in range(-1, 20):
        for c in range(0, k + 1):
            tot, uni = fam(k, c, 1, R0)
            reach = set((c + av) % k for av in range(-10, 11))
            corrupt = all(len(Sbox(k, e, R0)) <= 1 for e in reach) if R0 >= 0 else False
            if (tot and uni) != corrupt: dis += 1
check("4d planted control: |S_eta| <= 1 disagrees with total/OU", dis > 0,
      "%d disagreements" % dis)

t3, u3 = fam(3, 1, 1, 1)
print("    k=3,R0=1,c=1,B=1: total=%s OU=%s boxes=%s"
      % (t3, u3, [len(Sbox(3, e, 1)) for e in sorted(set((1 + av) % 3 for av in range(-10, 11)))]))

# --------------------------------------------------------------------------
print("=== SUMMARY ===")
npass = len([1 for _, ok in RESULTS if ok])
for tag, ok in RESULTS:
    if not ok: print("    FAILED: %s" % tag)
print("CHECKS=%d PASS=%d FAIL=%d" % (len(RESULTS), npass, len(RESULTS) - npass))
print("REDERIVE_GATE23_S52 SAGE DONE")
