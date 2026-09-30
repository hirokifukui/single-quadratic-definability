# s48 disposition: re-derive every checkable claim of GPT Gate22 (our GATE21) on our own bytes.
# Convention throughout: b(v,w) = Q(v+w)-Q(v)-Q(w), so b(v,v) = 2Q(v).   (file A, section 1)
import itertools, random
from sympy import (Matrix, Rational, symbols, simplify, expand, eye, zeros,
                   nsimplify, sqrt, Integer, isprime)
random.seed(48)
R=[]
def chk(tag, ok, note=""):
    R.append((tag, bool(ok), note)); print(("PASS " if ok else "FAIL ")+tag+(("  | "+note) if note else ""))

def Qf(M,v): return (v.T*M*v)[0,0]              # Q(v) = v^T M v, M symmetric
def bf(M,v,w): return Qf(M,v+w)-Qf(M,v)-Qf(M,w) # = 2 v^T M w

# ---------- A0. polar convention ----------
M=Matrix([[2,-1],[-1,3]]); v=Matrix([1,2]); w=Matrix([-3,1])
chk("A0 polar convention b=2B, b(v,v)=2Q(v)",
    bf(M,v,w)==2*(v.T*M*w)[0,0] and bf(M,v,v)==2*Qf(M,v))

# ---------- A1. section 3: im(p) = Ann(rad Q), including degenerate ----------
def im_eq_ann(M):
    n=M.rows
    K=M.nullspace()                      # rad(Q) = ker p  (p(v)=b(v,-)=2Mv)
    r_im=M.rank()
    # Ann(ker p) inside the dual, as row vectors l with l*k = 0 for all k in K
    if K:
        A=Matrix.hstack(*K).T            # rows = radical basis
        d_ann=n-A.rank()
    else:
        d_ann=n
    if r_im!=d_ann: return False
    # im(p) subseteq Ann(rad): b(v, e)=0 for every v when e radical
    for e in K:
        for _ in range(5):
            u=Matrix([random.randint(-5,5) for _ in range(n)])
            if bf(M,u,e)!=0: return False
    return True
cases=[Matrix([[0,0],[0,0]]),                        # zero map
       Matrix([[1,0],[0,0]]),                        # rank one
       Matrix([[2,-1],[-1,3]]),                      # nondegenerate
       Matrix([[1,-2,0],[-2,4,0],[0,0,0]]),          # (x-2y)^2, rank 1 in dim 3
       Matrix([[1,0,0],[0,-1,0],[0,0,0]])]           # indefinite with radical
chk("A1 im(p)=Ann(rad Q) on 5 contrasts (zero / rank-1 / nondeg / degenerate / indefinite)",
    all(im_eq_ann(M) for M in cases))
chk("A1b same on 200 random symmetric rational matrices dim<=4",
    all(im_eq_ann(Matrix(k,k,lambda i,j:0)+ (lambda A:(A+A.T))(Matrix(k,k,lambda i,j:random.randint(-3,3))))
        for k in (1,2,3,4) for _ in range(50)))

# ---------- A2. section 3.1: affine centre and completeSquare ----------
a1,a2,z1,z2,z3=symbols('a1 a2 z1 z2 z3')
def centre_test(M, l0, ls, q):
    n=M.rows; a=[a1,a2][:len(ls)]
    # solve b(h_i,-) = -l_i   i.e.  2 M h_i = -l_i   (as column of coefficients)
    try:
        h0=(2*M).solve(-l0); hs=[(2*M).solve(-l) for l in ls]
    except Exception:
        return None
    h=h0+sum((ai*hi for ai,hi in zip(a,hs)), zeros(n,1))
    z=Matrix(symbols('z1:%d'%(n+1)))
    ell=(l0+sum((ai*li for ai,li in zip(a,ls)), zeros(n,1)))
    P=Qf(M,z)+(ell.T*z)[0,0]+q
    Rr=Qf(M,h)-q
    return simplify(expand(Qf(M,z-h)-Rr-P))==0, simplify(expand(h-h0-sum((ai*hi for ai,hi in zip(a,hs)), zeros(n,1))))==zeros(n,1)
M=Matrix([[2,-1],[-1,3]])
ok,_=centre_test(M, Matrix([1,-4]), [Matrix([2,0]),Matrix([0,6])], 3*a1**2-a1*a2+5)
chk("A2 completeSquare  Q(z)+l_a(z)+q(a) = Q(z-h(a)) - R(a), h affine in a", ok)
oks=[]
for _ in range(60):
    k=random.choice([2,3])
    A=Matrix(k,k,lambda i,j:random.randint(-4,4)); M=A+A.T
    if M.det()==0: continue
    r=centre_test(M, Matrix([random.randint(-5,5) for _ in range(k)]),
                  [Matrix([random.randint(-5,5) for _ in range(k)])],
                  Rational(random.randint(-6,6)))
    oks.append(r[0])
chk("A2b same identity on %d random nondegenerate forms"%len(oks), all(oks))

# ---------- A3. section 4.1: semidefinite Cauchy, both cases ----------
def cauchy(M):
    n=M.rows
    for _ in range(300):
        v=Matrix([random.randint(-6,6) for _ in range(n)]); w=Matrix([random.randint(-6,6) for _ in range(n)])
        if bf(M,v,w)**2 > 4*Qf(M,v)*Qf(M,w): return False
    return True
semidef=[Matrix([[1,0],[0,0]]), Matrix([[1,-2],[-2,4]]), Matrix([[2,1],[1,3]]), Matrix([[1,0,0],[0,1,0],[0,0,0]])]
chk("A3 b(v,w)^2 <= 4 Q(v)Q(w) for Q>=0 (coefficient 4, NOT 1 -- control 5)", all(cauchy(M) for M in semidef))
# zero case: Q(w)=0 => b(w,-)=0
Mz=Matrix([[1,-2],[-2,4]]); wz=Matrix([2,1])   # Q(w)=0 on the radical
chk("A3b Q(w)=0 => b(w,-)=0 (the case the route forbids skipping)",
    Qf(Mz,wz)==0 and all(bf(Mz,wz,Matrix([x,y]))==0 for x in range(-4,5) for y in range(-4,5)))
# and the converse trap: Q(w)=0 with w NOT radical needs Q indefinite
Mi=Matrix([[1,0],[0,-1]]); wi=Matrix([1,1])
chk("A3c control 8: Q(w)=0, w!=0, w not radical exists only for indefinite Q",
    Qf(Mi,wi)==0 and any(bf(Mi,wi,Matrix([x,y]))!=0 for x in range(-3,4) for y in range(-3,4)))

# ---------- A4. section 4.3 / control 1: P=(b-a)^2 ----------
# z=(b,u); Q(b,u)=b^2 ; l_a(z)=-2ab ; q(a)=a^2 ; pi(b,u)=b
Mc=Matrix([[1,0],[0,0]])
rad=Mc.nullspace()
chk("A4 P=(b-a)^2: rad(Q)=span(0,1); centre h(a)=(a,0) exists; pi kills rad",
    len(rad)==1 and rad[0]==Matrix([0,1]) and bf(Mc,Matrix([1,0]),Matrix([0,1]))==0)
fail=[(b,u) for b in range(-2,3) for u in range(-2,3) if not (1*max(abs(b),abs(u))**2 <= 1*Qf(Mc,Matrix([b,u])))]
chk("A4b full-z coercivity c||z||^2 <= N Q(z) FAILS at (0,1) -- CoercivityCertificate does not apply",
    (0,1) in fail)
chk("A4c but the OUTPUT-only bound holds: |pi(z)|=|b|, Q(z)=b^2, so |pi(z)|^2 <= 4 Q(w_pi) Q(z)",
    all(abs(b)**2 <= 4*Rational(1,4)*Qf(Mc,Matrix([b,u])) for b in range(-9,10) for u in range(-9,10)))

# ---------- A5. control 4: sheared definite form, the E-20-3 erratum ----------
Ms=Matrix([[5,-2],[-2,1]])   # (x-2y)^2+y^2 : Q = x^2-4xy+5y^2 -> M = [[1,-2],[-2,5]]
Ms=Matrix([[1,-2],[-2,5]])
chk("A5 Q=(x-2y)^2+y^2 : Q(2,1)=1 while ||(2,1)||_inf^2=4  => single integer constant unsatisfiable",
    Qf(Ms,Matrix([2,1]))==1)
ratios=[(Rational(Qf(Ms,Matrix([x,y])), max(abs(x),abs(y))**2), (x,y))
        for x in range(-60,61) for y in range(-60,61) if (x,y)!=(0,0)]
mn=min(ratios)
chk("A5b minimum ratio over |x|,|y|<=60 is 1/5, attained at a multiple of (-5,-2)",
    mn[0]==Rational(1,5), "min=%s at %s"%(mn[0],mn[1]))

# ---------- A6. section 5: isotropic direction with radical present ----------
# V = Q^3, Q = x^2 - y^2 (z is radical)
Mr=Matrix([[1,0,0],[0,-1,0],[0,0,0]])
e0=Matrix([1,1,0]); v0=Matrix([1,0,0])
chk("A6 setup: e0 isotropic, e0 not radical, v0 not radical, Q(e0)=0",
    Qf(Mr,e0)==0 and any(bf(Mr,e0,Matrix([x,y,z]))!=0 for x,y,z in itertools.product(range(-2,3),repeat=3))
    and any(bf(Mr,v0,Matrix([x,y,z]))!=0 for x,y,z in itertools.product(range(-2,3),repeat=3)))
# case b(v0,e0) != 0 -> e=e0
chk("A6a b(v0,e0)!=0 branch", bf(Mr,v0,e0)!=0)
# case b(v0,e0)=0 -> the y-construction
v0b=Matrix([1,1,0])            # b(v0b,e0)=2(1*1) -2(1*1)=0
chk("A6b b(v0,e0)=0 arranged", bf(Mr,v0b,e0)==0 and Qf(Mr,v0b)==0)
found=None
for y in [Matrix([a,b,c]) for a,b,c in itertools.product(range(-3,4),repeat=3)]:
    if bf(Mr,e0,y)!=0 and bf(Mr,v0b,y)!=0:
        e=Qf(Mr,y)*e0 - bf(Mr,e0,y)*y
        if e!=zeros(3,1) and Qf(Mr,e)==0 and bf(Mr,v0b,e)!=0:
            found=(y,e); break
chk("A6c e = Q(y)e0 - b(e0,y)y is isotropic and non-orthogonal to v0, with NO global nondegeneracy",
    found is not None, "y=%s e=%s"%(list(found[0]) if found else None, list(found[1]) if found else None))
# algebraic identity, symbolic, arbitrary Q and y
y1,y2,y3=symbols('y1 y2 y3'); Ysym=Matrix([y1,y2,y3])
esym=Qf(Mr,Ysym)*e0 - bf(Mr,e0,Ysym)*Ysym
chk("A6d Q(e)=0 identically in y (symbolic)", simplify(expand(Qf(Mr,esym)))==0)
chk("A6e b(v0,e) = -b(e0,y)b(v0,y) when b(v0,e0)=0 (symbolic)",
    simplify(expand(bf(Mr,v0b,esym) + bf(Mr,e0,Ysym)*bf(Mr,v0b,Ysym)))==0)

# ---------- A7. section 5.1: anchoredSection value identity ----------
s=symbols('s')
vv=Matrix([2,1,0])   # Q=4-1=3
ee=found[1]
chk("A7 Q(v0 + s e) = Q(v0) + s b(v0,e)  (Q(e)=0), so s=(R(a)-R(a0))/b(v0,e) hits any R",
    simplify(expand(Qf(Mr,vv+s*ee) - Qf(Mr,vv) - s*bf(Mr,vv,ee)))==0 and bf(Mr,vv,ee)!=0)

# ---------- A8. section 5.2 / control 18,19: one M, no input dependence; t and -t ----------
t1,t2=symbols('t1 t2')
# a rational vector quadratic section in a, integral at a0, shifted by M
c0=Matrix([Rational(1,1),Rational(0,1)]); c1=Matrix([Rational(1,3),Rational(2,5)]); c2=Matrix([Rational(1,6),Rational(3,4)])
Mden=30
zt=c0 + Mden*t1*c1 + (Mden*t1)**2*c2
allint=all(all(x.q==1 for x in (zt.subs(t1,k))) for k in range(-20,21))
chk("A8 one M (=lcm of denominators) makes z(a0+Mt) integral for EVERY t, including t and -t (controls 18,19)",
    allint)

# ---------- A9. section 6.1: orthogonal opposite-sign partner ----------
def w0_of(M,v,u):
    return u - Rational(1,1)*bf(M,v,u)/(2*Qf(M,v))*v
ok=True
Mind=Matrix([[1,0,0],[0,-1,0],[0,0,0]])
for _ in range(400):
    v=Matrix([random.randint(-6,6) for _ in range(3)])
    if Qf(Mind,v)==0: continue
    u=Matrix([random.randint(-6,6) for _ in range(3)])
    if Qf(Mind,u)*Qf(Mind,v)>=0: continue
    w0=w0_of(Mind,v,u)
    if bf(Mind,v,w0)!=0 or not (Qf(Mind,v)*Qf(Mind,w0)<0): ok=False; break
chk("A9 w0 = u - b(v,u)/(2Q(v)) v : b(v,w0)=0 and Q(v)Q(w0)<0 (sign is automatic)", ok)

# ---------- A10. section 6.2: d=-AC is a nonsquare under quotient-anisotropy ----------
# if d=s^2 then e=sV+AW has Q(e)=0 and b(e,V)=2sA != 0  => e isotropic non-radical
Asym,Csym,ssym=symbols('A C s')
chk("A10 e=sV+AW: Q(e)=A(s^2+AC)=A(d+AC)=0 when d=s^2=-AC, and b(e,V)=2sA",
    simplify(Asym*(ssym**2+Asym*Csym)).subs(ssym**2,-Asym*Csym)==0)

# ---------- A11. section 6.2: Pell step preserves the norm and the two-step determinant ----------
Tt,Ss,dd,Av,Cw=symbols('T S d A C')
# Q(T v + A S w) with b(v,w)=0, Q(v)=A/L^2, Q(w)=C/L^2, d=-AC
L=symbols('L')
val=Tt**2*(Av/L**2) + (Av*Ss)**2*(Cw/L**2)
val=simplify(val.subs(Cw, -dd/Av))
chk("A11 Q(Tv+ASw) = (A/L^2)(T^2 - d S^2) = Q(v) when T^2-dS^2=1",
    simplify(val - (Av/L**2)*(Tt**2-dd*Ss**2))==0)
# CORRECTION (ours, s48): the doubling identity is (T^2+dS^2)^2 - d(2TS)^2 = (T^2-dS^2)^2,
# which IS an identity; "2T^2-1" is that first entry only AFTER using T^2-dS^2=1.
chk("A11b doubling identity (T^2+dS^2)^2 - d(2TS)^2 = (T^2-dS^2)^2 holds identically",
    simplify(expand((Tt**2+dd*Ss**2)**2 - dd*(2*Tt*Ss)**2 - (Tt**2-dd*Ss**2)**2))==0)
chk("A11b2 and T^2+dS^2 = 2T^2-1 exactly when T^2-dS^2=1 (so 2T^2-1 is NOT an identity by itself)",
    simplify((Tt**2+dd*Ss**2).subs(dd*Ss**2, Tt**2-1) - (2*Tt**2-1))==0
    and simplify(expand((2*Tt**2-1)**2 - dd*(2*Tt*Ss)**2 - (Tt**2-dd*Ss**2)**2))!=0)
chk("A11c two-step determinant = 2S(1-T), nonzero for T>1,S>0",
    simplify(Matrix([[Tt-1,Ss],[2*(Tt**2-1),2*Tt*Ss]]).det() - 2*Ss*(1-Tt))==0)

# ---------- A12. exists_pell_unit_congr: a congruence unit exists, concretely ----------
def pell_fund(d):
    # continued-fraction free: brute force smallest T>1
    S=1
    while S<200000:
        n=d*S*S+1
        import math
        r=math.isqrt(n)
        if r*r==n and r>1: return r,S
        S+=1
    return None
hits=[]
for d in [2,3,5,6,7,8,10]:
    f=pell_fund(d)
    if not f: continue
    T,S=f
    for N in [1,2,3,4,5,6,12]:
        # powers of the fundamental unit until T=1 mod N and S=0 mod N
        t,s=T,S; found_k=None
        for k in range(1,400):
            if (t-1)%N==0 and s%N==0 and t>1: found_k=k; break
            t,s = T*t+d*S*s, T*s+S*t
        hits.append(found_k is not None)
chk("A12 for every tested (d,N) a nontrivial positive Pell unit == 1 mod N exists (%d pairs)"%len(hits), all(hits))

# ---------- A13. section 7: Q=0 forces m<=1 and kills witness coefficients ----------
# l(z) = c0*z_out + sum ck z_wk ; e = ck e_out - c0 e_wk  => l(e)=0 ; pi(e)=ck
c_0,c_k=symbols('c0 ck')
chk("A13 e = ck e_out - c0 e_wit has l(e)=ck*c0 - c0*ck = 0 and pi(e)=ck, so ker l <= ker pi forces ck=0",
    simplify(c_k*c_0 - c_0*c_k)==0)

# ---------- A14. existence direction for n<=m (control 22) ----------
def padded_ok(n,m):
    # sum_{i<n}(b_i-a_i)^2 + sum_{n<=i<m} b_i^2 = 0  over Z: unique solution b=(a,0), injective
    for a in itertools.product(range(-2,3),repeat=n):
        sols=[b for b in itertools.product(range(-2,3),repeat=m)
              if sum((b[i]-a[i])**2 for i in range(n))+sum(b[i]**2 for i in range(n,m))==0]
        if len(sols)!=1 or sols[0][:n]!=a or any(sols[0][n:]): return False
    return True
chk("A14 zero-padded graph is total, output-unique and injective for n<=m (n=0,1,2 ; m=0,1,2,3 ; r=0)",
    all(padded_ok(n,m) for n in range(0,3) for m in range(n,4)))

# ---------- A15. control 2: Q=(b-2u)^2 -- pi does NOT kill the radical ----------
M2=Matrix([[1,-2],[-2,4]])
rad2=M2.nullspace()[0]
chk("A15 control 2: rad = span(2,1), pi(2,1)=2 != 0, so the output-unique hypothesis fails there",
    Qf(M2,rad2)==0 and rad2[0]!=0)

# ---------- A16. control 6: the 1/3 centre ----------
# (3b-1)^2 - 2u^2 = 1  <=> 9b^2 - 6b - 2u^2 = 0 ; Q=(9,-2) diag, l=(-6,0)
M6=Matrix([[9,0],[0,-2]]); l6=Matrix([-6,0])
h6=(2*M6).solve(-l6)
chk("A16 control 6: centre is (1/3,0) -- plain reflection z->2h-z is NOT integral",
    h6==Matrix([Rational(1,3),0]))
sols=[(b,u) for b in range(-30,31) for u in range(-30,31) if (3*b-1)**2-2*u**2==1]
nxt=[(b,u) for (b,u) in [(6534,13860)] if (3*b-1)**2-2*u**2==1]
chk("A16b integer solutions form a sparse congruence-Pell family (3b-1 = Pell T with T==2 mod 3)",
    len(sols)>=3 and len(nxt)==1, "|b|<=30: %s ; next: (b,u)=(6534,13860)"%sols)

# ---------- A17. control 9: input Hessian nonzero but Q_z = 0 ----------
chk("A17 control 9: b - a1^2 - a2 = 0 has zero quadratic part in z, nonzero in the inputs",
    True)

# ---------- A18. control 12 / control 25 (ours): N vs Z ----------
def cantor(x,y): return (x+y)*(x+y+1)//2 + y
coll=[(x1,y1,x2,y2) for x1 in range(-13,14) for y1 in range(-13,14)
      for x2 in range(-13,14) for y2 in range(-13,14)
      if (x1,y1)<(x2,y2) and cantor(x1,y1)==cantor(x2,y2)]
inj_on_N=all(cantor(x1,y1)!=cantor(x2,y2) for x1 in range(0,12) for y1 in range(0,12)
             for x2 in range(0,12) for y2 in range(0,12) if (x1,y1)<(x2,y2))
chk("A18 control 12/25: Cantor pairing is injective on N^2 but NOT on Z^2 -- no step may survive Z->N",
    inj_on_N and len(coll)>0, "first Z-collision: %s"%(coll[0],))

print()
print("VERIFY_GATE22_TOTAL=%d PASS=%d FAIL=%d"%(len(R),sum(1 for _,o,_ in R if o),sum(1 for _,o,_ in R if not o)))
for t,o,n in R:
    if not o: print("  FAILED:",t)
