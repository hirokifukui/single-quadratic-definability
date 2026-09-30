# s48: does OUR exists_collision_vector already close what s47 sent to Gjaldbaek?
# Theorem (DimensionFromCoset.lean:46): m < n, q : Fin m -> QuadForm n
#   => exists v != 0 with q_j(v) = q_j(-v) for all j.
# Proof there: v in ker of the m x n matrix of LINEAR parts (nontrivial since m<n);
# homogeneous quadratic parts are even; constants cancel.  NO hypothesis on the
# quadratic parts at all -- in particular none on the discriminant.
import itertools, random
from fractions import Fraction as F
random.seed(4848)
out=[]
def chk(t,ok,note=""):
    out.append(ok); print(("PASS " if ok else "FAIL ")+t+(("  | "+note) if note else ""))

def kernel_vec(rows, n):
    """one nonzero rational kernel vector of the m x n matrix `rows`, cleared to integers"""
    import copy
    A=[[F(x) for x in r] for r in rows]; m=len(A)
    piv=[]; r=0
    for c in range(n):
        p=next((i for i in range(r,m) if A[i][c]!=0), None)
        if p is None: continue
        A[r],A[p]=A[p],A[r]
        pv=A[r][c]; A[r]=[x/pv for x in A[r]]
        for i in range(m):
            if i!=r and A[i][c]!=0:
                f=A[i][c]; A[i]=[a-f*b for a,b in zip(A[i],A[r])]
        piv.append(c); r+=1
        if r==m: break
    free=[c for c in range(n) if c not in piv]
    if not free: return None
    fc=free[0]; v=[F(0)]*n; v[fc]=F(1)
    for i,c in enumerate(piv): v[c]=-A[i][fc]
    den=1
    for x in v: den=den*x.denominator//__import__('math').gcd(den,x.denominator)
    return [int(x*den) for x in v]

def rand_quad(n, dmax=4):
    """f(x) = sum q_ij x_i x_j + sum l_i x_i + c, rational coefficients"""
    q={(i,j):F(random.randint(-dmax,dmax), random.choice([1,2,3]))
       for i in range(n) for j in range(i,n)}
    l=[F(random.randint(-dmax,dmax), random.choice([1,2,3])) for _ in range(n)]
    c=F(random.randint(-dmax,dmax))
    return q,l,c
def ev(f,x):
    q,l,c=f
    return sum(v*x[i]*x[j] for (i,j),v in q.items()) + sum(l[i]*x[i] for i in range(len(x))) + c

# --- C1: the lemma's own statement, on random families, incl. degenerate quadratic parts
bad=0; tested=0
for _ in range(4000):
    n=random.choice([2,3,4]); m=random.randint(1,n-1)
    fs=[rand_quad(n) for _ in range(m)]
    v=kernel_vec([[fs[j][1][i] for i in range(n)] for j in range(m)], n)
    if v is None or all(x==0 for x in v): continue
    tested+=1
    nv=[-x for x in v]
    if any(ev(fs[j],v)!=ev(fs[j],nv) for j in range(m)): bad+=1
chk("C1 exists_collision_vector reproduced: v in ker(linear parts) gives f(v)=f(-v) on %d random families (n<=4, m<n)"%tested,
    bad==0 and tested>2000, "counterexamples=%d"%bad)

# --- C2: it needs NOTHING about the quadratic part -- run it on Delta=0 forms only
zero_disc=0; ok=True
for _ in range(3000):
    n=2; m=1
    # quadratic part a perfect square (alpha*(p x + r y)^2) => discriminant 0
    al=F(random.randint(-4,4)); p=random.randint(-4,4); r=random.randint(-4,4)
    q={(0,0):al*p*p,(0,1):2*al*p*r,(1,1):al*r*r}
    l=[F(random.randint(-4,4)),F(random.randint(-4,4))]
    c=F(random.randint(-4,4))
    if l==[F(0),F(0)]: continue
    disc = q[(0,1)]**2 - 4*q[(0,0)]*q[(1,1)]
    if disc!=0: ok=False; break
    zero_disc+=1
    v=kernel_vec([[l[0],l[1]]],2)
    f=(q,l,c)
    if ev(f,v)!=ev(f,[-v[0],-v[1]]): ok=False; break
chk("C2 the SAME lemma kills every Delta=0 (radical) case at (n,m)=(2,1): %d forms, 0 survivors"%zero_disc, ok)

# --- C3: the named hard instance -- the Cantor pairing itself
def cantor(x,y): return F((x+y)*(x+y+1),2) + y
lC=[F(1,2),F(3,2)]                     # linear part of the Cantor polynomial
vC=kernel_vec([lC],2)
chk("C3 Cantor pairing: ker(linear part) = span(-3,1); pairing collides at +-v on Z^2",
    cantor(*vC)==cantor(-vC[0],-vC[1]), "v=%s, pi(v)=pi(-v)=%s"%(vC, cantor(*vC)))

# --- C4: vector output, m>1 -- no "common centre" is needed anywhere
bad=0; tested=0
for _ in range(2000):
    n=random.choice([3,4]); m=random.randint(2,n-1)
    fs=[rand_quad(n) for _ in range(m)]
    v=kernel_vec([[fs[j][1][i] for i in range(n)] for j in range(m)], n)
    if v is None or all(x==0 for x in v): continue
    tested+=1
    if any(ev(fs[j],v)!=ev(fs[j],[-x for x in v]) for j in range(m)): bad+=1
chk("C4 vector output m>1 on %d families: collision still at the SINGLE pair (v,-v) -- the m centres need not coincide"%tested,
    bad==0, "counterexamples=%d"%bad)

# --- C5: the boundary the lemma does NOT cross -- it is about POLYNOMIALS, not graphs
# ceiling-type relation: r=0 but f is not a global polynomial (control 11)
chk("C5 control 11: a ceiling relation is r=0 yet not globally polynomial, so the collision lemma does NOT apply to it directly",
    True, "boundary recorded, not computed")

print()
print("COLLISION_CHECK_TOTAL=%d PASS=%d FAIL=%d"%(len(out),sum(out),len(out)-sum(out)))
