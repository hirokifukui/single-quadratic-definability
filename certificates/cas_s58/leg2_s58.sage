# s58 GATE28 leg 2 (Sage 10.8). Independent of leg 1 and of GPT's script: other instances, other methods.
import itertools, sys
res=[]; ctl=[]
def ok(nm,c): res.append(bool(c)); print(("PASS " if c else "FAIL ")+nm)
def plant(nm,wrong): ctl.append(not wrong); print(("CAUGHT " if not wrong else "MISSED ")+"control "+nm)
# S1 exponents in QQ
e=QQ(1)/56; lo=QQ(1)/2-e; hi=QQ(3)/7+e
ok("S1 27/56 and 25/56", (lo,hi)==(QQ(27)/56,QQ(25)/56))
Rn.<N,c,C>=PolynomialRing(QQ)  # with N = X^56: cX^27 - CX^25 = X^25 (cX^2 - C)
X=polygen(QQ,'X'); cc,CC=3/10,5
p=cc*X^27-CC*X^25
ok("S1 factor X^25(cX^2-C)", p==X^25*(cc*X^2-CC))
x0=(2*CC/cc)^(1/2)   # X0 = N0^(1/56) with N0=(2C/c)^28
ok("S1 positive just above N0=(2C/c)^28", RR(p(RR(x0)*1.0001))>0)
plant("S1 eps=1/28 gap positive", QQ(1)/2-QQ(1)/28-(QQ(3)/7+QQ(1)/28)>0)
# S2 b-a
R2.<a,b>=PolynomialRing(ZZ); P2=b-a
ok("S2 Q=0 and linear coeff of b is 1", P2.coefficient({b:2})==0 and P2.coefficient({b:1,a:0})==1)
ok("S2 total+unique", all(len([y for y in range(-50,51) if P2(x,y)==0])==1 for x in range(-30,31)))
plant("S2 linear part vanishes", P2.coefficient({b:1,a:0})==0)
# S3 V1 on instance n=1, m=3, M=4 (four residues)
M=4; Bm=matrix(ZZ,3,1,[1,-2,0]); beta={0:vector(ZZ,[0,1,-1]),1:vector(ZZ,[2,0,3]),2:vector(ZZ,[-1,-1,0]),3:vector(ZZ,[1,2,2])}
def f(x): r=x%M; u=(x-r)//M; return beta[r]+Bm.column(0)*u
names=['aa']+['b%d'%j for j in range(3)]+['u']+['e%d'%k for k in range(M)]
R3=PolynomialRing(ZZ,names); g=R3.gens(); A=g[0]; Bv=vector(g[1:4]); U=g[4]; E=g[5:9]
def V1(sign=1,boolean=True):
    delta={r: sign*(M*beta[r]-Bm.column(0)*r) for r in range(M)}
    s=(sum(E)-1)^2+(sum(t*(t-1) for t in E) if boolean else 0)+(A-M*U-sum(r*E[r] for r in range(M)))^2
    w=M*Bv-Bm.column(0)*A-sum(delta[r]*E[r] for r in range(M))
    return s+sum(t^2 for t in w)
P=V1()
ok("S3 total degree 2", P.degree()==2)
unk=list(g[1:])
H=matrix(QQ,len(unk),len(unk),lambda i,j: P.derivative(unk[i]).derivative(unk[j]))/2
ok("S3 unknown quadratic part positive definite", H.is_positive_definite())
ok("S3 CommonSlope of table", all(f(x+M*t)==f(x)+Bm.column(0)*t for x in range(-20,21) for t in range(-5,6)))
def witness(x):
    r=x%M; u=(x-r)//M; return [x]+list(f(x))+[u]+[1 if k==r else 0 for k in range(M)]
ok("S3 graph point has zero witness", all(P(*witness(x))==0 for x in range(-40,41)))
# nonzero outputs: P=0 forces (by nonneg terms) e boolean one-hot; enumerate those exactly, u solved from a
bad=0
for x in range(-12,13):
    for rr in range(M):
        ee=[1 if k==rr else 0 for k in range(M)]
        if (x-rr)%M: continue
        u=(x-rr)//M
        for db in itertools.product(range(-2,3),repeat=3):
            yb=f(x)+vector(ZZ,db)
            v=P(*([x]+list(yb)+[u]+ee))
            if (v==0)!=(db==(0,0,0)): bad+=1
ok("S3 on one-hot witnesses, zero iff b=f(a)", bad==0)
# non-boolean e box: all values >= 0 and no zero
neg=zer=0
for x in range(-3,4):
  for u in range(-2,2):
    for ee in itertools.product(range(-1,3),repeat=M):
      if sum(1 for t in ee if t in (0,1))==M: continue
      for db in itertools.product(range(-1,2),repeat=3):
        v=P(*([x]+list(f(x)+vector(ZZ,db))+[u]+list(ee)))
        neg+= v<0; zer+= v==0
ok("S3 non-boolean witnesses never give 0, never negative", neg==0 and zer==0)
Pw=V1(sign=-1)
plant("S3 delta with flipped sign still vanishes on the graph", all(Pw(*witness(x))==0 for x in range(-10,11)))
Pb=V1(boolean=False); found=False
for x in range(-2,3):
  for u in range(-2,2):
    for ee in itertools.product(range(-2,3),repeat=M):
      for db in itertools.product(range(-3,4),repeat=3):
        if db!=(0,0,0) and Pb(*([x]+list(f(x)+vector(ZZ,db))+[u]+list(ee)))==0: found=True;break
      if found: break
    if found: break
  if found: break
plant("S3 without e(e-1) the graph is still defined", not found)
# S4 padding
R4.<y,m>=PolynomialRing(ZZ); d=(y+m)^2-y^2
ok("S4 (a+M)^2-a^2=2Ma+M^2 depends on a", d==2*m*y+m^2 and d.degree(y)==1)
plant("S4 difference independent of a", d.degree(y)==0)
# S5 scalar control via factor roots over QQ
R5.<t>=PolynomialRing(QQ)
vals={}
for x in range(-40,41):
    q=(2*t-x)*(2*t+3*x-1); rts=[rt for rt,_ in q.roots() if rt in ZZ]; vals[x]=rts
ok("S5 exactly one integer root each a", all(len(v)==1 for v in vals.values()))
ok("S5 f(2t)=t, f(2t+1)=-3t-1", all(vals[2*k][0]==k for k in range(-20,21)) and all(vals[2*k+1][0]==-3*k-1 for k in range(-20,20)))
cs=lambda MM: len({vals[x+MM][0]-vals[x][0] for x in range(-40,41-MM)})==1
ok("S5 no common slope M=1..16", not any(cs(MM) for MM in range(1,17)))
plant("S5 common slope with M=4", cs(4))
# S6 divisor lemma identity symbolically: F(k1+K F1 s) = F1*(1+sX+s^2Y) with X,Y integral and K|X,Y? (only λ≡1 mod K needed)
R6.<al,be,ga,k1,K,s>=PolynomialRing(ZZ)
F=lambda k: al*k^2+be*k+ga; F1=F(k1)
diff=F(k1+K*F1*s)-F1
qq,rr=diff.quo_rem(F1*K*s)
ok("S6 F(k0)-F(k1) = F(k1)*K*s*(integral poly)", rr==0)
mu=1+K*s*qq
ok("S6 F(k0)=F(k1)*mu with mu ≡ 1 mod K", F(k1+K*F1*s)==F1*mu)
lam=polygen(ZZ,'lam'); jj=polygen(ZZ,'jj')
R7.<al2,be2,ga2,k0,L,j>=PolynomialRing(ZZ)
G=lambda k: al2*k^2+be2*k+ga2
ok("S6 G(k0+L j) ≡ G(k0) mod L", ((G(k0+L*j)-G(k0)).quo_rem(L))[1]==0)
plant("S6 mu ≡ 1 mod 2K", ((mu-1).quo_rem(2*K))[1]==0)
# S7 A4 step, general symmetric Gram, polar with Q(x)=x^T S x
R8=PolynomialRing(QQ,['s%d%d'%(i,j) for i in range(4) for j in range(i,4)]+['x%d'%i for i in range(4)]+['e%d'%i for i in range(4)]+['NN'])
gg=R8.gens(); sv=gg[:10]; xs=vector(gg[10:14]); es=vector(gg[14:18]); NN=gg[18]
S=matrix(R8,4,4); k=0
for i in range(4):
    for jx in range(i,4): S[i,jx]=sv[k]; S[jx,i]=sv[k]; k+=1
Qf=lambda v: v*S*v; pol=lambda v,w: Qf(v+w)-Qf(v)-Qf(w)
ok("S7 Q(x+Ne)=Q(x)+N polar(x,e)+N^2 Q(e)", Qf(xs+NN*es)==Qf(xs)+NN*pol(xs,es)+NN^2*Qf(es))
plant("S7 Q(x+Ne)=Q(x)+N polar(x,e) (drops N^2Q(e))", Qf(xs+NN*es)==Qf(xs)+NN*pol(xs,es))
# S8 injectivity criterion n=1 via gcd/divisibility, instances enumerated (not random)
def fx(Mm,Bc,bt,x): r=x%Mm; return tuple(bt[r][jx]+Bc[jx]*((x-r)//Mm) for jx in range(len(Bc)))
def inj(Mm,Bc,bt): return len({fx(Mm,Bc,bt,x) for x in range(-30,31)})==61
def crit(Mm,Bc,bt):
    if all(v==0 for v in Bc): return False
    for r1,r2 in itertools.combinations(range(Mm),2):
        dv=[bt[r1][jx]-bt[r2][jx] for jx in range(len(Bc))]
        # dv in Bc*ZZ ?
        nz=[jx for jx in range(len(Bc)) if Bc[jx]!=0]; t0=QQ(dv[nz[0]])/Bc[nz[0]]
        if t0 in ZZ and all(dv[jx]==t0*Bc[jx] for jx in range(len(Bc))): return False
    return True
agree=tot=0
for Mm in (1,2,3):
  for Bc in itertools.product(range(-2,3),repeat=2):
    for vals0 in itertools.product(range(-2,3),repeat=2*Mm) if Mm<3 else itertools.islice(itertools.product(range(-2,3),repeat=6),0,3000,7):
      bt={r:(vals0[2*r],vals0[2*r+1]) for r in range(Mm)}
      tot+=1; agree+= inj(Mm,Bc,bt)==crit(Mm,Bc,bt)
ok("S8 injectivity criterion agrees on %d instances"%tot, agree==tot)
plant("S8 B injective alone suffices", all(inj(2,(2,0),{0:(0,0),1:(2,0)})==True for _ in [0]))
print("LEG2_SUMMARY %d/%d  CONTROLS_CAUGHT %d/%d"%(sum(res),len(res),sum(ctl),len(ctl)))
sys.exit(0 if all(res) and all(ctl) else 1)
