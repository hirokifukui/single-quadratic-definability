import sympy as sp, random
random.seed(20260925)
def run(sign=+1, trials=300):
    ok=True
    for _ in range(trials):
        n=random.randint(3,6)
        S=sp.Matrix(n,n,lambda i,j:0)
        for i in range(n):
            for j in range(i,n):
                S[i,j]=S[j,i]=sp.Rational(random.randint(-5,5),random.randint(1,3))
        Q=lambda x:(x.T*S*x)[0]; P=lambda x,y:2*(x.T*S*y)[0]
        # isotropic e: take random y, z and solve Q(y+s z)=0 rationally when possible: use e = Q(z)*y - ... simpler: pick e with Q(e)=0 by
        # e = y - (Q(y)/P(y,w)) w where Q(w)=0? fallback: construct S to have isotropic e1 by forcing S[0,0]=0
        S[0,0]=0; e=sp.zeros(n,1); e[0]=1
        v=sp.Matrix([sp.Rational(random.randint(-6,6),random.randint(1,4)) for _ in range(n)])
        if P(e,e+sp.zeros(n,1))!=0: pass
        pe=P(e,v)
        # project v to e-perp using some y with P(e,y)!=0
        y=None
        for i in range(n):
            ui=sp.zeros(n,1); ui[i]=1
            if P(e,ui)!=0: y=ui;break
        if y is None: continue
        v=v-(pe/P(e,y))*y
        assert P(e,v)==0 and Q(e)==0
        x=sp.Matrix([sp.Rational(random.randint(-6,6),random.randint(1,4)) for _ in range(n)])
        t=sp.Rational(random.randint(-5,5),random.randint(1,3))
        Ex=x+P(x,e)*(t*v)-(P(x,t*v)+sign*Q(t*v)*P(x,e))*e
        ok&=(Q(Ex)==Q(x))
        A=P(x,e)*v-P(x,v)*e; B=-Q(v)*P(x,e)*e
        if sign==1: ok&=(Ex-x==t*A+t**2*B)
    return ok
print("EICHLER preserves Q (300 random exact instances, n=3..6):", run(+1))
print("CONTROL sign-flipped Eichler preserves Q:", run(-1,60), "(must be False)")
import random as R
ok=True; cnt=0
for _ in range(4000):
    a,b,c=[R.randint(-9,9) for _ in range(3)]
    if a==0 and b==0: continue
    K=R.randint(1,12); F=lambda k:a*k*k+b*k+c; found=False
    for k1 in range(0,3):
        if F(k1)==0: continue
        for s in range(1,6):
            k0=k1+K*F(k1)*s; lam=F(k0)//F(k1); assert F(k0)==F(k1)*lam and (lam-1)%K==0
            if lam not in (0,1): found=True;break
        if found: break
    ok&=found; cnt+=1
print("lambda lemma (k1 in 0..2 with F(k1)!=0, s in 1..5): found in all", cnt, ":", ok)
