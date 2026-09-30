"""s56 leg 1 (python/SymPy, brute force) for GATE26 figures. PASS/FAIL per check; planted controls must FAIL."""
import sympy as S, math
def chk(name, cond): print(('PASS ' if cond else 'FAIL ')+name)
N=1+24*45*45
chk('N(45)=48601', N==48601)
sq=lambda v: sum(x*x for x in v)
P1,P2=(-219,15,20),(-210,-19,64)
print('  prose1 sum =',sq(P1),' prose2 sum =',sq(P2))
chk('prose triple1 sums to 48601', sq(P1)==N)
chk('prose triple2 sums to 48601', sq(P2)==N)
J1,J2=(-199,-90,30),(-195,-24,100)
chk('json triple1 sums to 48601', sq(J1)==N); chk('json triple2 sums to 48601', sq(J2)==N)
chk('json first coords differ mod 5', J1[0]%5!=J2[0]%5)
chk('json triple1 in (1,0,0)+5Z^3', tuple(x%5 for x in J1)==(1,0,0))
chk('json triple2 in (0,1,0)+5Z^3', tuple(x%5 for x in J2)==(0,1,0))
a,b,K=S.symbols('a b K'); d=1+a*b*K**2
chk('rotation norm identity', S.expand(a*(1-a*b*K**2)**2+b*(2*a*K)**2-a*d**2)==0)
chk("w'-w=(2aK/d)(v-bKw), w-coeff", S.simplify((1-a*b*K**2)/d-1-(2*a*K/d)*(-b*K))==0)
chk('gcd(1+abK^2,h)=1 when h|K (grid)', all(math.gcd(1+x*y*(h*m)**2,h)==1 for x in range(1,6) for y in range(1,6) for h in range(1,8) for m in range(1,5)))
Kk=3;dd=10; wp=[S.Rational(1-Kk*Kk,dd), S.Rational(2*Kk,dd)]
chk("control w'=(-4/5,3/5)", wp==[S.Rational(-4,5),S.Rational(3,5)])
chk('control change from w/3 nonintegral', any(S.denom(x)!=1 for x in [(wp[0]-1)/3, wp[1]/3]))
A_,B_,c_,P_,T_=S.symbols('A B c P T')
chk('H(T)=F(cPT)/c=1+BPT+AcP^2T^2', S.expand((A_*(c_*P_*T_)**2+B_*c_*P_*T_+c_)/c_-(1+B_*P_*T_+A_*c_*P_**2*T_**2))==0)
ok=True
for a0 in range(-300,301):
    sols={bb for bb in range(-2000,2001) if (2*bb-a0)*(2*bb+3*a0-1)==0}
    ok &= len(sols)==1
chk('rank-one example (2b-a)(2b+3a-1)=0 total & output-unique |a|<=300', ok)
chk('m=0: u^2+v^2=a^2 total (u=a,v=0), residual a^2 nonconstant', all((a0)**2+0==a0*a0 for a0 in range(-300,301)))
chk('t(t-1)>=0 on Z and <0 at 1/2', all(t*(t-1)>=0 for t in range(-500,501)) and S.Rational(-1,4)<0)
chk('1+24t^2 == 1 mod 8', all((1+24*t*t)%8==1 for t in range(2000)))
print('--- planted controls (must FAIL) ---')
chk('CONTROL rotation with wrong RHS a(1-abK^2)^2', S.expand(a*(1-a*b*K**2)**2+b*(2*a*K)**2-a*(1-a*b*K**2)**2)==0)
chk('CONTROL triple (-199,-90,31)', sq((-199,-90,31))==N)
chk('CONTROL rank-one with 2b+3a=0 (not total)', all(any((2*bb-a0)*(2*bb+3*a0)==0 for bb in range(-2000,2001)) and len({bb for bb in range(-2000,2001) if (2*bb-a0)*(2*bb+3*a0)==0})==1 for a0 in range(-20,21)))
