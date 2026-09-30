#!/usr/bin/env python3
"""s59 truth check for H3 `slopeEncoder_eval_scale` (symbolic, SymPy): P(a, t b, t u, t e) = t^2 Q + t L + P(a,0,0,0),
with Q and L as frozen.  Planted control: L with -2 instead of -3 on sum(e) must fail."""
import itertools, sympy as sp
def check(n, m, M, coefL=-3):
    R = list(itertools.product(range(M), repeat=n))
    a = sp.symbols('a0:%d' % n); b = sp.symbols('b0:%d' % m); u = sp.symbols('u0:%d' % n); e = sp.symbols('e0:%d' % len(R))
    t = sp.Symbol('t')
    B = sp.Matrix(m, n, lambda j, i: sp.Symbol('B%d%d' % (j, i)))
    beta = {(r, j): sp.Symbol('be%d_%d' % (k, j)) for k, r in enumerate(R) for j in range(m)}
    delta = lambda k, j: M * beta[(R[k], j)] - sum(B[j, i] * R[k][i] for i in range(n))
    def P(bb, uu, ee):
        return ((sum(ee) - 1) ** 2 + sum(x * (x - 1) for x in ee)
                + sum((a[i] - M * uu[i] - sum(R[k][i] * ee[k] for k in range(len(R)))) ** 2 for i in range(n))
                + sum((M * bb[j] - sum(B[j, i] * a[i] for i in range(n)) - sum(delta(k, j) * ee[k] for k in range(len(R)))) ** 2 for j in range(m)))
    Q = (sum(e) ** 2 + sum(x ** 2 for x in e) + sum((M * u[i] + sum(R[k][i] * e[k] for k in range(len(R)))) ** 2 for i in range(n))
         + sum((M * b[j] - sum(delta(k, j) * e[k] for k in range(len(R)))) ** 2 for j in range(m)))
    L = (coefL * sum(e) - 2 * sum(a[i] * (M * u[i] + sum(R[k][i] * e[k] for k in range(len(R)))) for i in range(n))
         - 2 * sum(sum(B[j, i] * a[i] for i in range(n)) * (M * b[j] - sum(delta(k, j) * e[k] for k in range(len(R)))) for j in range(m)))
    lhs = P([t * x for x in b], [t * x for x in u], [t * x for x in e])
    rhs = t ** 2 * Q + t * L + P([0] * m, [0] * n, [0] * len(R))
    return sp.expand(lhs - rhs) == 0
ok = all(check(*c) for c in [(1, 1, 2), (1, 2, 2), (2, 1, 2), (1, 1, 3)])
print(("PASS" if ok else "FAIL") + " H3 scale identity (n,m,M) in {(1,1,2),(1,2,2),(2,1,2),(1,1,3)}, symbolic B, beta")
print(("CAUGHT" if not check(1, 1, 2, coefL=-2) else "MISSED") + " control L with -2*sum(e)")
