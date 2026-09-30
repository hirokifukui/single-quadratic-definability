# D3 finite-table example: f(a+M t) = f(a) + B t with M = 2, n = 1, m = 2.  Brute force vs the finite criterion.
M = 2
def mk(table, B):
    def f(a):
        u, r = divmod(a, M)
        return (table[r][0] + B[0]*u, table[r][1] + B[1]*u)
    return f
cases = {'inj': ([(0,0),(1,1)], (2,0)), 'noninj': ([(0,0),(0,0)], (1,0)), 'plant_overlap': ([(0,0),(2,0)], (2,0))}
R = range(-40, 41)
for name, (tab, B) in cases.items():
    f = mk(tab, B)
    # common slope check
    assert all(f(a + M*t) == (f(a)[0]+B[0]*t, f(a)[1]+B[1]*t) for a in R for t in range(-5,6))
    brute = len({f(a) for a in R}) == len(R)
    kerB = (B != (0,0))
    def inBZ(v):
        if B == (0,0): return v == (0,0)
        cand = [v[i]//B[i] for i in range(2) if B[i] != 0]
        k = cand[0]; return (B[0]*k, B[1]*k) == v
    sep = all(not inBZ((tab[r][0]-tab[s][0], tab[r][1]-tab[s][1])) for r in range(M) for s in range(M) if r != s)
    crit = kerB and sep
    img_ok = {f(a) for a in range(-10, 10)} <= {(tab[r][0]+B[0]*u, tab[r][1]+B[1]*u) for r in range(M) for u in range(-10, 10)}
    print(name, 'BRUTE_INJ=%s CRITERION=%s IMAGE_SUBSET=%s' % (brute, crit, img_ok), 'AGREE' if brute == crit else 'DISAGREE')
