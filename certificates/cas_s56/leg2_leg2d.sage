
set_random_seed(20260925)
bad = 0; tested = 0
for s in [2,3,4]:
    for it in range(10):
        while True:
            Bm = random_matrix(ZZ, s, s, x=-2, y=3); A = Bm.transpose()*Bm + identity_matrix(ZZ, s)
            if A.is_positive_definite(): break
        while True:
            wl = [randint(-3,3) for _ in range(s)]
            if any(wl): break
        g = gcd(wl); w = vector(ZZ, [c//g for c in wl])
        km = matrix(QQ, [list(A*w)]).right_kernel_matrix()
        vq = vector(QQ, list(km.row(0))); v = vector(ZZ, list(vq * lcm([c.denominator() for c in vq])))
        a = ZZ(w.dot_product(A*w)); b = ZZ(v.dot_product(A*v))
        assert w.dot_product(A*v) == 0
        h = randint(1,3); e = randint(-4,4); Nn = randint(1,5)
        Kk = Nn*h
        if w[0] == 0 and v[0] == 0: continue
        while (v - b*Kk*w)[0] == 0: Kk += Nn*h
        d = ZZ(1 + a*b*Kk^2)
        wp = ((1 - a*b*Kk^2)*vector(QQ,w) + 2*a*Kk*vector(QQ,v))/d
        t = ((-e) * inverse_mod(h, d)) % d
        if h*t + e == 0: t += d
        delta = ((h*t + e)/Nn) * (wp - vector(QQ,w))
        tested += 1
        ok = (wp.dot_product(A*wp) == a) and all(c.denominator()==1 for c in delta) and delta[0] != 0 and gcd(d,h)==1 and (h*t+e) % d == 0
        bad += (not ok)
print("ROTATION_LATTICE_TESTED", tested, "BAD", bad, "PASS" if bad==0 else "FAIL")
w = vector(QQ,[1,0]); v = vector(QQ,[0,1]); Kk=3; d=10
wp = ((1 - Kk^2)*w + 2*Kk*v)/d
delta = (1/3)*(wp - w)
print("CONTROL_CAUGHT", 1 if any(c.denominator()!=1 for c in delta) else 0, "wp", wp)
R.<a,b,Kv> = QQ[]
print("rotation scalar identity", "PASS" if a*(1-a*b*Kv^2)^2 + b*(2*a*Kv)^2 - a*(1+a*b*Kv^2)^2 == 0 else "FAIL")
