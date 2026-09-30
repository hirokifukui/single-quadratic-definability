# s59: diagnose leg2 K3 group-lemma FAIL, then re-run with plain tuples.
import itertools
A = AdditiveAbelianGroup([12, 4]); els = list(A)
S = A.submodule([els[1]])
x = list(S)[1]
print("DIAG parent(sub elt) =", x.parent() is A, "; in els:", x in els, "; hash-equal to some elt:", any(hash(x) == hash(y) and x == y for y in els))
# plain model: Z/12 x Z/4 as tuples
G = [(i, j) for i in range(12) for j in range(4)]
add = lambda u, v: ((u[0]+v[0]) % 12, (u[1]+v[1]) % 4)
def closure(gens):
    S = {(0, 0)}; frontier = [(0, 0)]
    while frontier:
        u = frontier.pop()
        for g in gens:
            w = add(u, g)
            if w not in S: S.add(w); frontier.append(w)
    return frozenset(S)
subs = {closure([u, v]) for u in G for v in G}
print("SUBGROUPS", len(subs))
cov = bad = 0; idx3 = 0
for H in subs:
    for K in subs:
        for b in G:
            bK = frozenset(add(b, k) for k in K)
            if not (H & bK) and len(H) + len(K) == len(G):
                cov += 1
                if not (H == K and 2 * len(H) == len(G)): bad += 1; print("BAD", sorted(H)[:4], sorted(K)[:4], b)
                if 3 * len(H) == len(G): idx3 += 1
print(("PASS" if cov > 0 and bad == 0 else "FAIL") + " K3' group lemma on Z/12xZ/4 (tuples): covers=%d bad=%d" % (cov, bad))
print(("CAUGHT" if idx3 == 0 else "MISSED") + " control K3' an index-3 cover exists")
# planted control that must be caught: drop disjointness -> non-index-2 'covers' appear
loose = sum(1 for H in subs for K in subs for b in G if len(H | frozenset(add(b, k) for k in K)) == len(G) and not (H == K and 2*len(H) == len(G)))
print(("CAUGHT" if loose > 0 else "MISSED") + " control K3' without disjointness the conclusion fails (%d instances)" % loose)
