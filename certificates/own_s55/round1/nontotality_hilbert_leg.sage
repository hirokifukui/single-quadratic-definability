# Independent leg: for each certified row, P(t) must NOT be a norm from Q(sqrt(-D)), i.e. some local
# Hilbert symbol (P(t), -D)_v equals -1 (v a prime or infinity).  Uses Sage's hilbert_symbol only.
# Planted control: a genuine value X^2 + D Y^2 must be reported as a norm.
import csv
rows = list(csv.DictReader(open('nontotality_certificates_sample.tsv'), delimiter='\t'))
def is_norm(q, D):
    if q == 0: return True
    ps = set(prime_divisors(2*q*D))
    places = list(ps) + [-1]
    return all(hilbert_symbol(q, -D, v) == 1 for v in places)
bad = 0
for r in rows:
    q = Integer(r['P(t)']); D = Integer(r['D'])
    if is_norm(q, D): bad += 1
plant = [(Integer(3)**2 + 5*Integer(2)**2, 5), (Integer(1) + 2*Integer(3)**2, 2)]
plant_ok = all(is_norm(q, D) for q, D in plant)
print("HILBERT_ROWS=%d HILBERT_NORM_FOUND=%d PLANT_NORMS_DETECTED=%s" % (len(rows), bad, plant_ok))
print("HILBERT_LEG_EXIT=%d" % (0 if bad == 0 and plant_ok else 1))
