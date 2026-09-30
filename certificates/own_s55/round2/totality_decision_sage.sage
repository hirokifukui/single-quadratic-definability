# totality_decision_sage.sage — independent leg for totality_decision.py (s55 own initiative, round 2).
# Uses only Sage's norm test in a number field (QQ(q).is_norm(K)), not our Hilbert-symbol code.
#   TOTAL rows: P(t) must be a norm from K = Q(sqrt(-D)) for every t in [-6, 6].
#   NOT rows:   P(t) must NOT be a norm at the certificate's t.
# Planted control: a fake TOTAL row (A,B,C,D) = (1,0,-2,1) must be flagged.
import csv, re
def P(A, B, C, t): return A*t*t + B*t + C
Ks = {}
def isnorm(q, D):
    if q == 0: return True
    if D not in Ks: Ks[D] = QuadraticField(-D, 'w')
    return QQ(q).is_norm(Ks[D])
rows = list(csv.DictReader(open('totality_decision_rows.tsv'), delimiter='\t'))
bad_total = bad_not = 0
for r in rows:
    A, B, C, D = (Integer(r[k]) for k in 'ABCD')
    if r['verdict'] == 'TOTAL':
        if not all(isnorm(P(A, B, C, t), D) for t in range(-6, 7)): bad_total += 1
    else:
        ints = [Integer(x) for x in re.findall(r'-?\d+', r['cert'])]
        t = ints[-1]
        if isnorm(P(A, B, C, t), D): bad_not += 1
plant_flagged = not all(isnorm(P(1, 0, -2, t), 1) for t in range(-6, 7))
nt = sum(1 for r in rows if r['verdict'] == 'TOTAL')
print("SAGE_ROWS=%d TOTAL_ROWS=%d TOTAL_REFUTED=%d NOT_ROWS=%d NOT_REFUTED=%d PLANT_FLAGGED=%s" % (
    len(rows), nt, bad_total, len(rows) - nt, bad_not, plant_flagged))
print("SAGE_LEG_EXIT=%d" % (0 if bad_total == 0 and bad_not == 0 and plant_flagged else 1))
