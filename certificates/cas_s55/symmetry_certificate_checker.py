#!/usr/bin/env python3
"""symmetry_certificate_checker.py — s55, GATE25 D4.

Checks the finite data that `QuadraticGraphData.symmetry_certificate_NF` (IsometryCertificate.lean)
takes as hypotheses, for a datum with output/witness block of size s = m + r (outputs first):

  (1) isometry   : Tᵢᵀ S Tᵢ = S, where S is the symmetric part of the output/witness form
                   (zQuadQ(T w) = zQuadQ(w) for all rational w);
  (2) base point : (I − Tᵢ)(c0 + C ρ) is an integer vector;
  (3) slope      : M (I − Tᵢ) C is an integer matrix;
  (4) certificate: π = Σᵢ Aᵢ π (Tᵢ − I) as rational matrices (π = first m coordinates).

Exact rational arithmetic (sympy).  This is a checker for the hypotheses, not a proof: the
conclusion is the Lean theorem.  Exit code 0 iff every case marked expect=PASS passes and every
case marked expect=FAIL fails.
"""
import sys
import sympy as sp

def check(name, Qform, m, Ts, c0, C, M, rho, As):
    s = Qform.shape[0]
    S = (Qform + Qform.T) / 2
    I = sp.eye(s)
    out = {}
    out['isometry'] = all((T.T * S * T - S) == sp.zeros(s, s) for T in Ts)
    base = c0 + C * rho
    out['base_point'] = all(all(x.is_integer for x in (I - T) * base) for T in Ts)
    out['slope'] = all(all(x.is_integer for x in M * (I - T) * C) for T in Ts)
    P = sp.Matrix.hstack(sp.eye(m), sp.zeros(m, s - m))
    total = sp.zeros(m, s)
    for A, T in zip(As, Ts):
        total += A * P * (T - I)
    out['certificate'] = (total - P) == sp.zeros(m, s)
    ok = all(out.values())
    print(f"{name}: " + " ".join(f"{k}={'ok' if v else 'NO'}" for k, v in out.items())
          + f"  => {'PASS' if ok else 'FAIL'}")
    return ok

# ctlD4: (2b − 2a)^2 + (3u − 1)^2 + v^2 = 1; block (b, u, v); zQuad = 4b^2 + 9u^2 + v^2
Q = sp.diag(4, 9, 1)
c0 = sp.Matrix([0, sp.Rational(1, 3), 0])
C = sp.Matrix([[1], [0], [0]])
rho = sp.Matrix([0])
T1 = sp.diag(-1, 1, 1)
T2 = sp.diag(1, -1, 1)
half = sp.Matrix([[sp.Rational(-1, 2)]])

cases = [
    ("ctlD4 output flip (Lean: ctlD4_certificate_NF)", Q, 1, [T1], c0, C, 1, rho, [half], True),
    ("planted: witness flip T2", Q, 1, [T2], c0, C, 1, rho, [half], False),
    ("planted: wrong certificate A = -1", Q, 1, [T1], c0, C, 1, rho, [sp.Matrix([[-1]])], False),
    ("planted: non-isometry diag(-1,2,1)", Q, 1, [sp.diag(-1, 2, 1)], c0, C, 1, rho, [half], False),
    ("T = -I (reduces to doubled centre; fails here since 2c is not integral)",
     Q, 1, [-sp.eye(3)], c0, C, 1, rho, [half], False),
]
bad = 0
for name, Qf, m, Ts, c0_, C_, M_, rho_, As, expect in cases:
    got = check(name, Qf, m, Ts, c0_, C_, M_, rho_, As)
    if got != expect:
        bad += 1
        print("  UNEXPECTED")
print(f"CHECKER_CASES={len(cases)} UNEXPECTED={bad}")
sys.exit(1 if bad else 0)
