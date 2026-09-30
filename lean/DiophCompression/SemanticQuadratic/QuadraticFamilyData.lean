/-
  DiophCompression/SemanticQuadratic/QuadraticFamilyData.lean — APAL Structural Theory Gate 5,
  必須F step 2 (leaf D2) (s28, 2026-09-02, claude.ai direct).

  Branch D2 (disc = 0, C ≠ 0) in the shape the 必須D packager wants. The sealed `mem_seq_a` already proves
  that the quadratic-in-`t` family through a fibre point stays on the fibre; the dichotomy proof then feeds
  it to `inf_of_family` and keeps only infinitude. Here the same family is presented as an explicit
  quadratic `α t² + β t + γ` with
      α = 4C²·(2Bm − 4Cl),  β = 4C·(2Cu₀ + Bc₀ + m),  γ = c₀,
  which is exactly the input of `extract_quadratic_family` (leading coefficient nonzero on the infinite
  branch, where 2Bm − 4Cl ≠ 0). No sorry; std-3.
-/
import DiophCompression.SemanticQuadratic.Class_D2

namespace DiophCompression.SemanticQuadratic

open MPUP

/-- The D2 family, written as a quadratic polynomial in `t`. -/
theorem d2_quadratic_family (A B C l m q c₀ u₀ : ℤ) (hfq : fq A B C l m q c₀ u₀ = 0)
    (hdisc : disc A B C = 0) (hC : C ≠ 0) (t : ℤ) :
    fq A B C l m q
        (4 * C ^ 2 * (2 * B * m - 4 * C * l) * t ^ 2
          + 4 * C * (2 * C * u₀ + B * c₀ + m) * t + c₀)
        (u₀ + (2 * B * m - 4 * C * l) * t - 2 * B * t * (2 * C * u₀ + B * c₀ + m)
          - 2 * B * C * (2 * B * m - 4 * C * l) * t ^ 2) = 0 := by
  have h := mem_seq_a A B C l m q c₀ u₀ t hfq hdisc hC
  have e : c₀ + 4 * C * t * (2 * C * u₀ + B * c₀ + m)
        + 4 * C ^ 2 * (2 * B * m - 4 * C * l) * t ^ 2
      = 4 * C ^ 2 * (2 * B * m - 4 * C * l) * t ^ 2
        + 4 * C * (2 * C * u₀ + B * c₀ + m) * t + c₀ := by ring
  rw [e] at h
  exact h

/-- The leading coefficient is nonzero exactly on the infinite branch of D2 (`2Bm − 4Cl ≠ 0`), so the
    family is a genuine degree-2 progression, not a degenerate one. -/
theorem d2_leading_ne_zero (B C l m : ℤ) (hC : C ≠ 0) (hβ : 2 * B * m - 4 * C * l ≠ 0) :
    4 * C ^ 2 * (2 * B * m - 4 * C * l) ≠ 0 := by
  have h4 : (4 : ℤ) ≠ 0 := by norm_num
  exact mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 hC)) hβ

/-- Growth of the D2 family for `t ≥ 0` when the leading coefficient is positive: the strict growth the
    packager asks for, from the branch's own sign condition. -/
theorem d2_family_growth (A B C l m q c₀ u₀ : ℤ) (hlead : 0 < 4 * C ^ 2 * (2 * B * m - 4 * C * l))
    (hlin : 0 ≤ 4 * C * (2 * C * u₀ + B * c₀ + m)) (t : ℕ) :
    4 * C ^ 2 * (2 * B * m - 4 * C * l) * (t : ℤ) ^ 2
        + 4 * C * (2 * C * u₀ + B * c₀ + m) * (t : ℤ) + c₀
      < 4 * C ^ 2 * (2 * B * m - 4 * C * l) * ((t : ℤ) + 1) ^ 2
        + 4 * C * (2 * C * u₀ + B * c₀ + m) * ((t : ℤ) + 1) + c₀ := by
  have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
  nlinarith

end DiophCompression.SemanticQuadratic

#print axioms DiophCompression.SemanticQuadratic.d2_quadratic_family
#print axioms DiophCompression.SemanticQuadratic.d2_leading_ne_zero
#print axioms DiophCompression.SemanticQuadratic.d2_family_growth
