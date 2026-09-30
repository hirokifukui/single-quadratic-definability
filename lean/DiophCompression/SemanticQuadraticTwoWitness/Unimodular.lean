/-
  DiophCompression/SemanticQuadraticTwoWitness/Unimodular.lean — invariance of Dichotomy2 under unimodular witness
  changes (2W swarm 2026-08-27 worker W3b, PASS 903s; re-audited by claude.ai s8). Body verbatim from the swarm
  file; only this header added.
-/
import DiophCompression.SemanticQuadraticTwoWitness.Bridge2W
namespace DiophCompression.SemanticQuadraticTwoWitness
open DiophCompression.SemanticQuadraticGeneral

/-- Substitution identity: applying the linear change of witnesses
    (u, v) ↦ (p·u + r·v, s·u + t·v) to `fq2` with the original coefficients equals
    `fq2` with the transformed coefficients at (u, v). Verified by `ring`. -/
theorem fq2_subst (A B₁ B₂ C₁₁ C₁₂ C₂₂ p r s t l m₁ m₂ q c u v : ℤ) :
    fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c (p * u + r * v) (s * u + t * v) =
    fq2 A (B₁ * p + B₂ * s) (B₁ * r + B₂ * t)
      (C₁₁ * p ^ 2 + C₁₂ * p * s + C₂₂ * s ^ 2)
      (2 * C₁₁ * p * r + C₁₂ * (p * t + r * s) + 2 * C₂₂ * s * t)
      (C₁₁ * r ^ 2 + C₁₂ * r * t + C₂₂ * t ^ 2)
      l (m₁ * p + m₂ * s) (m₁ * r + m₂ * t) q c u v := by
  unfold fq2; ring

set_option maxHeartbeats 1000000 in
/-- Monotonicity of the fiber bound under the induced change of the linear part
    m ↦ (m₁p+m₂s, m₁r+m₂t): the transformed bound with constant `K` is dominated by the
    original bound with constant `K·(1+|p|+|r|+|s|+|t|)²`. -/
theorem fbound2_mono (K : ℕ) (p r s t l m₁ m₂ q : ℤ) :
    fbound2 K l (m₁ * p + m₂ * s) (m₁ * r + m₂ * t) q ≤
    fbound2 (K * (1 + p.natAbs + r.natAbs + s.natAbs + t.natAbs) ^ 2) l m₁ m₂ q := by
  unfold fbound2
  have hcast : ((K * (1 + p.natAbs + r.natAbs + s.natAbs + t.natAbs) ^ 2 : ℕ) : ℤ)
      = (K : ℤ) * (1 + |p| + |r| + |s| + |t|) ^ 2 := by
    rw [Int.abs_eq_natAbs p, Int.abs_eq_natAbs r, Int.abs_eq_natAbs s, Int.abs_eq_natAbs t]
    push_cast; ring
  rw [hcast, mul_assoc]
  have hKz : (0:ℤ) ≤ (K:ℤ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hKz
  -- inner : inner_trans ≤ (1+|p|+|r|+|s|+|t|)^2 * inner_orig
  have hA : |m₁ * p + m₂ * s| ≤ |m₁| * |p| + |m₂| * |s| := by
    calc |m₁ * p + m₂ * s| ≤ |m₁ * p| + |m₂ * s| := abs_add_le _ _
      _ = |m₁| * |p| + |m₂| * |s| := by rw [abs_mul, abs_mul]
  have hB : |m₁ * r + m₂ * t| ≤ |m₁| * |r| + |m₂| * |t| := by
    calc |m₁ * r + m₂ * t| ≤ |m₁ * r| + |m₂ * t| := abs_add_le _ _
      _ = |m₁| * |r| + |m₂| * |t| := by rw [abs_mul, abs_mul]
  have hXY : |m₁ * p + m₂ * s| + |m₁ * r + m₂ * t| ≤ (|m₁| + |m₂|) * (|p| + |r| + |s| + |t|) := by
    nlinarith [hA, hB, abs_nonneg m₁, abs_nonneg m₂, abs_nonneg p, abs_nonneg r,
      abs_nonneg s, abs_nonneg t, mul_nonneg (abs_nonneg m₁) (abs_nonneg s),
      mul_nonneg (abs_nonneg m₁) (abs_nonneg t), mul_nonneg (abs_nonneg m₂) (abs_nonneg p),
      mul_nonneg (abs_nonneg m₂) (abs_nonneg r)]
  have hL : 1 + |l| + |m₁ * p + m₂ * s| + |m₁ * r + m₂ * t|
      ≤ (1 + |p| + |r| + |s| + |t|) * (1 + |l| + |m₁| + |m₂|) := by
    nlinarith [hXY, abs_nonneg l, abs_nonneg p, abs_nonneg r, abs_nonneg s, abs_nonneg t,
      abs_nonneg m₁, abs_nonneg m₂, mul_nonneg (abs_nonneg l) (abs_nonneg p),
      mul_nonneg (abs_nonneg l) (abs_nonneg r), mul_nonneg (abs_nonneg l) (abs_nonneg s),
      mul_nonneg (abs_nonneg l) (abs_nonneg t)]
  have hL0 : (0:ℤ) ≤ 1 + |l| + |m₁ * p + m₂ * s| + |m₁ * r + m₂ * t| := by positivity
  have hR0 : (0:ℤ) ≤ (1 + |p| + |r| + |s| + |t|) * (1 + |l| + |m₁| + |m₂|) := by positivity
  have hprod := mul_le_mul hL hL hL0 hR0
  have hone : (1:ℤ) ≤ (1 + |p| + |r| + |s| + |t|) ^ 2 := by
    nlinarith [abs_nonneg p, abs_nonneg r, abs_nonneg s, abs_nonneg t]
  have hq : |q| ≤ (1 + |p| + |r| + |s| + |t|) ^ 2 * |q| := le_mul_of_one_le_left (abs_nonneg q) hone
  nlinarith [hprod, hq]

/-- Frozen statement. -/
theorem dichotomy2_of_unimodular (A B₁ B₂ C₁₁ C₁₂ C₂₂ p r s t : ℤ) (hdet : p * t - r * s = 1 ∨ p * t - r * s = -1)
    (h : Dichotomy2 A (B₁ * p + B₂ * s) (B₁ * r + B₂ * t)
          (C₁₁ * p ^ 2 + C₁₂ * p * s + C₂₂ * s ^ 2)
          (2 * C₁₁ * p * r + C₁₂ * (p * t + r * s) + 2 * C₂₂ * s * t)
          (C₁₁ * r ^ 2 + C₁₂ * r * t + C₂₂ * t ^ 2)) :
    Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K * (1 + p.natAbs + r.natAbs + s.natAbs + t.natAbs) ^ 2, ?_⟩
  intro l m₁ m₂ q
  have hEq : fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q =
      fiberSet2 A (B₁ * p + B₂ * s) (B₁ * r + B₂ * t)
        (C₁₁ * p ^ 2 + C₁₂ * p * s + C₂₂ * s ^ 2)
        (2 * C₁₁ * p * r + C₁₂ * (p * t + r * s) + 2 * C₂₂ * s * t)
        (C₁₁ * r ^ 2 + C₁₂ * r * t + C₂₂ * t ^ 2)
        l (m₁ * p + m₂ * s) (m₁ * r + m₂ * t) q := by
    ext c
    simp only [fiberSet2, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, v, huv⟩
      rcases hdet with hε | hε
      · refine ⟨t * u - r * v, p * v - s * u, ?_⟩
        have key := fq2_subst A B₁ B₂ C₁₁ C₁₂ C₂₂ p r s t l m₁ m₂ q (c : ℤ) (t * u - r * v) (p * v - s * u)
        rw [← key]
        have hu : p * (t * u - r * v) + r * (p * v - s * u) = u := by linear_combination u * hε
        have hv : s * (t * u - r * v) + t * (p * v - s * u) = v := by linear_combination v * hε
        rw [hu, hv]; exact huv
      · refine ⟨r * v - t * u, s * u - p * v, ?_⟩
        have key := fq2_subst A B₁ B₂ C₁₁ C₁₂ C₂₂ p r s t l m₁ m₂ q (c : ℤ) (r * v - t * u) (s * u - p * v)
        rw [← key]
        have hu : p * (r * v - t * u) + r * (s * u - p * v) = u := by linear_combination (-u) * hε
        have hv : s * (r * v - t * u) + t * (s * u - p * v) = v := by linear_combination (-v) * hε
        rw [hu, hv]; exact huv
    · rintro ⟨u, v, huv⟩
      exact ⟨p * u + r * v, s * u + t * v, by rw [fq2_subst]; exact huv⟩
  rcases hK l (m₁ * p + m₂ * s) (m₁ * r + m₂ * t) q with hInf | hBd
  · left; rw [hEq]; exact hInf
  · right; intro c hc
    rw [hEq] at hc
    exact le_trans (hBd c hc) (fbound2_mono K p r s t l m₁ m₂ q)

end DiophCompression.SemanticQuadraticTwoWitness
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_of_unimodular
