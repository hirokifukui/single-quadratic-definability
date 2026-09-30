/-
  DiophCompression/SemanticQuadraticMatrix/QuadraticFamilyA2.lean — APAL Structural Theory Gate 5,
  必須F step 2 (leaf A2) (s28, 2026-09-02, claude.ai direct).

  Branch A2 (full-rank block, α = 0, β ≠ 0) in the shape the 必須D packager wants. The sealed dichotomy
  runs the scaled line at `z(t) = −2B₀t − N·W̃·β·t²` and hands the result to
  `fiberSetM_infinite_of_unbounded`, keeping only "arbitrarily large fibre elements". The same computation
  gives the family as an explicit quadratic in `t`:
      output(t) = −(N²·W̃·β)·t² + (−2N·B₀)·t + c₀,
  whose leading coefficient is positive exactly under the branch condition `β·W̃ < 0`. No sorry; std-3.
-/
import DiophCompression.SemanticQuadraticMatrix.FullRankGeneric

namespace DiophCompression.SemanticQuadraticMatrix

open Matrix DiophCompression.SemanticQuadratic

variable {r : ℕ}

/-- The A2 family, written as a quadratic polynomial in `t`. -/
theorem a2_quadratic_family (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ)
    (m : Fin r → ℤ) (q c₀ : ℤ) (u₀ w : Fin r → ℤ) (N Wt B₀ β : ℤ)
    (hNdef : N = (witnessGram C).det) (hWt : Wt = adjugateQuad (witnessGram C) w)
    (hB₀ : B₀ = completedVector B C m c₀ u₀ ⬝ᵥ (adjugate (witnessGram C) *ᵥ w))
    (hβdef : β = betaMatrix B C l m) (hα : alphaMatrix A B C = 0) (hN' : N ≠ 0)
    (h0 : fqM A B C l m q c₀ u₀ = 0) (t : ℤ) :
    fqM A B C l m q
        (-(N ^ 2 * Wt * β) * t ^ 2 + (-2 * N * B₀) * t + c₀)
        (scaledLineU B C u₀ w (-2 * B₀ * t - N * Wt * β * t ^ 2) (β * t)) = 0 := by
  have key := general_scaled_line_fq A B C l m u₀ w q c₀ (-2 * B₀ * t - N * Wt * β * t ^ 2) (β * t)
  rw [← hNdef, hα, ← hβdef, ← hWt, ← hB₀, h0] at key
  have h2 : 2 * N * fqM A B C l m q (c₀ + N * (-2 * B₀ * t - N * Wt * β * t ^ 2))
      (scaledLineU B C u₀ w (-2 * B₀ * t - N * Wt * β * t ^ 2) (β * t)) = 0 := by
    rw [key]; unfold DiophCompression.SemanticQuadratic.fq; ring
  have h3 : fqM A B C l m q (c₀ + N * (-2 * B₀ * t - N * Wt * β * t ^ 2))
      (scaledLineU B C u₀ w (-2 * B₀ * t - N * Wt * β * t ^ 2) (β * t)) = 0 := by
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact absurd (by linarith : N = 0) hN'
    · exact h1
  have e : c₀ + N * (-2 * B₀ * t - N * Wt * β * t ^ 2)
      = -(N ^ 2 * Wt * β) * t ^ 2 + (-2 * N * B₀) * t + c₀ := by ring
  rw [e] at h3
  exact h3

/-- On the infinite branch (`β·W̃ < 0`) the leading coefficient is positive, so the family is a genuine
    degree-2 progression. -/
theorem a2_leading_pos (N Wt β : ℤ) (hN' : N ≠ 0) (hw : β * Wt < 0) : 0 < -(N ^ 2 * Wt * β) := by
  have hN2 : 0 < N ^ 2 := by positivity
  nlinarith

theorem a2_leading_ne_zero (N Wt β : ℤ) (hN' : N ≠ 0) (hw : β * Wt < 0) :
    -(N ^ 2 * Wt * β) ≠ 0 := (a2_leading_pos N Wt β hN' hw).ne'

/-- Growth of the A2 family for `t ≥ 0` once the linear coefficient is nonnegative — the strict growth the
    packager asks for. (The sealed proof instead pushed `t` beyond `|2N·B₀|`, which is the same fact in the
    form needed for unboundedness.) -/
theorem a2_family_growth (N Wt B₀ β c₀ : ℤ) (hlead : 0 < -(N ^ 2 * Wt * β))
    (hlin : 0 ≤ -2 * N * B₀) (t : ℕ) :
    -(N ^ 2 * Wt * β) * (t : ℤ) ^ 2 + (-2 * N * B₀) * (t : ℤ) + c₀
      < -(N ^ 2 * Wt * β) * ((t : ℤ) + 1) ^ 2 + (-2 * N * B₀) * ((t : ℤ) + 1) + c₀ := by
  have ht : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
  nlinarith

end DiophCompression.SemanticQuadraticMatrix

#print axioms DiophCompression.SemanticQuadraticMatrix.a2_quadratic_family
#print axioms DiophCompression.SemanticQuadraticMatrix.a2_leading_pos
#print axioms DiophCompression.SemanticQuadraticMatrix.a2_leading_ne_zero
#print axioms DiophCompression.SemanticQuadraticMatrix.a2_family_growth
