/-
  DiophCompression/SemanticQuadraticTwoWitness/Bounds2W.lean — s8 helpers: explicit bounds on β = betaR and
  γ = gammaR in terms of (l, m₁, m₂, q), and the "unbounded ⇒ infinite" transfer for the fiber set.
-/
import DiophCompression.SemanticQuadraticTwoWitness.ScaledLine

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadraticGeneral

/-- K₀ := 2|N| + 4|C₂₂||B₁| + 2|C₁₂|(|B₁| + |B₂|) + 4|C₁₁||B₂|. -/
def kBeta (B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) : ℤ :=
  2 * |nW C₁₁ C₁₂ C₂₂| + 4 * |C₂₂| * |B₁| + 2 * |C₁₂| * (|B₁| + |B₂|) + 4 * |C₁₁| * |B₂|

/-- K₁ := 2|N| + 2|C₂₂| + 2|C₁₂| + 2|C₁₁|. -/
def kGamma (C₁₁ C₁₂ C₂₂ : ℤ) : ℤ := 2 * |nW C₁₁ C₁₂ C₂₂| + 2 * |C₂₂| + 2 * |C₁₂| + 2 * |C₁₁|

theorem kBeta_nonneg (B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) : 0 ≤ kBeta B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  unfold kBeta; positivity

theorem kGamma_nonneg (C₁₁ C₁₂ C₂₂ : ℤ) : 0 ≤ kGamma C₁₁ C₁₂ C₂₂ := by
  unfold kGamma; positivity

theorem betaR_abs_le (B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ : ℤ) :
    |betaR B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂| ≤ kBeta B₁ B₂ C₁₁ C₁₂ C₂₂ * (1 + |l| + |m₁| + |m₂|) := by
  unfold betaR kBeta
  have hl := abs_nonneg l; have h1 := abs_nonneg m₁; have h2 := abs_nonneg m₂
  have hN := abs_nonneg (nW C₁₁ C₁₂ C₂₂)
  have hB1 := abs_nonneg B₁; have hB2 := abs_nonneg B₂
  have hC11 := abs_nonneg C₁₁; have hC12 := abs_nonneg C₁₂; have hC22 := abs_nonneg C₂₂
  calc |2 * nW C₁₁ C₁₂ C₂₂ * l - 2 * (2 * C₂₂ * B₁ * m₁ - C₁₂ * (B₁ * m₂ + B₂ * m₁) + 2 * C₁₁ * B₂ * m₂)|
      ≤ |2 * nW C₁₁ C₁₂ C₂₂ * l| + |2 * (2 * C₂₂ * B₁ * m₁ - C₁₂ * (B₁ * m₂ + B₂ * m₁) + 2 * C₁₁ * B₂ * m₂)| :=
        abs_sub _ _
    _ ≤ 2 * |nW C₁₁ C₁₂ C₂₂| * |l|
        + 2 * (2 * |C₂₂| * |B₁| * |m₁| + |C₁₂| * (|B₁| * |m₂| + |B₂| * |m₁|) + 2 * |C₁₁| * |B₂| * |m₂|) := by
        have e1 : |2 * nW C₁₁ C₁₂ C₂₂ * l| = 2 * |nW C₁₁ C₁₂ C₂₂| * |l| := by
          rw [abs_mul, abs_mul]; norm_num
        have e2 : |2 * (2 * C₂₂ * B₁ * m₁ - C₁₂ * (B₁ * m₂ + B₂ * m₁) + 2 * C₁₁ * B₂ * m₂)|
            ≤ 2 * (2 * |C₂₂| * |B₁| * |m₁| + |C₁₂| * (|B₁| * |m₂| + |B₂| * |m₁|) + 2 * |C₁₁| * |B₂| * |m₂|) := by
          rw [abs_mul, abs_two]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc |2 * C₂₂ * B₁ * m₁ - C₁₂ * (B₁ * m₂ + B₂ * m₁) + 2 * C₁₁ * B₂ * m₂|
              ≤ |2 * C₂₂ * B₁ * m₁ - C₁₂ * (B₁ * m₂ + B₂ * m₁)| + |2 * C₁₁ * B₂ * m₂| := abs_add_le _ _
            _ ≤ |2 * C₂₂ * B₁ * m₁| + |C₁₂ * (B₁ * m₂ + B₂ * m₁)| + |2 * C₁₁ * B₂ * m₂| := by
                have := abs_sub (2 * C₂₂ * B₁ * m₁) (C₁₂ * (B₁ * m₂ + B₂ * m₁)); linarith
            _ ≤ 2 * |C₂₂| * |B₁| * |m₁| + |C₁₂| * (|B₁| * |m₂| + |B₂| * |m₁|) + 2 * |C₁₁| * |B₂| * |m₂| := by
                have a1 : |2 * C₂₂ * B₁ * m₁| = 2 * |C₂₂| * |B₁| * |m₁| := by
                  simp only [abs_mul, abs_two]
                have a3 : |2 * C₁₁ * B₂ * m₂| = 2 * |C₁₁| * |B₂| * |m₂| := by
                  simp only [abs_mul, abs_two]
                have a2 : |C₁₂ * (B₁ * m₂ + B₂ * m₁)| ≤ |C₁₂| * (|B₁| * |m₂| + |B₂| * |m₁|) := by
                  rw [abs_mul]
                  apply mul_le_mul_of_nonneg_left _ hC12
                  calc |B₁ * m₂ + B₂ * m₁| ≤ |B₁ * m₂| + |B₂ * m₁| := abs_add_le _ _
                    _ = |B₁| * |m₂| + |B₂| * |m₁| := by rw [abs_mul, abs_mul]
                linarith
        linarith
    _ ≤ (2 * |nW C₁₁ C₁₂ C₂₂| + 4 * |C₂₂| * |B₁| + 2 * |C₁₂| * (|B₁| + |B₂|) + 4 * |C₁₁| * |B₂|)
        * (1 + |l| + |m₁| + |m₂|) := by
        nlinarith [mul_nonneg hN hl, mul_nonneg (mul_nonneg hC22 hB1) h1, mul_nonneg (mul_nonneg hC12 hB1) h2,
          mul_nonneg (mul_nonneg hC12 hB2) h1, mul_nonneg (mul_nonneg hC11 hB2) h2,
          mul_nonneg hN (add_nonneg (add_nonneg h1 h2) (by norm_num : (0:ℤ) ≤ 1)),
          mul_nonneg (mul_nonneg hC22 hB1) (add_nonneg (add_nonneg hl h2) (by norm_num : (0:ℤ) ≤ 1)),
          mul_nonneg (mul_nonneg hC12 hB1) (add_nonneg (add_nonneg hl h1) (by norm_num : (0:ℤ) ≤ 1)),
          mul_nonneg (mul_nonneg hC12 hB2) (add_nonneg (add_nonneg hl h2) (by norm_num : (0:ℤ) ≤ 1)),
          mul_nonneg (mul_nonneg hC11 hB2) (add_nonneg (add_nonneg hl h1) (by norm_num : (0:ℤ) ≤ 1))]

theorem gammaR_abs_le (C₁₁ C₁₂ C₂₂ m₁ m₂ q : ℤ) :
    |gammaR C₁₁ C₁₂ C₂₂ m₁ m₂ q| ≤ kGamma C₁₁ C₁₂ C₂₂ * ((1 + |m₁| + |m₂|) ^ 2 + |q|) := by
  unfold gammaR kGamma
  have h1 := abs_nonneg m₁; have h2 := abs_nonneg m₂; have hq := abs_nonneg q
  have hN := abs_nonneg (nW C₁₁ C₁₂ C₂₂)
  have hC11 := abs_nonneg C₁₁; have hC12 := abs_nonneg C₁₂; have hC22 := abs_nonneg C₂₂
  have e1 : |2 * nW C₁₁ C₁₂ C₂₂ * q| = 2 * |nW C₁₁ C₁₂ C₂₂| * |q| := by simp only [abs_mul, abs_two]
  have e2 : |2 * C₂₂ * m₁ ^ 2 - 2 * C₁₂ * m₁ * m₂ + 2 * C₁₁ * m₂ ^ 2|
      ≤ 2 * |C₂₂| * |m₁| ^ 2 + 2 * |C₁₂| * |m₁| * |m₂| + 2 * |C₁₁| * |m₂| ^ 2 := by
    calc |2 * C₂₂ * m₁ ^ 2 - 2 * C₁₂ * m₁ * m₂ + 2 * C₁₁ * m₂ ^ 2|
        ≤ |2 * C₂₂ * m₁ ^ 2 - 2 * C₁₂ * m₁ * m₂| + |2 * C₁₁ * m₂ ^ 2| := abs_add_le _ _
      _ ≤ |2 * C₂₂ * m₁ ^ 2| + |2 * C₁₂ * m₁ * m₂| + |2 * C₁₁ * m₂ ^ 2| := by
          have := abs_sub (2 * C₂₂ * m₁ ^ 2) (2 * C₁₂ * m₁ * m₂); linarith
      _ = 2 * |C₂₂| * |m₁| ^ 2 + 2 * |C₁₂| * |m₁| * |m₂| + 2 * |C₁₁| * |m₂| ^ 2 := by
          simp only [abs_mul, abs_two, abs_pow]
  calc |2 * nW C₁₁ C₁₂ C₂₂ * q - (2 * C₂₂ * m₁ ^ 2 - 2 * C₁₂ * m₁ * m₂ + 2 * C₁₁ * m₂ ^ 2)|
      ≤ |2 * nW C₁₁ C₁₂ C₂₂ * q| + |2 * C₂₂ * m₁ ^ 2 - 2 * C₁₂ * m₁ * m₂ + 2 * C₁₁ * m₂ ^ 2| := abs_sub _ _
    _ ≤ 2 * |nW C₁₁ C₁₂ C₂₂| * |q| + (2 * |C₂₂| * |m₁| ^ 2 + 2 * |C₁₂| * |m₁| * |m₂| + 2 * |C₁₁| * |m₂| ^ 2) := by
        rw [e1]; linarith
    _ ≤ (2 * |nW C₁₁ C₁₂ C₂₂| + 2 * |C₂₂| + 2 * |C₁₂| + 2 * |C₁₁|) * ((1 + |m₁| + |m₂|) ^ 2 + |q|) := by
        nlinarith [mul_nonneg hN hq, mul_nonneg hC22 (sq_nonneg (1 + |m₁| + |m₂|)),
          mul_nonneg hC12 (sq_nonneg (1 + |m₁| + |m₂|)), mul_nonneg hC11 (sq_nonneg (1 + |m₁| + |m₂|)),
          mul_nonneg hN (sq_nonneg (1 + |m₁| + |m₂|)), mul_nonneg hC22 hq, mul_nonneg hC12 hq, mul_nonneg hC11 hq,
          mul_nonneg hC22 (mul_nonneg h1 h2), mul_nonneg hC11 (mul_nonneg h1 h2),
          mul_nonneg hC22 (add_nonneg h1 h2), mul_nonneg hC11 (add_nonneg h1 h2), mul_nonneg hC12 (add_nonneg h1 h2),
          mul_nonneg hC12 (sq_nonneg (|m₁| - |m₂|)), mul_nonneg hC12 (mul_nonneg h1 h2), mul_nonneg hC22 (sq_nonneg (|m₂|)),
          mul_nonneg hC11 (sq_nonneg (|m₁|))]

/-- The pieces of fbound2: (1 + |l| + |m₁| + |m₂|) ≤ (1 + |l| + |m₁| + |m₂|)² ≤ fbound-core. -/
theorem fbound2_core_ge_lin (l m₁ m₂ q : ℤ) :
    1 + |l| + |m₁| + |m₂| ≤ (1 + |l| + |m₁| + |m₂|) ^ 2 + |q| := by
  have hl := abs_nonneg l; have h1 := abs_nonneg m₁; have h2 := abs_nonneg m₂; have hq := abs_nonneg q
  nlinarith

theorem fbound2_core_ge_gamma (l m₁ m₂ q : ℤ) :
    (1 + |m₁| + |m₂|) ^ 2 + |q| ≤ (1 + |l| + |m₁| + |m₂|) ^ 2 + |q| := by
  have hl := abs_nonneg l; have h1 := abs_nonneg m₁; have h2 := abs_nonneg m₂
  nlinarith

/-- A fiber set that contains arbitrarily large elements is infinite. -/
theorem fiberSet2_infinite_of_unbounded (A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q : ℤ)
    (h : ∀ k : ℕ, ∃ c : ℤ, (k : ℤ) ≤ c ∧ ∃ u v : ℤ, fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v = 0) :
    (fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨k, hk⟩
  obtain ⟨c, hkc, u, v, huv⟩ := h (k + 1)
  have hc0 : 0 ≤ c := by push_cast at hkc; linarith
  have hmem : c.toNat ∈ fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q := by
    refine ⟨u, v, ?_⟩
    rw [Int.toNat_of_nonneg hc0]; exact huv
  have := hk hmem
  have : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc0
  push_cast at hkc
  omega

end DiophCompression.SemanticQuadraticTwoWitness
#print axioms DiophCompression.SemanticQuadraticTwoWitness.betaR_abs_le
#print axioms DiophCompression.SemanticQuadraticTwoWitness.gammaR_abs_le
#print axioms DiophCompression.SemanticQuadraticTwoWitness.fiberSet2_infinite_of_unbounded
