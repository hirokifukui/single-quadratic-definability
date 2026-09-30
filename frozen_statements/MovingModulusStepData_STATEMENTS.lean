/-
  frozen_statements/MovingModulusStepData_STATEMENTS.lean — Gate 4 必須E (s27, 2026-09-01): statement freeze of the
  data form of the B2 prime step, appended to DiophCompression/SemanticQuadraticSingular/MovingModulusGeneral.lean
  (the sealed theorems of that file have no live freeze; only the new theorem is frozen here).
-/
import DiophCompression.SemanticQuadraticSingular.DefsSingularGeneral
import DiophCompression.PeriodicProgressionCore
import DiophCompression.SemanticQuadraticSingular.FiniteFieldQuadratic
import DiophCompression.SemanticQuadraticSingular.FiniteFieldQuadraticGeneral
import DiophCompression.SemanticQuadraticSingular.QuotientRankZero

namespace DiophCompression.SemanticQuadraticSingular
open Matrix DiophCompression.SemanticQuadraticMatrix
variable {k : ℕ}

def movingRemainderPolyG (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (x : Fin k → ℤ) : ℤ :=
  witnessQuad C x + ((b • m - μ • B) ⬝ᵥ x) + (A * μ ^ 2 - b * l * μ + b ^ 2 * q)

theorem moving_modulus_prime_step_data (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q c₀ : ℤ)
    (u₀ : Fin k → ℤ) (hb : 0 < b) (hN : (C + Cᵀ).det ≠ 0) (ht₀ : 0 < b * c₀ + μ)
    (hdiv : (b * c₀ + μ) ∣ fqM A B C l m q c₀ u₀) :
    ∃ (p : ℕ) (c : ℤ) (u x : Fin k → ℤ), p.Prime ∧
      (2 * |(C + Cᵀ).det| * b * (b * c₀ + μ) : ℤ) < p ∧
      (p : ℤ) ≡ 1 [ZMOD 2 * |(C + Cᵀ).det| * b * (b * c₀ + μ)] ∧
      b * c + μ = (b * c₀ + μ) * p ∧
      (p : ℤ) ∣ movingRemainderPolyG A B C b l m μ q x ∧
      (∀ i, (b * c₀ + μ) ∣ u i - u₀ i) ∧ (∀ i, (p : ℤ) ∣ b * u i - x i) ∧
      (b * c + μ) ∣ fqM A B C l m q c u := by
  sorry


/-! ### 必須A (Gate 5): branch B4 is a WITNESS reflection, not an output reflection -/

/-- B4 identity: the singular-block polynomial is invariant under `(b, μ, w) ↦ (-b, -μ, -w)`. -/
theorem movingModulus_negSlope_witnessEquiv (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q c : ℤ) (u : Fin k → ℤ) (w : ℤ) :
    fqSG A B C b l m μ q c u w = fqSG A B C (-b) l m (-μ) q c u (-w) := by
  sorry

/-- B4 on fibres: the `b < 0` instance and its positive-slope partner have the SAME fibre. -/
theorem fiberSetSG_negSlope (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) :
    fiberSetSG A B C b l m μ q = fiberSetSG A B C (-b) l m (-μ) q := by
  sorry

/-- B4 on solutions: same output, same block witnesses, radical witness = cofactor. -/
theorem movingModulus_negSlope_dvd_transfer (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q c : ℤ) (u : Fin k → ℤ) (t : ℤ)
    (h : fqM A B C l m q c u = ((-b) * c + (-μ)) * t) :
    fqSG A B C b l m μ q c u t = 0 := by
  sorry

/-- B4 preserves growth: no decreasing family arises in branch B4. -/
theorem movingModulus_negSlope_strictMono_transfer (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (f : ℕ → ℕ)
    (hmono : StrictMono f) (hmem : ∀ j, f j ∈ fiberSetSG A B C (-b) l m (-μ) q) :
    StrictMono f ∧ ∀ j, f j ∈ fiberSetSG A B C b l m μ q := by
  sorry


/-! ### 必須F step 2 (branch B3): the fixed-modulus branch in data-carrying form -/

theorem dichotomySG_zero_periodic_data (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (hμ : μ ≠ 0) :
    Nonempty (DiophCompression.PeriodicProgression (fiberSetSG A B C 0 l m μ q)) ∨
      fiberSetSG A B C 0 l m μ q = ∅ := by
  sorry

end DiophCompression.SemanticQuadraticSingular
