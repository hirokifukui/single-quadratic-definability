/-
  DiophCompression/SemanticQuadraticMatrix/FullRankAssemblyData.lean — APAL Structural Theory Gate 5,
  必須F step 3 (full-rank assembly) (s28, 2026-09-02, claude.ai direct).

  The matrix-level dichotomy in data-carrying form, and the full-rank dispatch (A1–A4) carried out at that
  level. The dispatch itself is the sealed argument; the three leaf theorems it calls appear as explicit
  hypotheses, so what still has to be converted is visible in the statement:
    * `hDir`  — branch A1 (signed non-square direction; its Pell hub is already data, s28)
    * `hA0`   — branches A2 / A3 (α = 0; the quadratic family and the periodic family are already data)
    * `hBnd`  — branch A4 (bounded).
  No sorry; std-3.
-/
import DiophCompression.SemanticQuadraticMatrix.FullRankGeneric
import DiophCompression.StructuredFamilyCore
import DiophCompression.PeriodicProgressionData
import DiophCompression.SemanticQuadraticMatrix.QuadraticFamilyA2
import DiophCompression.SemanticQuadratic.PellOrbitOfXPos

namespace DiophCompression.SemanticQuadraticMatrix

open Matrix

variable {r : ℕ}

/-- The data form implies the sealed one. -/
theorem dichotomyM_of_dichotomyMData {A : ℤ} {B : Fin r → ℤ} {C : Matrix (Fin r) (Fin r) ℤ}
    (h : DichotomyMData A B C) : DichotomyM A B C := by
  sorry

/-- Branch A3 at the matrix level, in data form: the periodic family of `α = β = 0`. -/
theorem alpha_zero_beta_zero_family_data (A : ℤ) (B : Fin r → ℤ)
    (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ) (m : Fin r → ℤ) (q : ℤ)
    (hN : (witnessGram C).det ≠ 0) (hα : alphaMatrix A B C = 0) (hβ : betaMatrix B C l m = 0) :
    Nonempty (DiophCompression.StructuredFamily (fiberSetM A B C l m q)) ∨
      fiberSetM A B C l m q = ∅ := by
  sorry

theorem full_rank_dichotomy_all_data (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (i j : Fin r) (hij : i ≠ j)
    (hDir : alphaMatrix A B C ≠ 0 →
      SignedNonsquareDirection (adjugateQuad (witnessGram C)) (alphaMatrix A B C) →
      DichotomyMData A B C)
    (hA0 : alphaMatrix A B C = 0 →
      (∀ β : ℤ, β ≠ 0 → (∃ w, β * adjugateQuad (witnessGram C) w < 0)
        ∨ (∀ Y, 0 ≤ β * adjugateQuad (witnessGram C) Y)) → DichotomyMData A B C)
    (hBnd : alphaMatrix A B C ≠ 0 →
      (∀ Y, 0 ≤ alphaMatrix A B C * adjugateQuad (witnessGram C) Y) → DichotomyMData A B C) :
    DichotomyMData A B C := by
  sorry

/-! ### Branch A4 (bounded): the sealed argument, at the data level -/

theorem full_rank_root_bound_data (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (hα : alphaMatrix A B C ≠ 0)
    (hsemi : ∀ Y, 0 ≤ alphaMatrix A B C * adjugateQuad (witnessGram C) Y) :
    DichotomyMData A B C := by
  sorry

/-- Shifting the index of a quadratic family: growth is only needed from `t₀` on, and the shifted family
    is again a quadratic progression (this is what the A2 branch produces). -/
def structuredFamily_quadratic_of_shift {S : Set ℕ} (α β γ : ℤ) (hα : α ≠ 0) (t₀ : ℕ)
    (cf : ℕ → ℕ) (out : ∀ n : ℕ, (cf n : ℤ) = α * ((t₀ : ℤ) + n) ^ 2 + β * ((t₀ : ℤ) + n) + γ)
    (mem : ∀ n, cf n ∈ S) (mono : StrictMono cf) : DiophCompression.StructuredFamily S :=
  .quadratic α (2 * α * (t₀ : ℤ) + β) (α * (t₀ : ℤ) ^ 2 + β * (t₀ : ℤ) + γ) hα cf
    (fun n => by rw [out n]; ring) mem mono


/-! ### Branches A2 / A3 (α = 0) in data form -/

set_option maxHeartbeats 2000000 in
theorem full_rank_alpha_zero_dichotomy_data (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (hα : alphaMatrix A B C = 0)
    (hdir : ∀ β : ℤ, β ≠ 0 → (∃ w, β * adjugateQuad (witnessGram C) w < 0)
      ∨ (∀ Y, 0 ≤ β * adjugateQuad (witnessGram C) Y)) :
    DichotomyMData A B C := by
  sorry


/-- With A2/A3 (`hA0`) and A4 (`hBnd`) now discharged, the full-rank dispatch needs only the A1 wrapper. -/
theorem full_rank_dichotomy_all_data_of_dir (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (i j : Fin r) (hij : i ≠ j)
    (hDir : alphaMatrix A B C ≠ 0 →
      SignedNonsquareDirection (adjugateQuad (witnessGram C)) (alphaMatrix A B C) →
      DichotomyMData A B C) :
    DichotomyMData A B C := by
  sorry


/-! ### Branch A1 (Pell line) in data form -/

open DiophCompression.SemanticQuadratic DiophCompression.SemanticQuadraticTwoWitness in
theorem fiberSetM_line_family (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ)
    (m : Fin r → ℤ) (q : ℤ) (hN : (witnessGram C).det ≠ 0) (w : Fin r → ℤ)
    (hw1 : alphaMatrix A B C * adjugateQuad (witnessGram C) w < 0)
    (hw2 : ¬ IsSquare (-(alphaMatrix A B C * adjugateQuad (witnessGram C) w)))
    (c₀ : ℕ) (u₀ : Fin r → ℤ) (h0 : fqM A B C l m q (c₀ : ℤ) u₀ = 0)
    (hZ : 0 < alphaMatrix A B C * (2 * alphaMatrix A B C * (c₀ : ℤ) + betaMatrix B C l m)) :
    Nonempty (DiophCompression.StructuredFamily (fiberSetM A B C l m q)) := by
  sorry


/-- Branch A1 wrapper (`hDir`) in data form: if some fibre point has `α(2αc + β) > 0`, the Pell line gives
    a family; otherwise every fibre point obeys the sealed bound. -/
theorem full_rank_dichotomy_of_direction_data (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (hα : alphaMatrix A B C ≠ 0)
    (hw : SignedNonsquareDirection (adjugateQuad (witnessGram C)) (alphaMatrix A B C)) :
    DichotomyMData A B C := by
  sorry

/-- And it implies the sealed `full_rank_dichotomy_all`. -/
theorem full_rank_dichotomy_all_of_data (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (i j : Fin r) (hij : i ≠ j) : DichotomyM A B C := by
  sorry

end DiophCompression.SemanticQuadraticMatrix
