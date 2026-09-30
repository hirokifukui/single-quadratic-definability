/-
  frozen_statements/RankOneUncoupledData_STATEMENTS.lean — statement freeze (s28) of DiophCompression/SemanticQuadraticTwoWitness/RankOneUncoupledData.lean — APAL Structural Theory Gate 5,
  必須F step 3 (rank-one uncoupled layer) (s28, 2026-09-02, claude.ai direct).

  The first assembly layer above the leaves, in data-carrying form, and the first place where the
  set-generic family type pays off: the `m₂ = 0` branch is the one-witness fibre under a set EQUALITY, so
  the certificate travels by rewriting the set, and the `m₂ ≠ 0` branch is the periodic family already
  proved in s28. Nothing here re-does arithmetic; the layer is pure transport. No sorry; std-3.
-/
import DiophCompression.SemanticQuadraticTwoWitness.RankOne
import DiophCompression.SemanticQuadratic.DegenerateDichotomyData
import DiophCompression.PeriodicProgressionData

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadratic

/-- The two-witness dichotomy in data-carrying form. -/
def Dichotomy2Data (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) : Prop :=
  ∃ K : ℕ, ∀ l m₁ m₂ q : ℤ,
    Nonempty (DiophCompression.StructuredFamily (fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q)) ∨
      ∀ c ∈ fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q, (c : ℤ) ≤ fbound2 K l m₁ m₂ q

/-- The data form implies the sealed one. -/
theorem dichotomy2_of_dichotomy2Data {A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ}
    (h : Dichotomy2Data A B₁ B₂ C₁₁ C₁₂ C₂₂) : Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  sorry

/-- Branch B1b, complete: `m₂ = 0` transports the (now unconditional) one-witness certificate along the
    set equality; `m₂ ≠ 0` is the periodic family. -/
theorem rank_one_uncoupled_data (A B₁ k : ℤ) : Dichotomy2Data A B₁ 0 k 0 0 := by
  sorry

/-- And it still implies the sealed `rank_one_uncoupled`. -/
theorem rank_one_uncoupled_of_data (A B₁ k : ℤ) : Dichotomy2 A B₁ 0 k 0 0 := by
  sorry

end DiophCompression.SemanticQuadraticTwoWitness
