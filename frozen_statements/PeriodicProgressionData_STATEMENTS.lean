/-
  frozen_statements/PeriodicProgressionData_STATEMENTS.lean — statement freeze (s28) of
  DiophCompression/PeriodicProgressionData.lean (periodic leaves B1b and A3).
-/
import DiophCompression.PeriodicProgressionCore
import DiophCompression.SemanticQuadraticTwoWitness.RankOne
import DiophCompression.SemanticQuadraticMatrix.FullRankGeneric

namespace DiophCompression

namespace SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadratic

theorem rank_one_uncoupled_periodic_data (A B₁ k l m₁ m₂ q : ℤ) (hm₂ : m₂ ≠ 0) :
    Nonempty (PeriodicProgression (fiberSet2 A B₁ 0 k 0 0 l m₁ m₂ q)) ∨
      fiberSet2 A B₁ 0 k 0 0 l m₁ m₂ q = ∅ := by
  sorry

end SemanticQuadraticTwoWitness

namespace SemanticQuadraticMatrix

theorem alpha_zero_beta_zero_periodic_data {r : ℕ} (A : ℤ) (B : Fin r → ℤ)
    (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ) (m : Fin r → ℤ) (q : ℤ)
    (hN : (witnessGram C).det ≠ 0) (hα : alphaMatrix A B C = 0) (hβ : betaMatrix B C l m = 0) :
    Nonempty (PeriodicProgression (fiberSetM A B C l m q)) ∨ fiberSetM A B C l m q = ∅ := by
  sorry

end SemanticQuadraticMatrix

end DiophCompression
