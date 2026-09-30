/-
  frozen_statements/RankOneCoupledData_STATEMENTS.lean — statement freeze (s28) of
  DiophCompression/SemanticQuadraticTwoWitness/RankOneCoupledData.lean (必須F step 2, leaf B1c).
-/
import DiophCompression.SemanticQuadraticTwoWitness.RankOneCoupled

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadratic

theorem rank_one_coupled_prime_step_data (A B₁ B₂ k l m₁ m₂ q c₀ u₀ : ℤ) (hB₂ : 0 < B₂) (hk : k ≠ 0)
    (ht₀ : 0 < B₂ * c₀ + m₂) (hdiv : (B₂ * c₀ + m₂) ∣ qOne A B₁ k l m₁ q c₀ u₀) :
    ∃ (p M : ℕ) (c u : ℤ), p.Prime ∧ c₀ < c ∧
      M = 8 * (max 1 |dPrime A B₁ B₂ k l m₁ m₂ q|).natAbs * B₂.natAbs * (2 * k).natAbs
            * (B₂ * c₀ + m₂).natAbs ∧
      M < p ∧ p ≡ 1 [MOD M] ∧
      B₂ * c + m₂ = (B₂ * c₀ + m₂) * p ∧
      (B₂ * c₀ + m₂) ∣ u - u₀ ∧
      (B₂ * c + m₂) ∣ qOne A B₁ k l m₁ q c u := by
  sorry

end DiophCompression.SemanticQuadraticTwoWitness
