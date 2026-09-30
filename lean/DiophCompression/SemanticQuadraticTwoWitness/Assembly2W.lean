/-
  DiophCompression/SemanticQuadraticTwoWitness/Assembly2W.lean — GPT r07 必須8 (s8, claude.ai direct).
  Assembly over the witness-block classes (rank 0 / rank 1 / definite / split / anisotropic) and the final
  targets: `QuadraticProjectionDichotomyZ 2`, `GraphAchievableZ n 2 2 → n ≤ 2`, `graphCapacityZ 2 2 = 2`,
  `¬ GraphAchievableZ 3 2 2`. Frozen statements: `TwoWitness_STATEMENTS_v2.lean` (md5 3e2c4c02) (verbatim f396a2da).
-/
import DiophCompression.SemanticQuadraticTwoWitness.RankZero
import DiophCompression.SemanticQuadraticTwoWitness.RankOne
import DiophCompression.SemanticQuadraticTwoWitness.RankTwoLeaves

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadraticGeneral

theorem dichotomy2_all (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) : Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  rcases lt_trichotomy (discW C₁₁ C₁₂ C₂₂) 0 with hneg | hzero | hpos
  · exact dichotomy2_definite A B₁ B₂ C₁₁ C₁₂ C₂₂ hneg
  · by_cases hC : C₁₁ = 0 ∧ C₁₂ = 0 ∧ C₂₂ = 0
    · obtain ⟨h1, h2, h3⟩ := hC
      subst h1; subst h2; subst h3
      exact dichotomy2_rank_zero A B₁ B₂
    · exact dichotomy2_rank_one A B₁ B₂ C₁₁ C₁₂ C₂₂ hzero hC
  · by_cases hsq : IsSquare (discW C₁₁ C₁₂ C₂₂)
    · exact dichotomy2_split A B₁ B₂ C₁₁ C₁₂ C₂₂ hpos hsq
    · exact dichotomy2_anisotropic A B₁ B₂ C₁₁ C₁₂ C₂₂ hpos hsq

theorem quadraticProjectionDichotomyZ_two : QuadraticProjectionDichotomyZ 2 :=
  quadraticProjectionDichotomyZ_two_of_explicit dichotomy2_all

theorem graph_two_witness_degree_two_le_two {n : ℕ} : GraphAchievableZ n 2 2 → n ≤ 2 :=
  quadraticProjectionDichotomy_implies_capacity_two quadraticProjectionDichotomyZ_two n

theorem graphCapacityZ_two_two : graphCapacityZ 2 2 = 2 :=
  graphCapacityZ_two_of_projectionDichotomy quadraticProjectionDichotomyZ_two

theorem not_graphAchievableZ_three_two_two : ¬ GraphAchievableZ 3 2 2 := fun h => by
  have := graph_two_witness_degree_two_le_two h; omega

end DiophCompression.SemanticQuadraticTwoWitness
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_all
#print axioms DiophCompression.SemanticQuadraticTwoWitness.quadraticProjectionDichotomyZ_two
#print axioms DiophCompression.SemanticQuadraticTwoWitness.graph_two_witness_degree_two_le_two
#print axioms DiophCompression.SemanticQuadraticTwoWitness.graphCapacityZ_two_two
#print axioms DiophCompression.SemanticQuadraticTwoWitness.not_graphAchievableZ_three_two_two
