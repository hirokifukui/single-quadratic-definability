/-
  DiophCompression/SemanticQuadraticSingular/Assembly3W.lean — r10 必須M part 2: the singular branch closes
  r = 3. det G = 0 ⇒ congruent block form (U^T G U, last row/column zero) ⇒ DichotomyS (all blocks) ⇒
  DichotomyM; with the full-rank branch (r09) this gives QuadraticProjectionDichotomyZ 3 and
  G_ℤ(3,2) = 2. Statements frozen in `Singular_STATEMENTS.lean` (md5 281708fb).
  Session 10, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticSingular.BridgeSingular
import DiophCompression.SemanticQuadraticSingular.Unimodular3
import DiophCompression.SemanticQuadraticTwoWitness.Corollaries2W

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticTwoWitness
  DiophCompression.SemanticQuadraticGeneral DiophCompression.SemanticQuadraticThreeWitness

theorem aux_witnessGram_symm {r : ℕ} (C : Matrix (Fin r) (Fin r) ℤ) : (witnessGram C)ᵀ = witnessGram C := by
  unfold witnessGram
  rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

theorem dichotomy3_singular (A : ℤ) (B : Fin 3 → ℤ) (C : Matrix (Fin 3) (Fin 3) ℤ)
    (hN : (witnessGram C).det = 0) : DichotomyM A B C := by
  obtain ⟨U, hUdet, hcol, hrow⟩ := congruent_block_form_rank_two (witnessGram C) (aux_witnessGram_symm C) hN
  refine dichotomyM_of_change A B C U (Or.inl hUdet) ?_
  have hblock : SingularBlockForm3 (Uᵀ * C * U) := by
    intro i
    rw [witnessGram_conj]
    exact ⟨hcol i, hrow i⟩
  exact dichotomyM_of_dichotomyS A (Uᵀ *ᵥ B) (Uᵀ * C * U) hblock (dichotomyS_all _ _ _ _ _ _ _)

theorem dichotomy3_all (A : ℤ) (B : Fin 3 → ℤ) (C : Matrix (Fin 3) (Fin 3) ℤ) : DichotomyM A B C := by
  by_cases hN : (witnessGram C).det = 0
  · exact dichotomy3_singular A B C hN
  · exact dichotomy3_full_rank A B C hN

theorem quadraticProjectionDichotomyZ_three : QuadraticProjectionDichotomyZ 3 := by
  intro H hH
  obtain ⟨K, hK⟩ := dichotomy3_all (aOf H) (bVectorOf H) (witnessMatrixOf H)
  refine ⟨K, fun ℓ q => ?_⟩
  rw [fiberSetG_eq_fiberSetM H hH, fboundG_eq_fboundM]
  exact hK (ℓ 0) (fun k => ℓ k.succ) q

theorem graph_three_witness_degree_two_le_two {n : ℕ} : GraphAchievableZ n 3 2 → n ≤ 2 :=
  quadraticProjectionDichotomy_implies_capacity_two quadraticProjectionDichotomyZ_three n

theorem graphCapacityZ_three_two : graphCapacityZ 3 2 = 2 :=
  graphCapacityZ_two_of_projectionDichotomy quadraticProjectionDichotomyZ_three

theorem graphAchievableZ_three_two_iff {n : ℕ} : GraphAchievableZ n 3 2 ↔ n ≤ 2 := by
  rw [graphCapacityZ_spec 3 2 (by norm_num) n, graphCapacityZ_three_two]

theorem not_graphAchievableZ_three_three_two : ¬ GraphAchievableZ 3 3 2 := fun h => by
  have := graph_three_witness_degree_two_le_two h; omega

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.dichotomy3_singular
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomy3_all
#print axioms DiophCompression.SemanticQuadraticSingular.quadraticProjectionDichotomyZ_three
#print axioms DiophCompression.SemanticQuadraticSingular.graph_three_witness_degree_two_le_two
#print axioms DiophCompression.SemanticQuadraticSingular.graphCapacityZ_three_two
#print axioms DiophCompression.SemanticQuadraticSingular.graphAchievableZ_three_two_iff
#print axioms DiophCompression.SemanticQuadraticSingular.not_graphAchievableZ_three_three_two
