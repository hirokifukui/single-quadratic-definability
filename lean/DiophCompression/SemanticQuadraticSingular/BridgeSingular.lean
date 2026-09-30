/-
  DiophCompression/SemanticQuadraticSingular/BridgeSingular.lean — r10 必須M part 1: a matrix block in singular
  block form (Gram matrix zero on the last row/column) is exactly the explicit singular form `fq3S` with
  radical variable u 2; DichotomyS ⇒ DichotomyM. Statements frozen in `Singular_STATEMENTS.lean`
  (md5 281708fb). Session 10, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticSingular.MovingModulus

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticTwoWitness
  DiophCompression.SemanticQuadraticGeneral

theorem aux_gram_apply (C : Matrix (Fin 3) (Fin 3) ℤ) (i j : Fin 3) : witnessGram C i j = C i j + C j i := by
  simp [witnessGram, Matrix.add_apply, Matrix.transpose_apply]

theorem fqM_eq_fq3S (A : ℤ) (B : Fin 3 → ℤ) (C : Matrix (Fin 3) (Fin 3) ℤ) (hC : SingularBlockForm3 C)
    (l : ℤ) (m : Fin 3 → ℤ) (q c : ℤ) (u : Fin 3 → ℤ) :
    fqM A B C l m q c u =
      fq3S A (B 0) (B 1) (C 0 0) (C 0 1 + C 1 0) (C 1 1) (B 2) l (m 0) (m 1) (m 2) q c (u 0) (u 1) (u 2) := by
  have h02 : C 0 2 + C 2 0 = 0 := by have := (hC 0).1; rwa [aux_gram_apply] at this
  have h12 : C 1 2 + C 2 1 = 0 := by have := (hC 1).1; rwa [aux_gram_apply] at this
  have h22 : C 2 2 = 0 := by have := (hC 2).1; rw [aux_gram_apply] at this; linarith
  unfold fqM witnessQuad fq3S fq2
  simp only [dotProduct, mulVec, Fin.sum_univ_three]
  linear_combination (u 0 * u 2) * h02 + (u 1 * u 2) * h12 + (u 2 ^ 2) * h22

theorem fiberSetM_eq_fiberSet3S (A : ℤ) (B : Fin 3 → ℤ) (C : Matrix (Fin 3) (Fin 3) ℤ)
    (hC : SingularBlockForm3 C) (l : ℤ) (m : Fin 3 → ℤ) (q : ℤ) :
    fiberSetM A B C l m q =
      fiberSet3S A (B 0) (B 1) (C 0 0) (C 0 1 + C 1 0) (C 1 1) (B 2) l (m 0) (m 1) (m 2) q := by
  ext c
  simp only [fiberSetM, fiberSet3S, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u 0, u 1, u 2, by rw [← fqM_eq_fq3S A B C hC]; exact hu⟩
  · rintro ⟨u, v, w, h⟩
    refine ⟨![u, v, w], ?_⟩
    rw [fqM_eq_fq3S A B C hC]
    simpa using h

theorem fboundM_eq_fbound3S (K : ℕ) (l : ℤ) (m : Fin 3 → ℤ) (q : ℤ) :
    fboundM K l m q = fbound3S K l (m 0) (m 1) (m 2) q := by
  unfold fboundM fbound3S
  rw [Fin.sum_univ_three]
  ring

theorem dichotomyM_of_dichotomyS (A : ℤ) (B : Fin 3 → ℤ) (C : Matrix (Fin 3) (Fin 3) ℤ)
    (hC : SingularBlockForm3 C)
    (h : DichotomyS A (B 0) (B 1) (C 0 0) (C 0 1 + C 1 0) (C 1 1) (B 2)) : DichotomyM A B C := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun l m q => ?_⟩
  rw [fiberSetM_eq_fiberSet3S A B C hC, fboundM_eq_fbound3S]
  exact hK l (m 0) (m 1) (m 2) q

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.fqM_eq_fq3S
#print axioms DiophCompression.SemanticQuadraticSingular.fiberSetM_eq_fiberSet3S
#print axioms DiophCompression.SemanticQuadraticSingular.fboundM_eq_fbound3S
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomyM_of_dichotomyS
