/-
  DiophCompression/SemanticQuadraticGeneral/TopDichotomyData.lean — APAL Structural Theory Gate 5,
  必須F step 3 (the top of the projection dichotomy) (s28, 2026-09-02, claude.ai direct).

  The projection dichotomy for every r, in data-carrying form. Both blocks below it are unconditional
  since s28 (`full_rank_dichotomy_all_data_full`, `singular_projection_dichotomy_all_r_data_full`), and
  the bridge from the matrix level to the polynomial level is a set equality, so this layer is transport
  only. No sorry; std-3.
-/
import DiophCompression.SemanticQuadraticGeneral.ProjectionDichotomy
import DiophCompression.SemanticQuadraticSingular.SingularAssembly
import DiophCompression.SemanticQuadraticMatrix.FullRankAssemblyData

namespace DiophCompression.SemanticQuadraticGeneral

open MvPolynomial DiophCompression.SemanticQuadraticMatrix

variable {r : ℕ}

/-- The polynomial-level dichotomy in data-carrying form. -/
def DichotomyGData (H : MvPolynomial (Fin (r + 1)) ℤ) : Prop :=
  ∃ K : ℕ, ∀ (ℓ : Fin (r + 1) → ℤ) (q : ℤ),
    Nonempty (DiophCompression.StructuredFamily (fiberSetG H ℓ q)) ∨
      ∀ c ∈ fiberSetG H ℓ q, (c : ℤ) ≤ fboundG K ℓ q

/-- The data form implies the sealed one. -/
theorem dichotomyG_of_dichotomyGData {H : MvPolynomial (Fin (r + 1)) ℤ} (h : DichotomyGData H) :
    DichotomyG H := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun ℓ q => ?_⟩
  rcases hK ℓ q with hF | hb
  · exact Or.inl (hF.elim fun F => DiophCompression.infinite_of_structuredFamily F)
  · exact Or.inr hb

/-- The projection dichotomy for a given `r`, in data form. -/
def QuadraticProjectionDichotomyZData (r : ℕ) : Prop :=
  ∀ H : MvPolynomial (Fin (r + 1)) ℤ, H.IsHomogeneous 2 → DichotomyGData H

theorem dichotomyGData_of_dichotomyMData_general (H : MvPolynomial (Fin (r + 1)) ℤ)
    (hH : H.IsHomogeneous 2) :
    DiophCompression.SemanticQuadraticMatrix.DichotomyMData (aOfGeneral H) (bVectorOfGeneral H) (witnessMatrixOfGeneral H) → DichotomyGData H := by
  rintro ⟨K, hK⟩
  refine ⟨K, fun ℓ q => ?_⟩
  rw [fiberSetG_eq_fiberSetM_general H hH, fboundG_eq_fboundM_general]
  exact hK (ℓ 0) (fun k => ℓ k.succ) q

theorem quadraticProjectionDichotomyZ_one_data : QuadraticProjectionDichotomyZData 1 := by
  intro H hH
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = coeff (Finsupp.single 0 2) H := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = coeff (Finsupp.single 0 1 + Finsupp.single 1 1) H := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C = coeff (Finsupp.single 1 2) H := ⟨_, rfl⟩
  have hev : ∀ x : Fin 2 → ℤ, eval x H = A * x 0 ^ 2 + B * (x 0 * x 1) + C * x 1 ^ 2 := by
    intro x; rw [eval_binary_homogeneous_quadratic H hH x, hA, hB, hC]
  obtain ⟨K, hK⟩ := SemanticQuadratic.fiber_dichotomy_data_full A B C
  refine ⟨K, fun ℓ q => ?_⟩
  have hsum2 : ∀ (f : Fin (1 + 1) → ℤ), ∑ i, f i = f 0 + f 1 := fun f => by
    rw [Fin.sum_univ_succ, Fin.sum_univ_one]; rfl
  have hs1 : ℓ (Fin.succ 0) = ℓ 1 := rfl
  have hset : fiberSetG H ℓ q = SemanticQuadratic.fiberSet A B C (ℓ 0) (ℓ 1) q := by
    ext c
    simp only [fiberSetG, SemanticQuadratic.fiberSet, SemanticQuadratic.fq, Set.mem_setOf_eq,
      fiberVal, hev, Fin.cons_zero, Fin.cons_one]
    constructor
    · rintro ⟨u, hu⟩
      rw [Fin.sum_univ_succ, Fin.sum_univ_one] at hu
      simp only [Fin.cons_zero, Fin.cons_succ, hs1] at hu
      exact ⟨u 0, by linarith [hu]⟩
    · rintro ⟨u, hu⟩
      refine ⟨fun _ => u, ?_⟩
      rw [Fin.sum_univ_succ, Fin.sum_univ_one]
      simp only [Fin.cons_zero, Fin.cons_succ, hs1]
      linarith [hu]
  have hb : fboundG K ℓ q = SemanticQuadratic.fbound K (ℓ 0) (ℓ 1) q := by
    simp only [fboundG, SemanticQuadratic.fbound]
    rw [hsum2 (fun i => |ℓ i|)]; ring
  rw [hset, hb]
  rcases hK (ℓ 0) (ℓ 1) q with hF | hbd
  · exact Or.inl (hF.elim fun F =>
      ⟨SemanticQuadratic.OneWitnessFamilyData.toStructuredFamily F⟩)
  · exact Or.inr hbd

theorem quadraticProjectionDichotomyZ_zero_data : QuadraticProjectionDichotomyZData 0 := by
  intro H hH
  apply dichotomyGData_of_dichotomyMData_general H hH
  exact DiophCompression.SemanticQuadraticSingular.dichotomyMData_of_dichotomySGData_zero _ _ _
    (DiophCompression.SemanticQuadraticSingular.quotient_rank_zero_dichotomy_data
      (aOfGeneral H) 0 (bVectorOfGeneral H) (witnessMatrixOfGeneral H))

/-- 必須F step 3, MILESTONE: the projection dichotomy is UNCONDITIONAL in data-carrying form for every
    `r` — every fibre either carries an explicit structured certificate or obeys the sealed bound. -/
theorem quadraticProjectionDichotomyZ_all_data : ∀ r : ℕ, QuadraticProjectionDichotomyZData r := by
  intro r
  match r with
  | 0 => exact quadraticProjectionDichotomyZ_zero_data
  | 1 => exact quadraticProjectionDichotomyZ_one_data
  | (n + 2) =>
    intro H hH
    apply dichotomyGData_of_dichotomyMData_general H hH
    by_cases hdet : (witnessGram (witnessMatrixOfGeneral H)).det = 0
    · exact DiophCompression.SemanticQuadraticSingular.singular_projection_dichotomy_all_r_data_full
        (aOfGeneral H) (bVectorOfGeneral H) (witnessMatrixOfGeneral H) hdet
    · exact full_rank_dichotomy_all_data_full (aOfGeneral H) (bVectorOfGeneral H)
        (witnessMatrixOfGeneral H) hdet ⟨0, by omega⟩ ⟨1, by omega⟩
        (by intro h; have := congrArg Fin.val h; simp at this)

/-- And it implies the sealed `quadraticProjectionDichotomyZ_all`. -/
theorem quadraticProjectionDichotomyZ_all_of_data : ∀ r : ℕ, QuadraticProjectionDichotomyZ r :=
  fun r H hH => dichotomyG_of_dichotomyGData (quadraticProjectionDichotomyZ_all_data r H hH)

end DiophCompression.SemanticQuadraticGeneral

#print axioms DiophCompression.SemanticQuadraticGeneral.dichotomyG_of_dichotomyGData
#print axioms DiophCompression.SemanticQuadraticGeneral.quadraticProjectionDichotomyZ_all_data
#print axioms DiophCompression.SemanticQuadraticGeneral.quadraticProjectionDichotomyZ_all_of_data
