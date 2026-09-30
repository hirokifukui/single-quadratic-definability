/-
  Shadow/TopDichotomyDataR.lean — ray-carrying shadow of the top of the projection dichotomy.
  Verbatim transplant of DiophCompression/SemanticQuadraticGeneral/TopDichotomyData.lean, with
  `StructuredFamily` → `StructuredFamilyR` and the two unconditional blocks below it replaced by their
  ray-carrying shadows (`singular_projection_dichotomy_all_r_dataR_full`,
  `full_rank_dichotomy_all_data_full` with `DichotomyMDataR` type). The r = 1 leaf uses
  `OneWitnessFamilyData.toStructuredFamilyR`; `fiber_dichotomy_data_full` (family type
  `OneWitnessFamilyData`) is family-free and reused unchanged.
-/
import ResearchUpgrade.Shadow.FamilyR
import ResearchUpgrade.Shadow.OneWitnessFamilyDataR
import ResearchUpgrade.Shadow.DefsSingularGeneralR
import ResearchUpgrade.Shadow.QuotientRankZeroR
import ResearchUpgrade.Shadow.FullRankAssemblyDataR
import ResearchUpgrade.Shadow.SingularAssemblyR
import DiophCompression.SemanticQuadraticGeneral.ProjectionDichotomy
import DiophCompression.SemanticQuadraticSingular.SingularAssembly
import DiophCompression.SemanticQuadraticMatrix.FullRankAssemblyData
import DiophCompression.SemanticQuadratic.DegenerateDichotomyData

namespace DiophCompression.ResearchUpgrade

open MvPolynomial DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticGeneral

variable {r : ℕ}

/-- The polynomial-level dichotomy in ray-carrying data-carrying form. -/
def DichotomyGDataR (H : MvPolynomial (Fin (r + 1)) ℤ) : Prop :=
  ∃ K : ℕ, ∀ (ℓ : Fin (r + 1) → ℤ) (q : ℤ),
    Nonempty (StructuredFamilyR (fiberSetG H ℓ q)) ∨
      ∀ c ∈ fiberSetG H ℓ q, (c : ℤ) ≤ fboundG K ℓ q

/-- The projection dichotomy for a given `r`, in ray-carrying data form. -/
def QuadraticProjectionDichotomyZDataR (r : ℕ) : Prop :=
  ∀ H : MvPolynomial (Fin (r + 1)) ℤ, H.IsHomogeneous 2 → DichotomyGDataR H

theorem dichotomyGDataR_of_dichotomyMDataR_general (H : MvPolynomial (Fin (r + 1)) ℤ)
    (hH : H.IsHomogeneous 2) :
    DichotomyMDataR (aOfGeneral H) (bVectorOfGeneral H) (witnessMatrixOfGeneral H) → DichotomyGDataR H := by
  rintro ⟨K, hK⟩
  refine ⟨K, fun ℓ q => ?_⟩
  rw [fiberSetG_eq_fiberSetM_general H hH, fboundG_eq_fboundM_general]
  exact hK (ℓ 0) (fun k => ℓ k.succ) q

theorem quadraticProjectionDichotomyZ_one_dataR : QuadraticProjectionDichotomyZDataR 1 := by
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
      ⟨OneWitnessFamilyData.toStructuredFamilyR F⟩)
  · exact Or.inr hbd

theorem quadraticProjectionDichotomyZ_zero_dataR : QuadraticProjectionDichotomyZDataR 0 := by
  intro H hH
  apply dichotomyGDataR_of_dichotomyMDataR_general H hH
  exact dichotomyMDataR_of_dichotomySGDataR_zero _ _ _
    (quotient_rank_zero_dichotomy_dataR
      (aOfGeneral H) 0 (bVectorOfGeneral H) (witnessMatrixOfGeneral H))

/-- 必須F step 3, MILESTONE (ray-carrying): the projection dichotomy is UNCONDITIONAL in ray-carrying
    data-carrying form for every `r` — every fibre either carries an explicit ray-carrying structured
    certificate or obeys the sealed bound. -/
theorem quadraticProjectionDichotomyZ_all_dataR : ∀ r : ℕ, QuadraticProjectionDichotomyZDataR r := by
  intro r
  match r with
  | 0 => exact quadraticProjectionDichotomyZ_zero_dataR
  | 1 => exact quadraticProjectionDichotomyZ_one_dataR
  | (n + 2) =>
    intro H hH
    apply dichotomyGDataR_of_dichotomyMDataR_general H hH
    by_cases hdet : (witnessGram (witnessMatrixOfGeneral H)).det = 0
    · exact singular_projection_dichotomy_all_r_dataR_full
        (aOfGeneral H) (bVectorOfGeneral H) (witnessMatrixOfGeneral H) hdet
    · exact full_rank_dichotomy_all_data_full (aOfGeneral H) (bVectorOfGeneral H)
        (witnessMatrixOfGeneral H) hdet ⟨0, by omega⟩ ⟨1, by omega⟩
        (by intro h; have := congrArg Fin.val h; simp at this)

end DiophCompression.ResearchUpgrade
