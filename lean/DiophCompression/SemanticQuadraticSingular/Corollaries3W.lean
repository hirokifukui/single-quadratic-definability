/-
  DiophCompression/SemanticQuadraticSingular/Corollaries3W.lean — r10 side homework (GPT r09 宿題群 1.1, 3.9, 4.1,
  4.12, 11.1, 11.14, 12.6): corollaries of G_ℤ(3,2) = 2 (inertia up to r = 3, semantic gap, U_ℤ(3,2) ≤ 3), the
  r = 2 instantiation of the general full-rank theorem compared with r08, the finite residue-class certificate
  for periodic sets, minorContent = 0 ⟺ all pair minors vanish, invariance of affineGcd under invertible
  changes of the radical coordinates, kernel saturation for every r. Not part of the r10 freeze (written after
  it; statements new here). Session 10, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticSingular.Assembly3W

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticTwoWitness
  DiophCompression.SemanticQuadraticGeneral DiophCompression.SemanticQuadratic

/-! ## 宿題群 12.6 / 11.14: the exact table up to r = 3 and the universal-capacity corollary -/

/-- Quadratic witness inertia at r = 3: three integer witnesses add nothing to the degree-2 graph capacity. -/
theorem three_witness_quadratic_inertia_Z : graphCapacityZ 3 2 = graphCapacityZ 0 2 := by
  rw [graphCapacityZ_three_two, graphCapacityZ_noWitness 2 (by norm_num)]

/-- G_ℤ(r, 2) = 2 for r = 0, 1, 2, 3. -/
theorem quadratic_inertia_up_to_three_Z : ∀ r ≤ 3, graphCapacityZ r 2 = 2 := by
  intro r hr
  interval_cases r
  · exact graphCapacityZ_noWitness 2 (by norm_num)
  · exact graphCapacityZ_one_two
  · exact graphCapacityZ_two_two
  · exact graphCapacityZ_three_two

/-- Semantic 2 versus syntactic 6 at (r, d) = (3, 2). -/
theorem three_witness_semantic_gap_Z : graphCapacityZ 3 2 = 2 ∧ capBound 3 2 = 6 :=
  ⟨graphCapacityZ_three_two, by unfold capBound; norm_num [Nat.choose]⟩

/-- U_ℤ(3, 2) ≤ G_ℤ(3, 2) + 1 = 3. -/
theorem universalCapacityZ_three_two_le_three : universalCapacityZ 3 2 ≤ 3 := by
  have h := universalCapacityZ_le_graphCapacityZ_succ 3 2 (by norm_num)
  rw [graphCapacityZ_three_two] at h
  exact h

theorem not_universalAchievableZ_four_three_two : ¬ UniversalAchievableZ 4 3 2 := fun h => by
  have h4 := (universalCapacityZ_spec 3 2 4).mp h
  have h3 := universalCapacityZ_three_two_le_three
  omega

/-! ## 宿題群 1.1: the general full-rank theorem at r = 2 versus the r08 explicit theorem -/

theorem fqM_eq_fq2 (A : ℤ) (B : Fin 2 → ℤ) (C : Matrix (Fin 2) (Fin 2) ℤ) (l : ℤ) (m : Fin 2 → ℤ) (q c : ℤ)
    (u : Fin 2 → ℤ) :
    fqM A B C l m q c u = fq2 A (B 0) (B 1) (C 0 0) (C 0 1 + C 1 0) (C 1 1) l (m 0) (m 1) q c (u 0) (u 1) := by
  unfold fqM witnessQuad fq2
  simp only [dotProduct, mulVec, Fin.sum_univ_two]
  ring

theorem fiberSetM_eq_fiberSet2 (A : ℤ) (B : Fin 2 → ℤ) (C : Matrix (Fin 2) (Fin 2) ℤ) (l : ℤ) (m : Fin 2 → ℤ)
    (q : ℤ) :
    fiberSetM A B C l m q = fiberSet2 A (B 0) (B 1) (C 0 0) (C 0 1 + C 1 0) (C 1 1) l (m 0) (m 1) q := by
  ext c
  simp only [fiberSetM, fiberSet2, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu⟩; exact ⟨u 0, u 1, by rw [← fqM_eq_fq2]; exact hu⟩
  · rintro ⟨u, v, h⟩; exact ⟨![u, v], by rw [fqM_eq_fq2]; simpa using h⟩

theorem fboundM_eq_fbound2 (K : ℕ) (l : ℤ) (m : Fin 2 → ℤ) (q : ℤ) :
    fboundM K l m q = fbound2 K l (m 0) (m 1) q := by
  unfold fboundM fbound2; rw [Fin.sum_univ_two]; ring

/-- At r = 2 the matrix predicate is the r08 explicit predicate (with C₁₂ = C 0 1 + C 1 0). -/
theorem dichotomyM_two_iff_dichotomy2 (A : ℤ) (B : Fin 2 → ℤ) (C : Matrix (Fin 2) (Fin 2) ℤ) :
    DichotomyM A B C ↔ Dichotomy2 A (B 0) (B 1) (C 0 0) (C 0 1 + C 1 0) (C 1 1) := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, fun l m₁ m₂ q => ?_⟩
    have h := hK l ![m₁, m₂] q
    rw [fiberSetM_eq_fiberSet2, fboundM_eq_fbound2] at h
    simpa using h
  · rintro ⟨K, hK⟩
    refine ⟨K, fun l m q => ?_⟩
    rw [fiberSetM_eq_fiberSet2, fboundM_eq_fbound2]
    exact hK l (m 0) (m 1) q

/-- 宿題群 1.1: the r09 general full-rank theorem instantiated at r = 2 reproduces the r08 nondegenerate leaves
    (discW ≠ 0 ⟺ det(C + Cᵀ) ≠ 0 since det(C + Cᵀ) = −discW for the symmetrised coefficients). -/
theorem full_rank_two_matches_r08 (A : ℤ) (B : Fin 2 → ℤ) (C : Matrix (Fin 2) (Fin 2) ℤ)
    (hN : (witnessGram C).det ≠ 0) : Dichotomy2 A (B 0) (B 1) (C 0 0) (C 0 1 + C 1 0) (C 1 1) :=
  (dichotomyM_two_iff_dichotomy2 A B C).mp
    (full_rank_projection_dichotomy_of_direction_property (by norm_num) A B C hN)

theorem witnessGram_det_two (C : Matrix (Fin 2) (Fin 2) ℤ) :
    (witnessGram C).det = - discW (C 0 0) (C 0 1 + C 1 0) (C 1 1) := by
  unfold witnessGram discW
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.transpose_apply]
  ring

/-- Conversely r08 covers every r = 2 block, singular ones included. -/
theorem dichotomyM_two_all (A : ℤ) (B : Fin 2 → ℤ) (C : Matrix (Fin 2) (Fin 2) ℤ) : DichotomyM A B C :=
  (dichotomyM_two_iff_dichotomy2 A B C).mpr (dichotomy2_all _ _ _ _ _ _)

/-! ## 宿題群 3.9: finite residue-class certificate for a periodic set of naturals -/

theorem periodic_set_residue_certificate (S : Set ℕ) (T : ℕ) (hT : 1 ≤ T) (hper : ∀ c, c ∈ S ↔ c + T ∈ S)
    (c : ℕ) : c ∈ S ↔ c % T ∈ S := by
  have key : ∀ k c, c ∈ S ↔ c + k * T ∈ S := by
    intro k
    induction k with
    | zero => intro c; simp
    | succ k ih =>
      intro c
      rw [ih c, hper (c + k * T)]
      have e : c + k * T + T = c + (k + 1) * T := by ring
      rw [e]
  have := key (c / T) (c % T)
  rw [Nat.mod_add_div' c T] at this
  exact this.symm

/-! ## 宿題群 4.1 / 4.12: minorContent and invariance of affineGcd -/

theorem minorContent_eq_zero_iff {s : ℕ} (b m : Fin s → ℤ) :
    minorContent b m = 0 ↔ ∀ i j, pairMinor b m i j = 0 := by
  unfold minorContent
  rw [Finset.gcd_eq_zero_iff]
  constructor
  · intro h i j; exact h (i, j) (Finset.mem_univ _)
  · intro h p _; exact h p.1 p.2

/-- The affine gcd of the radical coefficients is invariant under an invertible integer change of the radical
    coordinates: for (b, m) ↦ (Uᵀ b, Uᵀ m) with U V = V U = 1. -/
theorem affineGcd_invariant_of_invertible {s : ℕ} (b m : Fin s → ℤ) (c : ℤ) (U V : Matrix (Fin s) (Fin s) ℤ)
    (hUV : U * V = 1) (hVU : V * U = 1) :
    affineGcd (Uᵀ *ᵥ b) (Uᵀ *ᵥ m) c = affineGcd b m c := by
  have hcoef : ∀ (W : Matrix (Fin s) (Fin s) ℤ) (b m : Fin s → ℤ) (i : Fin s),
      affineCoeff (Wᵀ *ᵥ b) (Wᵀ *ᵥ m) c i = ∑ j, W j i * affineCoeff b m c j := by
    intro W b m i
    simp only [affineCoeff, mulVec, dotProduct, transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have hdvd : ∀ (W : Matrix (Fin s) (Fin s) ℤ) (b m : Fin s → ℤ),
      affineGcd b m c ∣ affineGcd (Wᵀ *ᵥ b) (Wᵀ *ᵥ m) c := by
    intro W b m
    apply Finset.dvd_gcd
    intro i _
    rw [hcoef]
    exact Finset.dvd_sum (fun j _ => Dvd.dvd.mul_left (affineGcd_dvd_affineCoeff b m c j) _)
  apply Int.dvd_antisymm (affineGcd_nonneg _ _ _) (affineGcd_nonneg _ _ _)
  · have h := hdvd V (Uᵀ *ᵥ b) (Uᵀ *ᵥ m)
    rwa [mulVec_mulVec, mulVec_mulVec, ← transpose_mul, hUV, transpose_one, one_mulVec, one_mulVec] at h
  · exact hdvd U b m

/-! ## 宿題群 11.1: kernel saturation for every r -/

theorem kernel_saturated_general {r : ℕ} (G : Matrix (Fin r) (Fin r) ℤ) (d : ℤ) (hd : d ≠ 0) (v : Fin r → ℤ)
    (h : G *ᵥ (d • v) = 0) : G *ᵥ v = 0 := by
  rw [mulVec_smul] at h
  exact (smul_eq_zero.mp h).resolve_left hd

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.three_witness_quadratic_inertia_Z
#print axioms DiophCompression.SemanticQuadraticSingular.quadratic_inertia_up_to_three_Z
#print axioms DiophCompression.SemanticQuadraticSingular.three_witness_semantic_gap_Z
#print axioms DiophCompression.SemanticQuadraticSingular.universalCapacityZ_three_two_le_three
#print axioms DiophCompression.SemanticQuadraticSingular.not_universalAchievableZ_four_three_two
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomyM_two_iff_dichotomy2
#print axioms DiophCompression.SemanticQuadraticSingular.full_rank_two_matches_r08
#print axioms DiophCompression.SemanticQuadraticSingular.witnessGram_det_two
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomyM_two_all
#print axioms DiophCompression.SemanticQuadraticSingular.periodic_set_residue_certificate
#print axioms DiophCompression.SemanticQuadraticSingular.minorContent_eq_zero_iff
#print axioms DiophCompression.SemanticQuadraticSingular.affineGcd_invariant_of_invertible
#print axioms DiophCompression.SemanticQuadraticSingular.kernel_saturated_general
