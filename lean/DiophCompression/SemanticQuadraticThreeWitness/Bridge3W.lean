/-
  DiophCompression/SemanticQuadraticThreeWitness/Bridge3W.lean — r09 必須F (GPT r08 §6): the r = 3 full-rank
  branch. Fidelity bridge from a homogeneous quaternary quadratic H to the matrix form (ten monomials, the
  r = 3 analogue of Bridge2W), then `full_rank_dichotomy_all` (all r ≥ 2) specialised to r = 3.
  Statements frozen first in the frozen statement file `ThreeWitness_STATEMENTS.lean` (md5 7dbf4149).
  Session 9, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticMatrix.FullRankGeneric
import DiophCompression.SemanticQuadraticGeneral.Defs

namespace DiophCompression.SemanticQuadraticThreeWitness

open MvPolynomial Matrix DiophCompression.SemanticQuadraticGeneral DiophCompression.SemanticQuadraticMatrix

set_option maxHeartbeats 1000000 in
/-- Fidelity gate: a homogeneous quaternary quadratic has exactly the ten monomials. -/
theorem eval_quaternary_homogeneous_quadratic (H : MvPolynomial (Fin 4) ℤ) (hH : H.IsHomogeneous 2)
    (x : Fin 4 → ℤ) :
    eval x H = coeff (Finsupp.single 0 2) H * x 0 ^ 2
      + coeff (Finsupp.single 0 1 + Finsupp.single 1 1) H * x 0 * x 1
      + coeff (Finsupp.single 0 1 + Finsupp.single 2 1) H * x 0 * x 2
      + coeff (Finsupp.single 0 1 + Finsupp.single 3 1) H * x 0 * x 3
      + coeff (Finsupp.single 1 2) H * x 1 ^ 2
      + coeff (Finsupp.single 1 1 + Finsupp.single 2 1) H * x 1 * x 2
      + coeff (Finsupp.single 1 1 + Finsupp.single 3 1) H * x 1 * x 3
      + coeff (Finsupp.single 2 2) H * x 2 ^ 2
      + coeff (Finsupp.single 2 1 + Finsupp.single 3 1) H * x 2 * x 3
      + coeff (Finsupp.single 3 2) H * x 3 ^ 2 := by
  classical
  rw [eval_eq']
  set d00 : Fin 4 →₀ ℕ := Finsupp.single 0 2 with hd00
  set d01 : Fin 4 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1 with hd01
  set d02 : Fin 4 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 2 1 with hd02
  set d03 : Fin 4 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 3 1 with hd03
  set d11 : Fin 4 →₀ ℕ := Finsupp.single 1 2 with hd11
  set d12 : Fin 4 →₀ ℕ := Finsupp.single 1 1 + Finsupp.single 2 1 with hd12
  set d13 : Fin 4 →₀ ℕ := Finsupp.single 1 1 + Finsupp.single 3 1 with hd13
  set d22 : Fin 4 →₀ ℕ := Finsupp.single 2 2 with hd22
  set d23 : Fin 4 →₀ ℕ := Finsupp.single 2 1 + Finsupp.single 3 1 with hd23
  set d33 : Fin 4 →₀ ℕ := Finsupp.single 3 2 with hd33
  set T : Finset (Fin 4 →₀ ℕ) := {d00, d01, d02, d03, d11, d12, d13, d22, d23, d33} with hT
  have hsub : H.support ⊆ T := by
    intro d hd
    have hne : coeff d H ≠ 0 := mem_support_iff.mp hd
    have hdeg : Finsupp.degree d = 2 := by
      by_contra hc
      exact hne (hH.coeff_eq_zero hc)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_four] at hdeg
    have h0 : d 0 ≤ 2 := by omega
    have h1 : d 1 ≤ 2 := by omega
    have h2 : d 2 ≤ 2 := by omega
    simp only [hT, Finset.mem_insert, Finset.mem_singleton]
    interval_cases hd0 : d 0 <;> interval_cases hd1 : d 1 <;> interval_cases hd2 : d 2
    · -- (0, 0, 0, 2)
      right; right; right; right; right; right; right; right; right; ext i; fin_cases i <;> simp [hd33] <;> omega
    · -- (0, 0, 1, 1)
      right; right; right; right; right; right; right; right; left; ext i; fin_cases i <;> simp [hd23] <;> omega
    · -- (0, 0, 2, 0)
      right; right; right; right; right; right; right; left; ext i; fin_cases i <;> simp [hd22] <;> omega
    · -- (0, 1, 0, 1)
      right; right; right; right; right; right; left; ext i; fin_cases i <;> simp [hd13] <;> omega
    · -- (0, 1, 1, 0)
      right; right; right; right; right; left; ext i; fin_cases i <;> simp [hd12] <;> omega
    · omega
    · -- (0, 2, 0, 0)
      right; right; right; right; left; ext i; fin_cases i <;> simp [hd11] <;> omega
    · omega
    · omega
    · -- (1, 0, 0, 1)
      right; right; right; left; ext i; fin_cases i <;> simp [hd03] <;> omega
    · -- (1, 0, 1, 0)
      right; right; left; ext i; fin_cases i <;> simp [hd02] <;> omega
    · omega
    · -- (1, 1, 0, 0)
      right; left; ext i; fin_cases i <;> simp [hd01] <;> omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · -- (2, 0, 0, 0)
      left; ext i; fin_cases i <;> simp [hd00] <;> omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have hzero : ∀ d ∈ T, d ∉ H.support → coeff d H * ∏ i, x i ^ d i = 0 := by
    intro d _ hd
    have : coeff d H = 0 := by
      by_contra h
      exact hd (mem_support_iff.mpr h)
    rw [this, zero_mul]
  rw [Finset.sum_subset hsub hzero]
  have ne : ∀ (a b : Fin 4 →₀ ℕ) (i : Fin 4), a i ≠ b i → a ≠ b := by
    intro a b i h hab; exact h (by rw [hab])
  have n1 : d00 ∉ ({d01, d02, d03, d11, d12, d13, d22, d23, d33} : Finset (Fin 4 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne _ _ 0 (by simp [hd00, hd01]), ne _ _ 0 (by simp [hd00, hd02]), ne _ _ 0 (by simp [hd00, hd03]), ne _ _ 0 (by simp [hd00, hd11]), ne _ _ 0 (by simp [hd00, hd12]), ne _ _ 0 (by simp [hd00, hd13]), ne _ _ 0 (by simp [hd00, hd22]), ne _ _ 0 (by simp [hd00, hd23]), ne _ _ 0 (by simp [hd00, hd33])⟩
  have n2 : d01 ∉ ({d02, d03, d11, d12, d13, d22, d23, d33} : Finset (Fin 4 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne _ _ 1 (by simp [hd01, hd02]), ne _ _ 1 (by simp [hd01, hd03]), ne _ _ 0 (by simp [hd01, hd11]), ne _ _ 0 (by simp [hd01, hd12]), ne _ _ 0 (by simp [hd01, hd13]), ne _ _ 0 (by simp [hd01, hd22]), ne _ _ 0 (by simp [hd01, hd23]), ne _ _ 0 (by simp [hd01, hd33])⟩
  have n3 : d02 ∉ ({d03, d11, d12, d13, d22, d23, d33} : Finset (Fin 4 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne _ _ 2 (by simp [hd02, hd03]), ne _ _ 0 (by simp [hd02, hd11]), ne _ _ 0 (by simp [hd02, hd12]), ne _ _ 0 (by simp [hd02, hd13]), ne _ _ 0 (by simp [hd02, hd22]), ne _ _ 0 (by simp [hd02, hd23]), ne _ _ 0 (by simp [hd02, hd33])⟩
  have n4 : d03 ∉ ({d11, d12, d13, d22, d23, d33} : Finset (Fin 4 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne _ _ 0 (by simp [hd03, hd11]), ne _ _ 0 (by simp [hd03, hd12]), ne _ _ 0 (by simp [hd03, hd13]), ne _ _ 0 (by simp [hd03, hd22]), ne _ _ 0 (by simp [hd03, hd23]), ne _ _ 0 (by simp [hd03, hd33])⟩
  have n5 : d11 ∉ ({d12, d13, d22, d23, d33} : Finset (Fin 4 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne _ _ 1 (by simp [hd11, hd12]), ne _ _ 1 (by simp [hd11, hd13]), ne _ _ 1 (by simp [hd11, hd22]), ne _ _ 1 (by simp [hd11, hd23]), ne _ _ 1 (by simp [hd11, hd33])⟩
  have n6 : d12 ∉ ({d13, d22, d23, d33} : Finset (Fin 4 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne _ _ 2 (by simp [hd12, hd13]), ne _ _ 1 (by simp [hd12, hd22]), ne _ _ 1 (by simp [hd12, hd23]), ne _ _ 1 (by simp [hd12, hd33])⟩
  have n7 : d13 ∉ ({d22, d23, d33} : Finset (Fin 4 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne _ _ 1 (by simp [hd13, hd22]), ne _ _ 1 (by simp [hd13, hd23]), ne _ _ 1 (by simp [hd13, hd33])⟩
  have n8 : d22 ∉ ({d23, d33} : Finset (Fin 4 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne _ _ 2 (by simp [hd22, hd23]), ne _ _ 2 (by simp [hd22, hd33])⟩
  have n9 : d23 ∉ ({d33} : Finset (Fin 4 →₀ ℕ)) := by
    simp only [Finset.mem_singleton]
    exact ne _ _ 2 (by simp [hd23, hd33])
  rw [hT, Finset.sum_insert n1, Finset.sum_insert n2, Finset.sum_insert n3, Finset.sum_insert n4, Finset.sum_insert n5, Finset.sum_insert n6, Finset.sum_insert n7, Finset.sum_insert n8, Finset.sum_insert n9, Finset.sum_singleton]
  simp only [hd00, hd01, hd02, hd03, hd11, hd12, hd13, hd22, hd23, hd33, Fin.prod_univ_four, Finsupp.single_apply, Finsupp.add_apply]
  simp
  ring

/-- The c²-coefficient A of H. -/
noncomputable def aOf (H : MvPolynomial (Fin 4) ℤ) : ℤ := coeff (Finsupp.single 0 2) H

/-- The cross vector B = (B₁, B₂, B₃) of H (coefficients of c·uₖ). -/
noncomputable def bVectorOf (H : MvPolynomial (Fin 4) ℤ) : Fin 3 → ℤ :=
  ![coeff (Finsupp.single 0 1 + Finsupp.single 1 1) H,
    coeff (Finsupp.single 0 1 + Finsupp.single 2 1) H,
    coeff (Finsupp.single 0 1 + Finsupp.single 3 1) H]

/-- The upper-triangular witness coefficient matrix C(H) on the variables 1..3: W(u) = uᵀ C(H) u. -/
noncomputable def witnessMatrixOf (H : MvPolynomial (Fin 4) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![coeff (Finsupp.single 1 2) H, coeff (Finsupp.single 1 1 + Finsupp.single 2 1) H,
       coeff (Finsupp.single 1 1 + Finsupp.single 3 1) H;
     0, coeff (Finsupp.single 2 2) H, coeff (Finsupp.single 2 1 + Finsupp.single 3 1) H;
     0, 0, coeff (Finsupp.single 3 2) H]

/-- The fiber polynomial of H in matrix form. -/
theorem fiberVal_eq_fqM (H : MvPolynomial (Fin 4) ℤ) (hH : H.IsHomogeneous 2) (ℓ : Fin 4 → ℤ) (q : ℤ)
    (c : ℤ) (u : Fin 3 → ℤ) :
    fiberVal H ℓ q (Fin.cons c u) =
      fqM (aOf H) (bVectorOf H) (witnessMatrixOf H) (ℓ 0) (fun k => ℓ k.succ) q c u := by
  simp only [fiberVal, fqM, witnessQuad, aOf, bVectorOf, witnessMatrixOf]
  rw [eval_quaternary_homogeneous_quadratic H hH]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  have e0 : (Fin.cons c u : Fin 4 → ℤ) 0 = c := rfl
  have e1 : (Fin.cons c u : Fin 4 → ℤ) 1 = u 0 := rfl
  have e2 : (Fin.cons c u : Fin 4 → ℤ) 2 = u 1 := rfl
  have e3 : (Fin.cons c u : Fin 4 → ℤ) 3 = u 2 := rfl
  have l1 : ℓ (Fin.succ 0) = ℓ 1 := rfl
  have l2 : ℓ (Fin.succ 1) = ℓ 2 := rfl
  have l3 : ℓ (Fin.succ 2) = ℓ 3 := rfl
  try simp only [e0, e1, e2, e3, l1, l2, l3, Matrix.vecHead, Matrix.vecTail]
  ring

theorem fiberSetG_eq_fiberSetM (H : MvPolynomial (Fin 4) ℤ) (hH : H.IsHomogeneous 2) (ℓ : Fin 4 → ℤ) (q : ℤ) :
    fiberSetG H ℓ q = fiberSetM (aOf H) (bVectorOf H) (witnessMatrixOf H) (ℓ 0) (fun k => ℓ k.succ) q := by
  ext c
  simp only [fiberSetG, fiberSetM, Set.mem_setOf_eq, fiberVal_eq_fqM H hH]

theorem fboundG_eq_fboundM (K : ℕ) (ℓ : Fin 4 → ℤ) (q : ℤ) :
    fboundG K ℓ q = fboundM K (ℓ 0) (fun k => ℓ k.succ) q := by
  simp only [fboundG, fboundM]
  rw [Fin.sum_univ_succ]
  ring

/-- r = 3, explicit coordinates: every full-rank witness block satisfies the dichotomy. -/
theorem dichotomy3_full_rank (A : ℤ) (B : Fin 3 → ℤ) (C : Matrix (Fin 3) (Fin 3) ℤ)
    (hN : (witnessGram C).det ≠ 0) : DichotomyM A B C := full_rank_projection_dichotomy_of_direction_property (by norm_num) A B C hN

/-- r = 3, explicit coefficients (upper-triangular C): full rank ⇒ dichotomy. -/
theorem dichotomy3_full_rank_explicit (A B₁ B₂ B₃ C₁₁ C₁₂ C₁₃ C₂₂ C₂₃ C₃₃ : ℤ)
    (hN : (witnessGram !![C₁₁, C₁₂, C₁₃; 0, C₂₂, C₂₃; 0, 0, C₃₃]).det ≠ 0) :
    DichotomyM A ![B₁, B₂, B₃] !![C₁₁, C₁₂, C₁₃; 0, C₂₂, C₂₃; 0, 0, C₃₃] := dichotomy3_full_rank _ _ _ hN

/-- GPT r08 必須F: the abstract projection dichotomy for r = 3 on the full-rank branch. -/
theorem quadraticProjectionDichotomyZ_three_full_rank (H : MvPolynomial (Fin 4) ℤ) (hH : H.IsHomogeneous 2)
    (hN : (witnessGram (witnessMatrixOf H)).det ≠ 0) : DichotomyG H := by
  obtain ⟨K, hK⟩ := dichotomy3_full_rank (aOf H) (bVectorOf H) (witnessMatrixOf H) hN
  refine ⟨K, fun ℓ q => ?_⟩
  rw [fiberSetG_eq_fiberSetM H hH, fboundG_eq_fboundM]
  exact hK (ℓ 0) (fun k => ℓ k.succ) q

end DiophCompression.SemanticQuadraticThreeWitness

#print axioms DiophCompression.SemanticQuadraticThreeWitness.eval_quaternary_homogeneous_quadratic
#print axioms DiophCompression.SemanticQuadraticThreeWitness.fiberVal_eq_fqM
#print axioms DiophCompression.SemanticQuadraticThreeWitness.fiberSetG_eq_fiberSetM
#print axioms DiophCompression.SemanticQuadraticThreeWitness.fboundG_eq_fboundM
#print axioms DiophCompression.SemanticQuadraticThreeWitness.dichotomy3_full_rank
#print axioms DiophCompression.SemanticQuadraticThreeWitness.dichotomy3_full_rank_explicit
#print axioms DiophCompression.SemanticQuadraticThreeWitness.quadraticProjectionDichotomyZ_three_full_rank
