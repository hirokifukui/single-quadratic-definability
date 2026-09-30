/-
  DiophCompression/SemanticQuadraticTwoWitness/Bridge2W.lean — fidelity gate and bridge for the two-witness cell
  (r07 必須D). Statements frozen first: frozen statement file `TwoWitness_STATEMENTS.lean` (md5 f396a2da).
  `eval_ternary_homogeneous_quadratic` (six monomials), `quadraticProjectionDichotomyZ_two_of_explicit`
  (explicit dichotomy for all coefficient tuples ⇒ the abstract predicate), and the tool (Per).
  Session 7, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticTwoWitness.Defs2W
import DiophCompression.SemanticQuadraticGeneral.ProjectionDichotomy

namespace DiophCompression.SemanticQuadraticTwoWitness

open MvPolynomial DiophCompression.SemanticQuadraticGeneral

/-- Fidelity gate: a homogeneous ternary quadratic has exactly the six monomials. -/
theorem eval_ternary_homogeneous_quadratic (H : MvPolynomial (Fin 3) ℤ) (hH : H.IsHomogeneous 2)
    (x : Fin 3 → ℤ) :
    eval x H = coeff (Finsupp.single 0 2) H * x 0 ^ 2
      + coeff (Finsupp.single 0 1 + Finsupp.single 1 1) H * x 0 * x 1
      + coeff (Finsupp.single 0 1 + Finsupp.single 2 1) H * x 0 * x 2
      + coeff (Finsupp.single 1 2) H * x 1 ^ 2
      + coeff (Finsupp.single 1 1 + Finsupp.single 2 1) H * x 1 * x 2
      + coeff (Finsupp.single 2 2) H * x 2 ^ 2 := by
  classical
  rw [eval_eq']
  set d00 : Fin 3 →₀ ℕ := Finsupp.single 0 2 with hd00
  set d01 : Fin 3 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1 with hd01
  set d02 : Fin 3 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 2 1 with hd02
  set d11 : Fin 3 →₀ ℕ := Finsupp.single 1 2 with hd11
  set d12 : Fin 3 →₀ ℕ := Finsupp.single 1 1 + Finsupp.single 2 1 with hd12
  set d22 : Fin 3 →₀ ℕ := Finsupp.single 2 2 with hd22
  set T : Finset (Fin 3 →₀ ℕ) := {d00, d01, d02, d11, d12, d22} with hT
  have hsub : H.support ⊆ T := by
    intro d hd
    have hne : coeff d H ≠ 0 := mem_support_iff.mp hd
    have hdeg : Finsupp.degree d = 2 := by
      by_contra hc
      exact hne (hH.coeff_eq_zero hc)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hdeg
    have h0 : d 0 ≤ 2 := by omega
    have h1 : d 1 ≤ 2 := by omega
    simp only [hT, Finset.mem_insert, Finset.mem_singleton]
    interval_cases hd0 : d 0 <;> interval_cases hd1 : d 1
    · -- (0,0,2)
      right; right; right; right; right
      ext i; fin_cases i <;> simp [hd22] <;> omega
    · -- (0,1,1)
      right; right; right; right; left
      ext i; fin_cases i <;> simp [hd12] <;> omega
    · -- (0,2,0)
      right; right; right; left
      ext i; fin_cases i <;> simp [hd11] <;> omega
    · -- (1,0,1)
      right; right; left
      ext i; fin_cases i <;> simp [hd02] <;> omega
    · -- (1,1,0)
      right; left
      ext i; fin_cases i <;> simp [hd01] <;> omega
    · -- (1,2,·) impossible
      omega
    · -- (2,0,0)
      left
      ext i; fin_cases i <;> simp [hd00] <;> omega
    · omega
    · omega
  have hzero : ∀ d ∈ T, d ∉ H.support → coeff d H * ∏ i, x i ^ d i = 0 := by
    intro d _ hd
    have : coeff d H = 0 := by
      by_contra h
      exact hd (mem_support_iff.mpr h)
    rw [this, zero_mul]
  rw [Finset.sum_subset hsub hzero]
  have ne : ∀ (a b : Fin 3 →₀ ℕ) (i : Fin 3), a i ≠ b i → a ≠ b := by
    intro a b i h hab; exact h (by rw [hab])
  have n1 : d00 ∉ ({d01, d02, d11, d12, d22} : Finset (Fin 3 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne _ _ 0 (by simp [hd00, hd01]), ne _ _ 0 (by simp [hd00, hd02]),
      ne _ _ 0 (by simp [hd00, hd11]), ne _ _ 0 (by simp [hd00, hd12]), ne _ _ 0 (by simp [hd00, hd22])⟩
  have n2 : d01 ∉ ({d02, d11, d12, d22} : Finset (Fin 3 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne _ _ 1 (by simp [hd01, hd02]), ne _ _ 0 (by simp [hd01, hd11]),
      ne _ _ 0 (by simp [hd01, hd12]), ne _ _ 0 (by simp [hd01, hd22])⟩
  have n3 : d02 ∉ ({d11, d12, d22} : Finset (Fin 3 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne _ _ 0 (by simp [hd02, hd11]), ne _ _ 0 (by simp [hd02, hd12]),
      ne _ _ 0 (by simp [hd02, hd22])⟩
  have n4 : d11 ∉ ({d12, d22} : Finset (Fin 3 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne _ _ 1 (by simp [hd11, hd12]), ne _ _ 1 (by simp [hd11, hd22])⟩
  have n5 : d12 ∉ ({d22} : Finset (Fin 3 →₀ ℕ)) := by
    simp only [Finset.mem_singleton]
    exact ne _ _ 1 (by simp [hd12, hd22])
  rw [hT, Finset.sum_insert n1, Finset.sum_insert n2, Finset.sum_insert n3, Finset.sum_insert n4,
    Finset.sum_insert n5, Finset.sum_singleton]
  simp only [hd00, hd01, hd02, hd11, hd12, hd22, Fin.prod_univ_three, Finsupp.single_apply,
    Finsupp.add_apply]
  simp
  ring

/-- Bridge: explicit dichotomy for every coefficient tuple ⇒ the abstract predicate for r = 2. -/
theorem quadraticProjectionDichotomyZ_two_of_explicit
    (h : ∀ A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ, Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂) :
    QuadraticProjectionDichotomyZ 2 := by
  intro H hH
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = coeff (Finsupp.single 0 2) H := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ B : ℤ, B = coeff (Finsupp.single 0 1 + Finsupp.single 1 1) H := ⟨_, rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ B : ℤ, B = coeff (Finsupp.single 0 1 + Finsupp.single 2 1) H := ⟨_, rfl⟩
  obtain ⟨C₁₁, hC₁₁⟩ : ∃ C : ℤ, C = coeff (Finsupp.single 1 2) H := ⟨_, rfl⟩
  obtain ⟨C₁₂, hC₁₂⟩ : ∃ C : ℤ, C = coeff (Finsupp.single 1 1 + Finsupp.single 2 1) H := ⟨_, rfl⟩
  obtain ⟨C₂₂, hC₂₂⟩ : ∃ C : ℤ, C = coeff (Finsupp.single 2 2) H := ⟨_, rfl⟩
  have hev : ∀ x : Fin 3 → ℤ, eval x H = A * x 0 ^ 2 + B₁ * x 0 * x 1 + B₂ * x 0 * x 2
      + C₁₁ * x 1 ^ 2 + C₁₂ * x 1 * x 2 + C₂₂ * x 2 ^ 2 := by
    intro x; rw [eval_ternary_homogeneous_quadratic H hH x, hA, hB₁, hB₂, hC₁₁, hC₁₂, hC₂₂]
  obtain ⟨K, hK⟩ := h A B₁ B₂ C₁₁ C₁₂ C₂₂
  refine ⟨K, fun ℓ q => ?_⟩
  have key : ∀ (c : ℤ) (u : Fin 2 → ℤ), fiberVal H ℓ q (Fin.cons c u)
      = fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ (ℓ 0) (ℓ 1) (ℓ 2) q c (u 0) (u 1) := by
    intro c u
    simp only [fiberVal, fq2, hev]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
    have e0 : (Fin.cons c u : Fin 3 → ℤ) 0 = c := rfl
    have e1 : (Fin.cons c u : Fin 3 → ℤ) 1 = u 0 := rfl
    have e2 : (Fin.cons c u : Fin 3 → ℤ) 2 = u 1 := rfl
    have e1' : (Fin.cons c u : Fin 3 → ℤ) (Fin.succ 0) = u 0 := rfl
    have e2' : (Fin.cons c u : Fin 3 → ℤ) (Fin.succ (Fin.succ 0)) = u 1 := rfl
    have l1 : ℓ (Fin.succ 0) = ℓ 1 := rfl
    have l2 : ℓ (Fin.succ (Fin.succ 0)) = ℓ 2 := rfl
    rw [e0, e1, e2, e1', e2', l1, l2]; ring
  have hset : fiberSetG H ℓ q = fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ (ℓ 0) (ℓ 1) (ℓ 2) q := by
    ext c
    simp only [fiberSetG, fiberSet2, Set.mem_setOf_eq, key]
    constructor
    · rintro ⟨u, hu⟩; exact ⟨u 0, u 1, hu⟩
    · rintro ⟨u, v, huv⟩
      refine ⟨![u, v], ?_⟩
      simpa using huv
  have hs1 : ℓ (Fin.succ 0) = ℓ 1 := rfl
  have hs2 : ℓ (Fin.succ (Fin.succ 0)) = ℓ 2 := rfl
  have hb : fboundG K ℓ q = fbound2 K (ℓ 0) (ℓ 1) (ℓ 2) q := by
    simp only [fboundG, fbound2]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one, hs1, hs2]; ring
  rw [hset, hb]
  exact hK (ℓ 0) (ℓ 1) (ℓ 2) q

/-- Tool (Per): a set of naturals whose membership is periodic is infinite or empty. -/
theorem periodic_infinite_or_empty (S : Set ℕ) (M : ℕ) (hM : 1 ≤ M)
    (h : ∀ c, c ∈ S ↔ c + M ∈ S) : S.Infinite ∨ S = ∅ := by
  by_cases hS : S = ∅
  · exact Or.inr hS
  · left
    obtain ⟨c₀, hc₀⟩ := Set.nonempty_iff_ne_empty.mpr hS
    have hmem : ∀ k : ℕ, c₀ + k * M ∈ S := by
      intro k
      induction k with
      | zero => simpa using hc₀
      | succ k ih =>
        have := (h (c₀ + k * M)).mp ih
        convert this using 1; ring
    apply Set.infinite_of_not_bddAbove
    intro ⟨b, hb⟩
    have := hb (hmem (b + 1))
    nlinarith

end DiophCompression.SemanticQuadraticTwoWitness

#print axioms DiophCompression.SemanticQuadraticTwoWitness.eval_ternary_homogeneous_quadratic
#print axioms DiophCompression.SemanticQuadraticTwoWitness.quadraticProjectionDichotomyZ_two_of_explicit
#print axioms DiophCompression.SemanticQuadraticTwoWitness.periodic_infinite_or_empty
