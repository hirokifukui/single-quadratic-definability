/-
  DiophCompression/SpecializationCapacity.lean — r04 Task 3 upper bound (session 4, 2026-08-26, claude.ai direct).
  SpecializationAchievable n q d → n ≤ C(d+q, q+1).
  Mechanism: specialize P a = Σ_β monomial (β|inr) (coeff β · ∏ a_i^{β(inl i)}); the z^m-coefficient is
  bounded by K·N^{d−|m|} on the box, so the coefficient map ℕ^n → ℤ^{degLE d q} has degree profile
  m ↦ d−|m|, and box_counting_bound gives n ≤ Σ_{|m|≤d}(d−|m|) = wCount d q = C(d+q,q+1).
-/
import DiophCompression.Definitions
import DiophCompression.PolynomialMapCapacity
import DiophCompression.Counting

namespace DiophCompression

open MvPolynomial

variable {n q : ℕ}

/-- The `inr`-part (unknown-variable part) of an exponent vector on `Fin n ⊕ Fin q`. -/
noncomputable def inrPart (β : (Fin n ⊕ Fin q) →₀ ℕ) : Fin q →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => β (Sum.inr j))

theorem inrPart_apply (β : (Fin n ⊕ Fin q) →₀ ℕ) (j : Fin q) : inrPart β j = β (Sum.inr j) := rfl

/-- Total degree of β splits as (parameter part) + (unknown part). -/
theorem sum_split (β : (Fin n ⊕ Fin q) →₀ ℕ) :
    (β.sum fun _ e => e) = (∑ i, β (Sum.inl i)) + ∑ j, β (Sum.inr j) := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sum_type]

/-- Term decomposition of `specialize`. -/
theorem specialize_eq (P : MvPolynomial (Fin n ⊕ Fin q) ℤ) (a : Fin n → ℕ) :
    specialize P a
      = ∑ β ∈ P.support,
          monomial (inrPart β) (coeff β P * ∏ i, ((a i : ℤ)) ^ β (Sum.inl i)) := by
  unfold specialize
  rw [aeval_eq_eval₂Hom, coe_eval₂Hom, eval₂_eq']
  apply Finset.sum_congr rfl
  intro β _
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, algebraMap_eq]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [inrPart_apply]
  have hC : (∏ i, C ((a i : ℤ)) ^ β (Sum.inl i) : MvPolynomial (Fin q) ℤ)
      = C (∏ i, ((a i : ℤ)) ^ β (Sum.inl i)) := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [C_pow]
  rw [hC, ← mul_assoc, ← C_mul]

/-- Coefficients of the specialization vanish above degree `d`. -/
theorem coeff_specialize_eq_zero (P : MvPolynomial (Fin n ⊕ Fin q) ℤ) {d : ℕ}
    (hP : P.totalDegree ≤ d) (a : Fin n → ℕ) (m : Fin q →₀ ℕ) (hm : d < ∑ j, m j) :
    coeff m (specialize P a) = 0 := by
  classical
  rw [specialize_eq, coeff_sum]
  apply Finset.sum_eq_zero
  intro β hβ
  rw [coeff_monomial]
  split_ifs with h
  · exfalso
    have h1 : ∑ j, m j = ∑ j, β (Sum.inr j) := by
      rw [← h]; rfl
    have h2 := le_totalDegree hβ
    rw [sum_split] at h2
    omega
  · rfl

/-- Weighted coefficient bound: |z^m-coefficient of P(a, z)| ≤ (Σ|coeff|) · N^{d − |m|}. -/
theorem coeff_specialize_abs_le (P : MvPolynomial (Fin n ⊕ Fin q) ℤ) {d : ℕ}
    (hP : P.totalDegree ≤ d) {N : ℕ} (h1 : 1 ≤ N) (a : Fin n → ℕ) (ha : ∀ i, a i ≤ N)
    (m : Fin q →₀ ℕ) :
    |coeff m (specialize P a)|
      ≤ (∑ β ∈ P.support, |coeff β P|) * (N : ℤ) ^ (d - ∑ j, m j) := by
  classical
  rw [specialize_eq, coeff_sum]
  calc |∑ β ∈ P.support, coeff m (monomial (inrPart β) (coeff β P * ∏ i, ((a i : ℤ)) ^ β (Sum.inl i)))|
      ≤ ∑ β ∈ P.support,
          |coeff m (monomial (inrPart β) (coeff β P * ∏ i, ((a i : ℤ)) ^ β (Sum.inl i)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ β ∈ P.support, |coeff β P| * (N : ℤ) ^ (d - ∑ j, m j) := by
        apply Finset.sum_le_sum
        intro β hβ
        rw [coeff_monomial]
        split_ifs with h
        · rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [Finset.abs_prod]
          have hdeg : ∑ i, β (Sum.inl i) ≤ d - ∑ j, m j := by
            have h1' : ∑ j, m j = ∑ j, β (Sum.inr j) := by rw [← h]; rfl
            have h2 := le_totalDegree hβ
            rw [sum_split] at h2
            omega
          calc ∏ i, |((a i : ℤ)) ^ β (Sum.inl i)| ≤ ∏ i, (N : ℤ) ^ β (Sum.inl i) := by
                apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
                intro i _
                rw [abs_pow, abs_of_nonneg (by positivity)]
                exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast ha i) _
            _ = (N : ℤ) ^ (∑ i, β (Sum.inl i)) := Finset.prod_pow_eq_pow_sum _ _ _
            _ ≤ (N : ℤ) ^ (d - ∑ j, m j) := pow_le_pow_right₀ (by exact_mod_cast h1) hdeg
        · rw [abs_zero]; positivity
    _ = _ := by rw [Finset.sum_mul]

/-- SPECIALIZATION CAPACITY, upper bound: S(d, q) ≤ C(d+q, q+1). -/
theorem specialization_bound {d : ℕ} (h : SpecializationAchievable n q d) :
    n ≤ (d + q).choose (q + 1) := by
  classical
  obtain ⟨P, hP, hinj⟩ := h
  let F : (Fin n → ℕ) → (degLE d q) → ℤ :=
    fun a m => coeff (Finsupp.equivFunOnFinite.symm m.1) (specialize P a)
  have hF : Function.Injective F := by
    intro a a' haa
    apply hinj
    ext m
    by_cases hm : ∑ j, m j ≤ d
    · have hmem : (Finsupp.equivFunOnFinite m) ∈ degLE d q := by
        rw [mem_degLE]; exact hm
      have hc := congrFun haa ⟨Finsupp.equivFunOnFinite m, hmem⟩
      simp only [F, Equiv.symm_apply_apply] at hc
      exact hc
    · push Not at hm
      rw [coeff_specialize_eq_zero P hP a m hm, coeff_specialize_eq_zero P hP a' m hm]
  let K : ℕ := ∑ β ∈ P.support, (coeff β P).natAbs
  have hK : (∑ β ∈ P.support, |coeff β P|) = (K : ℤ) := by
    simp only [K, Nat.cast_sum, Int.natCast_natAbs]
  have hb : ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℕ, (∀ i, a i ≤ N) →
      ∀ m : degLE d q, |F a m| ≤ (K : ℤ) * (N : ℤ) ^ (d - ∑ j, m.1 j) := by
    intro N h1 a ha m
    have := coeff_specialize_abs_le P hP h1 a ha (Finsupp.equivFunOnFinite.symm m.1)
    rw [hK] at this
    exact this
  have hbound := box_counting_bound F hF (fun m => d - ∑ j, m.1 j) K hb
  have hsum : (∑ m : degLE d q, (d - ∑ j, m.1 j)) = wCount d q := by
    unfold wCount
    exact Finset.sum_coe_sort (degLE d q) (fun m => d - ∑ j, m j)
  rw [hsum, wCount_eq_choose'] at hbound
  exact hbound

end DiophCompression

#print axioms DiophCompression.specialization_bound
