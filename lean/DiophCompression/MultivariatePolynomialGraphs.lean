/-
  DiophCompression/MultivariatePolynomialGraphs.lean — APAL Structural Theory Gate 1, kernel item 必須C
  (session 24, 2026-08-31, claude.ai direct, 0 CC).
  GPT r21 必須C / Q2 (INS-mpup-s23-01): graph(p) ∈ SE_2 ⟺ totalDegree p ≤ 2 for every arity. The ⇒ direction is
  proved by exhibiting an integer line t·v on which p has exact degree d (top homogeneous component nonvanishing at v)
  and colliding the univariate lower bound (N−S)·N² ≤ |p(N·v)| with the quadratic growth of SE_2-definable functions.
  Statements frozen in frozen_statements/MultivariatePolynomialGraphs_STATEMENTS.lean.
-/
import DiophCompression.PolynomialGraphs

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Definitions -/

/-- The line polynomial `q_v(t) = p(t·v)`, written through the homogeneous components of `p`. -/
noncomputable def linePoly {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (v : Fin n → ℤ) : Polynomial ℤ :=
  ∑ e ∈ Finset.range (p.totalDegree + 1),
    Polynomial.C (eval v (homogeneousComponent e p)) * Polynomial.X ^ e

/-! ### Theorems -/

/-- Homogeneous scaling: `h(t·v) = t^e · h(v)` for `h` homogeneous of degree `e`. -/
theorem eval_mul_of_isHomogeneous {n : ℕ} (h : MvPolynomial (Fin n) ℤ) {e : ℕ}
    (hh : h.IsHomogeneous e) (t : ℤ) (v : Fin n → ℤ) :
    eval (fun i => t * v i) h = t ^ e * eval v h := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hdeg : ∑ i ∈ s.support, s i = e := by
    have := hh (mem_support_iff.mp hs)
    rw [Finsupp.weight_apply] at this
    simpa [Finsupp.sum] using this
  rw [← hdeg, ← Finset.prod_pow_eq_pow_sum]
  rw [show (∏ i ∈ s.support, (t * v i) ^ s i) = (∏ i ∈ s.support, t ^ s i) * ∏ i ∈ s.support, (v i) ^ s i by
    rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro i _; ring]
  ring

/-- The top homogeneous component of a nonzero polynomial is nonzero. -/
theorem topHomogeneous_ne_zero {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.mpr hp)
    (fun s => s.sum fun _ e => e)
  intro h0
  have hc : coeff s (homogeneousComponent p.totalDegree p) = coeff s p := by
    rw [coeff_homogeneousComponent, if_pos]
    rw [totalDegree, hsup]
    simp [Finsupp.degree, Finsupp.sum]
  rw [h0, coeff_zero] at hc
  exact (mem_support_iff.mp hs) hc.symm

/-- A nonzero integer polynomial does not vanish on all of ℤⁿ. -/
theorem exists_eval_ne_zero {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (hp : p ≠ 0) :
    ∃ v : Fin n → ℤ, eval v p ≠ 0 := by
  by_contra h
  apply hp
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  by_contra hx
  exact h ⟨x, hx⟩

/-- `q_v(t) = p(t·v)`. -/
theorem linePoly_eval {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (v : Fin n → ℤ) (t : ℤ) :
    (linePoly p v).eval t = eval (fun i => t * v i) p := by
  have hp := sum_homogeneousComponent p
  calc (linePoly p v).eval t
      = eval (fun i => t * v i) (∑ e ∈ Finset.range (p.totalDegree + 1), homogeneousComponent e p) := by
        unfold linePoly
        rw [Polynomial.eval_finsetSum, map_sum]
        apply Finset.sum_congr rfl
        intro e _
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
          eval_mul_of_isHomogeneous _ (homogeneousComponent_isHomogeneous e p) t v]
        ring
    _ = eval (fun i => t * v i) p := by rw [hp]

/-- Coefficients of the line polynomial: `p_e(v)` for `e ≤ d`, `0` above. -/
theorem linePoly_coeff {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (v : Fin n → ℤ) (e : ℕ) :
    (linePoly p v).coeff e =
      if e ∈ Finset.range (p.totalDegree + 1) then eval v (homogeneousComponent e p) else 0 := by
  unfold linePoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]

/-- If the top form does not vanish at `v`, the line polynomial has exact degree `d = totalDegree p`. -/
theorem linePoly_natDegree {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (v : Fin n → ℤ)
    (hv : eval v (homogeneousComponent p.totalDegree p) ≠ 0) :
    (linePoly p v).natDegree = p.totalDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro e he
    rw [linePoly_coeff, if_neg]
    rw [Finset.mem_range]
    omega
  · rw [linePoly_coeff, if_pos (by rw [Finset.mem_range]; omega)]
    exact hv

/-- Every nonzero `p` has an integer line along which it has exact degree `totalDegree p`. -/
theorem exists_line_natDegree_eq_totalDegree {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (hp : p ≠ 0) :
    ∃ v : Fin n → ℤ, (linePoly p v).natDegree = p.totalDegree := by
  obtain ⟨v, hv⟩ := exists_eval_ne_zero _ (topHomogeneous_ne_zero p hp)
  exact ⟨v, linePoly_natDegree p v hv⟩

/-- 必須C (⇒ direction): a polynomial of total degree ≥ 3 has no single-quadratic graph. -/
theorem polynomial_graph_not_singleQuadratic_of_degree_ge_three {n : ℕ} (p : MvPolynomial (Fin n) ℤ)
    (hd : 3 ≤ p.totalDegree) : ¬ WithinSingleEquationZZ 2 (polyGraphZZ p) := by
  intro hSE
  obtain ⟨C, hC⟩ := graphZZ_singleQuadratic_growth (fun a => eval a p) hSE
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hd
  obtain ⟨v, hv⟩ := exists_line_natDegree_eq_totalDegree p hp
  obtain ⟨S, hS⟩ := abs_eval_nat_ge_of_natDegree_ge_three (linePoly p v) (by rw [hv]; exact hd)
  set V : ℕ := 1 + ∑ i, (v i).natAbs with hV
  have hVi : ∀ i, |v i| ≤ (V : ℤ) := by
    intro i
    have : (v i).natAbs ≤ ∑ j, (v j).natAbs :=
      Finset.single_le_sum (f := fun j => (v j).natAbs) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [← Int.natCast_natAbs]
    exact_mod_cast (show (v i).natAbs ≤ V by omega)
  set N : ℕ := S + C * V ^ 2 + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hNV : 1 ≤ N * V := Nat.mul_pos (by omega) (by omega)
  have hbox : ∀ i, |(N : ℤ) * v i| ≤ ((N * V : ℕ) : ℤ) := by
    intro i
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    push_cast
    exact mul_le_mul_of_nonneg_left (hVi i) (Nat.cast_nonneg N)
  have hup := hC (N * V) hNV (fun i => (N : ℤ) * v i) hbox
  have hlow := hS N hN1
  rw [linePoly_eval] at hlow
  have h1 : ((N : ℤ) - S) * (N : ℤ) ^ 2 ≤ (C : ℤ) * ((N * V : ℕ) : ℤ) ^ 2 := hlow.trans hup
  push_cast at h1
  have h2 : ((N : ℤ) - S) ≤ (C : ℤ) * (V : ℤ) ^ 2 := by
    have hpos : (0 : ℤ) < (N : ℤ) ^ 2 := by positivity
    have h3 : ((N : ℤ) - S) * (N : ℤ) ^ 2 ≤ ((C : ℤ) * (V : ℤ) ^ 2) * (N : ℤ) ^ 2 := by
      calc ((N : ℤ) - S) * (N : ℤ) ^ 2 ≤ (C : ℤ) * ((N : ℤ) * (V : ℤ)) ^ 2 := h1
        _ = ((C : ℤ) * (V : ℤ) ^ 2) * (N : ℤ) ^ 2 := by ring
    exact le_of_mul_le_mul_right h3 hpos
  have hNeq : (N : ℤ) = S + C * V ^ 2 + 1 := by rw [hN]; push_cast; ring
  linarith

/-- 必須C: exact multivariate classification, every arity. -/
theorem polynomial_graph_singleQuadratic_iff {n : ℕ} (p : MvPolynomial (Fin n) ℤ) :
    WithinSingleEquationZZ 2 (polyGraphZZ p) ↔ p.totalDegree ≤ 2 := by
  refine ⟨fun h => ?_, fun h => polynomial_graph_singleQuadratic_of_degree_le p h⟩
  by_contra hlt
  exact polynomial_graph_not_singleQuadratic_of_degree_ge_three p (by omega) h

end DiophCompression

#print axioms DiophCompression.eval_mul_of_isHomogeneous
#print axioms DiophCompression.topHomogeneous_ne_zero
#print axioms DiophCompression.exists_eval_ne_zero
#print axioms DiophCompression.linePoly_eval
#print axioms DiophCompression.linePoly_coeff
#print axioms DiophCompression.linePoly_natDegree
#print axioms DiophCompression.exists_line_natDegree_eq_totalDegree
#print axioms DiophCompression.polynomial_graph_not_singleQuadratic_of_degree_ge_three
#print axioms DiophCompression.polynomial_graph_singleQuadratic_iff
