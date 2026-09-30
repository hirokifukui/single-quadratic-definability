/-
  frozen_statements/MultivariatePolynomialGraphs_STATEMENTS.lean — Gate 11 statement freeze (session 24, 2026-08-31).
  GPT r21 必須C: multivariate polynomial graph classification graph(p) ∈ SE_2 ⟺ totalDegree p ≤ 2, for every
  arity n (no 0 < n hypothesis: n = 0 is a constant, degree 0). Route (GPT Q2, INS-mpup-s23-01): top homogeneous
  component p_d ≠ 0 → integer point v with p_d(v) ≠ 0 → line polynomial q_v(t) = p(t·v) of natDegree d → the
  univariate lower bound (N−S)·N² ≤ |q_v(N)| against the quadratic growth of SE_2-definable functions on the box
  |t·v_i| ≤ N·V. No substitution into the defining equation is needed. Bodies are `sorry`.
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
  sorry

/-- The top homogeneous component of a nonzero polynomial is nonzero. -/
theorem topHomogeneous_ne_zero {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  sorry

/-- A nonzero integer polynomial does not vanish on all of ℤⁿ. -/
theorem exists_eval_ne_zero {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (hp : p ≠ 0) :
    ∃ v : Fin n → ℤ, eval v p ≠ 0 := by
  sorry

/-- `q_v(t) = p(t·v)`. -/
theorem linePoly_eval {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (v : Fin n → ℤ) (t : ℤ) :
    (linePoly p v).eval t = eval (fun i => t * v i) p := by
  sorry

/-- Coefficients of the line polynomial: `p_e(v)` for `e ≤ d`, `0` above. -/
theorem linePoly_coeff {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (v : Fin n → ℤ) (e : ℕ) :
    (linePoly p v).coeff e =
      if e ∈ Finset.range (p.totalDegree + 1) then eval v (homogeneousComponent e p) else 0 := by
  sorry

/-- If the top form does not vanish at `v`, the line polynomial has exact degree `d = totalDegree p`. -/
theorem linePoly_natDegree {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (v : Fin n → ℤ)
    (hv : eval v (homogeneousComponent p.totalDegree p) ≠ 0) :
    (linePoly p v).natDegree = p.totalDegree := by
  sorry

/-- Every nonzero `p` has an integer line along which it has exact degree `totalDegree p`. -/
theorem exists_line_natDegree_eq_totalDegree {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (hp : p ≠ 0) :
    ∃ v : Fin n → ℤ, (linePoly p v).natDegree = p.totalDegree := by
  sorry

/-- 必須C (⇒ direction): a polynomial of total degree ≥ 3 has no single-quadratic graph. -/
theorem polynomial_graph_not_singleQuadratic_of_degree_ge_three {n : ℕ} (p : MvPolynomial (Fin n) ℤ)
    (hd : 3 ≤ p.totalDegree) : ¬ WithinSingleEquationZZ 2 (polyGraphZZ p) := by
  sorry

/-- 必須C: exact multivariate classification, every arity. -/
theorem polynomial_graph_singleQuadratic_iff {n : ℕ} (p : MvPolynomial (Fin n) ℤ) :
    WithinSingleEquationZZ 2 (polyGraphZZ p) ↔ p.totalDegree ≤ 2 := by
  sorry

end DiophCompression
