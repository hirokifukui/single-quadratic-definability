/-
  frozen_statements/PolynomialGraphs_STATEMENTS.lean — Gate 7 statement freeze (session 23, 2026-08-31).
  GPT r20 必須C (polynomial graphs), 必須D (binary fragment separation by x³, padded to every arity ≥ 2),
  必須E (composition failure: x², x⁴). Bodies are `sorry`; frozen contract for DiophCompression/PolynomialGraphs.lean.
  Convention: graphZZ puts the output in the LAST coordinate; `powerGraphZZ k d` is the graph of a ↦ a₀^d on ℤ^{k+1},
  a relation of arity k+2 (k = 0 is the binary graph of x^d).  Univariate classification uses Polynomial ℤ / natDegree;
  the multivariate ⇐ direction is stated for MvPolynomial (Fin n) ℤ / totalDegree.  The multivariate ⇒ direction
  (nonvanishing direction of the top form) is NOT frozen here (later gate).
-/
import DiophCompression.FiniteFiberGrowth
import DiophCompression.OneSortedFragments

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Definitions -/

/-- Graph of the polynomial function `a ↦ p(a)` on ℤⁿ (relation arity n+1). -/
def polyGraphZZ {n : ℕ} (p : MvPolynomial (Fin n) ℤ) : Set (Fin (n + 1) → ℤ) :=
  graphZZ (fun a => eval a p)

/-- Graph of a univariate integer polynomial as a binary relation on ℤ. -/
def polyGraphOneZZ (p : Polynomial ℤ) : Set (Fin 2 → ℤ) :=
  graphZZ (fun a : Fin 1 → ℤ => p.eval (a 0))

/-- Graph of `a ↦ a₀ ^ d` on ℤ^{k+1} (relation arity k+2; the padding coordinates a₁..a_k are free). -/
def powerGraphZZ (k d : ℕ) : Set (Fin (k + 2) → ℤ) :=
  graphZZ (fun a : Fin (k + 1) → ℤ => (a 0) ^ d)

/-- A unary function `ℤ → ℤ` whose graph is in SE₂ (single quadratic equation, any number of witnesses). -/
def UnarySE2ZZ (e : ℤ → ℤ) : Prop :=
  WithinSingleEquationZZ 2 (graphZZ (fun a : Fin 1 → ℤ => e (a 0)))

/-- A unary function `ℤ → ℤ` whose graph is in PP₂ (finite conjunction of quadratics, witnesses). -/
def UnaryPP2ZZ (e : ℤ → ℤ) : Prop :=
  WithinPPZZ 2 (graphZZ (fun a : Fin 1 → ℤ => e (a 0)))

/-! ### 必須C — polynomial graphs -/

/-- Any polynomial of total degree ≤ 2 has a single-quadratic graph (`y − p(x̄) = 0`, no witnesses). -/
theorem polynomial_graph_singleQuadratic_of_degree_le {n : ℕ} (p : MvPolynomial (Fin n) ℤ)
    (hp : p.totalDegree ≤ 2) : WithinSingleEquationZZ 2 (polyGraphZZ p) := by
  sorry

/-- A univariate polynomial of degree ≥ 3 grows too fast for a single quadratic definition. -/
theorem polynomial_graph_one_not_singleQuadratic (p : Polynomial ℤ) (hd : 3 ≤ p.natDegree) :
    ¬ WithinSingleEquationZZ 2 (polyGraphOneZZ p) := by
  sorry

/-- Exact classification (univariate): `graph(p) ∈ SE₂ ⟺ deg p ≤ 2`. -/
theorem polynomial_graph_one_singleQuadratic_iff (p : Polynomial ℤ) :
    WithinSingleEquationZZ 2 (polyGraphOneZZ p) ↔ p.natDegree ≤ 2 := by
  sorry

/-! ### 必須D — binary fragment separation -/

/-- `a ↦ a₀^d` with `d ≥ 3` is not single-quadratic-definable at any padded arity (quadratic growth barrier). -/
theorem powerGraph_not_withinSingleEquationZZ (k d : ℕ) (hd : 3 ≤ d) :
    ¬ WithinSingleEquationZZ 2 (powerGraphZZ k d) := by
  sorry

/-- `y = x³` via `∃z, z = x² ∧ y = x·z` (2 quadratics, 1 witness), at every padded arity. -/
theorem cubic_graph_withinPPZZ (k : ℕ) : WithinPPZZ 2 (powerGraphZZ k 3) := by
  sorry

theorem cubic_graph_not_withinSingleEquationZZ (k : ℕ) :
    ¬ WithinSingleEquationZZ 2 (powerGraphZZ k 3) := by
  sorry

/-- `SE₂(2) ⊊ PP₂(2)`. -/
theorem quadratic_fragment_strict_arity_two : SingleEqFragmentZZ 2 2 ⊂ PPFragmentZZ 2 2 := by
  sorry

/-- `SE₂(k) ⊊ PP₂(k)` for every relation arity `k ≥ 2` (stated as `k + 2`). -/
theorem quadratic_fragment_strict_all_arity_ge_two (k : ℕ) :
    SingleEqFragmentZZ 2 (k + 2) ⊂ PPFragmentZZ 2 (k + 2) := by
  sorry

/-! ### 必須E — composition failure -/

theorem square_graph_singleQuadratic : UnarySE2ZZ (fun x => x ^ 2) := by
  sorry

theorem fourth_power_graph_not_singleQuadratic : ¬ UnarySE2ZZ (fun x => x ^ 4) := by
  sorry

/-- `y = x⁴` via `∃z, z = x² ∧ y = z²`. -/
theorem fourth_power_graph_ppQuadratic : UnaryPP2ZZ (fun x => x ^ 4) := by
  sorry

/-- The SE₂-definable unary functions are not closed under composition (witness: squaring twice). -/
theorem singleQuadratic_functions_not_closed_under_composition :
    ¬ ∀ f g : ℤ → ℤ, UnarySE2ZZ f → UnarySE2ZZ g → UnarySE2ZZ (g ∘ f) := by
  sorry

end DiophCompression
