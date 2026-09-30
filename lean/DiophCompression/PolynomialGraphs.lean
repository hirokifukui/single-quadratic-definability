/-
  DiophCompression/PolynomialGraphs.lean — APAL Functional-Definability Pivot, Gate 7
  (session 23, 2026-08-31, claude.ai direct, 0 CC).
  GPT r20 必須C (polynomial graphs: degree ≤ 2 ⇒ SE₂; univariate degree ≥ 3 ⇒ not SE₂; univariate iff),
  必須D (x³: PP₂ yes / SE₂ no at every padded arity ⇒ SE₂(k) ⊊ PP₂(k) for all k ≥ 2),
  必須E (x² ∈ SE₂, x⁴ ∉ SE₂, x⁴ ∈ PP₂ ⇒ SE₂ unary functions not closed under composition).
  Engine: singleQuadratic_function_quadratic_growth (Gate 6); the only new analysis is the univariate lower bound
  (N − S)·N² ≤ |p(N)| for deg p ≥ 3.
  Statements frozen in frozen_statements/PolynomialGraphs_STATEMENTS.lean (md5 2eb04490).
-/
import DiophCompression.FiniteFiberGrowth
import DiophCompression.OneSortedFragments

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Definitions (verbatim from the freeze) -/

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

/-! ### Helpers: growth of a graphZZ-defined function -/

theorem graphVecZZ_one_eq_graphZZ {n : ℕ} (e : (Fin n → ℤ) → ℤ) :
    graphVecZZ (fun a (_ : Fin 1) => e a) = graphZZ e := by
  ext v
  simp only [graphVecZZ, graphZZ, Set.mem_setOf_eq]
  have h0 : Fin.natAdd n (0 : Fin 1) = Fin.last n := by ext; simp
  constructor
  · intro h
    have := congrFun h 0
    rw [h0] at this
    exact this
  · intro h
    funext j
    rw [Subsingleton.elim j 0, h0]
    exact h

/-- Quadratic growth of any `e : ℤⁿ → ℤ` whose graph is in SE₂. -/
theorem graphZZ_singleQuadratic_growth {n : ℕ} (e : (Fin n → ℤ) → ℤ)
    (h : WithinSingleEquationZZ 2 (graphZZ e)) :
    ∃ C : ℕ, ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) → |e a| ≤ (C : ℤ) * (N : ℤ) ^ 2 := by
  obtain ⟨r, P, hP, hrep⟩ := h
  have hf : SingleQuadraticDefinableFunctionZZ (fun a (_ : Fin 1) => e a) :=
    ⟨r, P, hP, by rw [graphVecZZ_one_eq_graphZZ]; exact hrep⟩
  obtain ⟨C, hC⟩ := singleQuadratic_function_quadratic_growth _ hf
  exact ⟨C, fun N h1 a ha => hC N h1 a ha 0⟩

/-! ### 必須C — polynomial graphs -/

/-- Any polynomial of total degree ≤ 2 has a single-quadratic graph (`y − p(x̄) = 0`, no witnesses). -/
theorem polynomial_graph_singleQuadratic_of_degree_le {n : ℕ} (p : MvPolynomial (Fin n) ℤ)
    (hp : p.totalDegree ≤ 2) : WithinSingleEquationZZ 2 (polyGraphZZ p) := by
  let Q : Poly (n + 1) 0 := X (Sum.inl (Fin.last n)) - rename (fun i => Sum.inl (Fin.castSucc i)) p
  refine ⟨0, Q, ?_, ?_⟩
  · refine (totalDegree_sub _ _).trans (max_le ((totalDegree_X_le_one _).trans (by norm_num)) ?_)
    exact (totalDegree_rename_le _ _).trans hp
  · intro v
    have hev : ∀ y : Fin 0 → ℤ, evalAtZZ Q v y = v (Fin.last n) - eval (Fin.init v) p := by
      intro y
      simp only [Q, evalAtZZ, map_sub, eval_X, Sum.elim_inl, eval_rename]
      rfl
    show v (Fin.last n) = eval (Fin.init v) p ↔ ∃ y : Fin 0 → ℤ, evalAtZZ Q v y = 0
    constructor
    · intro h
      exact ⟨Fin.elim0, by rw [hev, h, sub_self]⟩
    · rintro ⟨y, hy⟩
      rw [hev] at hy
      exact sub_eq_zero.mp hy

/-- Univariate lower bound: for `deg p ≥ 3` there is `S` with `(N − S)·N² ≤ |p(N)|` for all `N ≥ 1`. -/
theorem abs_eval_nat_ge_of_natDegree_ge_three (p : Polynomial ℤ) (hd : 3 ≤ p.natDegree) :
    ∃ S : ℕ, ∀ N : ℕ, 1 ≤ N → ((N : ℤ) - S) * (N : ℤ) ^ 2 ≤ |p.eval (N : ℤ)| := by
  classical
  obtain ⟨e, he⟩ : ∃ e, p.natDegree = e + 3 := ⟨p.natDegree - 3, by omega⟩
  refine ⟨∑ i ∈ Finset.range (e + 3), (p.coeff i).natAbs, ?_⟩
  intro N h1
  set S : ℕ := ∑ i ∈ Finset.range (e + 3), (p.coeff i).natAbs with hS
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at he
  have hlead : (1 : ℤ) ≤ |p.leadingCoeff| :=
    Int.one_le_abs (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  have hNz : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast h1
  have hN0 : (0 : ℤ) ≤ (N : ℤ) := by positivity
  have heval : p.eval (N : ℤ)
      = (∑ i ∈ Finset.range (e + 3), p.coeff i * (N : ℤ) ^ i) + p.leadingCoeff * (N : ℤ) ^ (e + 3) := by
    rw [Polynomial.eval_eq_sum_range, he, Finset.sum_range_succ]
    simp only [Polynomial.leadingCoeff, he]
  have hlow : |∑ i ∈ Finset.range (e + 3), p.coeff i * (N : ℤ) ^ i| ≤ (S : ℤ) * (N : ℤ) ^ (e + 2) := by
    calc |∑ i ∈ Finset.range (e + 3), p.coeff i * (N : ℤ) ^ i|
        ≤ ∑ i ∈ Finset.range (e + 3), |p.coeff i * (N : ℤ) ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (e + 3), |p.coeff i| * (N : ℤ) ^ (e + 2) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_pow, abs_of_nonneg hN0]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact pow_le_pow_right₀ hNz (by have := Finset.mem_range.mp hi; omega)
      _ = (S : ℤ) * (N : ℤ) ^ (e + 2) := by
          rw [hS, Nat.cast_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Int.natCast_natAbs]
  have htop : (N : ℤ) ^ (e + 3) ≤ |p.leadingCoeff * (N : ℤ) ^ (e + 3)| := by
    rw [abs_mul, abs_pow, abs_of_nonneg hN0]
    have : (0 : ℤ) ≤ (N : ℤ) ^ (e + 3) := by positivity
    nlinarith
  have hge : (N : ℤ) ^ (e + 3) - (S : ℤ) * (N : ℤ) ^ (e + 2) ≤ |p.eval (N : ℤ)| := by
    rw [heval]
    have h := abs_sub_abs_le_abs_sub (p.leadingCoeff * (N : ℤ) ^ (e + 3))
      (-(∑ i ∈ Finset.range (e + 3), p.coeff i * (N : ℤ) ^ i))
    rw [abs_neg, sub_neg_eq_add,
      add_comm (p.leadingCoeff * (N : ℤ) ^ (e + 3)) (∑ i ∈ Finset.range (e + 3), p.coeff i * (N : ℤ) ^ i)] at h
    linarith
  have hpow : (N : ℤ) ^ (e + 3) - (S : ℤ) * (N : ℤ) ^ (e + 2)
      = (N : ℤ) ^ (e + 2) * ((N : ℤ) - S) := by ring
  rw [hpow] at hge
  rcases le_or_gt ((N : ℤ) - S) 0 with hneg | hposS
  · calc ((N : ℤ) - S) * (N : ℤ) ^ 2 ≤ 0 := by nlinarith [sq_nonneg (N : ℤ)]
      _ ≤ |p.eval (N : ℤ)| := abs_nonneg _
  · have h2 : (N : ℤ) ^ 2 ≤ (N : ℤ) ^ (e + 2) := pow_le_pow_right₀ hNz (by omega)
    calc ((N : ℤ) - S) * (N : ℤ) ^ 2 ≤ ((N : ℤ) - S) * (N : ℤ) ^ (e + 2) :=
          mul_le_mul_of_nonneg_left h2 hposS.le
      _ = (N : ℤ) ^ (e + 2) * ((N : ℤ) - S) := by ring
      _ ≤ _ := hge

/-- A univariate polynomial of degree ≥ 3 grows too fast for a single quadratic definition. -/
theorem polynomial_graph_one_not_singleQuadratic (p : Polynomial ℤ) (hd : 3 ≤ p.natDegree) :
    ¬ WithinSingleEquationZZ 2 (polyGraphOneZZ p) := by
  intro h
  obtain ⟨C, hC⟩ := graphZZ_singleQuadratic_growth _ h
  obtain ⟨S, hS⟩ := abs_eval_nat_ge_of_natDegree_ge_three p hd
  set N : ℕ := S + C + 1 with hN
  have h1 : 1 ≤ N := by omega
  have hb : |p.eval (N : ℤ)| ≤ (C : ℤ) * (N : ℤ) ^ 2 := by
    have := hC N h1 (fun _ => (N : ℤ)) (fun _ => by rw [abs_of_nonneg (by positivity)])
    simpa using this
  have hl := hS N h1
  have hN2 : (0 : ℤ) < (N : ℤ) ^ 2 := by positivity
  have h3 : ((N : ℤ) - S) ≤ C := le_of_mul_le_mul_right (le_trans hl hb) hN2
  have hNc : (N : ℤ) = (S : ℤ) + C + 1 := by rw [hN]; push_cast; ring
  linarith

/-- Degree ≤ 2 direction, univariate (`y − Σ cᵢ xⁱ = 0`, no witnesses). -/
theorem polynomial_graph_one_singleQuadratic_of_natDegree_le (p : Polynomial ℤ) (hp : p.natDegree ≤ 2) :
    WithinSingleEquationZZ 2 (polyGraphOneZZ p) := by
  classical
  let Q : Poly 2 0 := X (Sum.inl (Fin.last 1))
    - ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X (Sum.inl 0) ^ i
  refine ⟨0, Q, ?_, ?_⟩
  · have hsum : (∑ i ∈ Finset.range (p.natDegree + 1),
        C (p.coeff i) * (X (Sum.inl 0) : Poly 2 0) ^ i).totalDegree ≤ 2 := by
      refine (totalDegree_finsetSum _ _).trans ?_
      refine Finset.sup_le fun i hi => ?_
      have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      calc (C (p.coeff i) * (X (Sum.inl 0) : Poly 2 0) ^ i).totalDegree
          ≤ (C (p.coeff i) : Poly 2 0).totalDegree + ((X (Sum.inl 0) : Poly 2 0) ^ i).totalDegree :=
            totalDegree_mul _ _
        _ = 0 + i := by rw [totalDegree_C, totalDegree_X_pow]
        _ ≤ 2 := by omega
    exact (totalDegree_sub _ _).trans (max_le ((totalDegree_X_le_one _).trans (by norm_num)) hsum)
  · intro v
    have hev : ∀ y : Fin 0 → ℤ, evalAtZZ Q v y = v (Fin.last 1) - p.eval (v 0) := by
      intro y
      simp only [Q, evalAtZZ, map_sub, eval_X, Sum.elim_inl, map_sum, map_mul, eval_C, map_pow]
      rw [Polynomial.eval_eq_sum_range]
    show v (Fin.last 1) = p.eval (Fin.init v 0) ↔ ∃ y : Fin 0 → ℤ, evalAtZZ Q v y = 0
    have hinit : Fin.init v 0 = v 0 := rfl
    rw [hinit]
    constructor
    · intro h
      exact ⟨Fin.elim0, by rw [hev, h, sub_self]⟩
    · rintro ⟨y, hy⟩
      rw [hev] at hy
      exact sub_eq_zero.mp hy

/-- Exact classification (univariate): `graph(p) ∈ SE₂ ⟺ deg p ≤ 2`. -/
theorem polynomial_graph_one_singleQuadratic_iff (p : Polynomial ℤ) :
    WithinSingleEquationZZ 2 (polyGraphOneZZ p) ↔ p.natDegree ≤ 2 := by
  constructor
  · intro h
    by_contra hd
    exact polynomial_graph_one_not_singleQuadratic p (by omega) h
  · exact polynomial_graph_one_singleQuadratic_of_natDegree_le p

/-! ### 必須D — binary fragment separation -/

/-- `a ↦ a₀^d` with `d ≥ 3` is not single-quadratic-definable at any padded arity (quadratic growth barrier). -/
theorem powerGraph_not_withinSingleEquationZZ (k d : ℕ) (hd : 3 ≤ d) :
    ¬ WithinSingleEquationZZ 2 (powerGraphZZ k d) := by
  intro h
  obtain ⟨C, hC⟩ := graphZZ_singleQuadratic_growth _ h
  set N : ℕ := C + 1 with hN
  have h1 : 1 ≤ N := by omega
  have hb : (N : ℤ) ^ d ≤ (C : ℤ) * (N : ℤ) ^ 2 := by
    have := hC N h1 (fun i => if i = 0 then (N : ℤ) else 0) (fun i => by split_ifs <;> simp)
    simpa using this
  have hNz : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast h1
  have h3 : (N : ℤ) ^ 3 ≤ (N : ℤ) ^ d := pow_le_pow_right₀ hNz hd
  have hN2 : (0 : ℤ) < (N : ℤ) ^ 2 := by positivity
  have hcube : (N : ℤ) ^ 3 = (N : ℤ) * (N : ℤ) ^ 2 := by ring
  have hle : (N : ℤ) * (N : ℤ) ^ 2 ≤ (C : ℤ) * (N : ℤ) ^ 2 := by rw [← hcube]; exact le_trans h3 hb
  have h4 : (N : ℤ) ≤ C := le_of_mul_le_mul_right hle hN2
  have hNc : (N : ℤ) = (C : ℤ) + 1 := by rw [hN]; push_cast; ring
  linarith

/-- `y = x³` via `∃z, z = x² ∧ y = x·z` (2 quadratics, 1 witness), at every padded arity. -/
theorem cubic_graph_withinPPZZ (k : ℕ) : WithinPPZZ 2 (powerGraphZZ k 3) := by
  refine ⟨1, 2, ![X (Sum.inr 0) - X (Sum.inl 0) * X (Sum.inl 0),
    X (Sum.inl (Fin.last (k + 1))) - X (Sum.inl 0) * X (Sum.inr 0)], ?_, ?_⟩
  · intro i
    fin_cases i
    · show (X (Sum.inr 0) - X (Sum.inl 0) * X (Sum.inl 0) : Poly (k + 2) 1).totalDegree ≤ 2
      exact (totalDegree_sub _ _).trans
        (max_le ((totalDegree_X_le_one _).trans (by norm_num)) (totalDegree_XX_le_two _ _))
    · show (X (Sum.inl (Fin.last (k + 1))) - X (Sum.inl 0) * X (Sum.inr 0) : Poly (k + 2) 1).totalDegree ≤ 2
      exact (totalDegree_sub _ _).trans
        (max_le ((totalDegree_X_le_one _).trans (by norm_num)) (totalDegree_XX_le_two _ _))
  · intro v
    simp only [powerGraphZZ, graphZZ, Set.mem_setOf_eq]
    have hinit : Fin.init v 0 = v 0 := by simp [Fin.init]
    rw [hinit]
    constructor
    · intro h
      refine ⟨fun _ => v 0 ^ 2, ?_⟩
      intro i
      fin_cases i
      · simp [evalAtZZ]; ring
      · simp [evalAtZZ, h]; ring
    · rintro ⟨y, hy⟩
      have h0 := hy 0
      have h1 := hy 1
      simp [evalAtZZ] at h0 h1
      linear_combination h1 + v 0 * h0

theorem cubic_graph_not_withinSingleEquationZZ (k : ℕ) :
    ¬ WithinSingleEquationZZ 2 (powerGraphZZ k 3) :=
  powerGraph_not_withinSingleEquationZZ k 3 (le_refl 3)

/-- `SE₂(k) ⊊ PP₂(k)` for every relation arity `k ≥ 2` (stated as `k + 2`). -/
theorem quadratic_fragment_strict_all_arity_ge_two (k : ℕ) :
    SingleEqFragmentZZ 2 (k + 2) ⊂ PPFragmentZZ 2 (k + 2) := by
  rw [Set.ssubset_def]
  refine ⟨singleEqFragmentZZ_subset_ppFragmentZZ 2 _, fun hsub => ?_⟩
  exact cubic_graph_not_withinSingleEquationZZ k (hsub (cubic_graph_withinPPZZ k))

/-- `SE₂(2) ⊊ PP₂(2)`. -/
theorem quadratic_fragment_strict_arity_two : SingleEqFragmentZZ 2 2 ⊂ PPFragmentZZ 2 2 :=
  quadratic_fragment_strict_all_arity_ge_two 0

/-! ### 必須E — composition failure -/

theorem square_graph_singleQuadratic : UnarySE2ZZ (fun x => x ^ 2) := by
  have h := polynomial_graph_singleQuadratic_of_degree_le (X 0 * X 0 : MvPolynomial (Fin 1) ℤ)
    (totalDegree_XX_le_two _ _)
  have hg : polyGraphZZ (X 0 * X 0 : MvPolynomial (Fin 1) ℤ)
      = graphZZ (fun a : Fin 1 → ℤ => (fun x : ℤ => x ^ 2) (a 0)) := by
    unfold polyGraphZZ
    congr 1
    funext a
    simp [sq]
  unfold UnarySE2ZZ
  rw [← hg]
  exact h

theorem fourth_power_graph_not_singleQuadratic : ¬ UnarySE2ZZ (fun x => x ^ 4) :=
  powerGraph_not_withinSingleEquationZZ 0 4 (by norm_num)

/-- `y = x⁴` via `∃z, z = x² ∧ y = z²`. -/
theorem fourth_power_graph_ppQuadratic : UnaryPP2ZZ (fun x => x ^ 4) := by
  refine ⟨1, 2, ![X (Sum.inr 0) - X (Sum.inl 0) * X (Sum.inl 0),
    X (Sum.inl (Fin.last 1)) - X (Sum.inr 0) * X (Sum.inr 0)], ?_, ?_⟩
  · intro i
    fin_cases i
    · show (X (Sum.inr 0) - X (Sum.inl 0) * X (Sum.inl 0) : Poly 2 1).totalDegree ≤ 2
      exact (totalDegree_sub _ _).trans
        (max_le ((totalDegree_X_le_one _).trans (by norm_num)) (totalDegree_XX_le_two _ _))
    · show (X (Sum.inl (Fin.last 1)) - X (Sum.inr 0) * X (Sum.inr 0) : Poly 2 1).totalDegree ≤ 2
      exact (totalDegree_sub _ _).trans
        (max_le ((totalDegree_X_le_one _).trans (by norm_num)) (totalDegree_XX_le_two _ _))
  · intro v
    simp only [graphZZ, Set.mem_setOf_eq]
    have hinit : Fin.init v 0 = v 0 := rfl
    have hl : Fin.last 1 = (1 : Fin 2) := rfl
    rw [hinit, hl]
    constructor
    · intro h
      refine ⟨fun _ => v 0 ^ 2, ?_⟩
      intro i
      fin_cases i
      · simp [evalAtZZ]; ring
      · simp [evalAtZZ, h]; ring
    · rintro ⟨y, hy⟩
      have h0 := hy 0
      have h1 := hy 1
      simp [evalAtZZ] at h0 h1
      linear_combination h1 + (y 0 + v 0 ^ 2) * h0

/-- The SE₂-definable unary functions are not closed under composition (witness: squaring twice). -/
theorem singleQuadratic_functions_not_closed_under_composition :
    ¬ ∀ f g : ℤ → ℤ, UnarySE2ZZ f → UnarySE2ZZ g → UnarySE2ZZ (g ∘ f) := by
  intro h
  have h4 := h (fun x => x ^ 2) (fun x => x ^ 2) square_graph_singleQuadratic square_graph_singleQuadratic
  have hfun : ((fun x : ℤ => x ^ 2) ∘ (fun x : ℤ => x ^ 2)) = fun x : ℤ => x ^ 4 := by
    funext x
    simp only [Function.comp]
    ring
  rw [hfun] at h4
  exact fourth_power_graph_not_singleQuadratic h4

end DiophCompression

#print axioms DiophCompression.polynomial_graph_singleQuadratic_of_degree_le
#print axioms DiophCompression.polynomial_graph_one_not_singleQuadratic
#print axioms DiophCompression.polynomial_graph_one_singleQuadratic_iff
#print axioms DiophCompression.powerGraph_not_withinSingleEquationZZ
#print axioms DiophCompression.cubic_graph_withinPPZZ
#print axioms DiophCompression.cubic_graph_not_withinSingleEquationZZ
#print axioms DiophCompression.quadratic_fragment_strict_arity_two
#print axioms DiophCompression.quadratic_fragment_strict_all_arity_ge_two
#print axioms DiophCompression.square_graph_singleQuadratic
#print axioms DiophCompression.fourth_power_graph_not_singleQuadratic
#print axioms DiophCompression.fourth_power_graph_ppQuadratic
#print axioms DiophCompression.singleQuadratic_functions_not_closed_under_composition
