/-
  DiophCompression/SemanticQuadraticGeneral/NormalForm.lean — r07 必須B: quadratic normal form with an
  arbitrary number k of fiber variables (output c and r witnesses) and parameters σ.
  Statements frozen first: frozen statement file `SemanticQuadraticGeneral_STATEMENTS.lean` (md5 65776f2e).
  Mechanism: peel the fiber variables one at a time with mathlib's `optionEquivLeft` (induction on k);
  the degree bookkeeping is `totalDegree_coeff_optionEquivLeft_add_le`, the evaluation is
  `optionEquivLeft_elim_eval`. No monomial enumeration, no symmetrisation, nothing over ℚ or ℝ
  (GPT r06 必須B 禁止事項 are vacuous here: no 1/2, no orthogonal transformation, no diagonalisation).
  Session 7, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticGeneral.Defs

namespace DiophCompression.SemanticQuadraticGeneral

open MvPolynomial MPUP

/-- Peel the fiber variable 0: `Fin (k+1) ⊕ σ → Option (Fin k ⊕ σ)`, variable 0 ↦ none. -/
def peel (k : ℕ) (σ : Type) : Fin (k + 1) ⊕ σ → Option (Fin k ⊕ σ)
  | Sum.inl i => Fin.cases none (fun j => some (Sum.inl j)) i
  | Sum.inr s => some (Sum.inr s)

theorem elim_comp_peel {σ : Type} {k : ℕ} (x : Fin (k + 1) → ℤ) (a : σ → ℤ) :
    (fun o : Option (Fin k ⊕ σ) => o.elim (x 0) (Sum.elim (Fin.tail x) a)) ∘ peel k σ
      = Sum.elim x a := by
  funext v
  rcases v with i | s
  · refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  · rfl

/-- Evaluation through the peel: P(x, a) = Σ_i (eval of the i-th coefficient at (tail x, a)) · (x 0)^i. -/
theorem eval_peel {σ : Type} {k D : ℕ} (P : MvPolynomial (Fin (k + 1) ⊕ σ) ℤ) (hP : P.totalDegree ≤ D)
    (x : Fin (k + 1) → ℤ) (a : σ → ℤ) :
    eval (Sum.elim x a) P
      = ∑ i ∈ Finset.range (D + 1),
          eval (Sum.elim (Fin.tail x) a) ((optionEquivLeft ℤ (Fin k ⊕ σ) (rename (peel k σ) P)).coeff i)
            * (x 0) ^ i := by
  rw [← elim_comp_peel x a, ← eval_rename, optionEquivLeft_elim_eval]
  rw [Polynomial.eval_eq_sum_range' (n := D + 1)]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.coeff_map]
  · refine lt_of_le_of_lt Polynomial.natDegree_map_le ?_
    rw [natDegree_optionEquivLeft]
    exact lt_of_le_of_lt ((degreeOf_le_totalDegree _ _).trans ((totalDegree_rename_le _ _).trans hP))
      (Nat.lt_succ_self D)

/-- Degree of the i-th peeled coefficient: ≤ D − i. -/
theorem totalDegree_peel_coeff_le {σ : Type} {k D : ℕ} (P : MvPolynomial (Fin (k + 1) ⊕ σ) ℤ)
    (hP : P.totalDegree ≤ D) (i : ℕ) :
    ((optionEquivLeft ℤ (Fin k ⊕ σ) (rename (peel k σ) P)).coeff i).totalDegree ≤ D - i := by
  set P' := rename (peel k σ) P with hP'
  have hP'd : P'.totalDegree ≤ D := (totalDegree_rename_le _ _).trans hP
  by_cases hi : i ≤ P'.totalDegree
  · have := totalDegree_coeff_optionEquivLeft_add_le ℤ (Fin k ⊕ σ) P' i hi
    omega
  · push Not at hi
    have hz : (optionEquivLeft ℤ (Fin k ⊕ σ) P').coeff i = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [natDegree_optionEquivLeft]
      exact lt_of_le_of_lt (degreeOf_le_totalDegree _ _) hi
    rw [hz, totalDegree_zero]
    exact Nat.zero_le _

/-- Base case helper: a polynomial in `Fin 0 ⊕ σ` is a polynomial in σ. -/
theorem eval_fin_zero_sum {σ : Type} (P : MvPolynomial (Fin 0 ⊕ σ) ℤ) (x : Fin 0 → ℤ) (a : σ → ℤ) :
    eval (Sum.elim x a) P = eval a (rename (Sum.elim Fin.elim0 id) P) := by
  rw [eval_rename]
  refine congrArg (fun h => (eval h) P) ?_
  funext v
  rcases v with i | s
  · exact i.elim0
  · rfl

/-- 必須B, degree ≤ 1: constants on the fiber variables, a degree-≤1 polynomial in the parameters. -/
theorem normal_form_general_linear {σ : Type} (k : ℕ) (P : MvPolynomial (Fin k ⊕ σ) ℤ)
    (hP : P.totalDegree ≤ 1) :
    ∃ (β : Fin k → ℤ) (lam : MvPolynomial σ ℤ), lam.totalDegree ≤ 1 ∧
      ∀ (x : Fin k → ℤ) (a : σ → ℤ),
        eval (Sum.elim x a) P = ∑ i, β i * x i + eval a lam := by
  induction k with
  | zero =>
    refine ⟨Fin.elim0, rename (Sum.elim Fin.elim0 id) P, (totalDegree_rename_le _ _).trans hP, ?_⟩
    intro x a
    rw [eval_fin_zero_sum]
    simp
  | succ k ih =>
    set p := optionEquivLeft ℤ (Fin k ⊕ σ) (rename (peel k σ) P) with hp
    have h0 : (p.coeff 0).totalDegree ≤ 1 := by
      have := totalDegree_peel_coeff_le P hP 0; simpa using this
    have h1 : (p.coeff 1).totalDegree ≤ 0 := by
      have := totalDegree_peel_coeff_le P hP 1; simpa using this
    obtain ⟨β₀, lam₀, hlam₀, heval₀⟩ := ih (p.coeff 0) h0
    obtain ⟨b, hb⟩ : ∃ b : ℤ, b = coeff 0 (p.coeff 1) := ⟨_, rfl⟩
    have hc1 : p.coeff 1 = C b := by
      rw [hb]; exact totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp h1)
    refine ⟨Fin.cons b β₀, lam₀, hlam₀, ?_⟩
    intro x a
    rw [eval_peel P hP x a]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [heval₀, hc1, eval_C, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
    ring

/-- 必須B, degree ≤ 2: a homogeneous quadratic H in the fiber variables with constant coefficients,
    degree-≤1 parameter polynomials on the fiber variables, a degree-≤2 parameter polynomial. -/
theorem normal_form_general_quadratic {σ : Type} (k : ℕ) (P : MvPolynomial (Fin k ⊕ σ) ℤ)
    (hP : P.totalDegree ≤ 2) :
    ∃ (H : MvPolynomial (Fin k) ℤ) (ℓ : Fin k → MvPolynomial σ ℤ) (q : MvPolynomial σ ℤ),
      H.IsHomogeneous 2 ∧ H.totalDegree ≤ 2 ∧ (∀ i, (ℓ i).totalDegree ≤ 1) ∧ q.totalDegree ≤ 2 ∧
      ∀ (x : Fin k → ℤ) (a : σ → ℤ),
        eval (Sum.elim x a) P = eval x H + ∑ i, eval a (ℓ i) * x i + eval a q := by
  induction k with
  | zero =>
    refine ⟨0, Fin.elim0, rename (Sum.elim Fin.elim0 id) P, isHomogeneous_zero _ _ _, ?_,
      fun i => i.elim0, (totalDegree_rename_le _ _).trans hP, ?_⟩
    · rw [totalDegree_zero]; exact Nat.zero_le _
    · intro x a
      rw [eval_fin_zero_sum]
      simp
  | succ k ih =>
    set p := optionEquivLeft ℤ (Fin k ⊕ σ) (rename (peel k σ) P) with hp
    have h0 : (p.coeff 0).totalDegree ≤ 2 := by
      have := totalDegree_peel_coeff_le P hP 0; simpa using this
    have h1 : (p.coeff 1).totalDegree ≤ 1 := by
      have := totalDegree_peel_coeff_le P hP 1; simpa using this
    have h2 : (p.coeff 2).totalDegree ≤ 0 := by
      have := totalDegree_peel_coeff_le P hP 2; simpa using this
    obtain ⟨H₀, ℓ₀, q₀, hH₀, hH₀d, hℓ₀, hq₀, heval₀⟩ := ih (p.coeff 0) h0
    obtain ⟨β, lam, hlam, heval₁⟩ := normal_form_general_linear k (p.coeff 1) h1
    obtain ⟨A, hA⟩ : ∃ A : ℤ, A = coeff 0 (p.coeff 2) := ⟨_, rfl⟩
    have hc2 : p.coeff 2 = C A := by
      rw [hA]; exact totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp h2)
    let H : MvPolynomial (Fin (k + 1)) ℤ :=
      rename Fin.succ H₀ + (∑ j, C (β j) * X j.succ) * X 0 + C A * X 0 ^ 2
    have hH : H.IsHomogeneous 2 := by
      refine IsHomogeneous.add (IsHomogeneous.add hH₀.rename_isHomogeneous ?_) ?_
      · have : (∑ j, C (β j) * X (j.succ : Fin (k + 1))).IsHomogeneous 1 := by
          refine IsHomogeneous.sum _ _ _ fun j _ => ?_
          have := (isHomogeneous_C (Fin (k + 1)) (β j)).mul (isHomogeneous_X ℤ (j.succ : Fin (k + 1)))
          simpa using this
        have := this.mul (isHomogeneous_X ℤ (0 : Fin (k + 1)))
        simpa using this
      · have := (isHomogeneous_C (Fin (k + 1)) A).mul ((isHomogeneous_X ℤ (0 : Fin (k + 1))).pow 2)
        simpa using this
    refine ⟨H, Fin.cons lam ℓ₀, q₀, hH, hH.totalDegree_le, ?_, hq₀, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hlam
      · simpa using hℓ₀ j
    · intro x a
      rw [eval_peel P hP x a]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      rw [heval₀, heval₁, hc2, eval_C, Fin.sum_univ_succ]
      simp only [H, map_add, map_mul, map_sum, eval_C, eval_X, map_pow, eval_rename,
        Fin.cons_zero, Fin.cons_succ]
      have : (eval (x ∘ Fin.succ)) H₀ = eval (Fin.tail x) H₀ := rfl
      rw [this]
      simp only [Fin.tail]
      ring

/-- Relabel `Fin (n+1) ⊕ Fin r` (parameters-with-output ⊕ witnesses) to `Fin (r+1) ⊕ Fin n`
    (fiber ⊕ parameters): c ↦ inl 0, u_j ↦ inl (succ j), a_i ↦ inr i. -/
def relabelG (n r : ℕ) : Fin (n + 1) ⊕ Fin r → Fin (r + 1) ⊕ Fin n
  | Sum.inl i => Fin.lastCases (motive := fun _ => Fin (r + 1) ⊕ Fin n) (Sum.inl 0) (fun j => Sum.inr j) i
  | Sum.inr j => Sum.inl j.succ

theorem eval_relabelG {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℕ) (c : ℕ) (u : Fin r → ℤ) :
    eval (Sum.elim (Fin.cons (c : ℤ) u) (fun j => (a j : ℤ))) (rename (relabelG n r) P)
      = evalAt P (Fin.snoc a c) u := by
  unfold evalAt
  rw [eval_rename]
  refine congrArg (fun h => (eval h) P) ?_
  funext v
  rcases v with i | j
  · simp only [Function.comp_apply]
    induction i using Fin.lastCases with
    | last => simp [relabelG, Fin.snoc_last]
    | cast j => simp [relabelG, Fin.snoc_castSucc]
  · simp [relabelG]

/-- 必須B in the Poly (n+1) r form: P(a, c, u) = H(c, u) + L(a) c + Σ M_i(a) u_i + Q(a). -/
theorem quadratic_normal_form_general {n r : ℕ} (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2) :
    ∃ (H : MvPolynomial (Fin (r + 1)) ℤ) (ℓ : Fin (r + 1) → MvPolynomial (Fin n) ℤ)
      (q : MvPolynomial (Fin n) ℤ),
      H.IsHomogeneous 2 ∧ H.totalDegree ≤ 2 ∧ (∀ i, (ℓ i).totalDegree ≤ 1) ∧ q.totalDegree ≤ 2 ∧
      ∀ (a : Fin n → ℕ) (c : ℕ) (u : Fin r → ℤ),
        evalAt P (Fin.snoc a c) u
          = fiberVal H (fun i => eval (fun j => (a j : ℤ)) (ℓ i)) (eval (fun j => (a j : ℤ)) q)
              (Fin.cons (c : ℤ) u) := by
  obtain ⟨H, ℓ, q, hH, hHd, hℓ, hq, heval⟩ :=
    normal_form_general_quadratic (r + 1) (rename (relabelG n r) P)
      ((totalDegree_rename_le _ _).trans hP)
  refine ⟨H, ℓ, q, hH, hHd, hℓ, hq, ?_⟩
  intro a c u
  rw [← eval_relabelG P a c u, heval]
  rfl

end DiophCompression.SemanticQuadraticGeneral

#print axioms DiophCompression.SemanticQuadraticGeneral.normal_form_general_linear
#print axioms DiophCompression.SemanticQuadraticGeneral.normal_form_general_quadratic
#print axioms DiophCompression.SemanticQuadraticGeneral.quadratic_normal_form_general
