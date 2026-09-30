/-
  DiophCompression/SemanticQuadratic/NormalForm.lean — homework S1 (session 6, 2026-08-27, claude.ai direct, no CC).
  Statements frozen first: frozen statement file `NormalForm_STATEMENTS.lean` (md5 89ae11b0).
  Every P ∈ ℤ[a₁..aₙ, c, u] of total degree ≤ 2 (ℕ-parameters a, c; one ℤ-unknown u) is
     Σ_{k+j ≤ 2} r_{kj}(a) c^j u^k,   r_{kj} ∈ ℤ[a], deg r_{kj} ≤ 2 − k − j,
  hence A c² + B c u + C u² + L(a) c + M(a) u + Q(a) with A, B, C ∈ ℤ, deg L, M ≤ 1, deg Q ≤ 2.
  Mechanism: rename the variables to Fin (n+2) with u ↦ 0, c ↦ 1, aᵢ ↦ i+2, then split off u and then c with
  mathlib's `finSuccEquiv` (polynomial in one variable with coefficients in the remaining variables); the
  degree bookkeeping is `totalDegree_coeff_finSuccEquiv_add_le`, the evaluation is `eval_eq_eval_mv_eval'`.
  No monomial enumeration. This is the common ground of the S2 (destroyer) and S3 (constructor) wings.
-/
import DiophCompression.Definitions

namespace DiophCompression.SemanticQuadratic

open MvPolynomial MPUP

/-- Variable relabelling `Fin (n+1) ⊕ Fin 1 → Fin (n+2)`: unknown `u ↦ 0`, last parameter `c ↦ 1`,
    parameter `aᵢ ↦ i + 2`. -/
def relabel (n : ℕ) : (Fin (n + 1) ⊕ Fin 1) → Fin (n + 2)
  | Sum.inl i => Fin.lastCases (motive := fun _ => Fin (n + 2)) (1 : Fin (n + 2)) (fun j => j.succ.succ) i
  | Sum.inr _ => 0

theorem eval_relabel {n : ℕ} (P : Poly (n + 1) 1) (a : Fin n → ℕ) (c : ℕ) (u : ℤ) :
    eval (Fin.cons u (Fin.cons (c : ℤ) (fun i => (a i : ℤ)))) (rename (relabel n) P)
      = evalAt P (Fin.snoc a c) (fun _ => u) := by
  unfold evalAt
  rw [eval_rename]
  refine congrArg (fun h => (eval h) P) ?_
  funext v
  rcases v with i | j
  · simp only [Function.comp_apply, Sum.elim_inl]
    induction i using Fin.lastCases with
    | last => simp [relabel, Fin.snoc_last]
    | cast j => simp [relabel, Fin.snoc_castSucc]
  · simp [relabel]

/-- `natDegree` bound for the `finSuccEquiv` image of a polynomial of bounded total degree. -/
theorem natDegree_finSuccEquiv_le {m : ℕ} (f : MvPolynomial (Fin (m + 1)) ℤ) (D : ℕ)
    (hf : f.totalDegree ≤ D) : (finSuccEquiv ℤ m f).natDegree ≤ D := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  by_contra h
  have := totalDegree_coeff_finSuccEquiv_add_le f N h
  omega

/-- Coefficient form: r k j ∈ ℤ[a] is the coefficient of u^k c^j; degree ≤ 2 − k − j; zero beyond degree 2. -/
theorem quadratic_normal_form {n : ℕ} (P : Poly (n + 1) 1) (hP : P.totalDegree ≤ 2) :
    ∃ r : ℕ → ℕ → MvPolynomial (Fin n) ℤ,
      (∀ k j, 2 < k + j → r k j = 0) ∧
      (∀ k j, k + j ≤ 2 → (r k j).totalDegree ≤ 2 - k - j) ∧
      ∀ (a : Fin n → ℕ) (c : ℕ) (u : ℤ),
        evalAt P (Fin.snoc a c) (fun _ => u)
          = ∑ k ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
              eval (fun i => (a i : ℤ)) (r k j) * (c : ℤ) ^ j * u ^ k := by
  set P' : MvPolynomial (Fin (n + 2)) ℤ := rename (relabel n) P with hP'
  have hP'd : P'.totalDegree ≤ 2 := (totalDegree_rename_le _ _).trans hP
  set f₁ := finSuccEquiv ℤ (n + 1) P' with hf₁
  let q : ℕ → MvPolynomial (Fin (n + 1)) ℤ := fun k => f₁.coeff k
  have hq : ∀ k, q k ≠ 0 → (q k).totalDegree + k ≤ 2 := fun k hk =>
    (totalDegree_coeff_finSuccEquiv_add_le P' k hk).trans hP'd
  let g : ℕ → Polynomial (MvPolynomial (Fin n) ℤ) := fun k => finSuccEquiv ℤ n (q k)
  let r : ℕ → ℕ → MvPolynomial (Fin n) ℤ := fun k j => (g k).coeff j
  have hr : ∀ k j, r k j ≠ 0 → (r k j).totalDegree + k + j ≤ 2 := by
    intro k j hkj
    have h1 := totalDegree_coeff_finSuccEquiv_add_le (q k) j hkj
    have hqk : q k ≠ 0 := by
      intro h0
      apply hkj
      show (finSuccEquiv ℤ n (q k)).coeff j = 0
      rw [h0, map_zero, Polynomial.coeff_zero]
    have h2 := hq k hqk
    change ((finSuccEquiv ℤ n (q k)).coeff j).totalDegree + k + j ≤ 2
    omega
  refine ⟨r, ?_, ?_, ?_⟩
  · intro k j hkj
    by_contra h
    have := hr k j h
    omega
  · intro k j hkj
    by_cases h : r k j = 0
    · rw [h, totalDegree_zero]; exact Nat.zero_le _
    · have := hr k j h; omega
  · intro a c u
    rw [← eval_relabel P a c u]
    rw [eval_eq_eval_mv_eval' (Fin.cons (c : ℤ) (fun i => (a i : ℤ))) u P']
    rw [Polynomial.eval_eq_sum_range' (n := 3)]
    · apply Finset.sum_congr rfl
      intro k _
      rw [Polynomial.coeff_map]
      show eval (Fin.cons (c : ℤ) (fun i => (a i : ℤ))) (q k) * u ^ k = _
      rw [eval_eq_eval_mv_eval' (fun i => (a i : ℤ)) (c : ℤ) (q k)]
      rw [Polynomial.eval_eq_sum_range' (n := 3)]
      · rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [Polynomial.coeff_map]
      · refine lt_of_le_of_lt (Polynomial.natDegree_map_le) ?_
        by_cases hqk : q k = 0
        · show (finSuccEquiv ℤ n (q k)).natDegree < 3
          rw [hqk, map_zero, Polynomial.natDegree_zero]; norm_num
        · have := hq k hqk
          exact lt_of_le_of_lt (natDegree_finSuccEquiv_le (q k) (2 - k) (by omega)) (by omega)
    · refine lt_of_le_of_lt (Polynomial.natDegree_map_le) ?_
      exact lt_of_le_of_lt (natDegree_finSuccEquiv_le P' 2 hP'd) (by norm_num)

/-- Six-term form (GPT r05 S1): A c² + B c u + C u² + L(a) c + M(a) u + Q(a). -/
theorem quadratic_normal_form_explicit {n : ℕ} (P : Poly (n + 1) 1) (hP : P.totalDegree ≤ 2) :
    ∃ (A B C : ℤ) (L M Q : MvPolynomial (Fin n) ℤ),
      L.totalDegree ≤ 1 ∧ M.totalDegree ≤ 1 ∧ Q.totalDegree ≤ 2 ∧
      ∀ (a : Fin n → ℕ) (c : ℕ) (u : ℤ),
        evalAt P (Fin.snoc a c) (fun _ => u)
          = A * (c : ℤ) ^ 2 + B * (c : ℤ) * u + C * u ^ 2
            + eval (fun i => (a i : ℤ)) L * (c : ℤ) + eval (fun i => (a i : ℤ)) M * u
            + eval (fun i => (a i : ℤ)) Q := by
  obtain ⟨r, hzero, hdeg, heval⟩ := quadratic_normal_form P hP
  have hA : r 0 2 = C (coeff 0 (r 0 2)) := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp (hdeg 0 2 (by norm_num)))
  have hB : r 1 1 = C (coeff 0 (r 1 1)) := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp (hdeg 1 1 (by norm_num)))
  have hC : r 2 0 = C (coeff 0 (r 2 0)) := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp (hdeg 2 0 (by norm_num)))
  refine ⟨coeff 0 (r 0 2), coeff 0 (r 1 1), coeff 0 (r 2 0), r 0 1, r 1 0, r 0 0,
    hdeg 0 1 (by norm_num), hdeg 1 0 (by norm_num), hdeg 0 0 (by norm_num), ?_⟩
  intro a c u
  rw [heval a c u]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hzero 1 2 (by norm_num), hzero 2 1 (by norm_num), hzero 2 2 (by norm_num)]
  have eA : eval (fun i => (a i : ℤ)) (r 0 2) = coeff 0 (r 0 2) := by
    conv_lhs => rw [hA]
    exact eval_C _
  have eB : eval (fun i => (a i : ℤ)) (r 1 1) = coeff 0 (r 1 1) := by
    conv_lhs => rw [hB]
    exact eval_C _
  have eC : eval (fun i => (a i : ℤ)) (r 2 0) = coeff 0 (r 2 0) := by
    conv_lhs => rw [hC]
    exact eval_C _
  rw [eA, eB, eC]
  simp only [map_zero]
  ring

end DiophCompression.SemanticQuadratic

#print axioms DiophCompression.SemanticQuadratic.quadratic_normal_form
#print axioms DiophCompression.SemanticQuadratic.quadratic_normal_form_explicit
