/-
  DiophCompression/SkolemReduction.lean — APAL Functional-Definability Pivot, Gate 8
  (session 23, 2026-08-31, claude.ai direct, 0 CC).
  GPT r20 必須F: PP₂(k) = Dioph(k). Skolem degree reduction by structural induction on the polynomial
  (C / + / ·X), one fresh witness per node; the designated witness is forced to the value and the system is
  always satisfiable. Converse: PP_d ⊆ SE_{2d} ⊆ Dioph (sum of squares, OneSortedFragments).
  Statements frozen in frozen_statements/SkolemReduction_STATEMENTS.lean (md5 cabd8d0a).
-/
import DiophCompression.OneSortedFragments
import DiophCompression.OneSortedPPFolding

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Definitions (verbatim from the freeze) -/

/-- `A ⊆ ℤᵏ` is Diophantine: defined by ONE polynomial equation of any degree with integer witnesses. -/
def WithinDiophZZ {k : ℕ} (A : Set (Fin k → ℤ)) : Prop :=
  ∃ r, ∃ P : Poly k r, RepresentsZZ P A

/-- The Diophantine relations of arity `k`, as a set of relations. -/
def DiophFragmentZZ (k : ℕ) : Set (Set (Fin k → ℤ)) := {A | WithinDiophZZ A}

/-- `P` is Skolem-computable: a system of degree ≤ 2 over `k` inputs and `r` witnesses with a designated
    witness `w` such that every solution forces `y w = P(a)` and every input has a solution. -/
def SkolemComputable {k : ℕ} (P : MvPolynomial (Fin k) ℤ) : Prop :=
  ∃ (r m : ℕ) (S : PolySystem k r m) (w : Fin r), (∀ i, (S i).totalDegree ≤ 2) ∧
    (∀ (a : Fin k → ℤ) (y : Fin r → ℤ), (∀ i, evalAtZZ (S i) a y = 0) → y w = eval a P) ∧
    (∀ a : Fin k → ℤ, ∃ y : Fin r → ℤ, ∀ i, evalAtZZ (S i) a y = 0)

/-! ### Combining two systems with one fresh witness and one closing equation -/

section Combine

variable (k r₁ r₂ : ℕ)

def wIdx₁ (t : Fin r₁) : Fin (r₁ + r₂ + 1) := Fin.castAdd 1 (Fin.castAdd r₂ t)
def wIdx₂ (t : Fin r₂) : Fin (r₁ + r₂ + 1) := Fin.castAdd 1 (Fin.natAdd r₁ t)
def wIdxNew : Fin (r₁ + r₂ + 1) := Fin.natAdd (r₁ + r₂) 0

def wφ₁ : Fin k ⊕ Fin r₁ → Fin k ⊕ Fin (r₁ + r₂ + 1)
  | Sum.inl i => Sum.inl i
  | Sum.inr t => Sum.inr (wIdx₁ r₁ r₂ t)

def wφ₂ : Fin k ⊕ Fin r₂ → Fin k ⊕ Fin (r₁ + r₂ + 1)
  | Sum.inl i => Sum.inl i
  | Sum.inr t => Sum.inr (wIdx₂ r₁ r₂ t)

/-- Witness vector: the two blocks followed by the fresh value. -/
def wvec (y₁ : Fin r₁ → ℤ) (y₂ : Fin r₂ → ℤ) (c : ℤ) : Fin (r₁ + r₂ + 1) → ℤ :=
  Fin.append (Fin.append y₁ y₂) ![c]

variable {k r₁ r₂}

@[simp] theorem wvec_idx₁ (y₁ : Fin r₁ → ℤ) (y₂ : Fin r₂ → ℤ) (c : ℤ) (t : Fin r₁) :
    wvec r₁ r₂ y₁ y₂ c (wIdx₁ r₁ r₂ t) = y₁ t := by
  simp [wvec, wIdx₁]

@[simp] theorem wvec_idx₂ (y₁ : Fin r₁ → ℤ) (y₂ : Fin r₂ → ℤ) (c : ℤ) (t : Fin r₂) :
    wvec r₁ r₂ y₁ y₂ c (wIdx₂ r₁ r₂ t) = y₂ t := by
  simp [wvec, wIdx₂]

@[simp] theorem wvec_new (y₁ : Fin r₁ → ℤ) (y₂ : Fin r₂ → ℤ) (c : ℤ) :
    wvec r₁ r₂ y₁ y₂ c (wIdxNew r₁ r₂) = c := by
  simp [wvec, wIdxNew]

theorem evalAtZZ_rename_wφ₁ (Q : Poly k r₁) (a : Fin k → ℤ) (y : Fin (r₁ + r₂ + 1) → ℤ) :
    evalAtZZ (rename (wφ₁ k r₁ r₂) Q) a y = evalAtZZ Q a (fun t => y (wIdx₁ r₁ r₂ t)) := by
  apply evalAtZZ_rename_eq
  intro v
  rcases v with i | t <;> rfl

theorem evalAtZZ_rename_wφ₂ (Q : Poly k r₂) (a : Fin k → ℤ) (y : Fin (r₁ + r₂ + 1) → ℤ) :
    evalAtZZ (rename (wφ₂ k r₁ r₂) Q) a y = evalAtZZ Q a (fun t => y (wIdx₂ r₁ r₂ t)) := by
  apply evalAtZZ_rename_eq
  intro v
  rcases v with i | t <;> rfl

/-- The combined system: block 1, block 2, then the closing equation `E`. -/
noncomputable def combineSys {m₁ m₂ : ℕ} (S₁ : PolySystem k r₁ m₁) (S₂ : PolySystem k r₂ m₂)
    (E : Poly k (r₁ + r₂ + 1)) : PolySystem k (r₁ + r₂ + 1) (m₁ + m₂ + 1) :=
  Fin.append (Fin.append (fun i => rename (wφ₁ k r₁ r₂) (S₁ i)) (fun j => rename (wφ₂ k r₁ r₂) (S₂ j))) ![E]

theorem combineSys_left₁ {m₁ m₂ : ℕ} (S₁ : PolySystem k r₁ m₁) (S₂ : PolySystem k r₂ m₂)
    (E : Poly k (r₁ + r₂ + 1)) (i : Fin m₁) :
    combineSys S₁ S₂ E (Fin.castAdd 1 (Fin.castAdd m₂ i)) = rename (wφ₁ k r₁ r₂) (S₁ i) := by
  simp [combineSys]

theorem combineSys_left₂ {m₁ m₂ : ℕ} (S₁ : PolySystem k r₁ m₁) (S₂ : PolySystem k r₂ m₂)
    (E : Poly k (r₁ + r₂ + 1)) (j : Fin m₂) :
    combineSys S₁ S₂ E (Fin.castAdd 1 (Fin.natAdd m₁ j)) = rename (wφ₂ k r₁ r₂) (S₂ j) := by
  simp [combineSys]

theorem combineSys_last {m₁ m₂ : ℕ} (S₁ : PolySystem k r₁ m₁) (S₂ : PolySystem k r₂ m₂)
    (E : Poly k (r₁ + r₂ + 1)) (j : Fin 1) :
    combineSys S₁ S₂ E (Fin.natAdd (m₁ + m₂) j) = E := by
  simp [combineSys, Fin.fin_one_eq_zero j]

theorem totalDegree_X_le_two' {σ : Type} (v : σ) : (X v : MvPolynomial σ ℤ).totalDegree ≤ 2 :=
  (totalDegree_X_le_one v).trans (by norm_num)

/-- Degrees of the combined system. -/
theorem combineSys_degree {m₁ m₂ : ℕ} (S₁ : PolySystem k r₁ m₁) (S₂ : PolySystem k r₂ m₂)
    (E : Poly k (r₁ + r₂ + 1)) (h₁ : ∀ i, (S₁ i).totalDegree ≤ 2) (h₂ : ∀ j, (S₂ j).totalDegree ≤ 2)
    (hE : E.totalDegree ≤ 2) : ∀ i, (combineSys S₁ S₂ E i).totalDegree ≤ 2 := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [combineSys_left₁]; exact (totalDegree_rename_le _ _).trans (h₁ j)
    · rw [combineSys_left₂]; exact (totalDegree_rename_le _ _).trans (h₂ j)
  · rw [combineSys_last]; exact hE

/-- Solutions of the combined system restrict to solutions of the blocks. -/
theorem combineSys_sol₁ {m₁ m₂ : ℕ} (S₁ : PolySystem k r₁ m₁) (S₂ : PolySystem k r₂ m₂)
    (E : Poly k (r₁ + r₂ + 1)) (a : Fin k → ℤ) (y : Fin (r₁ + r₂ + 1) → ℤ)
    (hy : ∀ i, evalAtZZ (combineSys S₁ S₂ E i) a y = 0) :
    ∀ i, evalAtZZ (S₁ i) a (fun t => y (wIdx₁ r₁ r₂ t)) = 0 := by
  intro i
  have := hy (Fin.castAdd 1 (Fin.castAdd m₂ i))
  rwa [combineSys_left₁, evalAtZZ_rename_wφ₁] at this

theorem combineSys_sol₂ {m₁ m₂ : ℕ} (S₁ : PolySystem k r₁ m₁) (S₂ : PolySystem k r₂ m₂)
    (E : Poly k (r₁ + r₂ + 1)) (a : Fin k → ℤ) (y : Fin (r₁ + r₂ + 1) → ℤ)
    (hy : ∀ i, evalAtZZ (combineSys S₁ S₂ E i) a y = 0) :
    ∀ j, evalAtZZ (S₂ j) a (fun t => y (wIdx₂ r₁ r₂ t)) = 0 := by
  intro j
  have := hy (Fin.castAdd 1 (Fin.natAdd m₁ j))
  rwa [combineSys_left₂, evalAtZZ_rename_wφ₂] at this

theorem combineSys_solE {m₁ m₂ : ℕ} (S₁ : PolySystem k r₁ m₁) (S₂ : PolySystem k r₂ m₂)
    (E : Poly k (r₁ + r₂ + 1)) (a : Fin k → ℤ) (y : Fin (r₁ + r₂ + 1) → ℤ)
    (hy : ∀ i, evalAtZZ (combineSys S₁ S₂ E i) a y = 0) : evalAtZZ E a y = 0 := by
  have := hy (Fin.natAdd (m₁ + m₂) 0)
  rwa [combineSys_last] at this

/-- Block solutions plus a value satisfying `E` give a solution of the combined system. -/
theorem combineSys_of_blocks {m₁ m₂ : ℕ} (S₁ : PolySystem k r₁ m₁) (S₂ : PolySystem k r₂ m₂)
    (E : Poly k (r₁ + r₂ + 1)) (a : Fin k → ℤ) (y₁ : Fin r₁ → ℤ) (y₂ : Fin r₂ → ℤ) (c : ℤ)
    (h₁ : ∀ i, evalAtZZ (S₁ i) a y₁ = 0) (h₂ : ∀ j, evalAtZZ (S₂ j) a y₂ = 0)
    (hE : evalAtZZ E a (wvec r₁ r₂ y₁ y₂ c) = 0) :
    ∀ i, evalAtZZ (combineSys S₁ S₂ E i) a (wvec r₁ r₂ y₁ y₂ c) = 0 := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [combineSys_left₁, evalAtZZ_rename_wφ₁]
      simpa using h₁ j
    · rw [combineSys_left₂, evalAtZZ_rename_wφ₂]
      simpa using h₂ j
  · rw [combineSys_last]; exact hE

end Combine

/-! ### The three induction steps -/

theorem skolemComputable_C {k : ℕ} (c : ℤ) : SkolemComputable (C c : MvPolynomial (Fin k) ℤ) := by
  refine ⟨1, 1, ![X (Sum.inr 0) - C c], 0, ?_, ?_, ?_⟩
  · intro i
    rw [Fin.fin_one_eq_zero i]
    show (X (Sum.inr 0) - C c : Poly k 1).totalDegree ≤ 2
    exact (totalDegree_sub _ _).trans (max_le (totalDegree_X_le_two' _) (by rw [totalDegree_C]; omega))
  · intro a y hy
    have := hy 0
    simp [evalAtZZ] at this
    rw [eval_C]
    exact sub_eq_zero.mp this
  · intro a
    refine ⟨fun _ => c, fun i => ?_⟩
    rw [Fin.fin_one_eq_zero i]
    simp [evalAtZZ]

theorem skolemComputable_add {k : ℕ} {P Q : MvPolynomial (Fin k) ℤ}
    (hP : SkolemComputable P) (hQ : SkolemComputable Q) : SkolemComputable (P + Q) := by
  obtain ⟨r₁, m₁, S₁, w₁, hd₁, hf₁, hs₁⟩ := hP
  obtain ⟨r₂, m₂, S₂, w₂, hd₂, hf₂, hs₂⟩ := hQ
  let E : Poly k (r₁ + r₂ + 1) :=
    X (Sum.inr (wIdxNew r₁ r₂)) - X (Sum.inr (wIdx₁ r₁ r₂ w₁)) - X (Sum.inr (wIdx₂ r₁ r₂ w₂))
  have hEeval : ∀ (a : Fin k → ℤ) (y : Fin (r₁ + r₂ + 1) → ℤ),
      evalAtZZ E a y = y (wIdxNew r₁ r₂) - y (wIdx₁ r₁ r₂ w₁) - y (wIdx₂ r₁ r₂ w₂) := by
    intro a y; simp [E, evalAtZZ]
  refine ⟨r₁ + r₂ + 1, m₁ + m₂ + 1, combineSys S₁ S₂ E, wIdxNew r₁ r₂, ?_, ?_, ?_⟩
  · refine combineSys_degree S₁ S₂ E hd₁ hd₂ ?_
    exact (totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans
      (max_le (totalDegree_X_le_two' _) (totalDegree_X_le_two' _))) (totalDegree_X_le_two' _))
  · intro a y hy
    have h1 := hf₁ a _ (combineSys_sol₁ S₁ S₂ E a y hy)
    have h2 := hf₂ a _ (combineSys_sol₂ S₁ S₂ E a y hy)
    have hE := combineSys_solE S₁ S₂ E a y hy
    rw [hEeval] at hE
    rw [map_add, ← h1, ← h2]
    linarith
  · intro a
    obtain ⟨y₁, hy₁⟩ := hs₁ a
    obtain ⟨y₂, hy₂⟩ := hs₂ a
    refine ⟨wvec r₁ r₂ y₁ y₂ (y₁ w₁ + y₂ w₂), combineSys_of_blocks S₁ S₂ E a y₁ y₂ _ hy₁ hy₂ ?_⟩
    rw [hEeval]
    simp

theorem skolemComputable_mul_X {k : ℕ} {P : MvPolynomial (Fin k) ℤ} (n : Fin k)
    (hP : SkolemComputable P) : SkolemComputable (P * X n) := by
  obtain ⟨r₁, m₁, S₁, w₁, hd₁, hf₁, hs₁⟩ := hP
  let S₂ : PolySystem k 0 0 := Fin.elim0
  let E : Poly k (r₁ + 0 + 1) :=
    X (Sum.inr (wIdxNew r₁ 0)) - X (Sum.inr (wIdx₁ r₁ 0 w₁)) * X (Sum.inl n)
  have hEeval : ∀ (a : Fin k → ℤ) (y : Fin (r₁ + 0 + 1) → ℤ),
      evalAtZZ E a y = y (wIdxNew r₁ 0) - y (wIdx₁ r₁ 0 w₁) * a n := by
    intro a y; simp [E, evalAtZZ]
  refine ⟨r₁ + 0 + 1, m₁ + 0 + 1, combineSys S₁ S₂ E, wIdxNew r₁ 0, ?_, ?_, ?_⟩
  · refine combineSys_degree S₁ S₂ E hd₁ (fun j => j.elim0) ?_
    exact (totalDegree_sub _ _).trans (max_le (totalDegree_X_le_two' _) (totalDegree_XX_le_two _ _))
  · intro a y hy
    have h1 := hf₁ a _ (combineSys_sol₁ S₁ S₂ E a y hy)
    have hE := combineSys_solE S₁ S₂ E a y hy
    rw [hEeval] at hE
    rw [map_mul, eval_X, ← h1]
    linarith
  · intro a
    obtain ⟨y₁, hy₁⟩ := hs₁ a
    refine ⟨wvec r₁ 0 y₁ Fin.elim0 (y₁ w₁ * a n),
      combineSys_of_blocks S₁ S₂ E a y₁ Fin.elim0 _ hy₁ (fun j => j.elim0) ?_⟩
    rw [hEeval]
    simp

/-- Skolem's degree reduction: every integer polynomial is computed by a quadratic system. -/
theorem skolemComputable_all {k : ℕ} (P : MvPolynomial (Fin k) ℤ) : SkolemComputable P := by
  induction P using MvPolynomial.induction_on with
  | C c => exact skolemComputable_C c
  | add p q hp hq => exact skolemComputable_add hp hq
  | mul_X p n hp => exact skolemComputable_mul_X n hp

/-! ### From a Diophantine definition to a pp-quadratic one -/

section Dioph

variable (k r₀ r : ℕ)

/-- The last `r₀` inputs become the first `r₀` witnesses; the Skolem witnesses follow. -/
def dψ : Fin (k + r₀) ⊕ Fin r → Fin k ⊕ Fin (r₀ + r)
  | Sum.inl v => Fin.addCases (motive := fun _ => Fin k ⊕ Fin (r₀ + r))
      (fun i => Sum.inl i) (fun j => Sum.inr (Fin.castAdd r j)) v
  | Sum.inr t => Sum.inr (Fin.natAdd r₀ t)

variable {k r₀ r}

theorem evalAtZZ_rename_dψ (Q : Poly (k + r₀) r) (a : Fin k → ℤ) (y : Fin (r₀ + r) → ℤ) :
    evalAtZZ (rename (dψ k r₀ r) Q) a y
      = evalAtZZ Q (Fin.append a (fun j => y (Fin.castAdd r j))) (fun t => y (Fin.natAdd r₀ t)) := by
  apply evalAtZZ_rename_eq
  intro v
  rcases v with v | t
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) v
    · simp [dψ]
    · simp [dψ]
  · simp [dψ]

theorem eval_append_rename_finSumFinEquiv (P : Poly k r₀) (a : Fin k → ℤ) (u : Fin r₀ → ℤ) :
    eval (Fin.append a u) (rename finSumFinEquiv P) = evalAtZZ P a u := by
  unfold evalAtZZ
  rw [eval_rename]
  refine congrArg (fun h => (eval h) P) ?_
  funext v
  rcases v with i | j <;> simp

end Dioph

/-- `PP_d ⊆ Dioph` (sum of squares). -/
theorem withinDiophZZ_of_withinPPZZ {k d : ℕ} {A : Set (Fin k → ℤ)} (h : WithinPPZZ d A) :
    WithinDiophZZ A := by
  obtain ⟨r, P, _, hrep⟩ := withinSingleEquationZZ_double_of_withinPPZZ h
  exact ⟨r, P, hrep⟩

/-- `Dioph ⊆ PP₂` (Skolem reduction). -/
theorem withinPPZZ_two_of_withinDiophZZ {k : ℕ} {A : Set (Fin k → ℤ)} (h : WithinDiophZZ A) :
    WithinPPZZ 2 A := by
  classical
  obtain ⟨r₀, P, hrep⟩ := h
  obtain ⟨r, m, S, w, hd, hf, hs⟩ :=
    skolemComputable_all (rename finSumFinEquiv P : MvPolynomial (Fin (k + r₀)) ℤ)
  refine ⟨r₀ + r, m + 1,
    Fin.append (fun i => rename (dψ k r₀ r) (S i)) ![X (Sum.inr (Fin.natAdd r₀ w))], ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact (totalDegree_rename_le _ _).trans (hd j)
    · rw [Fin.append_right, Fin.fin_one_eq_zero j, Matrix.cons_val_fin_one]
      exact totalDegree_X_le_two' _
  · intro a
    rw [hrep a]
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨y₀, hy₀⟩ := hs (Fin.append a u)
      refine ⟨Fin.append u y₀, ?_⟩
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left, evalAtZZ_rename_dψ]
        simpa using hy₀ j
      · rw [Fin.append_right, Fin.fin_one_eq_zero j, Matrix.cons_val_fin_one]
        simp only [evalAtZZ, eval_X, Sum.elim_inr, Fin.append_right]
        rw [hf (Fin.append a u) y₀ hy₀, eval_append_rename_finSumFinEquiv, hu]
    · rintro ⟨y, hy⟩
      refine ⟨fun j => y (Fin.castAdd r j), ?_⟩
      have h1 : ∀ i, evalAtZZ (S i) (Fin.append a fun j => y (Fin.castAdd r j))
          (fun t => y (Fin.natAdd r₀ t)) = 0 := by
        intro i
        have := hy (Fin.castAdd 1 i)
        rwa [Fin.append_left, evalAtZZ_rename_dψ] at this
      have hE := hy (Fin.natAdd m 0)
      rw [Fin.append_right, Matrix.cons_val_fin_one] at hE
      simp only [evalAtZZ, eval_X, Sum.elim_inr] at hE
      have := hf _ _ h1
      rw [eval_append_rename_finSumFinEquiv] at this
      rw [← this]
      exact hE

/-- The classical phase transition: `PP₂(k) = Dioph(k)` relation by relation … -/
theorem withinPPZZ_two_iff_withinDiophZZ {k : ℕ} (A : Set (Fin k → ℤ)) :
    WithinPPZZ 2 A ↔ WithinDiophZZ A :=
  ⟨withinDiophZZ_of_withinPPZZ, withinPPZZ_two_of_withinDiophZZ⟩

/-- … and as fragments. -/
theorem ppFragmentZZ_two_eq_diophFragmentZZ (k : ℕ) : PPFragmentZZ 2 k = DiophFragmentZZ k :=
  Set.ext fun A => withinPPZZ_two_iff_withinDiophZZ A

end DiophCompression

#print axioms DiophCompression.skolemComputable_all
#print axioms DiophCompression.withinDiophZZ_of_withinPPZZ
#print axioms DiophCompression.withinPPZZ_two_of_withinDiophZZ
#print axioms DiophCompression.withinPPZZ_two_iff_withinDiophZZ
#print axioms DiophCompression.ppFragmentZZ_two_eq_diophFragmentZZ
