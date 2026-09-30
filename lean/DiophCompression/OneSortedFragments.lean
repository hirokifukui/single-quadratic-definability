/-
  DiophCompression/OneSortedFragments.lean — APAL r20 Gates 1+3 (session 22, 2026-08-31, claude.ai direct).
  GPT r19 reply-1 §1 / §10 Gates 1,3: the one-sorted relation classes SE_d(k) (one equation, any number of
  ℤ-witnesses) and PP_d(k) (finite conjunction), their Iff.rfl audit surface, the links to AtomGraphZZ/PPGraphZZ,
  and the headline chain  SE_2(k) ⊊ PP_2(k) ⊆ SE_4(k)  for every relation arity k ≥ 4 (= n+1 inputs n ≥ 3).
  Strictness at k ≤ 3 is NOT claimed (open cell, same as AtomGraphZZ(2,2)). Statements frozen in frozen_statements/OneSortedFragments_STATEMENTS.lean (md5 5d5843ca).
-/
import DiophCompression.OneSortedPPCoding

namespace DiophCompression

open MvPolynomial MPUP

/-! ### The fragments as classes of relations on ℤᵏ -/

/-- `SE_d(k)`: `A ⊆ ℤᵏ` is defined by ONE equation of total degree ≤ d with finitely many ℤ-witnesses. -/
def WithinSingleEquationZZ {k : ℕ} (d : ℕ) (A : Set (Fin k → ℤ)) : Prop :=
  ∃ r, ∃ P : Poly k r, P.totalDegree ≤ d ∧ RepresentsZZ P A

/-- `PP_d(k)`: `A ⊆ ℤᵏ` is defined by a finite conjunction of equations of total degree ≤ d with
    finitely many ℤ-witnesses. -/
def WithinPPZZ {k : ℕ} (d : ℕ) (A : Set (Fin k → ℤ)) : Prop :=
  ∃ r m, ∃ S : PolySystem k r m, (∀ i, (S i).totalDegree ≤ d) ∧ SystemRepresentsZZ S A

/-- The single-equation fragment of degree ≤ d at relation arity k, as a set of relations. -/
def SingleEqFragmentZZ (d k : ℕ) : Set (Set (Fin k → ℤ)) := {A | WithinSingleEquationZZ d A}

/-- The primitive-positive fragment of degree ≤ d at relation arity k, as a set of relations. -/
def PPFragmentZZ (d k : ℕ) : Set (Set (Fin k → ℤ)) := {A | WithinPPZZ d A}

/-! ### Characterizations (definitional audit surface) -/

theorem withinSingleEquationZZ_iff {k : ℕ} (d : ℕ) (A : Set (Fin k → ℤ)) :
    WithinSingleEquationZZ d A ↔ ∃ r, ∃ P : Poly k r, P.totalDegree ≤ d ∧
      ∀ a, a ∈ A ↔ ∃ y : Fin r → ℤ, evalAtZZ P a y = 0 := Iff.rfl

theorem withinPPZZ_iff {k : ℕ} (d : ℕ) (A : Set (Fin k → ℤ)) :
    WithinPPZZ d A ↔ ∃ r m, ∃ S : PolySystem k r m, (∀ i, (S i).totalDegree ≤ d) ∧
      ∀ a, a ∈ A ↔ ∃ y : Fin r → ℤ, ∀ i, evalAtZZ (S i) a y = 0 := Iff.rfl

theorem mem_singleEqFragmentZZ {d k : ℕ} (A : Set (Fin k → ℤ)) :
    A ∈ SingleEqFragmentZZ d k ↔ WithinSingleEquationZZ d A := Iff.rfl

theorem mem_ppFragmentZZ {d k : ℕ} (A : Set (Fin k → ℤ)) :
    A ∈ PPFragmentZZ d k ↔ WithinPPZZ d A := Iff.rfl

theorem atomGraphZZ_iff_within (d n : ℕ) :
    AtomGraphZZ d n ↔ ∃ e : (Fin n → ℤ) → ℤ, Function.Injective e ∧
      WithinSingleEquationZZ d (graphZZ e) := by
  constructor
  · rintro ⟨r, e, he, P, hP, hrep⟩
    exact ⟨e, he, r, P, hP, hrep⟩
  · rintro ⟨e, he, r, P, hP, hrep⟩
    exact ⟨r, e, he, P, hP, hrep⟩

theorem ppGraphZZ_iff_within (d n : ℕ) :
    PPGraphZZ d n ↔ ∃ e : (Fin n → ℤ) → ℤ, Function.Injective e ∧ WithinPPZZ d (graphZZ e) := by
  constructor
  · rintro ⟨r, m, e, he, S, hS, hrep⟩
    exact ⟨e, he, r, m, S, hS, hrep⟩
  · rintro ⟨e, he, r, m, S, hS, hrep⟩
    exact ⟨r, m, e, he, S, hS, hrep⟩

/-! ### Inclusions -/

/-- `SE_d ⊆ PP_d`: one equation is a one-term conjunction. -/
theorem withinPPZZ_of_withinSingleEquationZZ {k d : ℕ} {A : Set (Fin k → ℤ)}
    (h : WithinSingleEquationZZ d A) : WithinPPZZ d A := by
  obtain ⟨r, P, hP, hrep⟩ := h
  refine ⟨r, 1, ![P], fun i => ?_, fun a => ?_⟩
  · rw [Fin.eq_zero i]; exact hP
  · rw [hrep a]
    exact exists_congr fun y => by simp only [Fin.forall_fin_one, Matrix.cons_val_zero]

theorem singleEqFragmentZZ_subset_ppFragmentZZ (d k : ℕ) :
    SingleEqFragmentZZ d k ⊆ PPFragmentZZ d k := fun _ h => withinPPZZ_of_withinSingleEquationZZ h

theorem evalAtZZ_sum_sq {k r m : ℕ} (S : PolySystem k r m) (a : Fin k → ℤ) (y : Fin r → ℤ) :
    evalAtZZ (∑ i, (S i) ^ 2) a y = ∑ i, (evalAtZZ (S i) a y) ^ 2 := by
  unfold evalAtZZ
  simp only [map_sum, map_pow]

/-- `PP_d ⊆ SE_{2d}` over ℤ: sum of squares. -/
theorem withinSingleEquationZZ_double_of_withinPPZZ {k d : ℕ} {A : Set (Fin k → ℤ)}
    (h : WithinPPZZ d A) : WithinSingleEquationZZ (2 * d) A := by
  obtain ⟨r, m, S, hdeg, hrep⟩ := h
  refine ⟨r, ∑ i, (S i) ^ 2, ?_, fun a => ?_⟩
  · refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun i _ => ?_)
    exact le_trans (totalDegree_pow _ _) (Nat.mul_le_mul_left 2 (hdeg i))
  · rw [hrep a]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [evalAtZZ_sum_sq]
      exact Finset.sum_eq_zero fun i _ => by rw [hy i]; ring
    · rintro ⟨y, hy⟩
      refine ⟨y, fun i => ?_⟩
      rw [evalAtZZ_sum_sq, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at hy
      exact pow_eq_zero_iff (two_ne_zero) |>.mp (hy i (Finset.mem_univ i))

theorem ppZZ_degree_two_subset_singleEquationZZ_degree_four {k : ℕ} {A : Set (Fin k → ℤ)}
    (h : WithinPPZZ 2 A) : WithinSingleEquationZZ 4 A := withinSingleEquationZZ_double_of_withinPPZZ h

theorem ppFragmentZZ_two_subset_singleEqFragmentZZ_four (k : ℕ) :
    PPFragmentZZ 2 k ⊆ SingleEqFragmentZZ 4 k := fun _ h => ppZZ_degree_two_subset_singleEquationZZ_degree_four h

/-! ### Strictness at every arity n ≥ 3 (relation arity k = n+1 ≥ 4) -/

theorem graphZZ_intTupleCode_withinPPZZ (n : ℕ) : WithinPPZZ 2 (graphZZ (@intTupleCode n)) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    refine ⟨0, 1, ![X (Sum.inl 0)], ?_, ?_⟩
    · intro i
      rw [Fin.eq_zero i]
      simp only [Matrix.cons_val_zero]
      exact (totalDegree_X_le_one _).trans (by norm_num)
    · intro v
      have hg : v ∈ graphZZ (@intTupleCode 0) ↔ v 0 = 0 := by
        show v (Fin.last 0) = intTupleCode (Fin.init v) ↔ _
        simp [intTupleCode]
      rw [hg]
      constructor
      · intro hv
        refine ⟨fun t => t.elim0, ?_⟩
        intro i
        rw [Fin.eq_zero i]
        simp only [Matrix.cons_val_zero, evalAtZZ, eval_X, Sum.elim_inl]
        exact hv
      · rintro ⟨y, hy⟩
        have := hy 0
        simp only [Matrix.cons_val_zero, evalAtZZ, eval_X, Sum.elim_inl] at this
        exact this
  · obtain ⟨r, m, S, _, _, hd, hS⟩ := intTupleCode_system n hpos
    exact ⟨r, m, S, hd, hS⟩

theorem graphZZ_not_withinSingleEquationZZ_two {n : ℕ} (hn : 3 ≤ n) (e : (Fin n → ℤ) → ℤ)
    (he : Function.Injective e) : ¬ WithinSingleEquationZZ 2 (graphZZ e) := by
  rintro ⟨r, P, hP, hrep⟩
  have h2 : AtomGraphZZ 2 n := ⟨r, e, he, P, hP, hrep⟩
  have := atomGraphZZ_degree_two_le_two n h2
  omega

/-- For every n ≥ 3 the graph of the injection `intTupleCode : ℤⁿ → ℤ` lies in `PP_2(n+1) \ SE_2(n+1)`. -/
theorem pp_not_single_quadratic_at_arity {n : ℕ} (hn : 3 ≤ n) :
    ∃ A : Set (Fin (n + 1) → ℤ), WithinPPZZ 2 A ∧ ¬ WithinSingleEquationZZ 2 A := ⟨graphZZ (@intTupleCode n), graphZZ_intTupleCode_withinPPZZ n,
    graphZZ_not_withinSingleEquationZZ_two hn _ (intTupleCode_injective n)⟩

theorem quadratic_fragment_strict_at_arity {k : ℕ} (hk : 4 ≤ k) :
    SingleEqFragmentZZ 2 k ⊂ PPFragmentZZ 2 k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Set.ssubset_def]
  refine ⟨singleEqFragmentZZ_subset_ppFragmentZZ 2 _, fun hsub => ?_⟩
  obtain ⟨A, h1, h2⟩ := pp_not_single_quadratic_at_arity (n := n) (by omega)
  exact h2 (hsub h1)

/-- Headline: `SE_2(k) ⊊ PP_2(k) ⊆ SE_4(k)` for every relation arity k ≥ 4. -/
theorem quadratic_fragment_chain {k : ℕ} (hk : 4 ≤ k) :
    SingleEqFragmentZZ 2 k ⊂ PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k ⊆ SingleEqFragmentZZ 4 k := ⟨quadratic_fragment_strict_at_arity hk, ppFragmentZZ_two_subset_singleEqFragmentZZ_four k⟩

end DiophCompression

#print axioms DiophCompression.withinSingleEquationZZ_iff
#print axioms DiophCompression.withinPPZZ_iff
#print axioms DiophCompression.atomGraphZZ_iff_within
#print axioms DiophCompression.ppGraphZZ_iff_within
#print axioms DiophCompression.singleEqFragmentZZ_subset_ppFragmentZZ
#print axioms DiophCompression.ppZZ_degree_two_subset_singleEquationZZ_degree_four
#print axioms DiophCompression.pp_not_single_quadratic_at_arity
#print axioms DiophCompression.quadratic_fragment_strict_at_arity
#print axioms DiophCompression.quadratic_fragment_chain
