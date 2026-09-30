/-
  frozen_statements/OneSortedFragments_STATEMENTS.lean — APAL r20 Gates 1+3 (session 22, 2026-08-31, claude.ai direct).
  GPT r19 reply-1 §1 / §10 Gates 1,3: the one-sorted relation classes SE_d(k) (one equation, any number of
  ℤ-witnesses) and PP_d(k) (finite conjunction), their Iff.rfl audit surface, the links to AtomGraphZZ/PPGraphZZ,
  and the headline chain  SE_2(k) ⊊ PP_2(k) ⊆ SE_4(k)  for every relation arity k ≥ 4 (= n+1 inputs n ≥ 3).
  Strictness at k ≤ 3 is NOT claimed (open cell, same as AtomGraphZZ(2,2)). Statements only; sorry bodies.
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
      ∀ a, a ∈ A ↔ ∃ y : Fin r → ℤ, evalAtZZ P a y = 0 := by sorry

theorem withinPPZZ_iff {k : ℕ} (d : ℕ) (A : Set (Fin k → ℤ)) :
    WithinPPZZ d A ↔ ∃ r m, ∃ S : PolySystem k r m, (∀ i, (S i).totalDegree ≤ d) ∧
      ∀ a, a ∈ A ↔ ∃ y : Fin r → ℤ, ∀ i, evalAtZZ (S i) a y = 0 := by sorry

theorem mem_singleEqFragmentZZ {d k : ℕ} (A : Set (Fin k → ℤ)) :
    A ∈ SingleEqFragmentZZ d k ↔ WithinSingleEquationZZ d A := by sorry

theorem mem_ppFragmentZZ {d k : ℕ} (A : Set (Fin k → ℤ)) :
    A ∈ PPFragmentZZ d k ↔ WithinPPZZ d A := by sorry

theorem atomGraphZZ_iff_within (d n : ℕ) :
    AtomGraphZZ d n ↔ ∃ e : (Fin n → ℤ) → ℤ, Function.Injective e ∧
      WithinSingleEquationZZ d (graphZZ e) := by sorry

theorem ppGraphZZ_iff_within (d n : ℕ) :
    PPGraphZZ d n ↔ ∃ e : (Fin n → ℤ) → ℤ, Function.Injective e ∧ WithinPPZZ d (graphZZ e) := by sorry

/-! ### Inclusions -/

/-- `SE_d ⊆ PP_d`: one equation is a one-term conjunction. -/
theorem withinPPZZ_of_withinSingleEquationZZ {k d : ℕ} {A : Set (Fin k → ℤ)}
    (h : WithinSingleEquationZZ d A) : WithinPPZZ d A := by sorry

theorem singleEqFragmentZZ_subset_ppFragmentZZ (d k : ℕ) :
    SingleEqFragmentZZ d k ⊆ PPFragmentZZ d k := by sorry

theorem evalAtZZ_sum_sq {k r m : ℕ} (S : PolySystem k r m) (a : Fin k → ℤ) (y : Fin r → ℤ) :
    evalAtZZ (∑ i, (S i) ^ 2) a y = ∑ i, (evalAtZZ (S i) a y) ^ 2 := by sorry

/-- `PP_d ⊆ SE_{2d}` over ℤ: sum of squares. -/
theorem withinSingleEquationZZ_double_of_withinPPZZ {k d : ℕ} {A : Set (Fin k → ℤ)}
    (h : WithinPPZZ d A) : WithinSingleEquationZZ (2 * d) A := by sorry

theorem ppZZ_degree_two_subset_singleEquationZZ_degree_four {k : ℕ} {A : Set (Fin k → ℤ)}
    (h : WithinPPZZ 2 A) : WithinSingleEquationZZ 4 A := by sorry

theorem ppFragmentZZ_two_subset_singleEqFragmentZZ_four (k : ℕ) :
    PPFragmentZZ 2 k ⊆ SingleEqFragmentZZ 4 k := by sorry

/-! ### Strictness at every arity n ≥ 3 (relation arity k = n+1 ≥ 4) -/

theorem graphZZ_intTupleCode_withinPPZZ (n : ℕ) : WithinPPZZ 2 (graphZZ (@intTupleCode n)) := by sorry

theorem graphZZ_not_withinSingleEquationZZ_two {n : ℕ} (hn : 3 ≤ n) (e : (Fin n → ℤ) → ℤ)
    (he : Function.Injective e) : ¬ WithinSingleEquationZZ 2 (graphZZ e) := by sorry

/-- For every n ≥ 3 the graph of the injection `intTupleCode : ℤⁿ → ℤ` lies in `PP_2(n+1) \ SE_2(n+1)`. -/
theorem pp_not_single_quadratic_at_arity {n : ℕ} (hn : 3 ≤ n) :
    ∃ A : Set (Fin (n + 1) → ℤ), WithinPPZZ 2 A ∧ ¬ WithinSingleEquationZZ 2 A := by sorry

theorem quadratic_fragment_strict_at_arity {k : ℕ} (hk : 4 ≤ k) :
    SingleEqFragmentZZ 2 k ⊂ PPFragmentZZ 2 k := by sorry

/-- Headline: `SE_2(k) ⊊ PP_2(k) ⊆ SE_4(k)` for every relation arity k ≥ 4. -/
theorem quadratic_fragment_chain {k : ℕ} (hk : 4 ≤ k) :
    SingleEqFragmentZZ 2 k ⊂ PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k ⊆ SingleEqFragmentZZ 4 k := by sorry

end DiophCompression
