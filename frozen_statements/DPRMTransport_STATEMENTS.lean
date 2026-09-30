/-
  frozen_statements/DPRMTransport_STATEMENTS.lean — APAL Structural Theory Gate 3, 必須B (frozen s26, 2026-09-01). Diophantine over ℕ (evalAtNN / WithinDiophNN), the classical DPRM hypothesis DPRM_NN, r.e. transport through the difference map ℕ^{k+k} → ℤᵏ, the transported single equation (sum of squares: a = p − q, P(p,q,y) = 0, four-square witnesses; 5(2k+s) unknowns), and DPRM_ZZ_of_DPRM_NN.
-/
import DiophCompression.ComputabilityFragments
import DiophCompression.IntPrimrec
import Mathlib.NumberTheory.SumFourSquares

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Diophantine relations over ℕ and the classical DPRM hypothesis -/

/-- Evaluation of an integer polynomial at NATURAL parameters and NATURAL unknowns. -/
noncomputable def evalAtNN {k s : ℕ} (P : Poly k s) (a : Fin k → ℕ) (y : Fin s → ℕ) : ℤ :=
  eval (Sum.elim (fun i => (a i : ℤ)) (fun j => (y j : ℤ))) P

/-- `A ⊆ ℕᵏ` is Diophantine over ℕ: an integer-coefficient polynomial with natural unknowns. -/
def WithinDiophNN {k : ℕ} (A : Set (Fin k → ℕ)) : Prop :=
  ∃ s : ℕ, ∃ P : Poly k s, ∀ a, a ∈ A ↔ ∃ y : Fin s → ℕ, evalAtNN P a y = 0

/-- External hypothesis: the DPRM theorem over ℕ. -/
def DPRM_NN : Prop := ∀ (k : ℕ) (A : Set (Fin k → ℕ)), REPred (fun a => a ∈ A) → WithinDiophNN A

/-! ### The difference map and r.e. transport -/

/-- `b ↦ (b_i − b_{k+i})_i : ℕ^{k+k} → ℤᵏ`. -/
def diffMapZZ (k : ℕ) (b : Fin (k + k) → ℕ) : Fin k → ℤ :=
  fun i => (b (Fin.castAdd k i) : ℤ) - (b (Fin.natAdd k i) : ℤ)

theorem primrec_natCastInt : Primrec fun n : ℕ => (n : ℤ) := by
  sorry

theorem primrec_int_neg : Primrec fun z : ℤ => -z := by
  sorry

theorem primrec₂_int_sub : Primrec₂ ((· - ·) : ℤ → ℤ → ℤ) := by
  sorry

theorem primrec_diffMapZZ (k : ℕ) : Primrec (diffMapZZ k) := by
  sorry

theorem rePred_comp_computable {α β : Type} [Primcodable α] [Primcodable β] {p : β → Prop}
    (hp : REPred p) {f : α → β} (hf : Computable f) : REPred fun a => p (f a) := by
  sorry

/-- r.e. transport: the ℕ-preimage of an r.e. relation on ℤᵏ under the difference map is r.e. -/
theorem rePred_diffPreimage {k : ℕ} (A : Set (Fin k → ℤ)) (hA : REPred fun a => a ∈ A) :
    REPred fun b : Fin (k + k) → ℕ => diffMapZZ k b ∈ A := by
  sorry

/-! ### The transported polynomial -/

/-- Variable type of the transported equation: parameters `Fin k`; unknowns = the ℕ-unknowns
    `T = Fin (k+k) ⊕ Fin s` (p, q, y) and their four-square witnesses `T × Fin 4`. -/
abbrev TransportVars (k s : ℕ) : Type := (Fin (k + k) ⊕ Fin s) ⊕ ((Fin (k + k) ⊕ Fin s) × Fin 4)

/-- Number of integer unknowns of the transported equation: 5(2k + s). -/
def transportWitnessArity (k s : ℕ) : ℕ := Fintype.card (TransportVars k s)

theorem transportWitnessArity_eq (k s : ℕ) : transportWitnessArity k s = 5 * (k + k + s) := by
  sorry

/-- The transported polynomial in `MvPolynomial (Fin k ⊕ TransportVars k s) ℤ`:
    Σᵢ (aᵢ − pᵢ + qᵢ)² + P(p, q, y)² + Σ_t (t − Σₗ w_{t,l}²)². -/
noncomputable def transportPoly (k s : ℕ) (P : Poly (k + k) s) :
    MvPolynomial (Fin k ⊕ TransportVars k s) ℤ :=
  (∑ i : Fin k, (X (Sum.inl i) - X (Sum.inr (Sum.inl (Sum.inl (Fin.castAdd k i))))
      + X (Sum.inr (Sum.inl (Sum.inl (Fin.natAdd k i))))) ^ 2)
  + (rename (fun t => Sum.inr (Sum.inl t)) P) ^ 2
  + ∑ t : Fin (k + k) ⊕ Fin s, (X (Sum.inr (Sum.inl t)) - ∑ l : Fin 4, X (Sum.inr (Sum.inr (t, l))) ^ 2) ^ 2

theorem int_sum_sq_eq_zero_iff {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    ∑ i ∈ s, (f i) ^ 2 = 0 ↔ ∀ i ∈ s, f i = 0 := by
  sorry

/-- Zero set of the transported polynomial, coordinatewise. -/
theorem transportPoly_eval_eq_zero_iff (k s : ℕ) (P : Poly (k + k) s) (a : Fin k → ℤ)
    (w : TransportVars k s → ℤ) :
    eval (Sum.elim a w) (transportPoly k s P) = 0 ↔
      (∀ i, a i = w (Sum.inl (Sum.inl (Fin.castAdd k i))) - w (Sum.inl (Sum.inl (Fin.natAdd k i)))) ∧
      eval (fun t => w (Sum.inl t)) P = 0 ∧
      (∀ t, w (Sum.inl t) = ∑ l : Fin 4, (w (Sum.inr (t, l))) ^ 2) := by
  sorry

/-- Four-square witnesses for every natural number, as a `Fin 4`-indexed family. -/
theorem exists_fourSquares (n : ℕ) : ∃ f : Fin 4 → ℕ, ∑ l : Fin 4, (f l) ^ 2 = n := by
  sorry

/-- 必須B: DPRM over ℕ implies DPRM over ℤ. -/
theorem DPRM_ZZ_of_DPRM_NN (hN : DPRM_NN) : DPRM_ZZ := by
  sorry

/-- Degree of a negated polynomial (helper for the sub bound; mathlib pin has no totalDegree_neg). -/
theorem totalDegree_neg_eq {σ : Type} (p : MvPolynomial σ ℤ) : (-p).totalDegree = p.totalDegree := by
  sorry

theorem totalDegree_sub_le' {σ : Type} (p q : MvPolynomial σ ℤ) :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  sorry

/-- 必須D (Gate 4): total degree of the transported polynomial is at most `max (2·deg P) 4`. -/
theorem transportPoly_totalDegree_le (k s : ℕ) (P : Poly (k + k) s) :
    (transportPoly k s P).totalDegree ≤ max (2 * P.totalDegree) 4 := by
  sorry

/-- 必須D (Gate 4): the resource summary of the transport — witness arity and total degree in one statement. -/
theorem dprmTransport_resource_bound (k s : ℕ) (P : Poly (k + k) s) :
    transportWitnessArity k s = 5 * (k + k + s) ∧
      (transportPoly k s P).totalDegree ≤ max (2 * P.totalDegree) 4 := by
  sorry


/-! ### 必須G (Gate 5): resource bound on the FINAL representation polynomial -/

/-- Renaming never raises the total degree. -/
theorem transportedRepresentation_totalDegree_le {k s : ℕ} {ι : Type} (P : Poly (k + k) s)
    (f : TransportVars k s → ι) :
    (rename (Sum.map (id : Fin k → Fin k) f) (transportPoly k s P)).totalDegree
      ≤ max (2 * P.totalDegree) 4 := by
  sorry

/-- 必須G (Gate 5): arity and degree of the FINAL ℤ-representation of an r.e. set. -/
theorem DPRM_ZZ_resource_bound_final (hN : DPRM_NN) {k : ℕ} (A : Set (Fin k → ℤ))
    (hA : REPred fun a => a ∈ A) :
    ∃ (s : ℕ) (P : Poly (k + k) s) (Q : Poly k (transportWitnessArity k s)),
      (∀ a : Fin k → ℤ, a ∈ A ↔ ∃ z : Fin (transportWitnessArity k s) → ℤ, evalAtZZ Q a z = 0)
      ∧ transportWitnessArity k s = 5 * (k + k + s)
      ∧ Q.totalDegree ≤ max (2 * P.totalDegree) 4 := by
  sorry

end DiophCompression
