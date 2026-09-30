/-
  frozen_statements/ComputabilityFragments_STATEMENTS.lean — Gate 12 statement freeze (session 24, 2026-08-31).
  GPT r21 必須D (relation computability hierarchy) in mathlib's own vocabulary: `ComputablePred` (REC), `REPred` (RE),
  with `Fin k → ℤ` Primcodable via `Primcodable.finArrow` / `Primcodable.ofDenumerable ℤ`; ℤ arithmetic and integer
  polynomial evaluation made primitive recursive in DiophCompression/IntPrimrec.lean.
  External classical theorems enter ONLY as explicit Prop-valued hypotheses (never as `axiom`):
    * `QuadraticSolvabilityDecidableZZ` — Grunewald–Segal 1981 (Siegel 1972);
    * `DPRM_ZZ` — Davis–Putnam–Robinson–Matiyasevich over ℤ.
  Unconditional: SE_d ⊆ RE, PP_2 ⊆ RE, REC ⊆ RE, the x³ witness in REC \ SE_2. Conditional items name their
  hypothesis. The total-function hierarchy (必須E) is a separate draft (drafts/ComputableFunctions_STATEMENTS_draft.lean).
  Bodies are `sorry`.
-/
import DiophCompression.FragmentLattice
import DiophCompression.MultivariatePolynomialGraphs
import DiophCompression.IntPrimrec
import Mathlib.Computability.RE
import Mathlib.Computability.Halting

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Definitions -/

/-- REC(k): the recursive (decidable) relations on ℤᵏ. -/
def RecFragmentZZ (k : ℕ) : Set (Set (Fin k → ℤ)) := {A | ComputablePred fun a => a ∈ A}

/-- RE(k): the recursively enumerable relations on ℤᵏ. -/
def REFragmentZZ (k : ℕ) : Set (Set (Fin k → ℤ)) := {A | REPred fun a => a ∈ A}

/-- External hypothesis (Grunewald–Segal): for every fixed degree-≤2 integer polynomial, solvability in ℤ
    is a decidable predicate of the parameters. -/
def QuadraticSolvabilityDecidableZZ : Prop :=
  ∀ (k r : ℕ) (P : Poly k r), P.totalDegree ≤ 2 →
    ComputablePred fun a : Fin k → ℤ => ∃ u : Fin r → ℤ, evalAtZZ P a u = 0

/-- External hypothesis (DPRM over ℤ): every r.e. relation on ℤᵏ is Diophantine. -/
def DPRM_ZZ : Prop := ∀ (k : ℕ) (A : Set (Fin k → ℤ)), REPred (fun a => a ∈ A) → WithinDiophZZ A

/-- Boolean solution test `P(a,y) = 0`. -/
noncomputable def solTest {k r : ℕ} (P : Poly k r) (a : Fin k → ℤ) (y : Fin r → ℤ) : Bool :=
  decide (evalAtZZ P a y = 0)

/-- Witness checker: decode `n` as a witness vector and test the equation (search primitive). -/
noncomputable def solCheck {k r : ℕ} (P : Poly k r) (a : Fin k → ℤ) (n : ℕ) : Bool :=
  match @Encodable.decode (Fin r → ℤ) Primcodable.toEncodable n with
  | none => false
  | some y => solTest P a y

/-! ### Theorems -/

/-- The solution map `(a,u) ↦ P(a,u)` is primitive recursive. -/
theorem primrec_evalAtZZ {k r : ℕ} (P : Poly k r) :
    Primrec fun au : (Fin k → ℤ) × (Fin r → ℤ) => evalAtZZ P au.1 au.2 := by
  sorry

/-- The solution predicate `P(a,u) = 0` is primitive recursive in the pair `(a,u)`. -/
theorem primrecPred_evalAtZZ_eq_zero {k r : ℕ} (P : Poly k r) :
    PrimrecPred fun au : (Fin k → ℤ) × (Fin r → ℤ) => evalAtZZ P au.1 au.2 = 0 := by
  sorry

theorem primrec₂_solCheck {k r : ℕ} (P : Poly k r) : Primrec₂ (solCheck P) := by
  sorry

theorem exists_solCheck_iff {k r : ℕ} (P : Poly k r) (a : Fin k → ℤ) :
    (∃ y : Fin r → ℤ, evalAtZZ P a y = 0) ↔ ∃ n, solCheck P a n = true := by
  sorry

theorem rePred_exists_solCheck {k r : ℕ} (P : Poly k r) : REPred fun a => ∃ n, solCheck P a n = true := by
  sorry

/-- The graph of `a ↦ a₀^d` is a recursive relation. -/
theorem powerGraphZZ_computablePred (k d : ℕ) : ComputablePred fun v => v ∈ powerGraphZZ k d := by
  sorry

/-- Unconditional: every Diophantine relation is r.e. (search for the witness). -/
theorem dioph_relation_re {k : ℕ} {A : Set (Fin k → ℤ)} (h : WithinDiophZZ A) :
    REPred fun a => a ∈ A := by
  sorry

/-- Unconditional: PP_2(k) ⊆ RE(k) (the degree-two case of `ppRelation_re`). -/
theorem ppQuadratic_relation_re {k : ℕ} {A : Set (Fin k → ℤ)} (h : WithinPPZZ 2 A) :
    REPred fun a => a ∈ A := by
  sorry

/-- Unconditional: PP_d(k) ⊆ RE(k) for every degree bound `d` (Gate 13, A01). -/
theorem ppRelation_re {d k : ℕ} {A : Set (Fin k → ℤ)} (h : WithinPPZZ d A) :
    REPred fun a => a ∈ A := by
  sorry

/-- Unconditional: SE_d(k) ⊆ RE(k) for every degree bound `d` (Gate 13, A01). -/
theorem singleEquation_relation_re {d k : ℕ} {A : Set (Fin k → ℤ)} (h : WithinSingleEquationZZ d A) :
    REPred fun a => a ∈ A := by
  sorry

/-- Unconditional: SE_4(k) ⊆ RE(k). The degree-four case of `singleEquation_relation_re`; this
name is sealed (r29–r34) and is kept. -/
theorem singleQuartic_relation_re {k : ℕ} {A : Set (Fin k → ℤ)} (h : WithinSingleEquationZZ 4 A) :
    REPred fun a => a ∈ A := by
  sorry

/-- Unconditional: REC(k) ⊆ RE(k). -/
theorem recFragmentZZ_subset_reFragmentZZ (k : ℕ) : RecFragmentZZ k ⊆ REFragmentZZ k := by
  sorry

/-- Conditional on Grunewald–Segal: every SE_2 relation is recursive. -/
theorem singleQuadratic_relation_recursive (hGS : QuadraticSolvabilityDecidableZZ) {k : ℕ}
    {A : Set (Fin k → ℤ)} (h : WithinSingleEquationZZ 2 A) : ComputablePred fun a => a ∈ A := by
  sorry

/-- Conditional on Grunewald–Segal: SE_2(k) ⊆ REC(k). -/
theorem singleEqFragmentZZ_two_subset_recFragmentZZ (hGS : QuadraticSolvabilityDecidableZZ) (k : ℕ) :
    SingleEqFragmentZZ 2 k ⊆ RecFragmentZZ k := by
  sorry

/-- Conditional on DPRM: PP_2(k) = RE(k). -/
theorem ppQuadratic_eq_re_of_DPRM (hD : DPRM_ZZ) (k : ℕ) : PPFragmentZZ 2 k = REFragmentZZ k := by
  sorry

/-- Conditional on DPRM: SE_4(k) = RE(k). -/
theorem singleQuartic_eq_re_of_DPRM (hD : DPRM_ZZ) (k : ℕ) : SingleEqFragmentZZ 4 k = REFragmentZZ k := by
  sorry

/-- The phase diagram at arity k ≥ 2 (GS + DPRM): SE_2(k) ⊊ REC(k) ⊆ RE(k) = PP_2(k) = SE_4(k);
    strictness of the first inclusion is the unconditional x³ witness. -/
theorem relation_phase_diagram (hGS : QuadraticSolvabilityDecidableZZ) (hD : DPRM_ZZ) (k : ℕ) :
    SingleEqFragmentZZ 2 (k + 2) ⊂ RecFragmentZZ (k + 2) ∧
      RecFragmentZZ (k + 2) ⊆ REFragmentZZ (k + 2) ∧
      REFragmentZZ (k + 2) = PPFragmentZZ 2 (k + 2) ∧
      PPFragmentZZ 2 (k + 2) = SingleEqFragmentZZ 4 (k + 2) := by
  sorry

