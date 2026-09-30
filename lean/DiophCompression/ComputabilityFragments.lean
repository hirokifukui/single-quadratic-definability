/-
  DiophCompression/ComputabilityFragments.lean — APAL Structural Theory Gate 1, kernel item 必須D
  (session 24, 2026-08-31, claude.ai direct, 0 CC).
  Relation computability hierarchy in mathlib vocabulary: unconditional SE_d/PP_2 ⊆ RE (witness search via
  Nat.rfind on a primitive-recursive checker), REC ⊆ RE, the x³ graph in REC \ SE_2; Grunewald–Segal and DPRM
  as explicit Prop hypotheses (never axioms). Statements frozen in frozen_statements/ComputabilityFragments_STATEMENTS.lean.
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
  have h := primrec_eval_of_coords P (fun au : (Fin k → ℤ) × (Fin r → ℤ) => Sum.elim au.1 au.2) (fun i => by
    rcases i with i | i
    · exact Primrec.fin_app.comp Primrec.fst (Primrec.const i)
    · exact Primrec.fin_app.comp Primrec.snd (Primrec.const i))
  exact h

/-- The solution predicate `P(a,u) = 0` is primitive recursive in the pair `(a,u)`. -/
theorem primrecPred_evalAtZZ_eq_zero {k r : ℕ} (P : Poly k r) :
    PrimrecPred fun au : (Fin k → ℤ) × (Fin r → ℤ) => evalAtZZ P au.1 au.2 = 0 := by
  exact Primrec.eq.comp (primrec_evalAtZZ P) (Primrec.const 0)

theorem primrec₂_solCheck {k r : ℕ} (P : Poly k r) : Primrec₂ (solCheck P) := by
  have h := Primrec.option_casesOn (α := (Fin k → ℤ) × ℕ) (β := Fin r → ℤ) (σ := Bool)
    (o := fun p => @Encodable.decode (Fin r → ℤ) Primcodable.toEncodable p.2) (f := fun _ => false)
    (g := fun p y => solTest P p.1 y)
    (Primrec.decode.comp Primrec.snd) (Primrec.const false)
    ((primrecPred_evalAtZZ_eq_zero P).decide.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
  refine h.of_eq ?_
  rintro ⟨a, n⟩
  simp only [solCheck]
  rcases @Encodable.decode (Fin r → ℤ) Primcodable.toEncodable n with _ | y <;> rfl

theorem exists_solCheck_iff {k r : ℕ} (P : Poly k r) (a : Fin k → ℤ) :
    (∃ y : Fin r → ℤ, evalAtZZ P a y = 0) ↔ ∃ n, solCheck P a n = true := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨@Encodable.encode (Fin r → ℤ) Primcodable.toEncodable y, ?_⟩
    simp only [solCheck, Encodable.encodek, solTest, hy, decide_true]
  · rintro ⟨n, hn⟩
    unfold solCheck at hn
    rcases hdec : (@Encodable.decode (Fin r → ℤ) Primcodable.toEncodable n) with _ | y
    · rw [hdec] at hn; simp at hn
    · rw [hdec] at hn
      exact ⟨y, by simpa [solTest] using hn⟩

theorem rePred_exists_solCheck {k r : ℕ} (P : Poly k r) : REPred fun a => ∃ n, solCheck P a n = true := by
  have h : Partrec fun a : Fin k → ℤ => Nat.rfind fun n => (Part.some (solCheck P a n) : Part Bool) :=
    Partrec.rfind (primrec₂_solCheck P).to_comp.partrec
  refine h.dom_re.of_eq fun a => ?_
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨n, hn, _⟩
    exact ⟨n, (Part.mem_some_iff.mp hn).symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, Part.mem_some_iff.mpr hn.symm, fun {_} _ => trivial⟩

/-- The graph of `a ↦ a₀^d` is a recursive relation. -/
theorem powerGraphZZ_computablePred (k d : ℕ) : ComputablePred fun v => v ∈ powerGraphZZ k d := by
  have h : PrimrecPred fun v : Fin (k + 2) → ℤ => v (Fin.last (k + 1)) = (v (Fin.castSucc 0)) ^ d :=
    Primrec.eq.comp (Primrec.fin_app.comp Primrec.id (Primrec.const _))
      ((primrec_int_pow d).comp (Primrec.fin_app.comp Primrec.id (Primrec.const _)))
  exact h.computablePred.of_eq fun v => Iff.rfl

/-- Unconditional: every Diophantine relation is r.e. (search for the witness). -/
theorem dioph_relation_re {k : ℕ} {A : Set (Fin k → ℤ)} (h : WithinDiophZZ A) :
    REPred fun a => a ∈ A := by
  obtain ⟨r, P, hrep⟩ := h
  refine (rePred_exists_solCheck P).of_eq fun a => ?_
  rw [hrep a]
  exact (exists_solCheck_iff P a).symm

/-- Unconditional: PP_2(k) ⊆ RE(k) (the degree-two case of `ppRelation_re`). -/
theorem ppQuadratic_relation_re {k : ℕ} {A : Set (Fin k → ℤ)} (h : WithinPPZZ 2 A) :
    REPred fun a => a ∈ A := by
  exact dioph_relation_re (withinDiophZZ_of_withinPPZZ h)

/-- Unconditional: PP_d(k) ⊆ RE(k) for every degree bound `d` (Gate 13, A01). -/
theorem ppRelation_re {d k : ℕ} {A : Set (Fin k → ℤ)} (h : WithinPPZZ d A) :
    REPred fun a => a ∈ A := by
  exact dioph_relation_re (withinDiophZZ_of_withinPPZZ h)

/-- Unconditional: SE_d(k) ⊆ RE(k) for every degree bound `d` (Gate 13, A01). -/
theorem singleEquation_relation_re {d k : ℕ} {A : Set (Fin k → ℤ)} (h : WithinSingleEquationZZ d A) :
    REPred fun a => a ∈ A := by
  exact dioph_relation_re (withinDiophZZ_of_withinSingleEquationZZ h)

/-- Unconditional: SE_4(k) ⊆ RE(k). The degree-four case of `singleEquation_relation_re`; this
name is sealed (r29–r34) and is kept. -/
theorem singleQuartic_relation_re {k : ℕ} {A : Set (Fin k → ℤ)} (h : WithinSingleEquationZZ 4 A) :
    REPred fun a => a ∈ A := by
  exact singleEquation_relation_re h

/-- Unconditional: REC(k) ⊆ RE(k). -/
theorem recFragmentZZ_subset_reFragmentZZ (k : ℕ) : RecFragmentZZ k ⊆ REFragmentZZ k := by
  intro A hA
  exact ComputablePred.to_re hA

/-- Conditional on Grunewald–Segal: every SE_2 relation is recursive. -/
theorem singleQuadratic_relation_recursive (hGS : QuadraticSolvabilityDecidableZZ) {k : ℕ}
    {A : Set (Fin k → ℤ)} (h : WithinSingleEquationZZ 2 A) : ComputablePred fun a => a ∈ A := by
  obtain ⟨r, P, hdeg, hrep⟩ := h
  exact (hGS k r P hdeg).of_eq fun a => (hrep a).symm

/-- Conditional on Grunewald–Segal: SE_2(k) ⊆ REC(k). -/
theorem singleEqFragmentZZ_two_subset_recFragmentZZ (hGS : QuadraticSolvabilityDecidableZZ) (k : ℕ) :
    SingleEqFragmentZZ 2 k ⊆ RecFragmentZZ k := by
  intro A hA
  exact singleQuadratic_relation_recursive hGS hA

/-- Conditional on DPRM: PP_2(k) = RE(k). -/
theorem ppQuadratic_eq_re_of_DPRM (hD : DPRM_ZZ) (k : ℕ) : PPFragmentZZ 2 k = REFragmentZZ k := by
  ext A
  constructor
  · intro hA
    exact ppQuadratic_relation_re hA
  · intro hA
    exact withinPPZZ_two_of_withinDiophZZ (hD k A hA)

/-- Conditional on DPRM: SE_4(k) = RE(k). -/
theorem singleQuartic_eq_re_of_DPRM (hD : DPRM_ZZ) (k : ℕ) : SingleEqFragmentZZ 4 k = REFragmentZZ k := by
  rw [singleEqFragmentZZ_four_eq_ppFragmentZZ_two, ppQuadratic_eq_re_of_DPRM hD]

/-- The phase diagram at arity k ≥ 2 (GS + DPRM): SE_2(k) ⊊ REC(k) ⊆ RE(k) = PP_2(k) = SE_4(k);
    strictness of the first inclusion is the unconditional x³ witness. -/
theorem relation_phase_diagram (hGS : QuadraticSolvabilityDecidableZZ) (hD : DPRM_ZZ) (k : ℕ) :
    SingleEqFragmentZZ 2 (k + 2) ⊂ RecFragmentZZ (k + 2) ∧
      RecFragmentZZ (k + 2) ⊆ REFragmentZZ (k + 2) ∧
      REFragmentZZ (k + 2) = PPFragmentZZ 2 (k + 2) ∧
      PPFragmentZZ 2 (k + 2) = SingleEqFragmentZZ 4 (k + 2) := by
  refine ⟨?_, recFragmentZZ_subset_reFragmentZZ _, (ppQuadratic_eq_re_of_DPRM hD _).symm,
    (singleEqFragmentZZ_four_eq_ppFragmentZZ_two _).symm⟩
  rw [Set.ssubset_def]
  refine ⟨singleEqFragmentZZ_two_subset_recFragmentZZ hGS _, fun hsub => ?_⟩
  have hmem : powerGraphZZ k 3 ∈ RecFragmentZZ (k + 2) := powerGraphZZ_computablePred k 3
  exact cubic_graph_not_withinSingleEquationZZ k (hsub hmem)

#print axioms DiophCompression.primrec_evalAtZZ
#print axioms DiophCompression.primrecPred_evalAtZZ_eq_zero
#print axioms DiophCompression.primrec₂_solCheck
#print axioms DiophCompression.exists_solCheck_iff
#print axioms DiophCompression.rePred_exists_solCheck
#print axioms DiophCompression.powerGraphZZ_computablePred
#print axioms DiophCompression.dioph_relation_re
#print axioms DiophCompression.ppQuadratic_relation_re
#print axioms DiophCompression.singleQuartic_relation_re
#print axioms DiophCompression.recFragmentZZ_subset_reFragmentZZ
#print axioms DiophCompression.singleQuadratic_relation_recursive
#print axioms DiophCompression.singleEqFragmentZZ_two_subset_recFragmentZZ
#print axioms DiophCompression.ppQuadratic_eq_re_of_DPRM
#print axioms DiophCompression.singleQuartic_eq_re_of_DPRM
#print axioms DiophCompression.relation_phase_diagram
