/-
  frozen_statements/ArityZeroFragments_STATEMENTS.lean — APAL Structural Theory Gate 3, 必須D-1/D-3
  (frozen s26, 2026-09-01). The relation hierarchy at arity 0 collapses (every relation on the singleton
  ℤ^0 is ∅ or univ, both SE_2, REC, RE, PP_2, SE_4 — UNCONDITIONAL), and the phase diagram is indexed by
  arity: unary (code-uniform GS + DPRM) and arity ≥ 2 (per-equation GS + DPRM; the x³ witness).
-/
import DiophCompression.HaltingTransport
import DiophCompression.UnaryDiagonal

namespace DiophCompression

open MvPolynomial MPUP

/-- At arity 0 the parameter space `Fin 0 → ℤ` is a singleton, so a relation is `∅` or `univ`. -/
theorem set_arity_zero_eq_empty_or_univ (A : Set (Fin 0 → ℤ)) : A = ∅ ∨ A = Set.univ := by
  sorry

/-- `∅ ⊆ ℤ^0` is a single equation (`1 = 0`) of any degree bound. -/
theorem empty_withinSingleEquationZZ_arity_zero (d : ℕ) :
    WithinSingleEquationZZ d (∅ : Set (Fin 0 → ℤ)) := by
  sorry

/-- `univ ⊆ ℤ^0` is a single equation (`0 = 0`) of any degree bound. -/
theorem univ_withinSingleEquationZZ_arity_zero (d : ℕ) :
    WithinSingleEquationZZ d (Set.univ : Set (Fin 0 → ℤ)) := by
  sorry

/-- SE_d(0) is everything. -/
theorem singleEqFragmentZZ_arity_zero (d : ℕ) : SingleEqFragmentZZ d 0 = Set.univ := by
  sorry

/-- REC(0) is everything. -/
theorem recFragmentZZ_arity_zero : RecFragmentZZ 0 = Set.univ := by
  sorry

/-- RE(0) is everything. -/
theorem reFragmentZZ_arity_zero : REFragmentZZ 0 = Set.univ := by
  sorry

/-- PP_d(0) is everything. -/
theorem ppFragmentZZ_arity_zero (d : ℕ) : PPFragmentZZ d 0 = Set.univ := by
  sorry

/-- Unconditional: at arity 0 the whole hierarchy collapses,
    SE_2(0) = REC(0) = RE(0) = PP_2(0) = SE_4(0). -/
theorem relation_phase_diagram_arity_zero :
    SingleEqFragmentZZ 2 0 = RecFragmentZZ 0 ∧ RecFragmentZZ 0 = REFragmentZZ 0 ∧
      REFragmentZZ 0 = PPFragmentZZ 2 0 ∧ PPFragmentZZ 2 0 = SingleEqFragmentZZ 4 0 := by
  sorry

/-- Unary phase diagram (code-uniform GS + DPRM): SE_2(1) ⊊ REC(1) ⊊ RE(1) = PP_2(1) = SE_4(1).
    This is the only arity whose strictness SE_2 ⊊ REC uses the code-uniform diagonalization. -/
theorem relation_phase_diagram_unary (hU : UniformQuadraticSolvabilityDecidableZZ) (hD : DPRM_ZZ) :
    SingleEqFragmentZZ 2 1 ⊂ RecFragmentZZ 1 ∧ RecFragmentZZ 1 ⊂ REFragmentZZ 1 ∧
      REFragmentZZ 1 = PPFragmentZZ 2 1 ∧ PPFragmentZZ 2 1 = SingleEqFragmentZZ 4 1 := by
  sorry

/-- Phase diagram at arity k ≥ 2 (PER-EQUATION GS + DPRM; strictness by the x³ graph, no
    diagonalization): SE_2(k) ⊊ REC(k) ⊊ RE(k) = PP_2(k) = SE_4(k). -/
theorem relation_phase_diagram_arity_ge_two (hGS : QuadraticSolvabilityDecidableZZ) (hD : DPRM_ZZ)
    (k : ℕ) (hk : 2 ≤ k) :
    SingleEqFragmentZZ 2 k ⊂ RecFragmentZZ k ∧ RecFragmentZZ k ⊂ REFragmentZZ k ∧
      REFragmentZZ k = PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k := by
  sorry

end DiophCompression
