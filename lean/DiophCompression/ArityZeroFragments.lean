/-
  DiophCompression/ArityZeroFragments.lean — APAL Structural Theory Gate 3, 必須D-1/D-3
  (session 26, 2026-09-01, claude.ai direct). Statements frozen in
  frozen_statements/ArityZeroFragments_STATEMENTS.lean. No new mathematics; no sorry; std-3 expected.
-/
import DiophCompression.HaltingTransport
import DiophCompression.UnaryDiagonal

namespace DiophCompression

open MvPolynomial MPUP

/-- At arity 0 the parameter space `Fin 0 → ℤ` is a singleton, so a relation is `∅` or `univ`. -/
theorem set_arity_zero_eq_empty_or_univ (A : Set (Fin 0 → ℤ)) : A = ∅ ∨ A = Set.univ := by
  rcases A.eq_empty_or_nonempty with h | ⟨a, ha⟩
  · exact Or.inl h
  · right
    ext b
    simp only [Set.mem_univ, iff_true]
    rwa [Subsingleton.elim b a]

/-- `∅ ⊆ ℤ^0` is a single equation (`1 = 0`) of any degree bound. -/
theorem empty_withinSingleEquationZZ_arity_zero (d : ℕ) :
    WithinSingleEquationZZ d (∅ : Set (Fin 0 → ℤ)) := by
  refine ⟨0, C 1, ?_, ?_⟩
  · simp
  · intro a
    simp [evalAtZZ]

/-- `univ ⊆ ℤ^0` is a single equation (`0 = 0`) of any degree bound. -/
theorem univ_withinSingleEquationZZ_arity_zero (d : ℕ) :
    WithinSingleEquationZZ d (Set.univ : Set (Fin 0 → ℤ)) := by
  refine ⟨0, 0, ?_, ?_⟩
  · simp
  · intro a
    simp [evalAtZZ]

/-- SE_d(0) is everything. -/
theorem singleEqFragmentZZ_arity_zero (d : ℕ) : SingleEqFragmentZZ d 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro A
  rcases set_arity_zero_eq_empty_or_univ A with h | h <;> subst h
  · exact empty_withinSingleEquationZZ_arity_zero d
  · exact univ_withinSingleEquationZZ_arity_zero d

/-- REC(0) is everything. -/
theorem recFragmentZZ_arity_zero : RecFragmentZZ 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro A
  rcases set_arity_zero_eq_empty_or_univ A with h | h <;> subst h
  · exact ComputablePred.computable_iff.2 ⟨fun _ => false, Computable.const false, by funext a; simp⟩
  · exact ComputablePred.computable_iff.2 ⟨fun _ => true, Computable.const true, by funext a; simp⟩

/-- RE(0) is everything. -/
theorem reFragmentZZ_arity_zero : REFragmentZZ 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro A
  exact recFragmentZZ_subset_reFragmentZZ 0 (by rw [recFragmentZZ_arity_zero]; exact Set.mem_univ A)

/-- PP_d(0) is everything. -/
theorem ppFragmentZZ_arity_zero (d : ℕ) : PPFragmentZZ d 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro A
  exact singleEqFragmentZZ_subset_ppFragmentZZ d 0 (by rw [singleEqFragmentZZ_arity_zero]; exact Set.mem_univ A)

/-- Unconditional: at arity 0 the whole hierarchy collapses,
    SE_2(0) = REC(0) = RE(0) = PP_2(0) = SE_4(0). -/
theorem relation_phase_diagram_arity_zero :
    SingleEqFragmentZZ 2 0 = RecFragmentZZ 0 ∧ RecFragmentZZ 0 = REFragmentZZ 0 ∧
      REFragmentZZ 0 = PPFragmentZZ 2 0 ∧ PPFragmentZZ 2 0 = SingleEqFragmentZZ 4 0 := by
  rw [singleEqFragmentZZ_arity_zero, recFragmentZZ_arity_zero, reFragmentZZ_arity_zero,
    ppFragmentZZ_arity_zero, singleEqFragmentZZ_arity_zero]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Unary phase diagram (code-uniform GS + DPRM): SE_2(1) ⊊ REC(1) ⊊ RE(1) = PP_2(1) = SE_4(1).
    This is the only arity whose strictness SE_2 ⊊ REC uses the code-uniform diagonalization. -/
theorem relation_phase_diagram_unary (hU : UniformQuadraticSolvabilityDecidableZZ) (hD : DPRM_ZZ) :
    SingleEqFragmentZZ 2 1 ⊂ RecFragmentZZ 1 ∧ RecFragmentZZ 1 ⊂ REFragmentZZ 1 ∧
      REFragmentZZ 1 = PPFragmentZZ 2 1 ∧ PPFragmentZZ 2 1 = SingleEqFragmentZZ 4 1 := by
  exact relation_phase_diagram_all_positive_arity hU hD (by norm_num)

/-- Phase diagram at arity k ≥ 2 (PER-EQUATION GS + DPRM; strictness by the x³ graph, no
    diagonalization): SE_2(k) ⊊ REC(k) ⊊ RE(k) = PP_2(k) = SE_4(k). -/
theorem relation_phase_diagram_arity_ge_two (hGS : QuadraticSolvabilityDecidableZZ) (hD : DPRM_ZZ)
    (k : ℕ) (hk : 2 ≤ k) :
    SingleEqFragmentZZ 2 k ⊂ RecFragmentZZ k ∧ RecFragmentZZ k ⊂ REFragmentZZ k ∧
      REFragmentZZ k = PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  exact relation_phase_diagram_strict hGS hD j

end DiophCompression

#print axioms DiophCompression.relation_phase_diagram_arity_zero
#print axioms DiophCompression.relation_phase_diagram_unary
#print axioms DiophCompression.relation_phase_diagram_arity_ge_two
