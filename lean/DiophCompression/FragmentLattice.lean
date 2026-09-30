/-
  DiophCompression/FragmentLattice.lean — APAL Structural Theory Gate 1 (session 24, 2026-08-31, claude.ai direct, 0 CC).
  GPT r21 §4.1 / Q4: SE_4(k) = PP_2(k) = Dioph(k). PP_2 ⊆ SE_4 is `ppZZ_degree_two_subset_singleEquationZZ_degree_four`
  (sum of squares), PP_2 = Dioph is `ppFragmentZZ_two_eq_diophFragmentZZ` (Skolem reduction); the new piece is the
  trivial SE_d ⊆ Dioph. Statements frozen in frozen_statements/FragmentLattice_STATEMENTS.lean.
-/
import DiophCompression.SkolemReduction

namespace DiophCompression

open MvPolynomial MPUP

/-- A single equation of any degree is Diophantine. -/
theorem withinDiophZZ_of_withinSingleEquationZZ {k d : ℕ} {A : Set (Fin k → ℤ)}
    (h : WithinSingleEquationZZ d A) : WithinDiophZZ A := by
  obtain ⟨r, P, _, hrep⟩ := h
  exact ⟨r, P, hrep⟩

/-- SE_d(k) ⊆ Dioph(k) for every degree d. -/
theorem singleEqFragmentZZ_subset_diophFragmentZZ (d k : ℕ) :
    SingleEqFragmentZZ d k ⊆ DiophFragmentZZ k := by
  intro A hA
  exact withinDiophZZ_of_withinSingleEquationZZ hA

/-- SE_4(k) = PP_2(k): quartic single equations are exactly the quadratic pp-definable relations. -/
theorem singleEqFragmentZZ_four_eq_ppFragmentZZ_two (k : ℕ) :
    SingleEqFragmentZZ 4 k = PPFragmentZZ 2 k := by
  apply Set.Subset.antisymm
  · intro A hA
    rw [mem_ppFragmentZZ, withinPPZZ_two_iff_withinDiophZZ]
    exact withinDiophZZ_of_withinSingleEquationZZ hA
  · exact ppFragmentZZ_two_subset_singleEqFragmentZZ_four k

/-- SE_4(k) = Dioph(k). -/
theorem singleEqFragmentZZ_four_eq_diophFragmentZZ (k : ℕ) :
    SingleEqFragmentZZ 4 k = DiophFragmentZZ k := by
  rw [singleEqFragmentZZ_four_eq_ppFragmentZZ_two, ppFragmentZZ_two_eq_diophFragmentZZ]

/-- The lattice at every arity: SE_2(k) ⊆ PP_2(k) = SE_4(k) = Dioph(k). -/
theorem fragment_lattice_ZZ (k : ℕ) :
    SingleEqFragmentZZ 2 k ⊆ PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k ∧
      SingleEqFragmentZZ 4 k = DiophFragmentZZ k := by
  exact ⟨singleEqFragmentZZ_subset_ppFragmentZZ 2 k, (singleEqFragmentZZ_four_eq_ppFragmentZZ_two k).symm,
    singleEqFragmentZZ_four_eq_diophFragmentZZ k⟩

end DiophCompression

#print axioms DiophCompression.withinDiophZZ_of_withinSingleEquationZZ
#print axioms DiophCompression.singleEqFragmentZZ_subset_diophFragmentZZ
#print axioms DiophCompression.singleEqFragmentZZ_four_eq_ppFragmentZZ_two
#print axioms DiophCompression.singleEqFragmentZZ_four_eq_diophFragmentZZ
#print axioms DiophCompression.fragment_lattice_ZZ
