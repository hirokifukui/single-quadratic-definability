/-
  frozen_statements/RelationPhaseAllPositiveArityClassical_STATEMENTS.lean — Theorem 6.8 under the two literature hypotheses directly (frozen s41, 2026-09-11; Gate-15 F02). First conjunct of apal_full_phase_diagram_classical; no new mathematics.
-/
import DiophCompression.APALStructuralTheoryCore

namespace DiophCompression

open MvPolynomial MPUP

/-- The relation phase diagram at every positive arity under the code-uniform Grunewald–Segal hypothesis on
    standard codes and the classical DPRM theorem over ℕ (Theorem 6.8 as stated in the paper):
    SE₂(k) ⊊ REC(k) ⊊ RE(k) = PP₂(k) = SE₄(k) for every k ≥ 1.
    First conjunct of `apal_full_phase_diagram_classical`. -/
theorem relation_phase_diagram_all_positive_arity_of_classical
    (hC : UniformQuadraticSolvabilityOnCodes) (hN : DPRM_NN) :
    ∀ {k : ℕ}, 0 < k →
      SingleEqFragmentZZ 2 k ⊂ RecFragmentZZ k ∧ RecFragmentZZ k ⊂ REFragmentZZ k ∧
        REFragmentZZ k = PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k := by
  sorry

end DiophCompression
