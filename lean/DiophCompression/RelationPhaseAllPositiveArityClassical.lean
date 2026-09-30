/-
  DiophCompression/RelationPhaseAllPositiveArityClassical.lean — Theorem 6.8 stated under the two literature
  hypotheses directly (session 41, 2026-09-11, claude.ai direct; Gate-15 F02). The paper's Theorem 6.8 assumes
  UniformQuadraticSolvabilityOnCodes and DPRM_NN and concludes the RELATION phase diagram at every positive arity;
  the registry recorded the correspondence through the bundle apal_full_phase_diagram_classical (whose first
  conjunct is this diagram and whose remaining conjuncts are the function diagram of Theorem 7.1). This wrapper
  is that first conjunct alone: same hypotheses, relation diagram only, so the paper theorem and the Lean root
  have the same hypotheses and the same conclusion. No new mathematics. Statement frozen in
  frozen_statements/RelationPhaseAllPositiveArityClassical_STATEMENTS.lean. No sorry; std-3 expected.
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
        REFragmentZZ k = PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k :=
  (apal_full_phase_diagram_classical hC hN).1

end DiophCompression

#print axioms DiophCompression.relation_phase_diagram_all_positive_arity_of_classical
