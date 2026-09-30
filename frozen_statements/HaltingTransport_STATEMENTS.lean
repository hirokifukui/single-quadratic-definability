/-
  frozen_statements/HaltingTransport_STATEMENTS.lean — APAL Structural Theory Gate 2, 必須B part 1
  (frozen s25, 2026-09-01). REC(k) ⊊ RE(k) for every positive arity, UNCONDITIONALLY, by transporting
  mathlib's halting problem (ComputablePred.halting_problem / halting_problem_re) to ℤ^{k+1}; the strict
  relation phase diagram at arity ≥ 2 (SE_2 ⊊ REC ⊊ RE = PP_2 = SE_4, GS + DPRM as hypotheses).
-/
import DiophCompression.ComputabilityFragments

namespace DiophCompression

open MvPolynomial MPUP

/-- The halting relation transported to ℤ^{k+1}: read coordinate 0 as the code of a partial recursive
    function (through the ℤ-encoding) and ask whether it halts on input 0. -/
def haltingRelZZ (k : ℕ) : Set (Fin (k + 1) → ℤ) :=
  {v | ((Denumerable.ofNat Nat.Partrec.Code (Encodable.encode (v 0))).eval 0).Dom}

/-- The transported halting relation is r.e. -/
theorem haltingRelZZ_re (k : ℕ) : REPred fun v => v ∈ haltingRelZZ k := by
  sorry

/-- The transported halting relation is not recursive. -/
theorem haltingRelZZ_not_computablePred (k : ℕ) : ¬ ComputablePred fun v => v ∈ haltingRelZZ k := by
  sorry

/-- Unconditional: REC(k) ⊊ RE(k) for every positive arity. -/
theorem recursive_strictly_contained_re (k : ℕ) : RecFragmentZZ (k + 1) ⊂ REFragmentZZ (k + 1) := by
  sorry

/-- The strict phase diagram at arity k ≥ 2 (GS + DPRM): SE_2(k) ⊊ REC(k) ⊊ RE(k) = PP_2(k) = SE_4(k). -/
theorem relation_phase_diagram_strict (hGS : QuadraticSolvabilityDecidableZZ) (hD : DPRM_ZZ) (k : ℕ) :
    SingleEqFragmentZZ 2 (k + 2) ⊂ RecFragmentZZ (k + 2) ∧
      RecFragmentZZ (k + 2) ⊂ REFragmentZZ (k + 2) ∧
      REFragmentZZ (k + 2) = PPFragmentZZ 2 (k + 2) ∧
      PPFragmentZZ 2 (k + 2) = SingleEqFragmentZZ 4 (k + 2) := by
  sorry

end DiophCompression
