/-
  frozen_statements/DegenerateDichotomyData_STATEMENTS.lean — statement freeze (s28) of DiophCompression/SemanticQuadratic/DegenerateDichotomyData.lean — APAL Structural Theory Gate 5,
  必須F step 3 (leaf D2 wrapper) (s28, 2026-09-02, claude.ai direct).

  Branch D2 in data-carrying form, the last hypothesis of `fiber_dichotomy_data`. The bounded branch
  (β < 0) is the sealed argument verbatim. The two β = 0 branches are LINEAR families (the sealed proof
  uses the additive translation `mem_seq_b`), and the two β > 0 branches are the genuine QUADRATIC ones
  (`mem_seq_a`), with α = 4C²(2Bm − 4Cl), linear coefficient ±4C(2Cu₀ + Bc₀ + m), γ = c₀. Each
  `inf_of_family` call becomes the matching constructor of `OneWitnessFamilyData`; the cast lemmas the
  sealed proof already needed supply the `out` field. No sorry; std-3.
-/
import DiophCompression.SemanticQuadratic.FiberDichotomyData
import DiophCompression.SemanticQuadratic.PellDichotomyData

namespace DiophCompression.SemanticQuadratic

open MPUP

theorem dichotomy_degenerate_C_ne_data (A B C : ℤ) (h : disc A B C = 0) (hC : C ≠ 0) :
    DichotomyOneWitnessData A B C := by
  sorry

/-- 必須F step 3, MILESTONE: with D2 (here) and D7 (`dichotomy_pell_data`) both converted, the whole
    one-witness layer is UNCONDITIONAL in data-carrying form — every fibre of the one-witness normal form
    is either bounded by the sealed bound, or carries an explicit structured family. -/
theorem fiber_dichotomy_data_full (A B C : ℤ) : DichotomyOneWitnessData A B C := by
  sorry

/-- And it still implies the sealed `fiber_dichotomy`. -/
theorem fiber_dichotomy_of_data_full (A B C : ℤ) : Dichotomy A B C := by
  sorry

end DiophCompression.SemanticQuadratic
