/-
  frozen_statements/FiberDichotomyData_STATEMENTS.lean — statement freeze (s28) of DiophCompression/SemanticQuadratic/FiberDichotomyData.lean — APAL Structural Theory Gate 5,
  必須F step 3 (the one-witness aggregation) (s28, 2026-09-02, claude.ai direct).

  `fiber_dichotomy` dispatches the one-witness normal form to its leaves D1–D7 and returns `Dichotomy`,
  whose infinite side is bare `Set.Infinite`. Here the same ten-line dispatch is carried out at the DATA
  level: the leaves already converted in s28 (D1 bounded, D3/D4/D6 linear) are discharged, and the two
  still owed (D2 quadratic, D7 Pell — both have their families proved, only their dichotomy wrappers are
  not yet converted) appear as explicit hypotheses, so what remains is visible in the statement rather
  than hidden in prose. The data form implies the sealed one. No sorry; std-3.
-/
import DiophCompression.SemanticQuadratic.FiberDichotomy
import DiophCompression.SemanticQuadratic.OneWitnessFamilyData

namespace DiophCompression.SemanticQuadratic

open MPUP

/-- The one-witness dichotomy in data-carrying form. -/
def DichotomyOneWitnessData (A B C : ℤ) : Prop :=
  ∃ K : ℕ, ∀ l m q : ℤ, Nonempty (OneWitnessFamilyData A B C l m q) ∨
    ∀ c ∈ fiberSet A B C l m q, (c : ℤ) ≤ fbound K l m q

/-- The data form implies the sealed form: strengthening loses nothing. -/
theorem dichotomy_of_dichotomyOneWitnessData {A B C : ℤ} (h : DichotomyOneWitnessData A B C) :
    Dichotomy A B C := by
  sorry

/-- The linear leaves (D3, D4, D6) feed the aggregation through the `linear` constructor. -/
theorem dichotomyOneWitnessData_of_linear {A B C : ℤ} (h : DichotomyLinearData A B C) :
    DichotomyOneWitnessData A B C := by
  sorry

/-! ### Leaf D1 (negative discriminant): always bounded, so the data form is the sealed proof verbatim -/

theorem dichotomy_definite_data (A B C : ℤ) (h : disc A B C < 0) : DichotomyOneWitnessData A B C := by
  sorry

/-! ### The dispatch, at data level -/

/-- 必須F step 3: the one-witness dispatch in data-carrying form. D1 and the linear leaves are
    discharged; D2 and D7 are the two leaf wrappers still owed (their families are already proved in
    `QuadraticFamilyData.lean` and `PellOrbitOfXPos.lean`). -/
theorem fiber_dichotomy_data (A B C : ℤ)
    (hD2 : disc A B C = 0 → C ≠ 0 → DichotomyOneWitnessData A B C)
    (hD7 : 0 < disc A B C → ¬ IsSquare (disc A B C) → DichotomyOneWitnessData A B C) :
    DichotomyOneWitnessData A B C := by
  sorry

/-- The aggregated data form still implies the sealed `fiber_dichotomy`. -/
theorem fiber_dichotomy_of_data (A B C : ℤ)
    (hD2 : disc A B C = 0 → C ≠ 0 → DichotomyOneWitnessData A B C)
    (hD7 : 0 < disc A B C → ¬ IsSquare (disc A B C) → DichotomyOneWitnessData A B C) :
    Dichotomy A B C := by
  sorry

end DiophCompression.SemanticQuadratic
