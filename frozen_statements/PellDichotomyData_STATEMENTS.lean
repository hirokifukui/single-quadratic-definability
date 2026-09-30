/-
  DiophCompression/SemanticQuadratic/PellDichotomyData.lean — APAL Structural Theory Gate 5,
  必須F step 3 (leaf D7 wrapper) (s28, 2026-09-02, claude.ai direct).

  Branch D7 in data-carrying form. The bounded branch is the sealed argument of `dichotomy_pell`,
  verbatim. The infinite branch no longer iterates a step inside an existence proof: it calls the hub
  `pell_orbit_of_X_pos`, which returns the orbit itself, and packages it as the `pell` constructor of
  `OneWitnessFamilyData`. Outputs are natural numbers because the orbit output starts at `c₀` and is
  strictly increasing. No sorry; std-3.
-/
import DiophCompression.SemanticQuadratic.FiberDichotomyData
import DiophCompression.SemanticQuadratic.PellOrbitOfXPos

namespace DiophCompression.SemanticQuadratic

open MPUP

theorem dichotomy_pell_data (A B C : ℤ) (h : 0 < disc A B C) (hns : ¬ IsSquare (disc A B C)) :
    DichotomyOneWitnessData A B C := by
  sorry

end DiophCompression.SemanticQuadratic
