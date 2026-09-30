/-
  RefutedResiduals.lean — Gate-20 Packet 0, task T03a.

  `MultiWitnessInertObstruction` (GeneralResidual.lean, R4) was shipped at s46 as an OPEN
  statement.  It is FALSE.  The reviewer's counterexample is `r = 2`, `D₁ = D₂ = 1`, `p = 3`,
  `N = 3`, `x = z₁ = z₂ = 1`:  `-1` is a non-square mod 3, `v₃(3) = 1`, and `3 = 1² + 1² + 1²`.
  Every hypothesis of the `def` is met and its conclusion fails.

  The `def` is kept (it is what the reviewer's r > 1 question looked like), and this file records
  its refutation beside it.  s46 removed two VACUOUS residuals; this one is worse than vacuous,
  so it is refuted in the kernel rather than deleted in prose.

  Claim tag: [P] (std-3).  Baseline read-only.
-/
import Mathlib
import ResearchUpgrade.GeneralResidual

namespace DiophCompression.ResearchUpgrade

/-- `-1` is not a square mod 3 (hoisted to top level: `decide` fails on goals mentioning a
local instance — s46 trap). -/
private theorem neg_one_not_isSquare_zmod3 : ¬ IsSquare (-(1 : ZMod 3)) := by decide

/-- **T03a.**  The multi-witness inert-prime obstruction is FALSE. -/
theorem not_multiWitnessInertObstruction : ¬ MultiWitnessInertObstruction := by
  intro h
  have hpos : ∀ i : Fin 2, (0 : ℤ) < (fun _ : Fin 2 => (1 : ℤ)) i := by
    intro i; norm_num
  have hp : Nat.Prime 3 := by norm_num
  have hns : ∀ i : Fin 2, ¬ IsSquare (-(((fun _ : Fin 2 => (1 : ℤ)) i : ℤ) : ZMod 3)) := by
    intro i
    simpa using neg_one_not_isSquare_zmod3
  have hdvd : ((3 : ℕ) : ℤ) ∣ (3 : ℤ) := by norm_num
  have hndvd : ¬ (((3 : ℕ) : ℤ) ^ 2 ∣ (3 : ℤ)) := by decide
  refine h 2 (fun _ => (1 : ℤ)) hpos 3 hp hns 3 hdvd hndvd ⟨1, fun _ => 1, ?_⟩
  simp
  norm_num

end DiophCompression.ResearchUpgrade
