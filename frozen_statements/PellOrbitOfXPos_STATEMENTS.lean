/-
  frozen_statements/PellOrbitOfXPos_STATEMENTS.lean — statement freeze (s28) of DiophCompression/SemanticQuadratic/PellOrbitOfXPos.lean — APAL Structural Theory Gate 5, 必須F step 2
  (the Pell hub in data form) (s28, 2026-09-02, claude.ai direct).

  `pell_infinite_of_X_pos` is the hub of the whole Pell side: branch D7 uses it, branch A1 uses it through
  the scaled line (FullRankGeneric), and the rank-two generic block uses it too. It returns bare
  infinitude. Here is its data twin: from one fibre point with a positive `X = 2Dc + β` it returns the
  EXPLICIT orbit of fibre points — the unit `(P, Q)`, the base `(X₀, Y₀)`, the family `pt k = (c k, u k)`,
  the affine relation `2D·c k + β = X k`, and strict growth of the output. The sign of `Q` is chosen ONCE
  at the base (`pellOrbit_neg_snd`), where the sealed proof chose it at every step. No sorry; std-3.
-/
import DiophCompression.SemanticQuadraticTwoWitness.PellStep
import DiophCompression.SemanticQuadratic.PellFiberOrbit

namespace DiophCompression.SemanticQuadratic

open MPUP

theorem pell_orbit_of_X_pos (A B C l m q : ℤ) (h : 0 < disc A B C) (hns : ¬ IsSquare (disc A B C))
    (c₀ : ℕ) (hc₀ : c₀ ∈ fiberSet A B C l m q)
    (hX₀ : 0 < 2 * disc A B C * (c₀ : ℤ) + (2 * B * m - 4 * C * l)) :
    ∃ (P Q Y₀ : ℤ) (pt : ℕ → ℤ × ℤ),
      P ^ 2 - disc A B C * Q ^ 2 = 1 ∧ 2 ≤ P ∧
      (pt 0).1 = (c₀ : ℤ) ∧
      (∀ k, fq A B C l m q (pt k).1 (pt k).2 = 0) ∧
      (∀ k, 2 * disc A B C * (pt k).1 + (2 * B * m - 4 * C * l)
          = (DiophCompression.pellOrbit (disc A B C) P Q
              (2 * disc A B C * (c₀ : ℤ) + (2 * B * m - 4 * C * l)) Y₀ k).1) ∧
      StrictMono (fun k => (pt k).1) := by
  sorry

end DiophCompression.SemanticQuadratic
