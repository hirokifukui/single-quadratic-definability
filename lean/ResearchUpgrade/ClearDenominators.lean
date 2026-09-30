/-
  ClearDenominators.lean — Gate-20 Packet N3, the coefficient-clearing step of N3.3.

  `rational_norm_of_total` (N3.1) hands over a degree-≤2 polynomial and a form parameter over ℚ;
  `not_total_norm_of_separatingPrime` (N2.2) consumes them over ℤ.  This file closes that gap
  WITHOUT reopening N2.2 — the sealed integer statement stays exactly as proved.

  The two facts that make it free:
  * representability is invariant under multiplying the polynomial by a square: if
    `A't² + B't + C' = x² + D z²` then `κ²(A't² + B't + C') = (κx)² + D(κz)²`;
  * the form parameter clears the same way: `D = (D.num · D.den)/D.den²`, so
    `D z² = (D.num·D.den)·(z/D.den)²` with `D.num·D.den` an INTEGER, positive when `D > 0`.

  Choosing `κ = A'.den · B'.den · C'.den` makes `κ²A'`, `κ²B'`, `κ²C'` integers by inspection —
  each denominator cancels once and survives to the first power — so no divisibility lemma is
  needed and the integers are produced explicitly rather than extracted.

  * `rat_num_eq`                        — `(q.num : ℚ) = q · q.den`.
  * `clear_denominators_of_rational_norm` — the clearing, with `κ` returned so that `A ≠ 0`
                                            transfers from `A' ≠ 0`.
  * `integer_model_of_total`            — N3.1 ∘ clearing: total rational solvability of a
                                            non-degenerate `PQ` yields an INTEGER model
                                            `(A, B, C, Dz)` represented at every integer `t`.

  Claim tags: [P] (std-3).  Baseline read-only.
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.LinearCombination
import ResearchUpgrade.CompleteSquare

namespace DiophCompression.ResearchUpgrade

/-- `(q.num : ℚ) = q · q.den`. -/
theorem rat_num_eq (q : ℚ) : (q.num : ℚ) = q * (q.den : ℚ) := by
  have hd : ((q.den : ℚ)) ≠ 0 := by exact_mod_cast (Rat.den_pos q).ne'
  have hh := Rat.num_div_den q
  field_simp at hh
  linear_combination hh

/-- **Coefficient clearing.**  A rational degree-≤2 polynomial represented by `x² + D y²` at every
rational point yields an INTEGER polynomial represented by `x² + Dz y²` with `Dz : ℤ`, `0 < Dz`,
at every integer point.  `κ` is returned so that non-degeneracy transfers. -/
theorem clear_denominators_of_rational_norm (A' B' C' D : ℚ) (hD : 0 < D)
    (hrep : ∀ t : ℚ, ∃ x z : ℚ, A' * t ^ 2 + B' * t + C' = x ^ 2 + D * z ^ 2) :
    ∃ (A B C Dz : ℤ) (κ : ℚ), 0 < Dz ∧ κ ≠ 0 ∧
      (A : ℚ) = κ ^ 2 * A' ∧ (B : ℚ) = κ ^ 2 * B' ∧ (C : ℚ) = κ ^ 2 * C' ∧
      ∀ t : ℤ, ∃ r s : ℚ,
        ((A * t ^ 2 + B * t + C : ℤ) : ℚ) = r ^ 2 + (Dz : ℚ) * s ^ 2 := by
  have hAd : ((A'.den : ℚ)) ≠ 0 := by exact_mod_cast (Rat.den_pos A').ne'
  have hBd : ((B'.den : ℚ)) ≠ 0 := by exact_mod_cast (Rat.den_pos B').ne'
  have hCd : ((C'.den : ℚ)) ≠ 0 := by exact_mod_cast (Rat.den_pos C').ne'
  have hDd : ((D.den : ℚ)) ≠ 0 := by exact_mod_cast (Rat.den_pos D).ne'
  have hDq : (D.num : ℚ) = D * (D.den : ℚ) := rat_num_eq D
  refine ⟨(A'.den : ℤ) * (B'.den : ℤ) ^ 2 * (C'.den : ℤ) ^ 2 * A'.num,
    (A'.den : ℤ) ^ 2 * (B'.den : ℤ) * (C'.den : ℤ) ^ 2 * B'.num,
    (A'.den : ℤ) ^ 2 * (B'.den : ℤ) ^ 2 * (C'.den : ℤ) * C'.num,
    D.num * D.den,
    (A'.den : ℚ) * (B'.den : ℚ) * (C'.den : ℚ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : 0 < D.num := Rat.num_pos.mpr hD
    have h2 : 0 < (D.den : ℤ) := by exact_mod_cast Rat.den_pos D
    positivity
  · exact mul_ne_zero (mul_ne_zero hAd hBd) hCd
  · push_cast
    linear_combination ((B'.den : ℚ) ^ 2 * (C'.den : ℚ) ^ 2 * (A'.den : ℚ)) * rat_num_eq A'
  · push_cast
    linear_combination ((A'.den : ℚ) ^ 2 * (C'.den : ℚ) ^ 2 * (B'.den : ℚ)) * rat_num_eq B'
  · push_cast
    linear_combination ((A'.den : ℚ) ^ 2 * (B'.den : ℚ) ^ 2 * (C'.den : ℚ)) * rat_num_eq C'
  · intro t
    obtain ⟨x, z, hxz⟩ := hrep (t : ℚ)
    refine ⟨((A'.den : ℚ) * (B'.den : ℚ) * (C'.den : ℚ)) * x,
      ((A'.den : ℚ) * (B'.den : ℚ) * (C'.den : ℚ)) * z / (D.den : ℚ), ?_⟩
    have hDz : ((D.num * D.den : ℤ) : ℚ) = D * (D.den : ℚ) ^ 2 := by
      push_cast
      linear_combination (D.den : ℚ) * hDq
    rw [hDz]
    have hlhs : (((A'.den : ℤ) * (B'.den : ℤ) ^ 2 * (C'.den : ℤ) ^ 2 * A'.num * t ^ 2
        + (A'.den : ℤ) ^ 2 * (B'.den : ℤ) * (C'.den : ℤ) ^ 2 * B'.num * t
        + (A'.den : ℤ) ^ 2 * (B'.den : ℤ) ^ 2 * (C'.den : ℤ) * C'.num : ℤ) : ℚ)
        = ((A'.den : ℚ) * (B'.den : ℚ) * (C'.den : ℚ)) ^ 2
          * (A' * (t : ℚ) ^ 2 + B' * (t : ℚ) + C') := by
      push_cast
      linear_combination
        ((B'.den : ℚ) ^ 2 * (C'.den : ℚ) ^ 2 * (A'.den : ℚ) * (t : ℚ) ^ 2) * rat_num_eq A'
          + ((A'.den : ℚ) ^ 2 * (C'.den : ℚ) ^ 2 * (B'.den : ℚ) * (t : ℚ)) * rat_num_eq B'
          + ((A'.den : ℚ) ^ 2 * (B'.den : ℚ) ^ 2 * (C'.den : ℚ)) * rat_num_eq C'
    rw [hlhs, hxz]
    field_simp

/-- **N3.1 ∘ clearing.**  Total rational solvability of a non-degenerate `PQ` with positive-definite
`(y,u)`-part yields an integer model: integer `A, B, C` and an integer `Dz > 0` such that
`A t² + B t + C` is represented by `x² + Dz y²` at every integer `t`.  This is exactly the
hypothesis `not_total_norm_of_separatingPrime` (N2.2) consumes, so a prime certificate for
`(Dz, B² − 4AC)` now contradicts total solvability of the original quadratic. -/
theorem integer_model_of_total (a b c d e f g h i j : ℚ) (ha : 0 < a)
    (hΔ : 0 < 4 * a * c - b ^ 2)
    (htot : ∀ t : ℚ, ∃ y u : ℚ, PQ a b c d e f g h i j t y u = 0) :
    ∃ A B C Dz : ℤ, 0 < Dz ∧
      ∀ t : ℤ, ∃ r s : ℚ,
        ((A * t ^ 2 + B * t + C : ℤ) : ℚ) = r ^ 2 + (Dz : ℚ) * s ^ 2 := by
  obtain ⟨A', B', C', hrep⟩ :=
    rational_norm_of_total a b c d e f g h i j ha.ne' hΔ.ne' htot
  obtain ⟨A, B, C, Dz, κ, hDz, -, -, -, -, hmodel⟩ :=
    clear_denominators_of_rational_norm A' B' C' ((4 * a * c - b ^ 2) / (4 * a ^ 2))
      (diag_D_pos a b c ha hΔ) hrep
  exact ⟨A, B, C, Dz, hDz, hmodel⟩

end DiophCompression.ResearchUpgrade
