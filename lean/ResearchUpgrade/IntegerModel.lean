/-
  IntegerModel.lean — Gate-20 Packet N3, the wrapper back to the sealed integer relation (N3.3).

  The chain N3.1 → clearing is stated over ℚ-indexed totality.  The original SE₂ relation `Rgen`
  gives INTEGER solutions at INTEGER inputs, which is a strictly weaker hypothesis (integer points
  are rational points, but not conversely).  This file redoes the two steps at the weaker,
  correct index — `∀ t : ℤ` — and lands on the sealed vocabulary:

      RelTotal (Rgen a … j)  with the (y,u)-part positive definite
        ⟹  ∃ integers A, B, C, Dz > 0 with `A t² + B t + C` represented by `x² + Dz y²`
            at every integer t

  which is exactly the hypothesis `not_total_norm_of_separatingPrime` /
  `discriminant_rigidity_of_primeCertificate` (N2.2) consumes.  Hence the contrapositive
  `Rgen_not_total_of_no_model`: if no integer model of that shape is representable, the relation is
  not total.

  Nothing here weakens totality, uniqueness, witness count or degree (reviewer's standing
  prohibition): the hypothesis is the FULL `RelTotal` on the original relation, and the index set
  moves the correct way (from ℚ down to ℤ), making the theorem stronger, not the goal easier.

  Claim tags: [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.C3Reflection
import ResearchUpgrade.ClearDenominators
import ResearchUpgrade.CompleteSquare

namespace DiophCompression.ResearchUpgrade

/-- N3.1's bridge at the integer index. -/
theorem rational_norm_of_total_int (a b c d e f g h i j : ℚ) (ha : a ≠ 0)
    (hΔ : 4 * a * c - b ^ 2 ≠ 0)
    (htot : ∀ t : ℤ, ∃ y u : ℚ, PQ a b c d e f g h i j (t : ℚ) y u = 0) :
    ∃ A' B' C' : ℚ, ∀ t : ℤ, ∃ x z : ℚ,
      A' * (t : ℚ) ^ 2 + B' * (t : ℚ) + C'
        = x ^ 2 + ((4 * a * c - b ^ 2) / (4 * a ^ 2)) * z ^ 2 := by
  obtain ⟨p, q, r, s, n₂, n₁, n₀, hid⟩ := complete_square_compiler a b c d e f g h i j hΔ
  refine ⟨n₂ / a, n₁ / a, n₀ / a, fun t => ?_⟩
  obtain ⟨y, u, hyu⟩ := htot t
  have hF : a * (y - (p * (t : ℚ) + q)) ^ 2
      + b * (y - (p * (t : ℚ) + q)) * (u - (r * (t : ℚ) + s))
      + c * (u - (r * (t : ℚ) + s)) ^ 2 = n₂ * (t : ℚ) ^ 2 + n₁ * (t : ℚ) + n₀ := by
    linear_combination hyu - hid (t : ℚ) y u
  have hdiag := definite_diagonalization a b c ha (y - (p * (t : ℚ) + q)) (u - (r * (t : ℚ) + s))
  exact ⟨(y - (p * (t : ℚ) + q)) + (b / (2 * a)) * (u - (r * (t : ℚ) + s)),
    u - (r * (t : ℚ) + s), by
      linear_combination (norm := (field_simp; ring)) (-(1 : ℚ) / a) * hF + ((1 : ℚ) / a) * hdiag⟩

/-- Coefficient clearing at the integer index. -/
theorem clear_denominators_int (A' B' C' D : ℚ) (hD : 0 < D)
    (hrep : ∀ t : ℤ, ∃ x z : ℚ,
      A' * (t : ℚ) ^ 2 + B' * (t : ℚ) + C' = x ^ 2 + D * z ^ 2) :
    ∃ A B C Dz : ℤ, 0 < Dz ∧
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
    D.num * D.den, ?_, ?_⟩
  · have h1 : 0 < D.num := Rat.num_pos.mpr hD
    have h2 : 0 < (D.den : ℤ) := by exact_mod_cast Rat.den_pos D
    positivity
  · intro t
    obtain ⟨x, z, hxz⟩ := hrep t
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

/-- **N3.3 bridge.**  A total one-input / one-witness relation whose `(y,u)`-part is positive
definite yields an integer model in the shape N2.2 consumes. -/
theorem Rgen_total_yields_integer_model (a b c d e f g h i j : ℤ)
    (ha : 0 < a) (hΔ : 0 < 4 * a * c - b ^ 2)
    (hT : RelTotal (Rgen a b c d e f g h i j)) :
    ∃ A B C Dz : ℤ, 0 < Dz ∧
      ∀ t : ℤ, ∃ r s : ℚ,
        ((A * t ^ 2 + B * t + C : ℤ) : ℚ) = r ^ 2 + (Dz : ℚ) * s ^ 2 := by
  have haQ : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
  have hΔQ : (0 : ℚ) < 4 * (a : ℚ) * (c : ℚ) - (b : ℚ) ^ 2 := by
    have : ((4 * a * c - b ^ 2 : ℤ) : ℚ) = 4 * (a : ℚ) * (c : ℚ) - (b : ℚ) ^ 2 := by push_cast; ring
    rw [← this]
    exact_mod_cast hΔ
  have htot : ∀ t : ℤ, ∃ y u : ℚ,
      PQ (a : ℚ) b c d e f g h i j (t : ℚ) y u = 0 := by
    intro t
    obtain ⟨y, u, hyu⟩ := hT t
    refine ⟨(y : ℚ), (u : ℚ), ?_⟩
    rw [← PQ_cast a b c d e f g h i j t y u, hyu]
    norm_num
  obtain ⟨A', B', C', hrep⟩ :=
    rational_norm_of_total_int (a : ℚ) b c d e f g h i j haQ.ne' hΔQ.ne' htot
  exact clear_denominators_int A' B' C'
    ((4 * (a : ℚ) * (c : ℚ) - (b : ℚ) ^ 2) / (4 * (a : ℚ) ^ 2))
    (diag_D_pos (a : ℚ) b c haQ hΔQ) hrep

/-- **N3.3 (contrapositive).**  If no integer model of that shape is representable, a
positive-definite one-witness quadratic relation cannot be total. -/
theorem Rgen_not_total_of_no_model (a b c d e f g h i j : ℤ)
    (ha : 0 < a) (hΔ : 0 < 4 * a * c - b ^ 2)
    (hno : ∀ A B C Dz : ℤ, 0 < Dz →
      ¬ (∀ t : ℤ, ∃ r s : ℚ,
        ((A * t ^ 2 + B * t + C : ℤ) : ℚ) = r ^ 2 + (Dz : ℚ) * s ^ 2)) :
    ¬ RelTotal (Rgen a b c d e f g h i j) := by
  intro hT
  obtain ⟨A, B, C, Dz, hDz, hmodel⟩ :=
    Rgen_total_yields_integer_model a b c d e f g h i j ha hΔ hT
  exact hno A B C Dz hDz hmodel

end DiophCompression.ResearchUpgrade
