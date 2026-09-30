/-
  Transfer.lean — Gate-20 Packet N3, the bookkeeping between the ℚ layer and the integer model.

  `discriminant_trichotomy` (WeakAffine.lean) is stated for INTEGER `A, B, C, D`; the N3.1 bridge
  produces ℚ data.  This file carries the discriminant back across the clearing, so the positive
  form is available at the ℚ layer where N2.3 wants it.

  * `clear_denominators_full` — the clearing again, now also returning the two scalings:
    `κ` with `(A:ℚ) = κ²A'` (etc.) and `ν = D.den` with `(Dz:ℚ) = D ν²`.
  * `not_total_of_linear`     — the reviewer's separate branch for a GENUINELY LINEAR `F`: with
    `D > 0` the form `x² + D y²` is non-negative, while a linear polynomial with nonzero slope is
    eventually negative, so a genuinely linear `F` is never totally represented.  (The constant
    branch is not excluded and needs no argument: a constant is represented or it is not.)
  * `rat_discriminant_of_total` — the positive form of N2.2 at the ℚ layer: for `A' ≠ 0`,
    total representability forces `B'² − 4A'C' = −D h'²`.  Conditional on `CharacterSeparation`
    (= N1.1b), carried in the signature.

  Claim tags: [P] (std-3), with `CharacterSeparation` an explicit [OPEN] hypothesis.
  Baseline read-only.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import ResearchUpgrade.ClearDenominators
import ResearchUpgrade.IntegerModel
import ResearchUpgrade.WeakAffine

namespace DiophCompression.ResearchUpgrade

/-- Coefficient clearing, returning the scalings so the discriminant can be carried back. -/
theorem clear_denominators_full (A' B' C' D : ℚ) (hD : 0 < D)
    (hrep : ∀ t : ℤ, ∃ x z : ℚ,
      A' * (t : ℚ) ^ 2 + B' * (t : ℚ) + C' = x ^ 2 + D * z ^ 2) :
    ∃ (A B C Dz : ℤ) (κ ν : ℚ), 0 < Dz ∧ κ ≠ 0 ∧
      (A : ℚ) = κ ^ 2 * A' ∧ (B : ℚ) = κ ^ 2 * B' ∧ (C : ℚ) = κ ^ 2 * C' ∧
      (Dz : ℚ) = D * ν ^ 2 ∧
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
    (A'.den : ℚ) * (B'.den : ℚ) * (C'.den : ℚ), (D.den : ℚ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · push_cast
    linear_combination (D.den : ℚ) * hDq
  · intro t
    obtain ⟨x, z, hxz⟩ := hrep t
    refine ⟨((A'.den : ℚ) * (B'.den : ℚ) * (C'.den : ℚ)) * x,
      ((A'.den : ℚ) * (B'.den : ℚ) * (C'.den : ℚ)) * z / (D.den : ℚ), ?_⟩
    have hDzc : ((D.num * D.den : ℤ) : ℚ) = D * (D.den : ℚ) ^ 2 := by
      push_cast
      linear_combination (D.den : ℚ) * hDq
    rw [hDzc]
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

/-- **The genuinely linear branch.**  With `D > 0` the form `x² + D y²` is non-negative, so a
polynomial with zero quadratic coefficient and nonzero slope — eventually negative — is never
totally represented. -/
theorem not_total_of_linear (B' C' D : ℚ) (hD : 0 < D) (hB' : B' ≠ 0) :
    ¬ ∀ t : ℤ, ∃ x z : ℚ,
      (0 : ℚ) * (t : ℚ) ^ 2 + B' * (t : ℚ) + C' = x ^ 2 + D * z ^ 2 := by
  intro htot
  -- pick an integer where the line is negative
  obtain ⟨t, ht⟩ : ∃ t : ℤ, B' * (t : ℚ) + C' < 0 := by
    rcases lt_or_gt_of_ne hB' with hneg | hpos
    · obtain ⟨t, ht⟩ := exists_int_gt (-C' / B')
      refine ⟨t, ?_⟩
      have hmul := mul_lt_mul_of_neg_left ht hneg
      have hcancel : B' * (-C' / B') = -C' := by field_simp
      rw [hcancel] at hmul
      linarith
    · obtain ⟨t, ht⟩ := exists_int_lt (-C' / B')
      refine ⟨t, ?_⟩
      have hmul := mul_lt_mul_of_pos_left ht hpos
      have hcancel : B' * (-C' / B') = -C' := by field_simp
      rw [hcancel] at hmul
      linarith
  obtain ⟨x, z, hxz⟩ := htot t
  have hnn : (0 : ℚ) ≤ x ^ 2 + D * z ^ 2 := by positivity
  rw [← hxz] at hnn
  linarith

/-- **The positive form of N2.2 at the ℚ layer.**  Conditional on `CharacterSeparation` (= N1.1b),
carried in the signature. -/
theorem rat_discriminant_of_total (hCS : CharacterSeparation) (A' B' C' D : ℚ)
    (hD : 0 < D) (hA' : A' ≠ 0)
    (hrep : ∀ t : ℤ, ∃ x z : ℚ,
      A' * (t : ℚ) ^ 2 + B' * (t : ℚ) + C' = x ^ 2 + D * z ^ 2) :
    ∃ h' : ℚ, B' ^ 2 - 4 * A' * C' = -D * h' ^ 2 := by
  obtain ⟨A, B, C, Dz, κ, ν, hDz, hκ, hA, hB, hC, hν, hmodel⟩ :=
    clear_denominators_full A' B' C' D hD hrep
  have hAne : A ≠ 0 := by
    intro hz
    rw [hz] at hA
    exact hA' (by
      have : κ ^ 2 * A' = 0 := by exact_mod_cast hA.symm
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hκ
      · exact h)
  obtain ⟨hq, hh⟩ := discriminant_trichotomy hCS Dz A B C hAne hDz hmodel
  refine ⟨ν * hq / κ ^ 2, ?_⟩
  have hcast : ((B ^ 2 - 4 * A * C : ℤ) : ℚ) = (B : ℚ) ^ 2 - 4 * (A : ℚ) * (C : ℚ) := by
    push_cast; ring
  rw [hcast, hA, hB, hC, hν] at hh
  linear_combination (norm := (field_simp; ring)) ((1 : ℚ) / κ ^ 4) * hh

end DiophCompression.ResearchUpgrade
