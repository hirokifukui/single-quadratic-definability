/-
  NormTotality.lean — s55 (own initiative, installed on Dr. Fukui's instruction "全て足して").

  `norm_totality_iff` — a rational quadratic `A t² + B t + C` (A ≠ 0) is a value of `x² + D z²` (D > 0)
  at every integer `t` iff its discriminant is `−D h²` AND `A` itself is such a value.  Both directions
  construct their witnesses: the affine section (Brahmagupta), and a representation of `A` from one
  representation of a nonzero value.  With Lemma A.3 this makes totality of the one-variable fragment
  decidable with a finite certificate either way (the certificate tools are in certificates/own_s55/).

  Provenance: written with its proof before freezing; the statements were then compared with a `sorry`
  copy by `#check` output (identical, one planted change caught) before installation.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.Unconditional

namespace DiophCompression.ResearchUpgrade

/-- A nonzero value among `t = 0, 1, 2`. -/
theorem nt_nonroot (A B C : ℚ) (hA : A ≠ 0) :
    ∃ t : ℤ, A * (t : ℚ) ^ 2 + B * (t : ℚ) + C ≠ 0 := by
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  push_cast at h0 h1 h2
  apply hA
  linear_combination (h0 - 2 * h1 + h2) / 2

theorem norm_totality_iff (A B C D : ℚ) (hD : 0 < D) (hA : A ≠ 0) :
    (∀ t : ℤ, ∃ x z : ℚ, A * (t : ℚ) ^ 2 + B * (t : ℚ) + C = x ^ 2 + D * z ^ 2) ↔
      ((∃ h : ℚ, B ^ 2 - 4 * A * C = -D * h ^ 2) ∧ ∃ a0 b0 : ℚ, A = a0 ^ 2 + D * b0 ^ 2) := by
  constructor
  · intro htot
    obtain ⟨h, hh⟩ := rat_discriminant_of_total' A B C D hD hA htot
    refine ⟨⟨h, hh⟩, ?_⟩
    obtain ⟨t, ht⟩ := nt_nonroot A B C hA
    obtain ⟨x, z, hxz⟩ := htot t
    have hN0 : x ^ 2 + D * z ^ 2 ≠ 0 := hxz ▸ ht
    have key : 4 * A * (x ^ 2 + D * z ^ 2) = (2 * A * (t : ℚ) + B) ^ 2 + D * h ^ 2 := by
      rw [← hxz]; linear_combination (-1 : ℚ) * hh
    have hN2 : (2 * (x ^ 2 + D * z ^ 2)) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero two_ne_zero hN0)
    refine ⟨((2 * A * (t : ℚ) + B) * x + D * h * z) / (2 * (x ^ 2 + D * z ^ 2)),
      (h * x - (2 * A * (t : ℚ) + B) * z) / (2 * (x ^ 2 + D * z ^ 2)), ?_⟩
    rw [div_pow, div_pow, mul_div_assoc', ← add_div, eq_div_iff hN2]
    linear_combination (x ^ 2 + D * z ^ 2) * key
  · rintro ⟨⟨h, hh⟩, a0, b0, hab⟩ t
    have h2A : (2 * A) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero two_ne_zero hA)
    refine ⟨((2 * A * (t : ℚ) + B) * a0 + D * h * b0) / (2 * A),
      (h * a0 - (2 * A * (t : ℚ) + B) * b0) / (2 * A), ?_⟩
    rw [div_pow, div_pow, mul_div_assoc', ← add_div, eq_div_iff h2A]
    linear_combination (-A) * hh + ((2 * A * (t : ℚ) + B) ^ 2 + D * h ^ 2) * hab

end DiophCompression.ResearchUpgrade
