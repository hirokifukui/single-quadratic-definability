/-
  AnchoredSection.lean — Gate-20 Packet N2/N3, tasks N2.3 and the denominator-clearing half of N3.2.

  N2.3 (reviewer §4, the constructive half of Proposition N).  Given
    * `A ≠ 0`,
    * `δ = B² − 4AC = −D h²` for some rational `h`  (the CONCLUSION of N2.2 — taken here as a
      hypothesis, so this task does NOT wait on the open leaf N1.1b),
    * a base point `t₀` with `F(t₀) ≠ 0` and an existing representation `F(t₀) = r₀² + D s₀²`,
  construct rational AFFINE `g, k` with `F = g² + D k²` identically and `g(t₀) = r₀`, `k(t₀) = s₀`.

  The reviewer's `α(T) = α₀ · w(T)/w(t₀)` with `w(T) = T + B/(2A) + (h/(2A))√(−D)` is carried out in
  coordinates, so no field extension is constructed: `α` is a pair of rational affine polynomials and
  the norm identity is a polynomial identity.  Denominators are cleared once, over `2N` and `4AN`
  with `N = F(t₀)`.  The case `δ = 0` is the instance `h = 0` and needs no separate treatment.  The
  cases `A = 0` (constant and genuinely linear `F`) are NOT in scope here — the reviewer handles them
  separately, and `hA` excludes them.

  `integer_ap_section` is the denominator-clearing step of N3.2: an affine rational section that is
  integral at `t₀` is integral on the whole arithmetic progression `t₀ + M ℤ`, with `M` the product
  of the two slope denominators.

  Coefficients of the `linear_combination` below were derived symbolically (sympy) before the Lean
  was written, and the witness was checked on random rational instances.

  Claim tags: [P] (std-3).  Baseline read-only.
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.LinearCombination.Lemmas

namespace DiophCompression.ResearchUpgrade

/-- **N2.3 — anchored affine norm section.** -/
theorem anchored_affine_norm_section (D A B C h t₀ r₀ s₀ : ℚ) (hA : A ≠ 0)
    (hδ : B ^ 2 - 4 * A * C = -D * h ^ 2)
    (ht₀ : A * t₀ ^ 2 + B * t₀ + C ≠ 0)
    (hrep : A * t₀ ^ 2 + B * t₀ + C = r₀ ^ 2 + D * s₀ ^ 2) :
    ∃ g₁ g₀ k₁ k₀ : ℚ,
      (∀ T : ℚ, A * T ^ 2 + B * T + C = (g₁ * T + g₀) ^ 2 + D * (k₁ * T + k₀) ^ 2) ∧
        g₁ * t₀ + g₀ = r₀ ∧ k₁ * t₀ + k₀ = s₀ := by
  set N : ℚ := A * t₀ ^ 2 + B * t₀ + C with hN
  set U : ℚ := 2 * A * t₀ + B with hU
  refine ⟨(U * r₀ + D * h * s₀) / (2 * N),
    (U * (r₀ * B - D * s₀ * h) + D * h * (s₀ * B + r₀ * h)) / (4 * A * N),
    (U * s₀ - h * r₀) / (2 * N),
    (U * (s₀ * B + r₀ * h) - h * (r₀ * B - D * s₀ * h)) / (4 * A * N), ?_, ?_, ?_⟩
  · intro T
    linear_combination (norm := (field_simp; ring))
      (-(r₀ ^ 2 + D * s₀ ^ 2) *
          (4 * A ^ 2 * T ^ 2 + 4 * A * B * T + 4 * A ^ 2 * t₀ ^ 2 + 4 * A * B * t₀
            + 4 * A * C + B ^ 2 + D * h ^ 2) / (16 * A ^ 2 * N ^ 2)) * hδ
        + ((A * T ^ 2 + B * T + C) / N) * hrep
  · linear_combination (norm := (field_simp; ring)) (r₀ / (4 * A * N)) * hδ
  · linear_combination (norm := (field_simp; ring)) (s₀ / (4 * A * N)) * hδ

/-- **Denominator clearing (the N3.2 step).**  An affine rational section taking integer values at
`t₀` takes integer values on the whole arithmetic progression `t₀ + M ℤ`, where `M` is the product
of the two slope denominators. -/
theorem integer_ap_section (g₁ g₀ k₁ k₀ t₀ : ℚ) (r₀ s₀ : ℤ)
    (hg : g₁ * t₀ + g₀ = (r₀ : ℚ)) (hk : k₁ * t₀ + k₀ = (s₀ : ℚ)) :
    ∃ M : ℕ, 0 < M ∧ ∀ s : ℤ, ∃ a b : ℤ,
      g₁ * (t₀ + (M : ℚ) * (s : ℚ)) + g₀ = (a : ℚ) ∧
        k₁ * (t₀ + (M : ℚ) * (s : ℚ)) + k₀ = (b : ℚ) := by
  have hgn : (g₁.num : ℚ) = g₁ * (g₁.den : ℚ) := by
    have hh := Rat.num_div_den g₁
    have hd : ((g₁.den : ℚ)) ≠ 0 := by exact_mod_cast (Rat.den_pos g₁).ne'
    field_simp at hh
    linear_combination hh
  have hkn : (k₁.num : ℚ) = k₁ * (k₁.den : ℚ) := by
    have hh := Rat.num_div_den k₁
    have hd : ((k₁.den : ℚ)) ≠ 0 := by exact_mod_cast (Rat.den_pos k₁).ne'
    field_simp at hh
    linear_combination hh
  refine ⟨g₁.den * k₁.den, Nat.mul_pos (Rat.den_pos g₁) (Rat.den_pos k₁), fun s => ?_⟩
  refine ⟨r₀ + g₁.num * (k₁.den : ℤ) * s, s₀ + (g₁.den : ℤ) * k₁.num * s, ?_, ?_⟩
  · push_cast
    linear_combination hg - ((k₁.den : ℚ) * (s : ℚ)) * hgn
  · push_cast
    linear_combination hk - ((g₁.den : ℚ) * (s : ℚ)) * hkn

/-- The two joined: under the N2.2 conclusion and an INTEGER base representation, the quadratic has
an integer affine section on a full arithmetic progression through `t₀`. -/
theorem anchored_integer_ap_section (D A B C h t₀ : ℚ) (r₀ s₀ : ℤ) (hA : A ≠ 0)
    (hδ : B ^ 2 - 4 * A * C = -D * h ^ 2)
    (ht₀ : A * t₀ ^ 2 + B * t₀ + C ≠ 0)
    (hrep : A * t₀ ^ 2 + B * t₀ + C = (r₀ : ℚ) ^ 2 + D * (s₀ : ℚ) ^ 2) :
    ∃ (g₁ g₀ k₁ k₀ : ℚ) (M : ℕ), 0 < M ∧
      (∀ T : ℚ, A * T ^ 2 + B * T + C = (g₁ * T + g₀) ^ 2 + D * (k₁ * T + k₀) ^ 2) ∧
        (∀ s : ℤ, ∃ a b : ℤ,
          g₁ * (t₀ + (M : ℚ) * (s : ℚ)) + g₀ = (a : ℚ) ∧
            k₁ * (t₀ + (M : ℚ) * (s : ℚ)) + k₀ = (b : ℚ)) := by
  obtain ⟨g₁, g₀, k₁, k₀, hid, hga, hka⟩ :=
    anchored_affine_norm_section D A B C h t₀ (r₀ : ℚ) (s₀ : ℚ) hA hδ ht₀ hrep
  obtain ⟨M, hM, hint⟩ := integer_ap_section g₁ g₀ k₁ k₀ t₀ r₀ s₀ hga hka
  exact ⟨g₁, g₀, k₁, k₀, M, hM, hid, hint⟩

end DiophCompression.ResearchUpgrade
