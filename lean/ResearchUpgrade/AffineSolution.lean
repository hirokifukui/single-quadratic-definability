/-
  AffineSolution.lean — Gate-20 Packet N3, task N3.3 (positive direction, assembled).

  The inversion.  `model_has_affine_section` gives a section of the SCALAR polynomial `N(t)/a`;
  here it is pushed back through the diagonalisation and the complete-square compiler to the
  OUTPUT of the original relation:

      RelTotal (Rgen a … j), (y,u)-part positive definite, CharacterSeparation
        ⟹ ∃ rational AFFINE y(T), u(T) with P(T, y(T), u(T)) = 0 identically,
           agreeing at an integer base point with an actual integer solution,
           and integral on a full arithmetic progression t₀ + M ℤ.

  The inversion is explicit: with `v₁ = Y + (b/2a)U`, `v₂ = U` the diagonalising coordinates and
  `(g, k)` the scalar section,

      u(T) = (rT + s) + k(T),        y(T) = (pT + q) + g(T) − (b/2a)·k(T).

  Anchoring note (corrects the s46 in-session worry): the anchor is integral IN THE `y, u`
  COORDINATES — it is the original integer solution — even though the diagonalised `v₁` is not.
  So `integer_ap_section` is applied to the `y`- and `u`-sections, not to `(g, k)`.

  All three branches of the reviewer's §4 appear: `A' ≠ 0` (the main case, via N2.3),
  `A' = 0 ∧ B' ≠ 0` (impossible — `not_total_of_linear`), `A' = B' = 0` (constant section).

  Claim tags: [P] (std-3), with `CharacterSeparation` (= N1.1b) an explicit [OPEN] hypothesis
  carried in the signature.  Baseline read-only.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import ResearchUpgrade.AnchoredSection
import ResearchUpgrade.IntegerModel
import ResearchUpgrade.Transfer

namespace DiophCompression.ResearchUpgrade

/-- A genuinely quadratic rational polynomial is nonzero at one of the integers `0, 1, 2`. -/
theorem exists_nonroot_rat (A' B' C' : ℚ) (hA' : A' ≠ 0) :
    ∃ t₀ : ℤ, A' * (t₀ : ℚ) ^ 2 + B' * (t₀ : ℚ) + C' ≠ 0 := by
  by_cases h0 : A' * ((0 : ℤ) : ℚ) ^ 2 + B' * ((0 : ℤ) : ℚ) + C' = 0
  · by_cases h1 : A' * ((1 : ℤ) : ℚ) ^ 2 + B' * ((1 : ℤ) : ℚ) + C' = 0
    · refine ⟨2, fun h2 => hA' ?_⟩
      push_cast at h0 h1 h2
      linarith
    · exact ⟨1, h1⟩
  · exact ⟨0, h0⟩

/-- The scalar affine section, all three branches. -/
theorem scalar_affine_section (hCS : CharacterSeparation) (A' B' C' D : ℚ) (hD : 0 < D)
    (hrep : ∀ t : ℤ, ∃ x z : ℚ,
      A' * (t : ℚ) ^ 2 + B' * (t : ℚ) + C' = x ^ 2 + D * z ^ 2)
    (t₀ : ℤ) (x z : ℚ)
    (hanchor : A' * (t₀ : ℚ) ^ 2 + B' * (t₀ : ℚ) + C' = x ^ 2 + D * z ^ 2)
    (ht₀ : A' ≠ 0 → A' * (t₀ : ℚ) ^ 2 + B' * (t₀ : ℚ) + C' ≠ 0) :
    ∃ g₁ g₀ k₁ k₀ : ℚ,
      (∀ T : ℚ, A' * T ^ 2 + B' * T + C' = (g₁ * T + g₀) ^ 2 + D * (k₁ * T + k₀) ^ 2) ∧
        g₁ * (t₀ : ℚ) + g₀ = x ∧ k₁ * (t₀ : ℚ) + k₀ = z := by
  by_cases hA' : A' = 0
  · by_cases hB' : B' = 0
    · -- constant branch
      refine ⟨0, x, 0, z, fun T => ?_, by ring, by ring⟩
      rw [hA', hB'] at hanchor ⊢
      push_cast at hanchor
      linear_combination hanchor
    · -- genuinely linear: impossible
      exfalso
      rw [hA'] at hrep
      exact not_total_of_linear B' C' D hD hB' hrep
  · obtain ⟨h', hh'⟩ := rat_discriminant_of_total hCS A' B' C' D hD hA' hrep
    exact anchored_affine_norm_section D A' B' C' h' (t₀ : ℚ) x z hA' hh' (ht₀ hA') hanchor

/-- **N3.3 (positive direction).**  A total, positive-definite one-input / one-witness quadratic
relation has a rational AFFINE solution family, anchored at an actual integer solution and
integral on a full arithmetic progression. -/
theorem Rgen_affine_solution (hCS : CharacterSeparation) (a b c d e f g h i j : ℤ)
    (ha : 0 < a) (hΔ : 0 < 4 * a * c - b ^ 2)
    (hT : RelTotal (Rgen a b c d e f g h i j)) :
    ∃ (t₀ : ℤ) (y₁ y₀ u₁ u₀ : ℚ) (M : ℕ), 0 < M ∧
      (∀ T : ℚ, PQ (a : ℚ) b c d e f g h i j T (y₁ * T + y₀) (u₁ * T + u₀) = 0) ∧
      (∀ n : ℤ, ∃ Y U : ℤ,
        y₁ * ((t₀ : ℚ) + (M : ℚ) * (n : ℚ)) + y₀ = (Y : ℚ) ∧
          u₁ * ((t₀ : ℚ) + (M : ℚ) * (n : ℚ)) + u₀ = (U : ℚ)) := by
  have haQ : ((a : ℚ)) ≠ 0 := by
    have : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
    exact this.ne'
  have haQpos : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
  have hΔQpos : (0 : ℚ) < 4 * (a : ℚ) * (c : ℚ) - (b : ℚ) ^ 2 := by
    have hc : ((4 * a * c - b ^ 2 : ℤ) : ℚ) = 4 * (a : ℚ) * (c : ℚ) - (b : ℚ) ^ 2 := by
      push_cast; ring
    rw [← hc]; exact_mod_cast hΔ
  have hDpos := diag_D_pos (a : ℚ) (b : ℚ) (c : ℚ) haQpos hΔQpos
  obtain ⟨p, q, r, s, n₂, n₁, n₀, hid⟩ :=
    complete_square_compiler (a : ℚ) b c d e f g h i j hΔQpos.ne'
  -- the scalar representation, with the witnesses explicit in terms of a solution
  have hanchor_of : ∀ (t : ℤ) (Y U : ℚ),
      PQ (a : ℚ) b c d e f g h i j (t : ℚ) Y U = 0 →
      (n₂ / (a : ℚ)) * (t : ℚ) ^ 2 + (n₁ / (a : ℚ)) * (t : ℚ) + (n₀ / (a : ℚ))
        = ((Y - (p * (t : ℚ) + q)) + ((b : ℚ) / (2 * (a : ℚ))) * (U - (r * (t : ℚ) + s))) ^ 2
          + ((4 * (a : ℚ) * (c : ℚ) - (b : ℚ) ^ 2) / (4 * (a : ℚ) ^ 2))
            * (U - (r * (t : ℚ) + s)) ^ 2 := by
    intro t Y U hYU
    have hF : (a : ℚ) * (Y - (p * (t : ℚ) + q)) ^ 2
        + (b : ℚ) * (Y - (p * (t : ℚ) + q)) * (U - (r * (t : ℚ) + s))
        + (c : ℚ) * (U - (r * (t : ℚ) + s)) ^ 2
        = n₂ * (t : ℚ) ^ 2 + n₁ * (t : ℚ) + n₀ := by
      linear_combination hYU - hid (t : ℚ) Y U
    have hdiag := definite_diagonalization (a : ℚ) (b : ℚ) (c : ℚ) haQ
      (Y - (p * (t : ℚ) + q)) (U - (r * (t : ℚ) + s))
    linear_combination (norm := (field_simp; ring))
      (-(1 : ℚ) / (a : ℚ)) * hF + ((1 : ℚ) / (a : ℚ)) * hdiag
  have htotQ : ∀ t : ℤ, ∃ Y U : ℚ, PQ (a : ℚ) b c d e f g h i j (t : ℚ) Y U = 0 := by
    intro t
    obtain ⟨Y, U, hYU⟩ := hT t
    refine ⟨(Y : ℚ), (U : ℚ), ?_⟩
    rw [← PQ_cast a b c d e f g h i j t Y U, hYU]
    norm_num
  have hrep : ∀ t : ℤ, ∃ X Z : ℚ,
      (n₂ / (a : ℚ)) * (t : ℚ) ^ 2 + (n₁ / (a : ℚ)) * (t : ℚ) + (n₀ / (a : ℚ))
        = X ^ 2 + ((4 * (a : ℚ) * (c : ℚ) - (b : ℚ) ^ 2) / (4 * (a : ℚ) ^ 2)) * Z ^ 2 := by
    intro t
    obtain ⟨Y, U, hYU⟩ := htotQ t
    exact ⟨_, _, hanchor_of t Y U hYU⟩
  -- choose the base point
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℤ, (n₂ / (a : ℚ)) ≠ 0 →
      (n₂ / (a : ℚ)) * (t₀ : ℚ) ^ 2 + (n₁ / (a : ℚ)) * (t₀ : ℚ) + (n₀ / (a : ℚ)) ≠ 0 := by
    by_cases hn : (n₂ / (a : ℚ)) = 0
    · exact ⟨0, fun hc => absurd hn hc⟩
    · obtain ⟨t₀, ht₀⟩ := exists_nonroot_rat (n₂ / (a : ℚ)) (n₁ / (a : ℚ)) (n₀ / (a : ℚ)) hn
      exact ⟨t₀, fun _ => ht₀⟩
  obtain ⟨Ystar, Ustar, hstar⟩ := hT t₀
  have hstarQ : PQ (a : ℚ) b c d e f g h i j (t₀ : ℚ) (Ystar : ℚ) (Ustar : ℚ) = 0 := by
    rw [← PQ_cast a b c d e f g h i j t₀ Ystar Ustar, hstar]; norm_num
  obtain ⟨g₁, g₀, k₁, k₀, hsec, hga, hka⟩ :=
    scalar_affine_section hCS (n₂ / (a : ℚ)) (n₁ / (a : ℚ)) (n₀ / (a : ℚ))
      ((4 * (a : ℚ) * (c : ℚ) - (b : ℚ) ^ 2) / (4 * (a : ℚ) ^ 2)) hDpos hrep t₀
      _ _ (hanchor_of t₀ (Ystar : ℚ) (Ustar : ℚ) hstarQ) ht₀
  -- invert to the (y,u) coordinates
  refine ⟨t₀, p + (g₁ - ((b : ℚ) / (2 * (a : ℚ))) * k₁), q + (g₀ - ((b : ℚ) / (2 * (a : ℚ))) * k₀),
    r + k₁, s + k₀, ?_⟩
  have hyanchor : (p + (g₁ - ((b : ℚ) / (2 * (a : ℚ))) * k₁)) * (t₀ : ℚ)
      + (q + (g₀ - ((b : ℚ) / (2 * (a : ℚ))) * k₀)) = (Ystar : ℚ) := by
    linear_combination hga - ((b : ℚ) / (2 * (a : ℚ))) * hka
  have huanchor : (r + k₁) * (t₀ : ℚ) + (s + k₀) = (Ustar : ℚ) := by
    linear_combination hka
  obtain ⟨M, hM, hAP⟩ :=
    integer_ap_section (p + (g₁ - ((b : ℚ) / (2 * (a : ℚ))) * k₁))
      (q + (g₀ - ((b : ℚ) / (2 * (a : ℚ))) * k₀)) (r + k₁) (s + k₀) (t₀ : ℚ) Ystar Ustar
      hyanchor huanchor
  refine ⟨M, hM, fun T => ?_, hAP⟩
  have hcomp := hid T
    ((p + (g₁ - ((b : ℚ) / (2 * (a : ℚ))) * k₁)) * T + (q + (g₀ - ((b : ℚ) / (2 * (a : ℚ))) * k₀)))
    ((r + k₁) * T + (s + k₀))
  have hdiag := definite_diagonalization (a : ℚ) (b : ℚ) (c : ℚ) haQ
    ((g₁ * T + g₀) - ((b : ℚ) / (2 * (a : ℚ))) * (k₁ * T + k₀)) (k₁ * T + k₀)
  have hs := hsec T
  linear_combination (norm := (field_simp; ring)) hcomp + hdiag - (a : ℚ) * hs

end DiophCompression.ResearchUpgrade
