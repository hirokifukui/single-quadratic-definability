/-
  Unconditional.lean — Gate-20, discharging N1.1b.

  `NonResidue.lean` closes the last leaf `NonResidueClass`, and
  `CharacterSeparationReduction.lean` reduces `CharacterSeparation` to it.  So every result that
  was carried with `CharacterSeparation` in its signature is now UNCONDITIONAL, and this file says
  so in the type rather than in a comment.

  Headline: `rgen_weakCosetNF_definite` — a total, unique-output, positive-definite one-input /
  one-witness quadratic relation has its output affine on one full coset, with no hypothesis
  beyond the displayed ones.  That is N3.3 for the `n = 1, r = 1` positive-definite branch,
  unconditionally.

  Claim tags: [P] (std-3), no open hypothesis.  Baseline read-only.
-/
import ResearchUpgrade.AffineSolution
import ResearchUpgrade.CosetWrapper
import ResearchUpgrade.NonResidue
import ResearchUpgrade.Transfer

namespace DiophCompression.ResearchUpgrade

/-- **N1.1b, discharged.** -/
theorem characterSeparation_holds : CharacterSeparation :=
  characterSeparation_of_nonResidueClass nonResidueClass_holds

/-- N2.2 in positive form, unconditional. -/
theorem discriminant_trichotomy' (D A B C : ℤ) (hA : A ≠ 0) (hD : 0 < D)
    (htotal : ∀ t : ℤ, ∃ r s : ℚ,
      ((A * t ^ 2 + B * t + C : ℤ) : ℚ) = r ^ 2 + (D : ℚ) * s ^ 2) :
    ∃ h : ℚ, ((B ^ 2 - 4 * A * C : ℤ) : ℚ) = -(D : ℚ) * h ^ 2 :=
  discriminant_trichotomy characterSeparation_holds D A B C hA hD htotal

/-- The ℚ-layer positive form, unconditional. -/
theorem rat_discriminant_of_total' (A' B' C' D : ℚ) (hD : 0 < D) (hA' : A' ≠ 0)
    (hrep : ∀ t : ℤ, ∃ x z : ℚ,
      A' * (t : ℚ) ^ 2 + B' * (t : ℚ) + C' = x ^ 2 + D * z ^ 2) :
    ∃ h' : ℚ, B' ^ 2 - 4 * A' * C' = -D * h' ^ 2 :=
  rat_discriminant_of_total characterSeparation_holds A' B' C' D hD hA' hrep

/-- The affine solution family, unconditional. -/
theorem Rgen_affine_solution' (a b c d e f g h i j : ℤ)
    (ha : 0 < a) (hΔ : 0 < 4 * a * c - b ^ 2)
    (hT : RelTotal (Rgen a b c d e f g h i j)) :
    ∃ (t₀ : ℤ) (y₁ y₀ u₁ u₀ : ℚ) (M : ℕ), 0 < M ∧
      (∀ T : ℚ, PQ (a : ℚ) b c d e f g h i j T (y₁ * T + y₀) (u₁ * T + u₀) = 0) ∧
      (∀ n : ℤ, ∃ Y U : ℤ,
        y₁ * ((t₀ : ℚ) + (M : ℚ) * (n : ℚ)) + y₀ = (Y : ℚ) ∧
          u₁ * ((t₀ : ℚ) + (M : ℚ) * (n : ℚ)) + u₀ = (U : ℚ)) :=
  Rgen_affine_solution characterSeparation_holds a b c d e f g h i j ha hΔ hT

/-- **N3.3 for the `n = 1, r = 1` positive-definite branch, UNCONDITIONAL.**  A total,
unique-output quadratic relation whose `(y,u)`-part is positive definite has its output affine on
one full coset. -/
theorem rgen_weakCosetNF_definite (a b c d e f g h i j : ℤ)
    (ha : 0 < a) (hΔ : 0 < 4 * a * c - b ^ 2)
    (hT : RelTotal (Rgen a b c d e f g h i j))
    (hUq : RelUnique (Rgen a b c d e f g h i j)) :
    WeakScalarCosetNF (rgenOut a b c d e f g h i j hT) :=
  rgen_weakCosetNF_of_definite characterSeparation_holds a b c d e f g h i j ha hΔ hT hUq

end DiophCompression.ResearchUpgrade
