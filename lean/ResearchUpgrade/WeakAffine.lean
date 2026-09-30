/-
  WeakAffine.lean — Gate-20 Packet N2/N3, the POSITIVE direction.

  N2.2 is proved in contrapositive form (a separating prime kills totality).  The positive form
  — "totality ⇒ δ = 0 ∨ δ = −D h²" — needs exactly one extra input, and this file names it rather
  than hiding it:

      CharacterSeparation :=
        ∀ D δ ≠ 0, δ/(−D) not a rational square → a residue witness for (D, δ) exists

  That is N1.1b verbatim, carried as a `Prop` argument.  It is NEVER an `axiom`: every theorem
  below that uses it shows it in its type, and `#print axioms` stays std-3.  For any CONCRETE pair
  the hypothesis is discharged by a single prime certificate
  (`residueWitness_of_prime_std`, PrimeCertificate.lean), so the conditionality is uniformity, not
  provability.

  * `exists_nonroot`            — a genuinely quadratic integer polynomial is nonzero at one of
                                  `t = 0, 1, 2` (needed to anchor).
  * `discriminant_trichotomy`   — the POSITIVE form of N2.2, conditional on `CharacterSeparation`.
  * `model_has_affine_section`  — the positive chain: total representability of an integer
                                  `A t² + B t + C` by `x² + D y²` ⇒ a GLOBAL rational affine
                                  section `F = g² + D k²`, anchored at an integer base point.

  Reviewer regression control #18: the conditional statement is never moved to an unconditional
  root name.  Everything conditional on `CharacterSeparation` carries it in the signature.

  Claim tags: [P] (std-3), with `CharacterSeparation` an explicit [OPEN] hypothesis.
  Baseline read-only.
-/
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.LinearCombination
import ResearchUpgrade.AnchoredSection
import ResearchUpgrade.DiscriminantRigidity
import ResearchUpgrade.SeparatingPrime

namespace DiophCompression.ResearchUpgrade

/-- **N1.1b as a named hypothesis.**  If `δ/(−D)` is not a rational square, the pair `(D, δ)` has a
residue witness.  Discharged for any concrete pair by a prime certificate. -/
def CharacterSeparation : Prop :=
  ∀ D δ : ℤ, 0 < D → δ ≠ 0 → (¬ ∃ h : ℚ, (δ : ℚ) = -(D : ℚ) * h ^ 2) →
    ∃ M a : ℕ, ResidueWitness D δ M a

/-- A genuinely quadratic integer polynomial is nonzero at one of `0, 1, 2`. -/
theorem exists_nonroot (A B C : ℤ) (hA : A ≠ 0) :
    ∃ t₀ : ℤ, A * t₀ ^ 2 + B * t₀ + C ≠ 0 := by
  by_cases h0 : A * 0 ^ 2 + B * 0 + C = 0
  · by_cases h1 : A * 1 ^ 2 + B * 1 + C = 0
    · refine ⟨2, fun h2 => ?_⟩
      have e0 : C = 0 := by linear_combination h0
      have e1 : A + B + C = 0 := by linear_combination h1
      have e2 : 4 * A + 2 * B + C = 0 := by linear_combination h2
      omega
    · exact ⟨1, h1⟩
  · exact ⟨0, h0⟩

/-- **The positive form of N2.2**, conditional on `CharacterSeparation`: if the integer quadratic
`A t² + B t + C` is represented by `x² + D y²` at every integer, then its discriminant is `0` or
`−D h²`. -/
theorem discriminant_trichotomy (hCS : CharacterSeparation) (D A B C : ℤ)
    (hA : A ≠ 0) (hD : 0 < D)
    (htotal : ∀ t : ℤ, ∃ r s : ℚ,
      ((A * t ^ 2 + B * t + C : ℤ) : ℚ) = r ^ 2 + (D : ℚ) * s ^ 2) :
    ∃ h : ℚ, ((B ^ 2 - 4 * A * C : ℤ) : ℚ) = -(D : ℚ) * h ^ 2 := by
  by_cases hδ : B ^ 2 - 4 * A * C = 0
  · exact ⟨0, by rw [hδ]; push_cast; ring⟩
  · by_contra hno
    obtain ⟨M, a, hw⟩ := hCS D (B ^ 2 - 4 * A * C) hD hδ hno
    exact discriminant_rigidity_of_residueWitness D A B C hA M a hw htotal

/-- **The positive chain.**  Total representability of an integer quadratic by `x² + D y²` yields a
GLOBAL rational affine section, anchored at an integer base point where the polynomial does not
vanish. -/
theorem model_has_affine_section (hCS : CharacterSeparation) (D A B C : ℤ)
    (hA : A ≠ 0) (hD : 0 < D)
    (htotal : ∀ t : ℤ, ∃ r s : ℚ,
      ((A * t ^ 2 + B * t + C : ℤ) : ℚ) = r ^ 2 + (D : ℚ) * s ^ 2) :
    ∃ (t₀ : ℤ) (g₁ g₀ k₁ k₀ r₀ s₀ : ℚ),
      ((A : ℚ) * (t₀ : ℚ) ^ 2 + (B : ℚ) * (t₀ : ℚ) + (C : ℚ) ≠ 0) ∧
      (∀ T : ℚ, (A : ℚ) * T ^ 2 + (B : ℚ) * T + (C : ℚ)
        = (g₁ * T + g₀) ^ 2 + (D : ℚ) * (k₁ * T + k₀) ^ 2) ∧
      g₁ * (t₀ : ℚ) + g₀ = r₀ ∧ k₁ * (t₀ : ℚ) + k₀ = s₀ := by
  obtain ⟨h, hh⟩ := discriminant_trichotomy hCS D A B C hA hD htotal
  obtain ⟨t₀, ht₀⟩ := exists_nonroot A B C hA
  have haQ : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have ht₀Q : (A : ℚ) * (t₀ : ℚ) ^ 2 + (B : ℚ) * (t₀ : ℚ) + (C : ℚ) ≠ 0 := by
    intro hz
    apply ht₀
    have : ((A * t₀ ^ 2 + B * t₀ + C : ℤ) : ℚ) = 0 := by push_cast; linear_combination hz
    exact_mod_cast this
  have hδQ : (B : ℚ) ^ 2 - 4 * (A : ℚ) * (C : ℚ) = -(D : ℚ) * h ^ 2 := by
    have hc : ((B ^ 2 - 4 * A * C : ℤ) : ℚ) = (B : ℚ) ^ 2 - 4 * (A : ℚ) * (C : ℚ) := by
      push_cast; ring
    linear_combination hh - hc
  obtain ⟨r₀, s₀, hrep⟩ := htotal t₀
  have hrepQ : (A : ℚ) * (t₀ : ℚ) ^ 2 + (B : ℚ) * (t₀ : ℚ) + (C : ℚ) = r₀ ^ 2 + (D : ℚ) * s₀ ^ 2 := by
    have hc : ((A * t₀ ^ 2 + B * t₀ + C : ℤ) : ℚ)
        = (A : ℚ) * (t₀ : ℚ) ^ 2 + (B : ℚ) * (t₀ : ℚ) + (C : ℚ) := by push_cast; ring
    linear_combination hrep - hc
  obtain ⟨g₁, g₀, k₁, k₀, hid, hga, hka⟩ :=
    anchored_affine_norm_section (D : ℚ) (A : ℚ) (B : ℚ) (C : ℚ) h (t₀ : ℚ) r₀ s₀
      haQ hδQ ht₀Q hrepQ
  exact ⟨t₀, g₁, g₀, k₁, k₀, r₀, s₀, ht₀Q, hid, hga, hka⟩

end DiophCompression.ResearchUpgrade
