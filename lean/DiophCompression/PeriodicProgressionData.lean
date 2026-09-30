/-
  DiophCompression/PeriodicProgressionData.lean — APAL Structural Theory Gate 5, 必須F step 2
  (periodic leaves) (s28, 2026-09-02, claude.ai direct).

  Leaf-level data forms built on `PeriodicProgressionCore`: branch B1b (uncoupled rank-one, m₂ ≠ 0) and
  branch A3 (full-rank block, α = β = 0). Both periodicity proofs are the sealed ones, reused verbatim.
  Branch B3 lives in MovingModulusGeneral.lean because its periodicity uses a private lemma of that file.
  No sorry; std-3.
-/
import DiophCompression.PeriodicProgressionCore
import DiophCompression.SemanticQuadraticTwoWitness.RankOne
import DiophCompression.SemanticQuadraticMatrix.FullRankGeneric

namespace DiophCompression

namespace SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadratic

/-- Branch B1b (uncoupled rank-one leaf, `m₂ ≠ 0`) in data form: the fibre is empty, or it contains the
    explicit progression of period `|m₂|`. The periodicity argument is the one of `rank_one_uncoupled`. -/
theorem rank_one_uncoupled_periodic_data (A B₁ k l m₁ m₂ q : ℤ) (hm₂ : m₂ ≠ 0) :
    Nonempty (PeriodicProgression (fiberSet2 A B₁ 0 k 0 0 l m₁ m₂ q)) ∨
      fiberSet2 A B₁ 0 k 0 0 l m₁ m₂ q = ∅ := by
  have hM : 1 ≤ m₂.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hm₂)
  have hper : ∀ c : ℕ, c ∈ fiberSet2 A B₁ 0 k 0 0 l m₁ m₂ q ↔ c + m₂.natAbs ∈ fiberSet2 A B₁ 0 k 0 0 l m₁ m₂ q := by
    intro c
    have hm₂' : (m₂.natAbs : ℤ) = |m₂| := Int.natCast_natAbs m₂
    have hdvd : m₂ ∣ ((c + m₂.natAbs : ℕ) : ℤ) - (c : ℤ) := by
      push_cast; rw [add_sub_cancel_left]; exact self_dvd_abs m₂
    have key : ∀ c₁ c₂ : ℤ, m₂ ∣ c₂ - c₁ → ∀ u : ℤ,
        (∃ v, fq2 A B₁ 0 k 0 0 l m₁ m₂ q c₁ u v = 0) → ∃ v, fq2 A B₁ 0 k 0 0 l m₁ m₂ q c₂ u v = 0 := by
      intro c₁ c₂ hd u ⟨v, hv⟩
      obtain ⟨w, hw⟩ := hd
      -- Q(c₂,u) − Q(c₁,u) = (c₂ − c₁)(A(c₂ + c₁) + B₁ u + l) = m₂ w (…)
      refine ⟨v - w * (A * (c₂ + c₁) + B₁ * u + l), ?_⟩
      rw [fq2_rank_one] at hv ⊢
      have : qOne A B₁ k l m₁ q c₂ u - qOne A B₁ k l m₁ q c₁ u = (c₂ - c₁) * (A * (c₂ + c₁) + B₁ * u + l) := by
        unfold qOne; ring
      simp only [zero_mul, zero_add] at hv ⊢
      linear_combination hv + this + (A * (c₂ + c₁) + B₁ * u + l) * hw
    constructor
    · rintro ⟨u, v, huv⟩
      obtain ⟨v', hv'⟩ := key (c : ℤ) _ hdvd u ⟨v, huv⟩
      exact ⟨u, v', hv'⟩
    · rintro ⟨u, v, huv⟩
      obtain ⟨v', hv'⟩ := key _ (c : ℤ) ((dvd_neg).mpr hdvd |> fun h => by
        rw [neg_sub] at h; exact h) u ⟨v, huv⟩
      exact ⟨u, v', hv'⟩
  exact periodicProgression_or_empty _ _ hM hper

end SemanticQuadraticTwoWitness


namespace SemanticQuadraticMatrix

/-- Branch A3 (full-rank block, α = β = 0) in data form: the fibre is empty, or it contains the explicit
    progression of period `|det (witnessGram C)|`. The periodicity is the sealed
    `alpha_zero_beta_zero_periodic_M`. -/
theorem alpha_zero_beta_zero_periodic_data {r : ℕ} (A : ℤ) (B : Fin r → ℤ)
    (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ) (m : Fin r → ℤ) (q : ℤ)
    (hN : (witnessGram C).det ≠ 0) (hα : alphaMatrix A B C = 0) (hβ : betaMatrix B C l m = 0) :
    Nonempty (PeriodicProgression (fiberSetM A B C l m q)) ∨ fiberSetM A B C l m q = ∅ :=
  periodicProgression_or_empty _ _
    (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hN))
    (alpha_zero_beta_zero_periodic_M A B C l m q hN hα hβ)

end SemanticQuadraticMatrix

end DiophCompression

#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_one_uncoupled_periodic_data
#print axioms DiophCompression.SemanticQuadraticMatrix.alpha_zero_beta_zero_periodic_data
