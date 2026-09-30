/-
  DiophCompression/SemanticQuadraticTwoWitness/RankTwoAlphaZero.lean — GPT r07 必須7 (s8, claude.ai direct).
  α = 0: β = 0 ⇒ membership periodic in c mod |N| ⇒ (Per); β ≠ 0 ⇒ progression along a direction w with
  β·wt(w) < 0 (z = −2B₀t − N·wt(w)·β·t², s = βt), or the root bound c ≤ |γ| when wt ≥ 0 and β > 0. No Pell.
  Frozen statement: `TwoWitness_STATEMENTS_v2.lean` (md5 3e2c4c02). Mathematics: CLASSIFICATION_2W.md §3.4.
-/
import DiophCompression.SemanticQuadraticTwoWitness.Bounds2W
import DiophCompression.SemanticQuadraticTwoWitness.Bridge2W

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadraticGeneral

/-- Periodicity when α = β = 0: c ∈ S ↔ c + |N| ∈ S. -/
theorem alpha_zero_beta_zero_periodic (A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q : ℤ) (hN : nW C₁₁ C₁₂ C₂₂ ≠ 0)
    (hα : schur A B₁ B₂ C₁₁ C₁₂ C₂₂ = 0) (hβ : betaR B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ = 0) (c : ℕ) :
    c ∈ fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q
      ↔ c + (nW C₁₁ C₁₂ C₂₂).natAbs ∈ fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q := by
  have hsign : nW C₁₁ C₁₂ C₂₂ * (nW C₁₁ C₁₂ C₂₂).sign = ((nW C₁₁ C₁₂ C₂₂).natAbs : ℤ) :=
    Int.mul_sign_self _
  have hcast : (((c + (nW C₁₁ C₁₂ C₂₂).natAbs : ℕ)) : ℤ) = (c : ℤ) + ((nW C₁₁ C₁₂ C₂₂).natAbs : ℤ) := by
    exact Nat.cast_add _ _
  constructor
  · rintro ⟨u, v, huv⟩
    have hzs : nW C₁₁ C₁₂ C₂₂ * schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * ((nW C₁₁ C₁₂ C₂₂).sign) ^ 2
        + (2 * schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * (c : ℤ) + betaR B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂) * (nW C₁₁ C₁₂ C₂₂).sign
        + 2 * wtBil C₁₁ C₁₂ C₂₂ (y1 B₁ C₁₁ C₁₂ m₁ (c : ℤ) u v) (y2 B₂ C₁₂ C₂₂ m₂ (c : ℤ) u v) 0 0 * 0
        + nW C₁₁ C₁₂ C₂₂ * wt C₁₁ C₁₂ C₂₂ 0 0 * 0 ^ 2 = 0 := by
      rw [hα, hβ]; ring
    obtain ⟨u', v', h'⟩ := scaled_line_solution A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q (c : ℤ) u v 0 0 _ 0 hN huv hzs
    refine ⟨u', v', ?_⟩
    rw [hcast, ← hsign]; exact h'
  · rintro ⟨u, v, huv⟩
    have hzs : nW C₁₁ C₁₂ C₂₂ * schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * (-(nW C₁₁ C₁₂ C₂₂).sign) ^ 2
        + (2 * schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * ((c + (nW C₁₁ C₁₂ C₂₂).natAbs : ℕ) : ℤ)
            + betaR B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂) * (-(nW C₁₁ C₁₂ C₂₂).sign)
        + 2 * wtBil C₁₁ C₁₂ C₂₂ (y1 B₁ C₁₁ C₁₂ m₁ ((c + (nW C₁₁ C₁₂ C₂₂).natAbs : ℕ) : ℤ) u v)
            (y2 B₂ C₁₂ C₂₂ m₂ ((c + (nW C₁₁ C₁₂ C₂₂).natAbs : ℕ) : ℤ) u v) 0 0 * 0
        + nW C₁₁ C₁₂ C₂₂ * wt C₁₁ C₁₂ C₂₂ 0 0 * 0 ^ 2 = 0 := by
      rw [hα, hβ]; ring
    obtain ⟨u', v', h'⟩ := scaled_line_solution A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q _ u v 0 0 _ 0 hN huv hzs
    refine ⟨u', v', ?_⟩
    have e : ((c + (nW C₁₁ C₁₂ C₂₂).natAbs : ℕ) : ℤ) + nW C₁₁ C₁₂ C₂₂ * (-(nW C₁₁ C₁₂ C₂₂).sign) = (c : ℤ) := by
      rw [hcast]; linear_combination (-1 : ℤ) * hsign
    rw [e] at h'; exact h'

theorem rank_two_alpha_zero_periodic_or_progression (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ)
    (hN : nW C₁₁ C₁₂ C₂₂ ≠ 0) (hα : schur A B₁ B₂ C₁₁ C₁₂ C₂₂ = 0)
    (hpos : ∃ w₁ w₂ : ℤ, 0 < wt C₁₁ C₁₂ C₂₂ w₁ w₂)
    (hneg : (∃ w₁ w₂ : ℤ, wt C₁₁ C₁₂ C₂₂ w₁ w₂ < 0) ∨ (∀ Y₁ Y₂ : ℤ, 0 ≤ wt C₁₁ C₁₂ C₂₂ Y₁ Y₂)) :
    Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  refine ⟨(kGamma C₁₁ C₁₂ C₂₂).toNat, ?_⟩
  intro l m₁ m₂ q
  have hK : (((kGamma C₁₁ C₁₂ C₂₂).toNat : ℕ) : ℤ) = kGamma C₁₁ C₁₂ C₂₂ :=
    Int.toNat_of_nonneg (kGamma_nonneg _ _ _)
  obtain ⟨β, hβdef⟩ : ∃ β : ℤ, β = betaR B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ := ⟨_, rfl⟩
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℤ, γ = gammaR C₁₁ C₁₂ C₂₂ m₁ m₂ q := ⟨_, rfl⟩
  by_cases hβ : β = 0
  · -- periodic
    have hM : 1 ≤ (nW C₁₁ C₁₂ C₂₂).natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hN)
    have hper := alpha_zero_beta_zero_periodic A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q hN hα (by rw [← hβdef]; exact hβ)
    rcases periodic_infinite_or_empty _ _ hM hper with hinf | hemp
    · exact Or.inl hinf
    · right; intro c hc; rw [hemp] at hc; exact absurd hc (Set.notMem_empty c)
  · have hdir : (∃ w₁ w₂ : ℤ, β * wt C₁₁ C₁₂ C₂₂ w₁ w₂ < 0)
        ∨ (0 < β ∧ ∀ Y₁ Y₂ : ℤ, 0 ≤ wt C₁₁ C₁₂ C₂₂ Y₁ Y₂) := by
      rcases lt_or_gt_of_ne hβ with hβn | hβp
      · obtain ⟨w₁, w₂, hw⟩ := hpos
        exact Or.inl ⟨w₁, w₂, mul_neg_of_neg_of_pos hβn hw⟩
      · rcases hneg with ⟨w₁, w₂, hw⟩ | hnn
        · exact Or.inl ⟨w₁, w₂, mul_neg_of_pos_of_neg hβp hw⟩
        · exact Or.inr ⟨hβp, hnn⟩
    rcases hdir with ⟨w₁, w₂, hw⟩ | ⟨hβp, hnn⟩
    · -- progression
      by_cases hne : (fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q).Nonempty
      · left
        obtain ⟨c₀, u₀, v₀, h0⟩ := hne
        apply fiberSet2_infinite_of_unbounded
        intro k
        obtain ⟨N, hNdef⟩ : ∃ N : ℤ, N = nW C₁₁ C₁₂ C₂₂ := ⟨_, rfl⟩
        obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℤ, B₀ = wtBil C₁₁ C₁₂ C₂₂ (y1 B₁ C₁₁ C₁₂ m₁ (c₀ : ℤ) u₀ v₀)
          (y2 B₂ C₁₂ C₂₂ m₂ (c₀ : ℤ) u₀ v₀) w₁ w₂ := ⟨_, rfl⟩
        obtain ⟨Wt, hWt⟩ : ∃ Wt : ℤ, Wt = wt C₁₁ C₁₂ C₂₂ w₁ w₂ := ⟨_, rfl⟩
        rw [← hWt] at hw
        obtain ⟨t, ht⟩ : ∃ t : ℤ, t = (k : ℤ) + |2 * N * B₀| + (c₀ : ℤ) + 1 := ⟨_, rfl⟩
        have ht1 : 1 ≤ t := by
          rw [ht]; have := abs_nonneg (2 * N * B₀)
          have hk0 : (0 : ℤ) ≤ k := by positivity
          have hc0' : (0 : ℤ) ≤ c₀ := by positivity
          linarith
        have htk : (k : ℤ) + |2 * N * B₀| + 1 ≤ t := by rw [ht]; linarith
        obtain ⟨z, hz⟩ : ∃ z : ℤ, z = -2 * B₀ * t - N * Wt * β * t ^ 2 := ⟨_, rfl⟩
        have hzs : nW C₁₁ C₁₂ C₂₂ * schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * z ^ 2
            + (2 * schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * (c₀ : ℤ) + betaR B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂) * z
            + 2 * wtBil C₁₁ C₁₂ C₂₂ (y1 B₁ C₁₁ C₁₂ m₁ (c₀ : ℤ) u₀ v₀) (y2 B₂ C₁₂ C₂₂ m₂ (c₀ : ℤ) u₀ v₀) w₁ w₂
                * (β * t)
            + nW C₁₁ C₁₂ C₂₂ * wt C₁₁ C₁₂ C₂₂ w₁ w₂ * (β * t) ^ 2 = 0 := by
          rw [hα, ← hβdef, ← hB₀, ← hWt, ← hNdef, hz]; ring
        obtain ⟨u, v, huv⟩ := scaled_line_solution A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q (c₀ : ℤ) u₀ v₀ w₁ w₂ z (β * t)
          hN h0 hzs
        refine ⟨(c₀ : ℤ) + nW C₁₁ C₁₂ C₂₂ * z, ?_, u, v, huv⟩
        rw [← hNdef, hz]
        -- c₀ + N(−2B₀t − N Wt β t²) = c₀ − 2NB₀ t + (N²·(−Wt β)) t² ≥ k
        have ha : 1 ≤ N ^ 2 * (-(Wt * β)) := by
          have h1 : 1 ≤ N ^ 2 := by
            have : N ≠ 0 := by rw [hNdef]; exact hN
            have : 0 < N ^ 2 := by positivity
            omega
          have h2 : 1 ≤ -(Wt * β) := by
            have : Wt * β < 0 := by rw [mul_comm]; exact hw
            omega
          nlinarith
        have hc₀ : (0 : ℤ) ≤ c₀ := by positivity
        have habs : -|2 * N * B₀| ≤ 2 * N * B₀ := neg_abs_le _
        have hkey : (c₀ : ℤ) + N * (-2 * B₀ * t - N * Wt * β * t ^ 2)
            = (c₀ : ℤ) - (2 * N * B₀) * t + (N ^ 2 * (-(Wt * β))) * t ^ 2 := by ring
        rw [hkey]
        have h3 : (N ^ 2 * (-(Wt * β))) * t ^ 2 ≥ t ^ 2 := by nlinarith [sq_nonneg t]
        have h4 : -(2 * N * B₀) * t ≥ -|2 * N * B₀| * t := by
          have := mul_le_mul_of_nonneg_right (le_abs_self (2 * N * B₀)) (by linarith : (0 : ℤ) ≤ t)
          linarith
        nlinarith
      · right; intro c hc; exact absurd ⟨c, hc⟩ hne
    · -- root bound
      right
      intro c hc
      obtain ⟨u, v, huv⟩ := hc
      have id := rank_two_identity A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q (c : ℤ) u v
      rw [huv, mul_zero, hα, ← hβdef, ← hγdef] at id
      have hwt := hnn (y1 B₁ C₁₁ C₁₂ m₁ (c : ℤ) u v) (y2 B₂ C₁₂ C₂₂ m₂ (c : ℤ) u v)
      have h1 : β * (c : ℤ) ≤ |γ| := by
        have := neg_le_abs γ; linarith
      have hc0 : (0 : ℤ) ≤ c := by positivity
      have h2 : (c : ℤ) ≤ β * (c : ℤ) := le_mul_of_one_le_left hc0 (by omega)
      have hγ := gammaR_abs_le C₁₁ C₁₂ C₂₂ m₁ m₂ q
      rw [← hγdef] at hγ
      have h3 := fbound2_core_ge_gamma l m₁ m₂ q
      have hKnn := kGamma_nonneg C₁₁ C₁₂ C₂₂
      unfold fbound2
      rw [hK]
      calc (c : ℤ) ≤ β * c := h2
        _ ≤ |γ| := h1
        _ ≤ kGamma C₁₁ C₁₂ C₂₂ * ((1 + |m₁| + |m₂|) ^ 2 + |q|) := hγ
        _ ≤ kGamma C₁₁ C₁₂ C₂₂ * ((1 + |l| + |m₁| + |m₂|) ^ 2 + |q|) := mul_le_mul_of_nonneg_left h3 hKnn

end DiophCompression.SemanticQuadraticTwoWitness
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_two_alpha_zero_periodic_or_progression
