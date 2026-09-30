/-
  DiophCompression/SemanticQuadraticTwoWitness/RankTwoLeaves.lean — s8 (claude.ai direct): the rank-2 leaves.
  Definite block (oriented Schur complement > 0 / = 0 / < 0), split block, anisotropic block; each is
  the generic theorem `rank_two_dichotomy_of_line_direction` with the matching direction lemma, or the
  α = 0 theorem, or the root bound (definite, α_or > 0). Frozen statements: `TwoWitness_STATEMENTS_v2.lean` (md5 3e2c4c02).
  Mathematics: CLASSIFICATION_2W.md §3.5.
-/
import DiophCompression.SemanticQuadraticTwoWitness.SignNormalisation
import DiophCompression.SemanticQuadraticTwoWitness.RankTwoGeneric
import DiophCompression.SemanticQuadraticTwoWitness.RankTwoAlphaZero

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadraticGeneral

/-! ### Facts about the adjugate form -/

theorem discW_neg (C₁₁ C₁₂ C₂₂ : ℤ) : discW (-C₁₁) (-C₁₂) (-C₂₂) = discW C₁₁ C₁₂ C₂₂ := by
  unfold discW; ring

theorem nW_eq_neg_discW (C₁₁ C₁₂ C₂₂ : ℤ) : nW C₁₁ C₁₂ C₂₂ = - discW C₁₁ C₁₂ C₂₂ := by
  unfold nW discW; ring

theorem wt_eq_form (C₁₁ C₁₂ C₂₂ x y : ℤ) :
    wt C₁₁ C₁₂ C₂₂ x y = (2 * C₂₂) * x ^ 2 + (-2 * C₁₂) * x * y + (2 * C₁₁) * y ^ 2 := by
  unfold wt; ring

/-- Oriented definite block: C₁₁ > 0 and discW < 0 ⇒ C₂₂ > 0 and wt ≥ 0. -/
theorem wt_nonneg_of_definite (C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ < 0) (hC : 0 < C₁₁) (Y₁ Y₂ : ℤ) :
    0 ≤ wt C₁₁ C₁₂ C₂₂ Y₁ Y₂ := by
  unfold discW at hd
  have hC22 : 0 < C₂₂ := by nlinarith [sq_nonneg C₁₂]
  have h : 2 * C₂₂ * wt C₁₁ C₁₂ C₂₂ Y₁ Y₂ = (2 * C₂₂ * Y₁ - C₁₂ * Y₂) ^ 2 + (4 * C₁₁ * C₂₂ - C₁₂ ^ 2) * Y₂ ^ 2 := by
    unfold wt; ring
  have h2 : 0 ≤ 2 * C₂₂ * wt C₁₁ C₁₂ C₂₂ Y₁ Y₂ := by
    rw [h]; have : 0 < 4 * C₁₁ * C₂₂ - C₁₂ ^ 2 := by linarith
    positivity
  exact nonneg_of_mul_nonneg_right h2 (by positivity) |> fun h => by
    rcases le_or_gt 0 (wt C₁₁ C₁₂ C₂₂ Y₁ Y₂) with h' | h'
    · exact h'
    · exfalso; nlinarith

theorem C22_pos_of_definite (C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ < 0) (hC : 0 < C₁₁) : 0 < C₂₂ := by
  unfold discW at hd; nlinarith [sq_nonneg C₁₂]

theorem C11_ne_zero_of_definite (C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ < 0) : C₁₁ ≠ 0 := by
  rintro rfl; unfold discW at hd; nlinarith [sq_nonneg C₁₂]

/-! ### Oriented definite leaves, C₁₁ > 0 -/

theorem definite_pos_of_oriented (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ < 0) (hC : 0 < C₁₁)
    (hs : 0 < schur A B₁ B₂ C₁₁ C₁₂ C₂₂) : Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  refine ⟨(kBeta B₁ B₂ C₁₁ C₁₂ C₂₂ + kGamma C₁₁ C₁₂ C₂₂).toNat, ?_⟩
  intro l m₁ m₂ q
  right
  intro c hc
  obtain ⟨u, v, huv⟩ := hc
  have id := rank_two_identity A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q (c : ℤ) u v
  rw [huv, mul_zero] at id
  have hwt := wt_nonneg_of_definite C₁₁ C₁₂ C₂₂ hd hC (y1 B₁ C₁₁ C₁₂ m₁ (c : ℤ) u v) (y2 B₂ C₁₂ C₂₂ m₂ (c : ℤ) u v)
  obtain ⟨β, hβdef⟩ : ∃ β : ℤ, β = betaR B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ := ⟨_, rfl⟩
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℤ, γ = gammaR C₁₁ C₁₂ C₂₂ m₁ m₂ q := ⟨_, rfl⟩
  rw [← hβdef, ← hγdef] at id
  have hc0 : (0 : ℤ) ≤ c := by positivity
  -- α c² ≤ |β| c + |γ| with α ≥ 1 ⇒ c² ≤ |β| c + |γ| ⇒ c ≤ |β| + |γ|
  have h1 : schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * (c : ℤ) ^ 2 ≤ |β| * c + |γ| := by
    have := neg_le_abs β; have := neg_le_abs γ
    have hb : -β * c ≤ |β| * c := mul_le_mul_of_nonneg_right (neg_le_abs β) hc0
    nlinarith
  have h2 : (c : ℤ) ^ 2 ≤ |β| * c + |γ| := by
    have : (c : ℤ) ^ 2 ≤ schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * (c : ℤ) ^ 2 :=
      le_mul_of_one_le_left (by positivity) (by omega)
    linarith
  have h3 : (c : ℤ) ≤ |β| + |γ| := by
    by_contra hcon; push Not at hcon
    have hβ0 := abs_nonneg β; have hγ0 := abs_nonneg γ
    have hc1 : (1 : ℤ) ≤ c := by linarith
    have : (|β| + |γ|) * c < (c : ℤ) * c := mul_lt_mul_of_pos_right hcon (by linarith)
    have : |γ| ≤ |γ| * c := le_mul_of_one_le_right hγ0 hc1
    nlinarith
  have hβb := betaR_abs_le B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂
  have hγb := gammaR_abs_le C₁₁ C₁₂ C₂₂ m₁ m₂ q
  rw [← hβdef] at hβb; rw [← hγdef] at hγb
  have hlin := fbound2_core_ge_lin l m₁ m₂ q
  have hgam := fbound2_core_ge_gamma l m₁ m₂ q
  have hK1 := kBeta_nonneg B₁ B₂ C₁₁ C₁₂ C₂₂
  have hK2 := kGamma_nonneg C₁₁ C₁₂ C₂₂
  have hK : (((kBeta B₁ B₂ C₁₁ C₁₂ C₂₂ + kGamma C₁₁ C₁₂ C₂₂).toNat : ℕ) : ℤ)
      = kBeta B₁ B₂ C₁₁ C₁₂ C₂₂ + kGamma C₁₁ C₁₂ C₂₂ := Int.toNat_of_nonneg (by linarith)
  unfold fbound2; rw [hK]
  have e1 : |β| ≤ kBeta B₁ B₂ C₁₁ C₁₂ C₂₂ * ((1 + |l| + |m₁| + |m₂|) ^ 2 + |q|) :=
    hβb.trans (mul_le_mul_of_nonneg_left hlin hK1)
  have e2 : |γ| ≤ kGamma C₁₁ C₁₂ C₂₂ * ((1 + |l| + |m₁| + |m₂|) ^ 2 + |q|) :=
    hγb.trans (mul_le_mul_of_nonneg_left hgam hK2)
  nlinarith

theorem definite_zero_of_oriented (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ < 0) (hC : 0 < C₁₁)
    (hs : schur A B₁ B₂ C₁₁ C₁₂ C₂₂ = 0) : Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  have hN : nW C₁₁ C₁₂ C₂₂ ≠ 0 := by rw [nW_eq_neg_discW]; omega
  have hC22 := C22_pos_of_definite C₁₁ C₁₂ C₂₂ hd hC
  apply rank_two_alpha_zero_periodic_or_progression A B₁ B₂ C₁₁ C₁₂ C₂₂ hN hs
  · exact ⟨1, 0, by unfold wt; nlinarith⟩
  · exact Or.inr (wt_nonneg_of_definite C₁₁ C₁₂ C₂₂ hd hC)

theorem definite_neg_of_oriented (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ < 0) (hC : 0 < C₁₁)
    (hs : schur A B₁ B₂ C₁₁ C₁₂ C₂₂ < 0) : Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  have hN : nW C₁₁ C₁₂ C₂₂ ≠ 0 := by rw [nW_eq_neg_discW]; omega
  have hC22 := C22_pos_of_definite C₁₁ C₁₂ C₂₂ hd hC
  obtain ⟨α, hαdef⟩ : ∃ α : ℤ, α = schur A B₁ B₂ C₁₁ C₁₂ C₂₂ := ⟨_, rfl⟩
  rw [← hαdef] at hs
  -- T = (−α)·wt = p x² + h x y + q y² with p = −2αC₂₂, h = 2αC₁₂, q = −2αC₁₁
  have hp : 0 < -2 * α * C₂₂ := by nlinarith
  have hq : 0 < -2 * α * C₁₁ := by nlinarith
  have hdef : (2 * α * C₁₂) ^ 2 < 4 * (-2 * α * C₂₂) * (-2 * α * C₁₁) := by
    unfold discW at hd
    have hα2 : 0 < α ^ 2 := by nlinarith
    nlinarith
  have heven : Even (2 * α * C₁₂) := ⟨α * C₁₂, by ring⟩
  obtain ⟨x, y, hTpos, hTns⟩ := definite_nonsquare_direction (-2 * α * C₂₂) (2 * α * C₁₂) (-2 * α * C₁₁) hp hq hdef heven
  have hT : (-2 * α * C₂₂) * x ^ 2 + (2 * α * C₁₂) * x * y + (-2 * α * C₁₁) * y ^ 2 = -(α * wt C₁₁ C₁₂ C₂₂ x y) := by
    unfold wt; ring
  rw [hT] at hTpos hTns
  apply rank_two_dichotomy_of_line_direction A B₁ B₂ C₁₁ C₁₂ C₂₂ hN (by rw [← hαdef]; exact hs.ne)
  exact ⟨x, y, by rw [← hαdef]; linarith, by rw [← hαdef]; exact hTns⟩

/-! ### Orientation transfer -/

/-- Reduce a definite-block statement to the oriented case C₁₁ > 0 via `dichotomy2_neg_iff`. -/
theorem definite_orient (P : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → Prop)
    (hP : ∀ A B₁ B₂ C₁₁ C₁₂ C₂₂, P A B₁ B₂ C₁₁ C₁₂ C₂₂ → P (-A) (-B₁) (-B₂) (-C₁₁) (-C₁₂) (-C₂₂))
    (hor : ∀ A B₁ B₂ C₁₁ C₁₂ C₂₂, discW C₁₁ C₁₂ C₂₂ < 0 → 0 < C₁₁ → P A B₁ B₂ C₁₁ C₁₂ C₂₂
      → Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂)
    (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ < 0) (h : P A B₁ B₂ C₁₁ C₁₂ C₂₂) :
    Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  rcases lt_or_gt_of_ne (C11_ne_zero_of_definite C₁₁ C₁₂ C₂₂ hd) with hneg | hpos
  · rw [← dichotomy2_neg_iff]
    exact hor _ _ _ _ _ _ (by rw [discW_neg]; exact hd) (by linarith) (hP _ _ _ _ _ _ h)
  · exact hor _ _ _ _ _ _ hd hpos h

theorem dichotomy2_definite_pos_oriented (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ < 0)
    (hs : 0 < orientedSchur A B₁ B₂ C₁₁ C₁₂ C₂₂) : Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  refine definite_orient (fun A B₁ B₂ C₁₁ C₁₂ C₂₂ => 0 < orientedSchur A B₁ B₂ C₁₁ C₁₂ C₂₂)
    (fun A B₁ B₂ C₁₁ C₁₂ C₂₂ h => by rw [orientedSchur_neg]; exact h) ?_ A B₁ B₂ C₁₁ C₁₂ C₂₂ hd hs
  intro A B₁ B₂ C₁₁ C₁₂ C₂₂ hd hC hs
  apply definite_pos_of_oriented A B₁ B₂ C₁₁ C₁₂ C₂₂ hd hC
  unfold orientedSchur at hs; rw [Int.sign_eq_one_of_pos hC, one_mul] at hs; exact hs

theorem dichotomy2_definite_zero_oriented (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ < 0)
    (hs : orientedSchur A B₁ B₂ C₁₁ C₁₂ C₂₂ = 0) : Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  refine definite_orient (fun A B₁ B₂ C₁₁ C₁₂ C₂₂ => orientedSchur A B₁ B₂ C₁₁ C₁₂ C₂₂ = 0)
    (fun A B₁ B₂ C₁₁ C₁₂ C₂₂ h => by rw [orientedSchur_neg]; exact h) ?_ A B₁ B₂ C₁₁ C₁₂ C₂₂ hd hs
  intro A B₁ B₂ C₁₁ C₁₂ C₂₂ hd hC hs
  apply definite_zero_of_oriented A B₁ B₂ C₁₁ C₁₂ C₂₂ hd hC
  unfold orientedSchur at hs; rw [Int.sign_eq_one_of_pos hC, one_mul] at hs; exact hs

theorem dichotomy2_definite_neg_oriented (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ < 0)
    (hs : orientedSchur A B₁ B₂ C₁₁ C₁₂ C₂₂ < 0) : Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  refine definite_orient (fun A B₁ B₂ C₁₁ C₁₂ C₂₂ => orientedSchur A B₁ B₂ C₁₁ C₁₂ C₂₂ < 0)
    (fun A B₁ B₂ C₁₁ C₁₂ C₂₂ h => by rw [orientedSchur_neg]; exact h) ?_ A B₁ B₂ C₁₁ C₁₂ C₂₂ hd hs
  intro A B₁ B₂ C₁₁ C₁₂ C₂₂ hd hC hs
  apply definite_neg_of_oriented A B₁ B₂ C₁₁ C₁₂ C₂₂ hd hC
  unfold orientedSchur at hs; rw [Int.sign_eq_one_of_pos hC, one_mul] at hs; exact hs

theorem dichotomy2_definite (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ < 0) :
    Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  rcases lt_trichotomy (orientedSchur A B₁ B₂ C₁₁ C₁₂ C₂₂) 0 with h | h | h
  · exact dichotomy2_definite_neg_oriented A B₁ B₂ C₁₁ C₁₂ C₂₂ hd h
  · exact dichotomy2_definite_zero_oriented A B₁ B₂ C₁₁ C₁₂ C₂₂ hd h
  · exact dichotomy2_definite_pos_oriented A B₁ B₂ C₁₁ C₁₂ C₂₂ hd h

/-! ### Indefinite leaves through a signed direction lemma -/

/-- Common finish for indefinite blocks: a signed non-square direction lemma for the adjugate form
    (with h := |α|, σ := −sign α) feeds the generic theorem; α = 0 goes to the α = 0 theorem. -/
theorem indefinite_of_signed_direction (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : 0 < discW C₁₁ C₁₂ C₂₂)
    (hdir : ∀ h σ : ℤ, 0 < h → (σ = 1 ∨ σ = -1) →
      ∃ x y : ℤ, 0 < σ * wt C₁₁ C₁₂ C₂₂ x y ∧ ¬ IsSquare (h * |wt C₁₁ C₁₂ C₂₂ x y|)) :
    Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  have hN : nW C₁₁ C₁₂ C₂₂ ≠ 0 := by rw [nW_eq_neg_discW]; omega
  obtain ⟨α, hαdef⟩ : ∃ α : ℤ, α = schur A B₁ B₂ C₁₁ C₁₂ C₂₂ := ⟨_, rfl⟩
  rcases lt_trichotomy α 0 with hneg | hzero | hpos
  · -- σ = 1
    obtain ⟨x, y, h1, h2⟩ := hdir (-α) 1 (by linarith) (Or.inl rfl)
    rw [one_mul] at h1
    apply rank_two_dichotomy_of_line_direction A B₁ B₂ C₁₁ C₁₂ C₂₂ hN (by rw [← hαdef]; exact hneg.ne)
    refine ⟨x, y, ?_, ?_⟩
    · rw [← hαdef]; exact mul_neg_of_neg_of_pos hneg h1
    · rw [← hαdef, show -(α * wt C₁₁ C₁₂ C₂₂ x y) = (-α) * |wt C₁₁ C₁₂ C₂₂ x y| by
        rw [abs_of_pos h1]; ring]
      exact h2
  · apply rank_two_alpha_zero_periodic_or_progression A B₁ B₂ C₁₁ C₁₂ C₂₂ hN (by rw [← hαdef]; exact hzero)
    · obtain ⟨x, y, h1, -⟩ := hdir 1 1 one_pos (Or.inl rfl)
      exact ⟨x, y, by linarith⟩
    · obtain ⟨x, y, h1, -⟩ := hdir 1 (-1) one_pos (Or.inr rfl)
      exact Or.inl ⟨x, y, by linarith⟩
  · -- σ = −1
    obtain ⟨x, y, h1, h2⟩ := hdir α (-1) hpos (Or.inr rfl)
    have h1' : wt C₁₁ C₁₂ C₂₂ x y < 0 := by linarith
    apply rank_two_dichotomy_of_line_direction A B₁ B₂ C₁₁ C₁₂ C₂₂ hN (by rw [← hαdef]; exact hpos.ne')
    refine ⟨x, y, ?_, ?_⟩
    · rw [← hαdef]; exact mul_neg_of_pos_of_neg hpos h1'
    · rw [← hαdef, show -(α * wt C₁₁ C₁₂ C₂₂ x y) = α * |wt C₁₁ C₁₂ C₂₂ x y| by
        rw [abs_of_neg h1']; ring]
      exact h2

theorem dichotomy2_split (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : 0 < discW C₁₁ C₁₂ C₂₂)
    (hsq : IsSquare (discW C₁₁ C₁₂ C₂₂)) : Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  apply indefinite_of_signed_direction A B₁ B₂ C₁₁ C₁₂ C₂₂ hd
  intro h σ hh hσ
  have hD : (-2 * C₁₂) ^ 2 - 4 * (2 * C₂₂) * (2 * C₁₁) = 4 * discW C₁₁ C₁₂ C₂₂ := by unfold discW; ring
  have hD0 : 0 < (-2 * C₁₂) ^ 2 - 4 * (2 * C₂₂) * (2 * C₁₁) := by rw [hD]; linarith
  have hDsq : IsSquare ((-2 * C₁₂) ^ 2 - 4 * (2 * C₂₂) * (2 * C₁₁)) := by
    rw [hD]; obtain ⟨d, hd'⟩ := hsq; exact ⟨2 * d, by rw [hd']; ring⟩
  obtain ⟨x, y, h1, h2⟩ := split_signed_nonsquare_direction (2 * C₂₂) (-2 * C₁₂) (2 * C₁₁) h σ hD0 hDsq hh hσ
  refine ⟨x, y, ?_, ?_⟩
  · rw [wt_eq_form]; exact h1
  · rw [wt_eq_form]; exact h2

theorem dichotomy2_anisotropic (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : 0 < discW C₁₁ C₁₂ C₂₂)
    (hsq : ¬ IsSquare (discW C₁₁ C₁₂ C₂₂)) : Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  apply indefinite_of_signed_direction A B₁ B₂ C₁₁ C₁₂ C₂₂ hd
  intro h σ hh hσ
  have hD : (-2 * C₁₂) ^ 2 - 4 * (2 * C₂₂) * (2 * C₁₁) = 2 ^ 2 * discW C₁₁ C₁₂ C₂₂ := by unfold discW; ring
  have hD0 : 0 < (-2 * C₁₂) ^ 2 - 4 * (2 * C₂₂) * (2 * C₁₁) := by rw [hD]; linarith
  have hDns : ¬ IsSquare ((-2 * C₁₂) ^ 2 - 4 * (2 * C₂₂) * (2 * C₁₁)) := by
    rw [hD]; exact not_isSquare_sq_mul 2 _ two_ne_zero hsq
  obtain ⟨x, y, h1, h2⟩ := anisotropic_signed_nonsquare_direction (2 * C₂₂) (-2 * C₁₂) (2 * C₁₁) h σ hD0 hDns hh hσ
  refine ⟨x, y, ?_, ?_⟩
  · rw [wt_eq_form]; exact h1
  · rw [wt_eq_form]; exact h2

end DiophCompression.SemanticQuadraticTwoWitness
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_definite
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_split
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_anisotropic
