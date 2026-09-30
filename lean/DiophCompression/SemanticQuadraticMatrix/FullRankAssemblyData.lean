/-
  DiophCompression/SemanticQuadraticMatrix/FullRankAssemblyData.lean — APAL Structural Theory Gate 5,
  必須F step 3 (full-rank assembly) (s28, 2026-09-02, claude.ai direct).

  The matrix-level dichotomy in data-carrying form, and the full-rank dispatch (A1–A4) carried out at that
  level. The dispatch itself is the sealed argument; the three leaf theorems it calls appear as explicit
  hypotheses, so what still has to be converted is visible in the statement:
    * `hDir`  — branch A1 (signed non-square direction; its Pell hub is already data, s28)
    * `hA0`   — branches A2 / A3 (α = 0; the quadratic family and the periodic family are already data)
    * `hBnd`  — branch A4 (bounded).
  No sorry; std-3.
-/
import DiophCompression.SemanticQuadraticMatrix.FullRankGeneric
import DiophCompression.StructuredFamilyCore
import DiophCompression.PeriodicProgressionData
import DiophCompression.SemanticQuadraticMatrix.QuadraticFamilyA2
import DiophCompression.SemanticQuadratic.PellOrbitOfXPos

namespace DiophCompression.SemanticQuadraticMatrix

open Matrix

variable {r : ℕ}

/-- The data form implies the sealed one. -/
theorem dichotomyM_of_dichotomyMData {A : ℤ} {B : Fin r → ℤ} {C : Matrix (Fin r) (Fin r) ℤ}
    (h : DichotomyMData A B C) : DichotomyM A B C := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun l m q => ?_⟩
  rcases hK l m q with hF | hb
  · exact Or.inl (hF.elim fun F => DiophCompression.infinite_of_structuredFamily F)
  · exact Or.inr hb

/-- Branch A3 at the matrix level, in data form: the periodic family of `α = β = 0`. -/
theorem alpha_zero_beta_zero_family_data (A : ℤ) (B : Fin r → ℤ)
    (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ) (m : Fin r → ℤ) (q : ℤ)
    (hN : (witnessGram C).det ≠ 0) (hα : alphaMatrix A B C = 0) (hβ : betaMatrix B C l m = 0) :
    Nonempty (DiophCompression.StructuredFamily (fiberSetM A B C l m q)) ∨
      fiberSetM A B C l m q = ∅ := by
  rcases alpha_zero_beta_zero_periodic_data A B C l m q hN hα hβ with hF | hE
  · exact Or.inl (hF.elim fun F => ⟨DiophCompression.PeriodicProgression.toStructuredFamily F⟩)
  · exact Or.inr hE

theorem full_rank_dichotomy_all_data (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (i j : Fin r) (hij : i ≠ j)
    (hDir : alphaMatrix A B C ≠ 0 →
      SignedNonsquareDirection (adjugateQuad (witnessGram C)) (alphaMatrix A B C) →
      DichotomyMData A B C)
    (hA0 : alphaMatrix A B C = 0 →
      (∀ β : ℤ, β ≠ 0 → (∃ w, β * adjugateQuad (witnessGram C) w < 0)
        ∨ (∀ Y, 0 ≤ β * adjugateQuad (witnessGram C) Y)) → DichotomyMData A B C)
    (hBnd : alphaMatrix A B C ≠ 0 →
      (∀ Y, 0 ≤ alphaMatrix A B C * adjugateQuad (witnessGram C) Y) → DichotomyMData A B C) :
    DichotomyMData A B C := by
  obtain ⟨α, hαdef⟩ : ∃ α : ℤ, α = alphaMatrix A B C := ⟨_, rfl⟩
  by_cases hneg : ∃ w, adjugateQuad (witnessGram C) w < 0
  · by_cases hpos : ∃ w, 0 < adjugateQuad (witnessGram C) w
    · obtain ⟨v, hv⟩ := hpos
      obtain ⟨w, hw⟩ := hneg
      rcases lt_trichotomy α 0 with hlt | heq | hgt
      · obtain ⟨x, h1, h2⟩ :=
          indefinite_signed_nonsquare_direction_M C v w hv hw (-α) 1 (by linarith) (Or.inl rfl)
        rw [one_mul] at h1
        apply hDir (by rw [← hαdef]; exact hlt.ne)
        refine ⟨x, ?_, ?_⟩
        · rw [← hαdef]; exact mul_neg_of_neg_of_pos hlt h1
        · rw [← hαdef, show -(α * adjugateQuad (witnessGram C) x) = (-α) * |adjugateQuad (witnessGram C) x| by
            rw [abs_of_pos h1]; ring]
          exact h2
      · apply hA0 (by rw [← hαdef]; exact heq)
        intro β hβ
        rcases lt_or_gt_of_ne hβ with hb | hb
        · exact Or.inl ⟨v, mul_neg_of_neg_of_pos hb hv⟩
        · exact Or.inl ⟨w, mul_neg_of_pos_of_neg hb hw⟩
      · obtain ⟨x, h1, h2⟩ :=
          indefinite_signed_nonsquare_direction_M C v w hv hw α (-1) hgt (Or.inr rfl)
        have h1' : adjugateQuad (witnessGram C) x < 0 := by linarith
        apply hDir (by rw [← hαdef]; exact hgt.ne')
        refine ⟨x, ?_, ?_⟩
        · rw [← hαdef]; exact mul_neg_of_pos_of_neg hgt h1'
        · rw [← hαdef, show -(α * adjugateQuad (witnessGram C) x) = α * |adjugateQuad (witnessGram C) x| by
            rw [abs_of_neg h1']; ring]
          exact h2
    · push Not at hpos
      rcases lt_trichotomy α 0 with hlt | heq | hgt
      · exact hBnd (by rw [← hαdef]; exact hlt.ne)
          (fun Y => by rw [← hαdef]; exact mul_nonneg_of_nonpos_of_nonpos hlt.le (hpos Y))
      · apply hA0 (by rw [← hαdef]; exact heq)
        intro β hβ
        rcases lt_or_gt_of_ne hβ with hb | hb
        · exact Or.inr (fun Y => mul_nonneg_of_nonpos_of_nonpos hb.le (hpos Y))
        · obtain ⟨w, hw⟩ := hneg
          exact Or.inl ⟨w, mul_neg_of_pos_of_neg hb hw⟩
      · apply hDir (by rw [← hαdef]; exact hgt.ne')
        rw [← hαdef]
        exact definite_signed_nonsquare_direction_M C hN i j hij α hgt.ne'
          (fun Y => by have := hpos Y; nlinarith)
  · push Not at hneg
    rcases lt_trichotomy α 0 with hlt | heq | hgt
    · apply hDir (by rw [← hαdef]; exact hlt.ne)
      rw [← hαdef]
      exact definite_signed_nonsquare_direction_M C hN i j hij α hlt.ne
        (fun Y => by have := hneg Y; nlinarith)
    · apply hA0 (by rw [← hαdef]; exact heq)
      intro β hβ
      rcases lt_or_gt_of_ne hβ with hb | hb
      · obtain ⟨w, hw⟩ := exists_adjugateQuad_sign C hN i 1 one_ne_zero (fun Y => by rw [one_mul]; exact hneg Y)
        rw [one_mul] at hw
        exact Or.inl ⟨w, mul_neg_of_neg_of_pos hb hw⟩
      · exact Or.inr (fun Y => mul_nonneg hb.le (hneg Y))
    · exact hBnd (by rw [← hαdef]; exact hgt.ne')
        (fun Y => by rw [← hαdef]; exact mul_nonneg hgt.le (hneg Y))

/-! ### Branch A4 (bounded): the sealed argument, at the data level -/

theorem full_rank_root_bound_data (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (hα : alphaMatrix A B C ≠ 0)
    (hsemi : ∀ Y, 0 ≤ alphaMatrix A B C * adjugateQuad (witnessGram C) Y) :
    DichotomyMData A B C := by
  refine ⟨(kBetaM B C + kGammaM C).toNat, ?_⟩
  intro l m q
  have hK : (((kBetaM B C + kGammaM C).toNat : ℕ) : ℤ) = kBetaM B C + kGammaM C :=
    Int.toNat_of_nonneg (add_nonneg (kBetaM_nonneg _ _) (kGammaM_nonneg _))
  right
  intro c hc
  obtain ⟨u, hu⟩ := hc
  obtain ⟨α, hαdef⟩ : ∃ α : ℤ, α = alphaMatrix A B C := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ℤ, β = betaMatrix B C l m := ⟨_, rfl⟩
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℤ, γ = gammaMatrix C m q := ⟨_, rfl⟩
  have id := general_rank_identity A B C l m q (c : ℤ) u
  rw [hu, mul_zero, ← hαdef, ← hβdef, ← hγdef] at id
  have hwt := hsemi (completedVector B C m (c : ℤ) u)
  rw [← hαdef] at hwt
  have hα' : α ≠ 0 := by rw [hαdef]; exact hα
  have hc0 : (0 : ℤ) ≤ c := by positivity
  -- α(αc² + βc + γ) = −α·W̃(Y) ≤ 0
  have h1 : α ^ 2 * (c : ℤ) ^ 2 ≤ |α| * |β| * c + |α| * |γ| := by
    have e : α * (α * (c : ℤ) ^ 2 + β * c + γ) = -(α * adjugateQuad (witnessGram C) (completedVector B C m (c : ℤ) u)) := by
      linear_combination (-α) * id
    have h2 : α * (α * (c : ℤ) ^ 2 + β * c + γ) ≤ 0 := by rw [e]; linarith
    have h3 := neg_abs_le (α * β)
    have h4 := neg_abs_le (α * γ)
    rw [abs_mul] at h3 h4
    nlinarith
  have hα1 : 1 ≤ |α| := Int.one_le_abs hα'
  have hα2 : |α| * |α| = α ^ 2 := by rw [← sq, sq_abs]
  -- c² ≤ |β| c + |γ| (dividing by |α| ≥ 1)
  have h5 : (c : ℤ) ^ 2 ≤ |β| * c + |γ| := by
    have h7 : |α| * ((c : ℤ) ^ 2) ≤ α ^ 2 * (c : ℤ) ^ 2 := by
      rw [← hα2]
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (abs_nonneg α) hα1) (sq_nonneg _)
    have h6 : |α| * ((c : ℤ) ^ 2) ≤ |α| * (|β| * c + |γ|) := by nlinarith
    exact le_of_mul_le_mul_left h6 (by linarith)
  have h7 : (c : ℤ) ≤ |β| + |γ| := by
    by_contra hcon; push Not at hcon
    have hγ0 := abs_nonneg γ; have hβ0 := abs_nonneg β
    nlinarith
  have hβb := betaMatrix_abs_le B C l m
  rw [← hβdef] at hβb
  have hγb := gammaMatrix_abs_le C m q
  rw [← hγdef] at hγb
  have hlin := fboundM_core_ge_lin l m q
  have hg := fboundM_core_ge_gamma l m q
  have hKb := kBetaM_nonneg B C
  have hKg := kGammaM_nonneg C
  skip
  rw [hK]
  nlinarith

/-- Shifting the index of a quadratic family: growth is only needed from `t₀` on, and the shifted family
    is again a quadratic progression (this is what the A2 branch produces). -/
def structuredFamily_quadratic_of_shift {S : Set ℕ} (α β γ : ℤ) (hα : α ≠ 0) (t₀ : ℕ)
    (cf : ℕ → ℕ) (out : ∀ n : ℕ, (cf n : ℤ) = α * ((t₀ : ℤ) + n) ^ 2 + β * ((t₀ : ℤ) + n) + γ)
    (mem : ∀ n, cf n ∈ S) (mono : StrictMono cf) : DiophCompression.StructuredFamily S :=
  .quadratic α (2 * α * (t₀ : ℤ) + β) (α * (t₀ : ℤ) ^ 2 + β * (t₀ : ℤ) + γ) hα cf
    (fun n => by rw [out n]; ring) mem mono


/-! ### Branches A2 / A3 (α = 0) in data form -/

set_option maxHeartbeats 2000000 in
theorem full_rank_alpha_zero_dichotomy_data (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (hα : alphaMatrix A B C = 0)
    (hdir : ∀ β : ℤ, β ≠ 0 → (∃ w, β * adjugateQuad (witnessGram C) w < 0)
      ∨ (∀ Y, 0 ≤ β * adjugateQuad (witnessGram C) Y)) :
    DichotomyMData A B C := by
  refine ⟨(kGammaM C).toNat, ?_⟩
  intro l m q
  have hK : (((kGammaM C).toNat : ℕ) : ℤ) = kGammaM C := Int.toNat_of_nonneg (kGammaM_nonneg _)
  obtain ⟨N, hNdef⟩ : ∃ N : ℤ, N = (witnessGram C).det := ⟨_, rfl⟩
  have hN' : N ≠ 0 := by rw [hNdef]; exact hN
  obtain ⟨β, hβdef⟩ : ∃ β : ℤ, β = betaMatrix B C l m := ⟨_, rfl⟩
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℤ, γ = gammaMatrix C m q := ⟨_, rfl⟩
  by_cases hβ : β = 0
  · rcases alpha_zero_beta_zero_family_data A B C l m q hN hα (by rw [← hβdef]; exact hβ) with hF | hE
    · exact Or.inl hF
    · right; intro c hc; rw [hE] at hc; exact absurd hc (Set.notMem_empty c)
  · rcases hdir β hβ with ⟨w, hw⟩ | hnn
    · by_cases hne : (fiberSetM A B C l m q).Nonempty
      · left
        obtain ⟨c₀, u₀, h0⟩ := hne
        obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℤ,
          B₀ = completedVector B C m (c₀ : ℤ) u₀ ⬝ᵥ (adjugate (witnessGram C) *ᵥ w) := ⟨_, rfl⟩
        obtain ⟨Wt, hWt⟩ : ∃ Wt : ℤ, Wt = adjugateQuad (witnessGram C) w := ⟨_, rfl⟩
        rw [← hWt] at hw
        obtain ⟨T, hT⟩ : ∃ T : ℤ, T = |2 * N * B₀| + (c₀ : ℤ) + 1 := ⟨_, rfl⟩
        have hc₀ : (0 : ℤ) ≤ (c₀ : ℤ) := Int.natCast_nonneg c₀
        have habs : (0 : ℤ) ≤ |2 * N * B₀| := abs_nonneg _
        have hT1 : (1 : ℤ) ≤ T := by rw [hT]; linarith
        have ha : 1 ≤ N ^ 2 * (-(Wt * β)) := by
          have h1 : 1 ≤ N ^ 2 := by
            have : 0 < N ^ 2 := by positivity
            omega
          have h2 : 1 ≤ -(Wt * β) := by
            have : Wt * β < 0 := by rw [mul_comm]; exact hw
            omega
          nlinarith
        -- the family: t n = T + n
        have hval : ∀ n : ℕ, (c₀ : ℤ) + N * (-2 * B₀ * (T + (n : ℤ))
              - N * Wt * β * (T + (n : ℤ)) ^ 2)
            = (N ^ 2 * (-(Wt * β))) * (T + (n : ℤ)) ^ 2 - (2 * N * B₀) * (T + (n : ℤ)) + c₀ := by
          intro n; ring
        have hnn' : ∀ n : ℕ, (0 : ℤ) ≤ (c₀ : ℤ) + N * (-2 * B₀ * (T + (n : ℤ))
            - N * Wt * β * (T + (n : ℤ)) ^ 2) := by
          intro n
          rw [hval n]
          have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
          have h3 : (N ^ 2 * (-(Wt * β))) * (T + (n : ℤ)) ^ 2 ≥ (T + (n : ℤ)) ^ 2 := by
            nlinarith [sq_nonneg (T + (n : ℤ))]
          have h4 : -(2 * N * B₀) * (T + (n : ℤ)) ≥ -|2 * N * B₀| * (T + (n : ℤ)) := by
            have := mul_le_mul_of_nonneg_right (le_abs_self (2 * N * B₀))
              (by linarith : (0 : ℤ) ≤ T + (n : ℤ))
            linarith
          nlinarith
        have hmem : ∀ n : ℕ, ((c₀ : ℤ) + N * (-2 * B₀ * (T + (n : ℤ))
            - N * Wt * β * (T + (n : ℤ)) ^ 2)).toNat ∈ fiberSetM A B C l m q := by
          intro n
          have hline := a2_quadratic_family A B C l m q (c₀ : ℤ) u₀ w N Wt B₀ β
            hNdef hWt hB₀ hβdef hα hN' h0 (T + (n : ℤ))
          refine ⟨scaledLineU B C u₀ w (-2 * B₀ * (T + (n : ℤ))
            - N * Wt * β * (T + (n : ℤ)) ^ 2) (β * (T + (n : ℤ))), ?_⟩
          rw [Int.toNat_of_nonneg (hnn' n)]
          have e : (c₀ : ℤ) + N * (-2 * B₀ * (T + (n : ℤ)) - N * Wt * β * (T + (n : ℤ)) ^ 2)
              = -(N ^ 2 * Wt * β) * (T + (n : ℤ)) ^ 2 + (-2 * N * B₀) * (T + (n : ℤ)) + c₀ := by ring
          rw [e]
          exact hline
        have hmono : StrictMono (fun n : ℕ => ((c₀ : ℤ) + N * (-2 * B₀ * (T + (n : ℤ))
            - N * Wt * β * (T + (n : ℤ)) ^ 2)).toNat) := by
          refine strictMono_nat_of_lt_succ (fun n => ?_)
          have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
          have hlt : (c₀ : ℤ) + N * (-2 * B₀ * (T + (n : ℤ))
                - N * Wt * β * (T + (n : ℤ)) ^ 2)
              < (c₀ : ℤ) + N * (-2 * B₀ * (T + ((n : ℤ) + 1))
                - N * Wt * β * (T + ((n : ℤ) + 1)) ^ 2) := by
            rw [hval n]
            have e2 : (c₀ : ℤ) + N * (-2 * B₀ * (T + ((n : ℤ) + 1))
                  - N * Wt * β * (T + ((n : ℤ) + 1)) ^ 2)
                = (N ^ 2 * (-(Wt * β))) * (T + (n : ℤ) + 1) ^ 2
                  - (2 * N * B₀) * (T + (n : ℤ) + 1) + c₀ := by ring
            rw [e2]
            have hTb : |2 * N * B₀| + 1 ≤ T := by rw [hT]; linarith
            have hle := neg_abs_le (2 * N * B₀)
            have hle2 := le_abs_self (2 * N * B₀)
            nlinarith [sq_nonneg (T + (n : ℤ))]
          have h1 := hnn' n
          have h2 : (0 : ℤ) ≤ (c₀ : ℤ) + N * (-2 * B₀ * (T + ((n : ℤ) + 1))
              - N * Wt * β * (T + ((n : ℤ) + 1)) ^ 2) := by
            have := hnn' (n + 1)
            push_cast at this ⊢
            linarith
          push_cast
          omega
        refine ⟨DiophCompression.StructuredFamily.quadratic (N ^ 2 * (-(Wt * β)))
          (2 * (N ^ 2 * (-(Wt * β))) * T - 2 * N * B₀)
          ((N ^ 2 * (-(Wt * β))) * T ^ 2 - (2 * N * B₀) * T + c₀) (by nlinarith)
          (fun n => ((c₀ : ℤ) + N * (-2 * B₀ * (T + (n : ℤ))
            - N * Wt * β * (T + (n : ℤ)) ^ 2)).toNat) ?_ hmem hmono⟩
        intro n
        rw [Int.toNat_of_nonneg (hnn' n), hval n]
        ring
      · right; intro c hc; exact absurd ⟨c, hc⟩ hne
    · right
      intro c hc
      obtain ⟨u, hu⟩ := hc
      have id := general_rank_identity A B C l m q (c : ℤ) u
      rw [hu, mul_zero, hα, ← hβdef, ← hγdef] at id
      have hwt := hnn (completedVector B C m (c : ℤ) u)
      have hβ1 : 1 ≤ |β| := Int.one_le_abs hβ
      have hc0 : (0 : ℤ) ≤ c := by positivity
      have h1 : β ^ 2 * (c : ℤ) ≤ |β| * |γ| := by
        have e : β ^ 2 * (c : ℤ) = -(β * γ) - β * adjugateQuad (witnessGram C) (completedVector B C m (c : ℤ) u) := by
          linear_combination (-β) * id
        have h3 := neg_abs_le (β * γ)
        rw [abs_mul] at h3
        rw [e]; linarith
      have hβ2 : |β| * |β| = β ^ 2 := by rw [← sq, sq_abs]
      have h2 : (c : ℤ) ≤ |γ| := by
        have h5 : |β| * (c : ℤ) ≤ β ^ 2 * (c : ℤ) := by
          rw [← hβ2]
          exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (abs_nonneg β) hβ1) hc0
        have h4 : |β| * (c : ℤ) ≤ |β| * |γ| := by linarith
        exact le_of_mul_le_mul_left h4 (by linarith)
      have hγ := gammaMatrix_abs_le C m q
      rw [← hγdef] at hγ
      have h3 := fboundM_core_ge_gamma l m q
      have hKnn := kGammaM_nonneg C
      skip
      rw [hK]
      calc (c : ℤ) ≤ |γ| := h2
        _ ≤ kGammaM C * ((1 + ∑ i, |m i|) ^ 2 + |q|) := hγ
        _ ≤ kGammaM C * ((1 + |l| + ∑ i, |m i|) ^ 2 + |q|) := mul_le_mul_of_nonneg_left h3 hKnn


/-- With A2/A3 (`hA0`) and A4 (`hBnd`) now discharged, the full-rank dispatch needs only the A1 wrapper. -/
theorem full_rank_dichotomy_all_data_of_dir (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (i j : Fin r) (hij : i ≠ j)
    (hDir : alphaMatrix A B C ≠ 0 →
      SignedNonsquareDirection (adjugateQuad (witnessGram C)) (alphaMatrix A B C) →
      DichotomyMData A B C) :
    DichotomyMData A B C :=
  full_rank_dichotomy_all_data A B C hN i j hij hDir
    (fun hα hdir => full_rank_alpha_zero_dichotomy_data A B C hN hα hdir)
    (fun hα hsemi => full_rank_root_bound_data A B C hN hα hsemi)


/-! ### Branch A1 (Pell line) in data form -/

open DiophCompression.SemanticQuadratic DiophCompression.SemanticQuadraticTwoWitness in
theorem fiberSetM_line_family (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ)
    (m : Fin r → ℤ) (q : ℤ) (hN : (witnessGram C).det ≠ 0) (w : Fin r → ℤ)
    (hw1 : alphaMatrix A B C * adjugateQuad (witnessGram C) w < 0)
    (hw2 : ¬ IsSquare (-(alphaMatrix A B C * adjugateQuad (witnessGram C) w)))
    (c₀ : ℕ) (u₀ : Fin r → ℤ) (h0 : fqM A B C l m q (c₀ : ℤ) u₀ = 0)
    (hZ : 0 < alphaMatrix A B C * (2 * alphaMatrix A B C * (c₀ : ℤ) + betaMatrix B C l m)) :
    Nonempty (DiophCompression.StructuredFamily (fiberSetM A B C l m q)) := by
  obtain ⟨N, hNdef⟩ : ∃ N : ℤ, N = (witnessGram C).det := ⟨_, rfl⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℤ, α = alphaMatrix A B C := ⟨_, rfl⟩
  obtain ⟨Wt, hWt⟩ : ∃ Wt : ℤ, Wt = adjugateQuad (witnessGram C) w := ⟨_, rfl⟩
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : ℤ, Z₀ = 2 * α * (c₀ : ℤ) + betaMatrix B C l m := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℤ,
    B₀ = completedVector B C m (c₀ : ℤ) u₀ ⬝ᵥ (adjugate (witnessGram C) *ᵥ w) := ⟨_, rfl⟩
  rw [← hαdef, ← hWt] at hw1 hw2
  rw [← hαdef, ← hZ₀] at hZ
  have hN' : N ≠ 0 := by rw [hNdef]; exact hN
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε = N.sign := ⟨_, rfl⟩
  have hε2 : ε * ε = 1 := by
    rcases lt_or_gt_of_ne hN' with h | h
    · rw [hε, Int.sign_eq_neg_one_of_neg h]; norm_num
    · rw [hε, Int.sign_eq_one_of_pos h]; norm_num
  have hNε : N * ε = (N.natAbs : ℤ) := by rw [hε]; exact Int.mul_sign_self N
  have hdisc : disc (N * α) 0 (N * Wt) = (2 * N) ^ 2 * (-(α * Wt)) := by unfold disc; ring
  have hdpos : 0 < disc (N * α) 0 (N * Wt) := by
    rw [hdisc]; have : 0 < (2 * N) ^ 2 := by positivity
    have : 0 < -(α * Wt) := by linarith
    positivity
  have hdns : ¬ IsSquare (disc (N * α) 0 (N * Wt)) := by
    rw [hdisc]; exact not_isSquare_sq_mul (2 * N) _ (by positivity) hw2
  have hmem0 : (0 : ℕ) ∈ fiberSet (N * α) 0 (N * Wt) (ε * Z₀) (2 * B₀) 0 := ⟨0, by unfold fq; ring⟩
  have hX0 : 0 < 2 * disc (N * α) 0 (N * Wt) * ((0 : ℕ) : ℤ)
      + (2 * 0 * (2 * B₀) - 4 * (N * Wt) * (ε * Z₀)) := by
    have hWZ : Wt * Z₀ < 0 := by
      have h1 : (α * Wt) * (α * Z₀) < 0 := mul_neg_of_neg_of_pos hw1 hZ
      have h2 : (α * Wt) * (α * Z₀) = α ^ 2 * (Wt * Z₀) := by ring
      have hα2 : 0 < α ^ 2 := by
        have : α ≠ 0 := by rintro rfl; simp at hw1
        positivity
      rw [h2] at h1; nlinarith
    have hNabs : 0 < (N.natAbs : ℤ) := by exact_mod_cast Int.natAbs_pos.mpr hN'
    have e : 2 * disc (N * α) 0 (N * Wt) * ((0 : ℕ) : ℤ) + (2 * 0 * (2 * B₀) - 4 * (N * Wt) * (ε * Z₀))
        = -4 * (N * ε) * (Wt * Z₀) := by push_cast; ring
    rw [e, hNε]; nlinarith
  obtain ⟨P, Q, Y₀, pt, hunit, hP2, hpt0, hfq, hout, hmono0⟩ :=
    pell_orbit_of_X_pos (N * α) 0 (N * Wt) (ε * Z₀) (2 * B₀) 0 hdpos hdns 0 hmem0 hX0
  have hM1 : 1 ≤ N.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hN')
  have hptnn : ∀ n : ℕ, (0 : ℤ) ≤ (pt n).1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hpt0]; norm_num
    · have := hmono0 (Nat.pos_of_ne_zero (by omega) : 0 < n)
      simp only at this
      rw [hpt0] at this
      push_cast at this
      linarith
  have hmem : ∀ n : ℕ, c₀ + N.natAbs * ((pt n).1).toNat ∈ fiberSetM A B C l m q := by
    intro n
    obtain ⟨z', hz'⟩ : ∃ z' : ℕ, (z' : ℤ) = (pt n).1 :=
      ⟨((pt n).1).toNat, Int.toNat_of_nonneg (hptnn n)⟩
    obtain ⟨s, hs⟩ : ∃ s : ℤ, fq (N * α) 0 (N * Wt) (ε * Z₀) (2 * B₀) 0 (z' : ℤ) s = 0 :=
      ⟨(pt n).2, by rw [hz']; exact hfq n⟩
    have hzeq : ((pt n).1).toNat = z' := by rw [← hz']; exact Int.toNat_natCast z'
    rw [hzeq]
    have hs' : fq (N * α) 0 (N * Wt) Z₀ (2 * B₀) 0 (ε * z') s = 0 := by
      unfold fq at hs ⊢
      linear_combination hs + (N * α * (z' : ℤ) ^ 2) * hε2
    have hline : fqM A B C l m q ((c₀ : ℤ) + N * (ε * z')) (scaledLineU B C u₀ w (ε * z') s) = 0 := by
      have key := general_scaled_line_fq A B C l m u₀ w q (c₀ : ℤ) (ε * z') s
      rw [← hNdef, ← hαdef, ← hWt, ← hZ₀, ← hB₀, h0, hs'] at key
      have h2 : 2 * N * fqM A B C l m q ((c₀ : ℤ) + N * (ε * z')) (scaledLineU B C u₀ w (ε * z') s) = 0 := by
        rw [key]; ring
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (by linarith : N = 0) hN'
      · exact h
    have hc : (0 : ℤ) ≤ (c₀ : ℤ) + N * (ε * z') := by
      have : N * (ε * z') = (N.natAbs : ℤ) * z' := by rw [← mul_assoc, hNε]
      rw [this]; positivity
    rw [hNdef] at hline hc
    have hmem := general_scaled_line_solution A B C l m u₀ w q (c₀ : ℤ) (ε * z') s hline hc
    have e : (c₀ : ℤ) + (witnessGram C).det * (ε * z') = ((c₀ + N.natAbs * z' : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_mul, ← mul_assoc, ← hNdef, hNε]
    rw [e, Int.toNat_natCast] at hmem
    exact hmem
  have hmono : StrictMono (fun n : ℕ => c₀ + N.natAbs * ((pt n).1).toNat) := by
    refine strictMono_nat_of_lt_succ (fun n => ?_)
    have h1 := hmono0 (Nat.lt_succ_self n)
    have h2 := hptnn n
    have hb : 0 < (pt (n + 1)).1 := lt_of_le_of_lt h2 h1
    have hlt : ((pt n).1).toNat < ((pt (n + 1)).1).toNat := (Int.toNat_lt_toNat hb).mpr h1
    have hpos : 0 < N.natAbs := hM1
    exact Nat.add_lt_add_left (mul_lt_mul_of_pos_left hlt hpos) c₀
  have hD2 : (2 * disc (N * α) 0 (N * Wt) : ℤ) ≠ 0 := by
    have := hdpos; intro h0; omega
  refine ⟨DiophCompression.StructuredFamily.pell (disc (N * α) 0 (N * Wt)) P Q hunit hP2
    (fun k => (DiophCompression.pellOrbit (disc (N * α) 0 (N * Wt)) P Q
      (2 * disc (N * α) 0 (N * Wt) * ((0 : ℕ) : ℤ)
        + (2 * 0 * (2 * B₀) - 4 * (N * Wt) * (ε * Z₀))) Y₀ k).1)
    (fun k => (DiophCompression.pellOrbit (disc (N * α) 0 (N * Wt)) P Q
      (2 * disc (N * α) 0 (N * Wt) * ((0 : ℕ) : ℤ)
        + (2 * 0 * (2 * B₀) - 4 * (N * Wt) * (ε * Z₀))) Y₀ k).2)
    (fun k => DiophCompression.pellOrbit_succ_fst _ _ _ _ _ k)
    (fun k => DiophCompression.pellOrbit_succ_snd _ _ _ _ _ k)
    (2 * disc (N * α) 0 (N * Wt)) (N.natAbs : ℤ)
    (2 * disc (N * α) 0 (N * Wt) * (c₀ : ℤ)
      - (N.natAbs : ℤ) * (2 * 0 * (2 * B₀) - 4 * (N * Wt) * (ε * Z₀))) hD2
    (fun n => c₀ + N.natAbs * ((pt n).1).toNat) (fun k => ?_) hmem hmono⟩
  have hk := hout k
  have hcast : ((c₀ + N.natAbs * ((pt k).1).toNat : ℕ) : ℤ)
      = (c₀ : ℤ) + (N.natAbs : ℤ) * (pt k).1 := by
    push_cast [Int.toNat_of_nonneg (hptnn k)]; ring
  rw [hcast]
  linear_combination (N.natAbs : ℤ) * hk


/-- Branch A1 wrapper (`hDir`) in data form: if some fibre point has `α(2αc + β) > 0`, the Pell line gives
    a family; otherwise every fibre point obeys the sealed bound. -/
theorem full_rank_dichotomy_of_direction_data (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (hα : alphaMatrix A B C ≠ 0)
    (hw : SignedNonsquareDirection (adjugateQuad (witnessGram C)) (alphaMatrix A B C)) :
    DichotomyMData A B C := by
  obtain ⟨w, hw1, hw2⟩ := hw
  refine ⟨(kBetaM B C).toNat, ?_⟩
  intro l m q
  have hK : (((kBetaM B C).toNat : ℕ) : ℤ) = kBetaM B C := Int.toNat_of_nonneg (kBetaM_nonneg _ _)
  obtain ⟨α, hαdef⟩ : ∃ α : ℤ, α = alphaMatrix A B C := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ℤ, β = betaMatrix B C l m := ⟨_, rfl⟩
  have hα' : α ≠ 0 := by rw [hαdef]; exact hα
  by_cases hex : ∃ c ∈ fiberSetM A B C l m q, 0 < α * (2 * α * (c : ℤ) + β)
  · left
    obtain ⟨c, hc, hgt⟩ := hex
    obtain ⟨u, hu⟩ := hc
    exact fiberSetM_line_family A B C l m q hN w hw1 hw2 c u hu
      (by rw [← hαdef, ← hβdef]; exact hgt)
  · right
    intro c hc
    push_neg at hex
    have hle := hex c hc
    · have hα1 : 1 ≤ |α| := Int.one_le_abs hα'
      have hc0 : (0 : ℤ) ≤ c := by positivity
      have h1 : 2 * α ^ 2 * (c : ℤ) ≤ |α| * |β| := by
        have := neg_abs_le (α * β)
        rw [abs_mul] at this
        nlinarith
      have h2 : |α| * (c : ℤ) ≤ α ^ 2 * (c : ℤ) := by
        have : |α| ≤ α ^ 2 := by rw [← sq_abs]; nlinarith
        exact mul_le_mul_of_nonneg_right this hc0
      have h3 : (c : ℤ) ≤ |β| := by
        have h4 : |α| * (2 * (c : ℤ)) ≤ |α| * |β| := by nlinarith
        have := le_of_mul_le_mul_left h4 (by linarith)
        linarith
      have hβb := betaMatrix_abs_le B C l m
      rw [← hβdef] at hβb
      have hlin := fboundM_core_ge_lin l m q
      have hKnn := kBetaM_nonneg B C
      skip
      rw [hK]
      nlinarith
/-- 必須F step 3, MILESTONE: the full-rank block is UNCONDITIONAL in data-carrying form. -/
theorem full_rank_dichotomy_all_data_full (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (i j : Fin r) (hij : i ≠ j) : DichotomyMData A B C :=
  full_rank_dichotomy_all_data_of_dir A B C hN i j hij
    (fun hα hw => full_rank_dichotomy_of_direction_data A B C hN hα hw)

/-- And it implies the sealed `full_rank_dichotomy_all`. -/
theorem full_rank_dichotomy_all_of_data (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (i j : Fin r) (hij : i ≠ j) : DichotomyM A B C :=
  dichotomyM_of_dichotomyMData (full_rank_dichotomy_all_data_full A B C hN i j hij)

end DiophCompression.SemanticQuadraticMatrix
#print axioms DiophCompression.SemanticQuadraticMatrix.fiberSetM_line_family
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_dichotomy_of_direction_data
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_dichotomy_all_data_full
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_dichotomy_all_of_data
