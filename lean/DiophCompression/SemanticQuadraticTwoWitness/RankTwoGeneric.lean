/-
  DiophCompression/SemanticQuadraticTwoWitness/RankTwoGeneric.lean — GPT r07 必須6 (s8, claude.ai direct).
  The generic rank-2 theorem: α ≠ 0 and a direction w with α·wt(w) < 0, −α·wt(w) not a square ⇒ Dichotomy2.
  For each fiber element (c₀, Y₀): either α·Z₀ ≤ 0 (Z₀ = 2αc₀ + β) and then c₀ ≤ |β|/(2|α|) ≤ |β|, or α·Z₀ > 0
  and the scaled line z' ↦ (c₀ + |N| z', Y₀ + N s w) carries a one-witness Pell form with X₀ = −4|N|·wt(w)·Z₀ > 0,
  so `pell_infinite_of_X_pos` (Class_D7 step) makes the fiber set infinite.
  Frozen statement: `TwoWitness_STATEMENTS_v2.lean` (md5 3e2c4c02). Mathematics: CLASSIFICATION_2W.md §3.1–3.2.
-/
import DiophCompression.SemanticQuadraticTwoWitness.Bounds2W
import DiophCompression.SemanticQuadraticTwoWitness.Directions
import DiophCompression.SemanticQuadraticTwoWitness.PellStep

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadraticGeneral
open DiophCompression.SemanticQuadratic (fq fiberSet disc pell_infinite_of_X_pos)

/-- From one fiber element with α·Z₀ > 0 and a direction w with α·wt(w) < 0 non-square, the fiber set is infinite. -/
theorem fiberSet2_infinite_of_line (A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q : ℤ) (hN : nW C₁₁ C₁₂ C₂₂ ≠ 0)
    (w₁ w₂ : ℤ) (hw1 : schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * wt C₁₁ C₁₂ C₂₂ w₁ w₂ < 0)
    (hw2 : ¬ IsSquare (-(schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * wt C₁₁ C₁₂ C₂₂ w₁ w₂)))
    (c₀ : ℕ) (u₀ v₀ : ℤ) (h0 : fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q (c₀ : ℤ) u₀ v₀ = 0)
    (hZ : 0 < schur A B₁ B₂ C₁₁ C₁₂ C₂₂
      * (2 * schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * (c₀ : ℤ) + betaR B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂)) :
    (fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q).Infinite := by
  obtain ⟨N, hNdef⟩ : ∃ N : ℤ, N = nW C₁₁ C₁₂ C₂₂ := ⟨_, rfl⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℤ, α = schur A B₁ B₂ C₁₁ C₁₂ C₂₂ := ⟨_, rfl⟩
  obtain ⟨Wt, hWt⟩ : ∃ Wt : ℤ, Wt = wt C₁₁ C₁₂ C₂₂ w₁ w₂ := ⟨_, rfl⟩
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : ℤ, Z₀ = 2 * α * (c₀ : ℤ) + betaR B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℤ, B₀ = wtBil C₁₁ C₁₂ C₂₂ (y1 B₁ C₁₁ C₁₂ m₁ (c₀ : ℤ) u₀ v₀)
    (y2 B₂ C₁₂ C₂₂ m₂ (c₀ : ℤ) u₀ v₀) w₁ w₂ := ⟨_, rfl⟩
  rw [← hαdef, ← hWt] at hw1 hw2
  rw [← hαdef, ← hZ₀] at hZ
  have hN' : N ≠ 0 := by rw [hNdef]; exact hN
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε = N.sign := ⟨_, rfl⟩
  have hε2 : ε * ε = 1 := by
    rcases lt_or_gt_of_ne hN' with h | h
    · rw [hε, Int.sign_eq_neg_one_of_neg h]; norm_num
    · rw [hε, Int.sign_eq_one_of_pos h]; norm_num
  have hNε : N * ε = (N.natAbs : ℤ) := by rw [hε]; exact Int.mul_sign_self N
  -- the one-witness Pell form on the scaled line: (A', B', C', l', m', q') = (Nα, 0, N·Wt, ε Z₀, 2B₀, 0)
  have hdisc : disc (N * α) 0 (N * Wt) = (2 * N) ^ 2 * (-(α * Wt)) := by unfold disc; ring
  have hdpos : 0 < disc (N * α) 0 (N * Wt) := by
    rw [hdisc]; have : 0 < (2 * N) ^ 2 := by positivity
    have : 0 < -(α * Wt) := by linarith
    positivity
  have hdns : ¬ IsSquare (disc (N * α) 0 (N * Wt)) := by
    rw [hdisc]; exact not_isSquare_sq_mul (2 * N) _ (by positivity) hw2
  have hmem0 : (0 : ℕ) ∈ fiberSet (N * α) 0 (N * Wt) (ε * Z₀) (2 * B₀) 0 := ⟨0, by unfold fq; ring⟩
  have hX0 : 0 < 2 * disc (N * α) 0 (N * Wt) * ((0 : ℕ) : ℤ) + (2 * 0 * (2 * B₀) - 4 * (N * Wt) * (ε * Z₀)) := by
    -- = −4 N ε Wt Z₀ = −4|N| Wt Z₀ > 0 since Wt Z₀ < 0
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
  have hinf := pell_infinite_of_X_pos (N * α) 0 (N * Wt) (ε * Z₀) (2 * B₀) 0 hdpos hdns 0 hmem0 hX0
  -- transfer along z' ↦ c₀ + |N| z'
  have hM1 : 1 ≤ N.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hN')
  have hinj : Set.InjOn (fun z' : ℕ => c₀ + N.natAbs * z') (fiberSet (N * α) 0 (N * Wt) (ε * Z₀) (2 * B₀) 0) := by
    intro a _ b _ hab
    simp only at hab
    have := Nat.add_left_cancel hab
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  refine Set.Infinite.mono ?_ (hinf.image hinj)
  rintro _ ⟨z', ⟨s, hs⟩, rfl⟩
  simp only
  -- scaled-line equation with z = ε z'
  have hzs : nW C₁₁ C₁₂ C₂₂ * schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * (ε * z') ^ 2
      + (2 * schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * (c₀ : ℤ) + betaR B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂) * (ε * z')
      + 2 * wtBil C₁₁ C₁₂ C₂₂ (y1 B₁ C₁₁ C₁₂ m₁ (c₀ : ℤ) u₀ v₀) (y2 B₂ C₁₂ C₂₂ m₂ (c₀ : ℤ) u₀ v₀) w₁ w₂ * s
      + nW C₁₁ C₁₂ C₂₂ * wt C₁₁ C₁₂ C₂₂ w₁ w₂ * s ^ 2 = 0 := by
    rw [← hNdef, ← hαdef, ← hZ₀, ← hB₀, ← hWt]
    unfold fq at hs
    linear_combination hs + (N * α * (z' : ℤ) ^ 2) * hε2
  obtain ⟨u, v, huv⟩ := scaled_line_solution A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q (c₀ : ℤ) u₀ v₀ w₁ w₂ (ε * z') s hN h0 hzs
  refine ⟨u, v, ?_⟩
  have hNε' : N * ε = |N| := by rw [hNε, Int.natCast_natAbs]
  have e : (((c₀ + N.natAbs * z' : ℕ)) : ℤ) = (c₀ : ℤ) + nW C₁₁ C₁₂ C₂₂ * (ε * z') := by
    push_cast; rw [← hNdef]; linear_combination (-(z' : ℤ)) * hNε'
  rw [e]; exact huv

theorem rank_two_dichotomy_of_line_direction (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hN : nW C₁₁ C₁₂ C₂₂ ≠ 0)
    (hα : schur A B₁ B₂ C₁₁ C₁₂ C₂₂ ≠ 0)
    (hw : ∃ w₁ w₂ : ℤ, schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * wt C₁₁ C₁₂ C₂₂ w₁ w₂ < 0
      ∧ ¬ IsSquare (-(schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * wt C₁₁ C₁₂ C₂₂ w₁ w₂))) :
    Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  obtain ⟨w₁, w₂, hw1, hw2⟩ := hw
  refine ⟨(kBeta B₁ B₂ C₁₁ C₁₂ C₂₂).toNat, ?_⟩
  intro l m₁ m₂ q
  have hK : (((kBeta B₁ B₂ C₁₁ C₁₂ C₂₂).toNat : ℕ) : ℤ) = kBeta B₁ B₂ C₁₁ C₁₂ C₂₂ :=
    Int.toNat_of_nonneg (kBeta_nonneg _ _ _ _ _)
  by_cases hinf : (fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q).Infinite
  · exact Or.inl hinf
  · right
    intro c hc
    obtain ⟨u, v, huv⟩ := hc
    obtain ⟨α, hαdef⟩ : ∃ α : ℤ, α = schur A B₁ B₂ C₁₁ C₁₂ C₂₂ := ⟨_, rfl⟩
    obtain ⟨β, hβdef⟩ : ∃ β : ℤ, β = betaR B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ := ⟨_, rfl⟩
    have hα' : α ≠ 0 := by rw [hαdef]; exact hα
    rcases le_or_gt (α * (2 * α * (c : ℤ) + β)) 0 with hle | hgt
    · -- bounded branch: 2α²c ≤ −αβ ≤ |α||β| ⇒ c ≤ |β|
      have hα1 : 1 ≤ |α| := Int.one_le_abs hα'
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
      have hβb := betaR_abs_le B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂
      rw [← hβdef] at hβb
      have hlin := fbound2_core_ge_lin l m₁ m₂ q
      have hKnn := kBeta_nonneg B₁ B₂ C₁₁ C₁₂ C₂₂
      unfold fbound2; rw [hK]
      calc (c : ℤ) ≤ |β| := h3
        _ ≤ kBeta B₁ B₂ C₁₁ C₁₂ C₂₂ * (1 + |l| + |m₁| + |m₂|) := hβb
        _ ≤ kBeta B₁ B₂ C₁₁ C₁₂ C₂₂ * ((1 + |l| + |m₁| + |m₂|) ^ 2 + |q|) :=
            mul_le_mul_of_nonneg_left hlin hKnn
    · exfalso; apply hinf
      rw [hαdef, hβdef] at hgt
      exact fiberSet2_infinite_of_line A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q hN w₁ w₂ hw1 hw2 c u v huv hgt

end DiophCompression.SemanticQuadraticTwoWitness
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_two_dichotomy_of_line_direction
