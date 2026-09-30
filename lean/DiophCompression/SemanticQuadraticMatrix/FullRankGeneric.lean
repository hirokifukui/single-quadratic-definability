/-
  DiophCompression/SemanticQuadraticMatrix/FullRankGeneric.lean — r09 必須E and the general-r full-rank programme
  (GPT r08 §5/§8): the projection dichotomy for every witness block with det G ≠ 0, all r ≥ 2, in explicit
  coordinates. Mechanism lifted from r08 (RankTwoGeneric / RankTwoAlphaZero / RankTwoLeaves) to vectors through the
  adjugate identity: generic Pell line for α ≠ 0 with a signed non-square direction, α = 0 by periodicity /
  progression / root bound, semidefinite case by the root bound, and the direction lemmas by restriction to a
  binary sublattice (both signs ⇒ indefinite binary form; semidefinite + nondegenerate ⇒ definite binary form on
  two coordinates). Statements frozen first in the frozen statement file `FullRank_STATEMENTS.lean` (md5 b07da190).
  Session 9, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticMatrix.AdjugateIdentity
import DiophCompression.SemanticQuadraticTwoWitness.PellStep
import DiophCompression.SemanticQuadraticTwoWitness.Directions
import DiophCompression.SemanticQuadraticTwoWitness.Bridge2W

namespace DiophCompression.SemanticQuadraticMatrix

open Matrix
open DiophCompression.SemanticQuadratic (fq fiberSet disc pell_infinite_of_X_pos)
open DiophCompression.SemanticQuadraticTwoWitness (periodic_infinite_or_empty
  not_isSquare_sq_mul definite_nonsquare_direction split_signed_nonsquare_direction
  anisotropic_signed_nonsquare_direction)

variable {r : ℕ}

/-- The bound shape K·((1 + |l| + Σ|mᵢ|)² + |q|). -/
def fboundM (K : ℕ) (l : ℤ) (m : Fin r → ℤ) (q : ℤ) : ℤ :=
  (K : ℤ) * ((1 + |l| + ∑ i, |m i|) ^ 2 + |q|)

/-- Projection dichotomy for a fixed quadratic part (A, B, C) with r witnesses. -/
def DichotomyM (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) : Prop :=
  ∃ K : ℕ, ∀ (l : ℤ) (m : Fin r → ℤ) (q : ℤ), (fiberSetM A B C l m q).Infinite ∨
    ∀ c ∈ fiberSetM A B C l m q, (c : ℤ) ≤ fboundM K l m q

/-- GPT r08 必須E: the direction condition. -/
def SignedNonsquareDirection (Q : (Fin r → ℤ) → ℤ) (α : ℤ) : Prop :=
  ∃ w, α * Q w < 0 ∧ ¬ IsSquare (-(α * Q w))

/-- K for β: 2|N| + 2 Σᵢⱼ |Bᵢ (adj G)ᵢⱼ|. -/
def kBetaM (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) : ℤ :=
  2 * |(witnessGram C).det| + 2 * ∑ i, ∑ j, |B i * adjugate (witnessGram C) i j|

/-- K for γ: 2|N| + Σᵢⱼ |(adj G)ᵢⱼ|. -/
def kGammaM (C : Matrix (Fin r) (Fin r) ℤ) : ℤ :=
  2 * |(witnessGram C).det| + ∑ i, ∑ j, |adjugate (witnessGram C) i j|

/-! ## bounds -/

theorem kBetaM_nonneg (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) : 0 ≤ kBetaM B C := by
  unfold kBetaM; positivity

theorem kGammaM_nonneg (C : Matrix (Fin r) (Fin r) ℤ) : 0 ≤ kGammaM C := by
  unfold kGammaM; positivity

theorem abs_dotProduct_mulVec_le (x : Fin r → ℤ) (M : Matrix (Fin r) (Fin r) ℤ) (m : Fin r → ℤ) :
    |x ⬝ᵥ (M *ᵥ m)| ≤ (∑ i, ∑ j, |x i * M i j|) * ∑ j, |m j| := by
  have hS : ∀ j, |m j| ≤ ∑ k, |m k| :=
    fun j => Finset.single_le_sum (fun k _ => abs_nonneg (m k)) (Finset.mem_univ j)
  have e0 : x ⬝ᵥ (M *ᵥ m) = ∑ i, x i * ∑ j, M i j * m j := by
    simp only [dotProduct, Matrix.mulVec]
  rw [e0]
  calc |∑ i, x i * ∑ j, M i j * m j| ≤ ∑ i, |x i * ∑ j, M i j * m j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |x i| * ∑ j, |M i j * m j| := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ = ∑ i, ∑ j, |x i * M i j| * |m j| := by
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        simp only [abs_mul]; ring
    _ ≤ ∑ i, ∑ j, |x i * M i j| * ∑ k, |m k| := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (hS j) (abs_nonneg _)
    _ = (∑ i, ∑ j, |x i * M i j|) * ∑ k, |m k| := by
        simp only [Finset.sum_mul]

theorem betaMatrix_abs_le (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ) (m : Fin r → ℤ) :
    |betaMatrix B C l m| ≤ kBetaM B C * (1 + |l| + ∑ i, |m i|) := by
  unfold betaMatrix kBetaM
  have h1 := abs_dotProduct_mulVec_le B (adjugate (witnessGram C)) m
  have hS : 0 ≤ ∑ i, |m i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hT : 0 ≤ ∑ i, ∑ j, |B i * adjugate (witnessGram C) i j| :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hl := abs_nonneg l
  have hN := abs_nonneg (witnessGram C).det
  have h2 : |2 * (witnessGram C).det * l - 2 * (B ⬝ᵥ (adjugate (witnessGram C) *ᵥ m))|
      ≤ 2 * |(witnessGram C).det| * |l| + 2 * |B ⬝ᵥ (adjugate (witnessGram C) *ᵥ m)| := by
    calc _ ≤ |2 * (witnessGram C).det * l| + |2 * (B ⬝ᵥ (adjugate (witnessGram C) *ᵥ m))| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_mul]; norm_num
  have h3 := abs_nonneg (B ⬝ᵥ (adjugate (witnessGram C) *ᵥ m))
  nlinarith

theorem gammaMatrix_abs_le (C : Matrix (Fin r) (Fin r) ℤ) (m : Fin r → ℤ) (q : ℤ) :
    |gammaMatrix C m q| ≤ kGammaM C * ((1 + ∑ i, |m i|) ^ 2 + |q|) := by
  unfold gammaMatrix kGammaM
  have hS : 0 ≤ ∑ i, |m i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hT : 0 ≤ ∑ i, ∑ j, |adjugate (witnessGram C) i j| :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hq := abs_nonneg q
  have hN := abs_nonneg (witnessGram C).det
  have h1 := abs_dotProduct_mulVec_le m (adjugate (witnessGram C)) m
  have h1' : ∑ i, ∑ j, |m i * adjugate (witnessGram C) i j|
      ≤ (∑ k, |m k|) * ∑ i, ∑ j, |adjugate (witnessGram C) i j| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro j _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => abs_nonneg (m k)) (Finset.mem_univ i)) (abs_nonneg _)
  have h2 : |2 * (witnessGram C).det * q - m ⬝ᵥ (adjugate (witnessGram C) *ᵥ m)|
      ≤ 2 * |(witnessGram C).det| * |q| + |m ⬝ᵥ (adjugate (witnessGram C) *ᵥ m)| := by
    calc _ ≤ |2 * (witnessGram C).det * q| + |m ⬝ᵥ (adjugate (witnessGram C) *ᵥ m)| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_mul]; norm_num
  have h3 := abs_nonneg (m ⬝ᵥ (adjugate (witnessGram C) *ᵥ m))
  have h4 : |m ⬝ᵥ (adjugate (witnessGram C) *ᵥ m)|
      ≤ (∑ i, ∑ j, |adjugate (witnessGram C) i j|) * (∑ k, |m k|) ^ 2 := by
    calc _ ≤ (∑ i, ∑ j, |m i * adjugate (witnessGram C) i j|) * ∑ j, |m j| := h1
      _ ≤ ((∑ k, |m k|) * ∑ i, ∑ j, |adjugate (witnessGram C) i j|) * ∑ j, |m j| :=
          mul_le_mul_of_nonneg_right h1' hS
      _ = _ := by ring
  nlinarith

theorem fboundM_core_ge_lin (l : ℤ) (m : Fin r → ℤ) (q : ℤ) :
    1 + |l| + ∑ i, |m i| ≤ (1 + |l| + ∑ i, |m i|) ^ 2 + |q| := by
  have hS : 0 ≤ ∑ i, |m i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hl := abs_nonneg l; have hq := abs_nonneg q
  nlinarith

theorem fboundM_core_ge_gamma (l : ℤ) (m : Fin r → ℤ) (q : ℤ) :
    (1 + ∑ i, |m i|) ^ 2 + |q| ≤ (1 + |l| + ∑ i, |m i|) ^ 2 + |q| := by
  have hS : 0 ≤ ∑ i, |m i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hl := abs_nonneg l
  nlinarith

theorem fiberSetM_infinite_of_unbounded (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ)
    (m : Fin r → ℤ) (q : ℤ)
    (h : ∀ k : ℕ, ∃ c : ℤ, (k : ℤ) ≤ c ∧ ∃ u : Fin r → ℤ, fqM A B C l m q c u = 0) :
    (fiberSetM A B C l m q).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨k, hk⟩
  obtain ⟨c, hkc, u, hu⟩ := h (k + 1)
  have hc0 : 0 ≤ c := by push_cast at hkc; linarith
  have hmem : c.toNat ∈ fiberSetM A B C l m q := by
    refine ⟨u, ?_⟩
    rw [Int.toNat_of_nonneg hc0]; exact hu
  have := hk hmem
  have : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc0
  push_cast at hkc
  omega

/-! ## (1) the generic theorem -/

/-- The scaled line carries the one-witness Pell form (Nα, 0, N·W̃(w), Z₀, 2B₀, 0) in (t, s):
    2N·F(line) = 2N·F(c₀,u₀) + N·fq(Nα, 0, N·W̃(w), Z₀, 2B₀, 0)(t, s), Z₀ = 2αc₀ + β, B₀ = Y₀·(adj G)w. -/
theorem general_scaled_line_fq (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ)
    (m u₀ w : Fin r → ℤ) (q c₀ t s : ℤ) :
    2 * (witnessGram C).det * fqM A B C l m q (c₀ + (witnessGram C).det * t) (scaledLineU B C u₀ w t s) =
      2 * (witnessGram C).det * fqM A B C l m q c₀ u₀
        + (witnessGram C).det * DiophCompression.SemanticQuadratic.fq
            ((witnessGram C).det * alphaMatrix A B C) 0
            ((witnessGram C).det * adjugateQuad (witnessGram C) w)
            (2 * alphaMatrix A B C * c₀ + betaMatrix B C l m)
            (2 * (completedVector B C m c₀ u₀ ⬝ᵥ (adjugate (witnessGram C) *ᵥ w))) 0 t s := by
  rw [general_scaled_line_identity, general_rank_identity]
  unfold DiophCompression.SemanticQuadratic.fq
  ring

/-- From one fiber element with α·Z₀ > 0 and a direction w with αW̃(w) < 0 non-square, the fiber set is infinite. -/
theorem fiberSetM_infinite_of_line (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ)
    (m : Fin r → ℤ) (q : ℤ) (hN : (witnessGram C).det ≠ 0) (w : Fin r → ℤ)
    (hw1 : alphaMatrix A B C * adjugateQuad (witnessGram C) w < 0)
    (hw2 : ¬ IsSquare (-(alphaMatrix A B C * adjugateQuad (witnessGram C) w)))
    (c₀ : ℕ) (u₀ : Fin r → ℤ) (h0 : fqM A B C l m q (c₀ : ℤ) u₀ = 0)
    (hZ : 0 < alphaMatrix A B C * (2 * alphaMatrix A B C * (c₀ : ℤ) + betaMatrix B C l m)) :
    (fiberSetM A B C l m q).Infinite := by
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
  have hinf := pell_infinite_of_X_pos (N * α) 0 (N * Wt) (ε * Z₀) (2 * B₀) 0 hdpos hdns 0 hmem0 hX0
  have hM1 : 1 ≤ N.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hN')
  have hinj : Set.InjOn (fun z' : ℕ => c₀ + N.natAbs * z')
      (fiberSet (N * α) 0 (N * Wt) (ε * Z₀) (2 * B₀) 0) := by
    intro a _ b _ hab
    simp only at hab
    have := Nat.add_left_cancel hab
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  refine Set.Infinite.mono ?_ (hinf.image hinj)
  rintro _ ⟨z', ⟨s, hs⟩, rfl⟩
  simp only
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

/-- GPT r08 必須E: α ≠ 0 and a signed non-square direction for W̃ ⇒ the dichotomy. -/
theorem full_rank_dichotomy_of_direction (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (hα : alphaMatrix A B C ≠ 0)
    (hw : SignedNonsquareDirection (adjugateQuad (witnessGram C)) (alphaMatrix A B C)) :
    DichotomyM A B C := by
  obtain ⟨w, hw1, hw2⟩ := hw
  refine ⟨(kBetaM B C).toNat, ?_⟩
  intro l m q
  have hK : (((kBetaM B C).toNat : ℕ) : ℤ) = kBetaM B C := Int.toNat_of_nonneg (kBetaM_nonneg _ _)
  by_cases hinf : (fiberSetM A B C l m q).Infinite
  · exact Or.inl hinf
  · right
    intro c hc
    obtain ⟨u, hu⟩ := hc
    obtain ⟨α, hαdef⟩ : ∃ α : ℤ, α = alphaMatrix A B C := ⟨_, rfl⟩
    obtain ⟨β, hβdef⟩ : ∃ β : ℤ, β = betaMatrix B C l m := ⟨_, rfl⟩
    have hα' : α ≠ 0 := by rw [hαdef]; exact hα
    rcases le_or_gt (α * (2 * α * (c : ℤ) + β)) 0 with hle | hgt
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
      unfold fboundM
      rw [hK]
      nlinarith
    · exfalso; apply hinf
      exact fiberSetM_infinite_of_line A B C l m q hN w hw1 hw2 c u hu
        (by rw [← hαdef, ← hβdef]; exact hgt)

/-! ## (2) α = 0 -/

theorem alpha_zero_beta_zero_periodic_M (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ)
    (m : Fin r → ℤ) (q : ℤ) (hN : (witnessGram C).det ≠ 0) (hα : alphaMatrix A B C = 0)
    (hβ : betaMatrix B C l m = 0) (c : ℕ) :
    c ∈ fiberSetM A B C l m q ↔ c + (witnessGram C).det.natAbs ∈ fiberSetM A B C l m q := by
  obtain ⟨N, hNdef⟩ : ∃ N : ℤ, N = (witnessGram C).det := ⟨_, rfl⟩
  have hN' : N ≠ 0 := by rw [hNdef]; exact hN
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε = N.sign := ⟨_, rfl⟩
  have hNε : N * ε = (N.natAbs : ℤ) := by rw [hε]; exact Int.mul_sign_self N
  have hshift : ∀ (c₀ t : ℤ) (u : Fin r → ℤ), fqM A B C l m q c₀ u = 0 →
      fqM A B C l m q (c₀ + N * t) (scaledLineU B C u 0 t 0) = 0 := by
    intro c₀ t u h
    have key := general_scaled_line_fq A B C l m u 0 q c₀ t 0
    rw [← hNdef, hα, hβ, h] at key
    have h2 : 2 * N * fqM A B C l m q (c₀ + N * t) (scaledLineU B C u 0 t 0) = 0 := by
      rw [key]; unfold DiophCompression.SemanticQuadratic.fq; ring
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact absurd (by linarith : N = 0) hN'
    · exact h1
  rw [← hNdef]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨scaledLineU B C u 0 ε 0, ?_⟩
    have := hshift (c : ℤ) ε u hu
    have e : ((c + N.natAbs : ℕ) : ℤ) = (c : ℤ) + N * ε := by rw [Nat.cast_add, hNε]
    rw [e]; exact this
  · rintro ⟨u, hu⟩
    refine ⟨scaledLineU B C u 0 (-ε) 0, ?_⟩
    have := hshift ((c + N.natAbs : ℕ) : ℤ) (-ε) u hu
    have e : ((c + N.natAbs : ℕ) : ℤ) + N * (-ε) = (c : ℤ) := by
      rw [Nat.cast_add]; linear_combination (-1 : ℤ) * hNε
    rw [e] at this; exact this

/-- GPT r08 必須E: α = 0. For every β ≠ 0 either a progression direction (βW̃(w) < 0) or βW̃ ≥ 0 everywhere. -/
theorem full_rank_alpha_zero_dichotomy (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (hα : alphaMatrix A B C = 0)
    (hdir : ∀ β : ℤ, β ≠ 0 → (∃ w, β * adjugateQuad (witnessGram C) w < 0)
      ∨ (∀ Y, 0 ≤ β * adjugateQuad (witnessGram C) Y)) :
    DichotomyM A B C := by
  refine ⟨(kGammaM C).toNat, ?_⟩
  intro l m q
  have hK : (((kGammaM C).toNat : ℕ) : ℤ) = kGammaM C := Int.toNat_of_nonneg (kGammaM_nonneg _)
  obtain ⟨N, hNdef⟩ : ∃ N : ℤ, N = (witnessGram C).det := ⟨_, rfl⟩
  have hN' : N ≠ 0 := by rw [hNdef]; exact hN
  obtain ⟨β, hβdef⟩ : ∃ β : ℤ, β = betaMatrix B C l m := ⟨_, rfl⟩
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℤ, γ = gammaMatrix C m q := ⟨_, rfl⟩
  by_cases hβ : β = 0
  · have hM : 1 ≤ N.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hN')
    have hper := alpha_zero_beta_zero_periodic_M A B C l m q hN hα (by rw [← hβdef]; exact hβ)
    rw [← hNdef] at hper
    rcases periodic_infinite_or_empty _ _ hM hper with hinf | hemp
    · exact Or.inl hinf
    · right; intro c hc; rw [hemp] at hc; exact absurd hc (Set.notMem_empty c)
  · rcases hdir β hβ with ⟨w, hw⟩ | hnn
    · by_cases hne : (fiberSetM A B C l m q).Nonempty
      · left
        obtain ⟨c₀, u₀, h0⟩ := hne
        apply fiberSetM_infinite_of_unbounded
        intro k
        obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℤ,
          B₀ = completedVector B C m (c₀ : ℤ) u₀ ⬝ᵥ (adjugate (witnessGram C) *ᵥ w) := ⟨_, rfl⟩
        obtain ⟨Wt, hWt⟩ : ∃ Wt : ℤ, Wt = adjugateQuad (witnessGram C) w := ⟨_, rfl⟩
        rw [← hWt] at hw
        obtain ⟨t, ht⟩ : ∃ t : ℤ, t = (k : ℤ) + |2 * N * B₀| + (c₀ : ℤ) + 1 := ⟨_, rfl⟩
        have ht1 : 1 ≤ t := by
          rw [ht]; have := abs_nonneg (2 * N * B₀)
          have hk0 : (0 : ℤ) ≤ k := by positivity
          have hc0' : (0 : ℤ) ≤ c₀ := by positivity
          linarith
        obtain ⟨z, hz⟩ : ∃ z : ℤ, z = -2 * B₀ * t - N * Wt * β * t ^ 2 := ⟨_, rfl⟩
        have hline : fqM A B C l m q ((c₀ : ℤ) + N * z) (scaledLineU B C u₀ w z (β * t)) = 0 := by
          have key := general_scaled_line_fq A B C l m u₀ w q (c₀ : ℤ) z (β * t)
          rw [← hNdef, hα, ← hβdef, ← hWt, ← hB₀, h0] at key
          have h2 : 2 * N * fqM A B C l m q ((c₀ : ℤ) + N * z) (scaledLineU B C u₀ w z (β * t)) = 0 := by
            rw [key, hz]; unfold DiophCompression.SemanticQuadratic.fq; ring
          rcases mul_eq_zero.mp h2 with h1 | h1
          · exact absurd (by linarith : N = 0) hN'
          · exact h1
        refine ⟨(c₀ : ℤ) + N * z, ?_, scaledLineU B C u₀ w z (β * t), hline⟩
        rw [hz]
        have ha : 1 ≤ N ^ 2 * (-(Wt * β)) := by
          have h1 : 1 ≤ N ^ 2 := by
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
        have htk : (k : ℤ) + |2 * N * B₀| + 1 ≤ t := by rw [ht]; linarith
        nlinarith
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
      unfold fboundM
      rw [hK]
      calc (c : ℤ) ≤ |γ| := h2
        _ ≤ kGammaM C * ((1 + ∑ i, |m i|) ^ 2 + |q|) := hγ
        _ ≤ kGammaM C * ((1 + |l| + ∑ i, |m i|) ^ 2 + |q|) := mul_le_mul_of_nonneg_left h3 hKnn

/-! ## (3) root bound -/

/-- α ≠ 0 and αW̃ ≥ 0 everywhere (H semidefinite in the α-orientation): c ≤ |β| + |γ|. -/
theorem full_rank_root_bound (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (hα : alphaMatrix A B C ≠ 0)
    (hsemi : ∀ Y, 0 ≤ alphaMatrix A B C * adjugateQuad (witnessGram C) Y) :
    DichotomyM A B C := by
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
  unfold fboundM
  rw [hK]
  nlinarith

/-! ## (4) directions -/

theorem adjugateQuad_smul_add_smul (C : Matrix (Fin r) (Fin r) ℤ) (x y : ℤ) (v w : Fin r → ℤ) :
    adjugateQuad (witnessGram C) (x • v + y • w) =
      adjugateQuad (witnessGram C) v * x ^ 2
        + (2 * (v ⬝ᵥ (adjugate (witnessGram C) *ᵥ w))) * x * y
        + adjugateQuad (witnessGram C) w * y ^ 2 := by
  rw [adjugateQuad_add, adjugateQuad_smul, adjugateQuad_smul, dotProduct_adjugate_smul, smul_dotProduct,
    smul_eq_mul]
  ring

/-- W̃ taking both signs ⇒ signed non-square direction for every h > 0 and σ = ±1. -/
theorem indefinite_signed_nonsquare_direction_M (C : Matrix (Fin r) (Fin r) ℤ) (v w : Fin r → ℤ)
    (hv : 0 < adjugateQuad (witnessGram C) v) (hw : adjugateQuad (witnessGram C) w < 0)
    (h σ : ℤ) (hh : 0 < h) (hσ : σ = 1 ∨ σ = -1) :
    ∃ x : Fin r → ℤ, 0 < σ * adjugateQuad (witnessGram C) x
      ∧ ¬ IsSquare (h * |adjugateQuad (witnessGram C) x|) := by
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = adjugateQuad (witnessGram C) v := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = adjugateQuad (witnessGram C) w := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, b = 2 * (v ⬝ᵥ (adjugate (witnessGram C) *ᵥ w)) := ⟨_, rfl⟩
  rw [← ha] at hv; rw [← hc] at hw
  have hD : 0 < b ^ 2 - 4 * a * c := by
    have : a * c < 0 := mul_neg_of_pos_of_neg hv hw
    nlinarith [sq_nonneg b]
  have hval : ∀ x y : ℤ, adjugateQuad (witnessGram C) (x • v + y • w) = a * x ^ 2 + b * x * y + c * y ^ 2 := by
    intro x y; rw [adjugateQuad_smul_add_smul, ← ha, ← hb, ← hc]
  by_cases hsq : IsSquare (b ^ 2 - 4 * a * c)
  · obtain ⟨x, y, h1, h2⟩ := split_signed_nonsquare_direction a b c h σ hD hsq hh hσ
    exact ⟨x • v + y • w, by rw [hval]; exact h1, by rw [hval]; exact h2⟩
  · obtain ⟨x, y, h1, h2⟩ := anisotropic_signed_nonsquare_direction a b c h σ hD hsq hh hσ
    exact ⟨x • v + y • w, by rw [hval]; exact h1, by rw [hval]; exact h2⟩

/-- Semidefinite (εW̃ ≥ 0, ε ≠ 0) and nondegenerate (N ≠ 0) ⇒ W̃(w) = 0 only at w = 0. -/
theorem eq_zero_of_adjugateQuad_eq_zero (C : Matrix (Fin r) (Fin r) ℤ) (hN : (witnessGram C).det ≠ 0)
    (ε : ℤ) (hε : ε ≠ 0) (hsemi : ∀ Y, 0 ≤ ε * adjugateQuad (witnessGram C) Y)
    (w : Fin r → ℤ) (hw : adjugateQuad (witnessGram C) w = 0) : w = 0 := by
  have hpair : ∀ v : Fin r → ℤ, w ⬝ᵥ (adjugate (witnessGram C) *ᵥ v) = 0 := by
    intro v
    obtain ⟨b, hb⟩ : ∃ b : ℤ, b = w ⬝ᵥ (adjugate (witnessGram C) *ᵥ v) := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d : ℤ, d = adjugateQuad (witnessGram C) v := ⟨_, rfl⟩
    rw [← hb]
    by_contra hb0
    have key := hsemi ((-(ε * b) * (|d| + 1)) • w + (1 : ℤ) • v)
    rw [adjugateQuad_smul_add_smul, hw, ← hb, ← hd] at key
    have hεb : 1 ≤ (ε * b) ^ 2 := by
      have : ε * b ≠ 0 := mul_ne_zero hε hb0
      have : 0 < (ε * b) ^ 2 := by positivity
      omega
    have hd1 := le_abs_self d
    have hε1 : ε * d ≤ |ε| * |d| := by
      have := le_abs_self (ε * d); rw [abs_mul] at this; exact this
    have hε2 : 1 ≤ |ε| := Int.one_le_abs hε
    have hεε : |ε| * |ε| = ε ^ 2 := by rw [← sq, sq_abs]
    have hd0 := abs_nonneg d
    have e : ε * (0 * (-(ε * b) * (|d| + 1)) ^ 2 + 2 * b * (-(ε * b) * (|d| + 1)) * 1 + d * 1 ^ 2)
        = -2 * (ε * b) ^ 2 * (|d| + 1) + ε * d := by ring
    rw [e] at key
    have h3 : (ε * b) ^ 2 * (|d| + 1) ≥ |d| + 1 := by nlinarith
    have h4 : ε * d ≤ |ε| * |d| := hε1
    have h5 : |ε| * |d| ≤ (ε * b) ^ 2 * |d| := by
      have : |ε| ≤ (ε * b) ^ 2 := by
        have : |ε| ≤ ε ^ 2 := by rw [← hεε]; nlinarith
        have : ε ^ 2 ≤ (ε * b) ^ 2 := by
          have hb1 : 1 ≤ b ^ 2 := by
            have : 0 < b ^ 2 := by positivity
            omega
          nlinarith [sq_nonneg ε]
        linarith
      exact mul_le_mul_of_nonneg_right this hd0
    nlinarith
  have hadj : adjugate (witnessGram C) *ᵥ w = 0 := by
    ext i
    have := hpair (Pi.single i 1)
    rw [adjugate_pairing_comm, single_dotProduct, one_mul] at this
    simpa using this
  have h2 := witnessGram_mulVec_adjugate C w
  rw [hadj, mulVec_zero] at h2
  rcases smul_eq_zero.mp h2.symm with h | h
  · exact absurd h hN
  · exact h

/-- Semidefinite and nondegenerate ⇒ W̃ takes a value of the sign of ε. -/
theorem exists_adjugateQuad_sign (C : Matrix (Fin r) (Fin r) ℤ) (hN : (witnessGram C).det ≠ 0)
    (i : Fin r) (ε : ℤ) (hε : ε ≠ 0) (hsemi : ∀ Y, 0 ≤ ε * adjugateQuad (witnessGram C) Y) :
    ∃ w, 0 < ε * adjugateQuad (witnessGram C) w := by
  refine ⟨Pi.single i 1, ?_⟩
  have h1 := hsemi (Pi.single i 1)
  rcases h1.lt_or_eq with h | h
  · exact h
  · exfalso
    have hQ : adjugateQuad (witnessGram C) (Pi.single i 1) = 0 := by
      rcases mul_eq_zero.mp h.symm with h' | h'
      · exact absurd h' hε
      · exact h'
    have h0 := eq_zero_of_adjugateQuad_eq_zero C hN ε hε hsemi _ hQ
    have := congrFun h0 i
    simp at this

/-- −αW̃ ≥ 0 everywhere, α ≠ 0, N ≠ 0, two coordinates i ≠ j ⇒ signed non-square direction for α
    (restriction to the (i, j)-plane is a positive definite binary form with even cross term). -/
theorem definite_signed_nonsquare_direction_M (C : Matrix (Fin r) (Fin r) ℤ) (hN : (witnessGram C).det ≠ 0)
    (i j : Fin r) (hij : i ≠ j) (α : ℤ) (hα : α ≠ 0)
    (hsemi : ∀ Y, 0 ≤ -(α * adjugateQuad (witnessGram C) Y)) :
    SignedNonsquareDirection (adjugateQuad (witnessGram C)) α := by
  obtain ⟨p, hp⟩ : ∃ p : ℤ, p = -α * adjugateQuad (witnessGram C) (Pi.single i 1) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℤ, q = -α * adjugateQuad (witnessGram C) (Pi.single j 1) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℤ,
    e = -2 * α * (Pi.single i 1 ⬝ᵥ (adjugate (witnessGram C) *ᵥ Pi.single j 1)) := ⟨_, rfl⟩
  have hT : ∀ x y : ℤ, -(α * adjugateQuad (witnessGram C) (x • Pi.single i 1 + y • Pi.single j 1))
      = p * x ^ 2 + e * x * y + q * y ^ 2 := by
    intro x y; rw [adjugateQuad_smul_add_smul, hp, hq, he]; ring
  have hTnn : ∀ x y : ℤ, 0 ≤ p * x ^ 2 + e * x * y + q * y ^ 2 := fun x y => by
    rw [← hT]; exact hsemi _
  have hne : ∀ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) →
      x • (Pi.single i 1 : Fin r → ℤ) + y • (Pi.single j 1 : Fin r → ℤ) ≠ 0 := by
    intro x y hxy h0
    have hi := congrFun h0 i
    have hj := congrFun h0 j
    simp [Pi.single_apply, hij, Ne.symm hij] at hi hj
    rcases hxy with hx | hy
    · exact hx hi
    · exact hy hj
  have hsemi' : ∀ Y, 0 ≤ (-α) * adjugateQuad (witnessGram C) Y := fun Y => by
    have := hsemi Y; linarith
  have hTpos : ∀ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) → 0 < p * x ^ 2 + e * x * y + q * y ^ 2 := by
    intro x y hxy
    rcases (hTnn x y).lt_or_eq with h | h
    · exact h
    · exfalso
      have hQ : adjugateQuad (witnessGram C) (x • Pi.single i 1 + y • Pi.single j 1) = 0 := by
        have h1 := hT x y
        rw [← h] at h1
        have h2 : α * adjugateQuad (witnessGram C) (x • Pi.single i 1 + y • Pi.single j 1) = 0 := by
          linarith
        rcases mul_eq_zero.mp h2 with h' | h'
        · exact absurd h' hα
        · exact h'
      exact hne x y hxy
        (eq_zero_of_adjugateQuad_eq_zero C hN (-α) (neg_ne_zero.mpr hα) hsemi' _ hQ)
  have hp0 : 0 < p := by
    have := hTpos 1 0 (Or.inl one_ne_zero)
    simpa using this
  have hq0 : 0 < q := by
    have := hTpos 0 1 (Or.inr one_ne_zero)
    simpa using this
  have hdef : e ^ 2 < 4 * p * q := by
    have h1 := hTpos e (-2 * p) (Or.inr (by linarith))
    have h2 : p * e ^ 2 + e * e * (-2 * p) + q * (-2 * p) ^ 2 = p * (4 * p * q - e ^ 2) := by ring
    rw [h2] at h1
    by_contra hc
    push Not at hc
    nlinarith
  have heven : Even e :=
    ⟨-α * (Pi.single i 1 ⬝ᵥ (adjugate (witnessGram C) *ᵥ Pi.single j 1)), by rw [he]; ring⟩
  obtain ⟨x, y, h1, h2⟩ := definite_nonsquare_direction p e q hp0 hq0 hdef heven
  refine ⟨x • Pi.single i 1 + y • Pi.single j 1, ?_, ?_⟩
  · have := hT x y; linarith
  · rw [hT x y]; exact h2

/-! ## (5) assembly -/

/-- The full-rank projection dichotomy in explicit coordinates, every r with two distinct coordinates. -/
theorem full_rank_dichotomy_all (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (hN : (witnessGram C).det ≠ 0) (i j : Fin r) (hij : i ≠ j) : DichotomyM A B C := by
  obtain ⟨α, hαdef⟩ : ∃ α : ℤ, α = alphaMatrix A B C := ⟨_, rfl⟩
  by_cases hneg : ∃ w, adjugateQuad (witnessGram C) w < 0
  · by_cases hpos : ∃ w, 0 < adjugateQuad (witnessGram C) w
    · obtain ⟨v, hv⟩ := hpos
      obtain ⟨w, hw⟩ := hneg
      rcases lt_trichotomy α 0 with hlt | heq | hgt
      · obtain ⟨x, h1, h2⟩ :=
          indefinite_signed_nonsquare_direction_M C v w hv hw (-α) 1 (by linarith) (Or.inl rfl)
        rw [one_mul] at h1
        apply full_rank_dichotomy_of_direction A B C hN (by rw [← hαdef]; exact hlt.ne)
        refine ⟨x, ?_, ?_⟩
        · rw [← hαdef]; exact mul_neg_of_neg_of_pos hlt h1
        · rw [← hαdef, show -(α * adjugateQuad (witnessGram C) x) = (-α) * |adjugateQuad (witnessGram C) x| by
            rw [abs_of_pos h1]; ring]
          exact h2
      · apply full_rank_alpha_zero_dichotomy A B C hN (by rw [← hαdef]; exact heq)
        intro β hβ
        rcases lt_or_gt_of_ne hβ with hb | hb
        · exact Or.inl ⟨v, mul_neg_of_neg_of_pos hb hv⟩
        · exact Or.inl ⟨w, mul_neg_of_pos_of_neg hb hw⟩
      · obtain ⟨x, h1, h2⟩ :=
          indefinite_signed_nonsquare_direction_M C v w hv hw α (-1) hgt (Or.inr rfl)
        have h1' : adjugateQuad (witnessGram C) x < 0 := by linarith
        apply full_rank_dichotomy_of_direction A B C hN (by rw [← hαdef]; exact hgt.ne')
        refine ⟨x, ?_, ?_⟩
        · rw [← hαdef]; exact mul_neg_of_pos_of_neg hgt h1'
        · rw [← hαdef, show -(α * adjugateQuad (witnessGram C) x) = α * |adjugateQuad (witnessGram C) x| by
            rw [abs_of_neg h1']; ring]
          exact h2
    · push Not at hpos
      rcases lt_trichotomy α 0 with hlt | heq | hgt
      · exact full_rank_root_bound A B C hN (by rw [← hαdef]; exact hlt.ne)
          (fun Y => by rw [← hαdef]; exact mul_nonneg_of_nonpos_of_nonpos hlt.le (hpos Y))
      · apply full_rank_alpha_zero_dichotomy A B C hN (by rw [← hαdef]; exact heq)
        intro β hβ
        rcases lt_or_gt_of_ne hβ with hb | hb
        · exact Or.inr (fun Y => mul_nonneg_of_nonpos_of_nonpos hb.le (hpos Y))
        · obtain ⟨w, hw⟩ := hneg
          exact Or.inl ⟨w, mul_neg_of_pos_of_neg hb hw⟩
      · apply full_rank_dichotomy_of_direction A B C hN (by rw [← hαdef]; exact hgt.ne')
        rw [← hαdef]
        exact definite_signed_nonsquare_direction_M C hN i j hij α hgt.ne'
          (fun Y => by have := hpos Y; nlinarith)
  · push Not at hneg
    rcases lt_trichotomy α 0 with hlt | heq | hgt
    · apply full_rank_dichotomy_of_direction A B C hN (by rw [← hαdef]; exact hlt.ne)
      rw [← hαdef]
      exact definite_signed_nonsquare_direction_M C hN i j hij α hlt.ne
        (fun Y => by have := hneg Y; nlinarith)
    · apply full_rank_alpha_zero_dichotomy A B C hN (by rw [← hαdef]; exact heq)
      intro β hβ
      rcases lt_or_gt_of_ne hβ with hb | hb
      · obtain ⟨w, hw⟩ := exists_adjugateQuad_sign C hN i 1 one_ne_zero (fun Y => by rw [one_mul]; exact hneg Y)
        rw [one_mul] at hw
        exact Or.inl ⟨w, mul_neg_of_neg_of_pos hb hw⟩
      · exact Or.inr (fun Y => mul_nonneg hb.le (hneg Y))
    · exact full_rank_root_bound A B C hN (by rw [← hαdef]; exact hgt.ne')
        (fun Y => by rw [← hαdef]; exact mul_nonneg hgt.le (hneg Y))

/-- GPT r08 必須E (named). Despite its name this theorem takes **no direction hypothesis**: the direction
    property is established internally (`full_rank_dichotomy_all`, parity-free assembly on the sign pattern
    of the adjugate form), so this is simply the explicit-coordinate full-rank dichotomy for every (A, B, C)
    with N ≠ 0 and every r ≥ 2 (`hr` supplies two distinct witness indices). The name is kept for reference
    stability (it is cited in the r08/r09 correspondence); the transport to the abstract predicate
    `DichotomyG` exists only for r = 3 (`SemanticQuadraticThreeWitness/Bridge3W.lean`). Docstring corrected
    in r10 (GPT r09 §6, E-r10-2). -/
theorem full_rank_projection_dichotomy_of_direction_property (hr : 2 ≤ r) :
    ∀ (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ), (witnessGram C).det ≠ 0 → DichotomyM A B C := by
  intro A B C hN
  exact full_rank_dichotomy_all A B C hN ⟨0, by omega⟩ ⟨1, by omega⟩
    (by intro h; have := congrArg Fin.val h; simp at this)

end DiophCompression.SemanticQuadraticMatrix

#print axioms DiophCompression.SemanticQuadraticMatrix.kBetaM_nonneg
#print axioms DiophCompression.SemanticQuadraticMatrix.kGammaM_nonneg
#print axioms DiophCompression.SemanticQuadraticMatrix.abs_dotProduct_mulVec_le
#print axioms DiophCompression.SemanticQuadraticMatrix.betaMatrix_abs_le
#print axioms DiophCompression.SemanticQuadraticMatrix.gammaMatrix_abs_le
#print axioms DiophCompression.SemanticQuadraticMatrix.fboundM_core_ge_lin
#print axioms DiophCompression.SemanticQuadraticMatrix.fboundM_core_ge_gamma
#print axioms DiophCompression.SemanticQuadraticMatrix.fiberSetM_infinite_of_unbounded
#print axioms DiophCompression.SemanticQuadraticMatrix.general_scaled_line_fq
#print axioms DiophCompression.SemanticQuadraticMatrix.fiberSetM_infinite_of_line
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_dichotomy_of_direction
#print axioms DiophCompression.SemanticQuadraticMatrix.alpha_zero_beta_zero_periodic_M
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_alpha_zero_dichotomy
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_root_bound
#print axioms DiophCompression.SemanticQuadraticMatrix.adjugateQuad_smul_add_smul
#print axioms DiophCompression.SemanticQuadraticMatrix.indefinite_signed_nonsquare_direction_M
#print axioms DiophCompression.SemanticQuadraticMatrix.eq_zero_of_adjugateQuad_eq_zero
#print axioms DiophCompression.SemanticQuadraticMatrix.exists_adjugateQuad_sign
#print axioms DiophCompression.SemanticQuadraticMatrix.definite_signed_nonsquare_direction_M
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_dichotomy_all
#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_projection_dichotomy_of_direction_property
