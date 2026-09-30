/-
  DiophCompression/SemanticQuadratic/PellDichotomyData.lean — APAL Structural Theory Gate 5,
  必須F step 3 (leaf D7 wrapper) (s28, 2026-09-02, claude.ai direct).

  Branch D7 in data-carrying form. The bounded branch is the sealed argument of `dichotomy_pell`,
  verbatim. The infinite branch no longer iterates a step inside an existence proof: it calls the hub
  `pell_orbit_of_X_pos`, which returns the orbit itself, and packages it as the `pell` constructor of
  `OneWitnessFamilyData`. Outputs are natural numbers because the orbit output starts at `c₀` and is
  strictly increasing. No sorry; std-3.
-/
import DiophCompression.SemanticQuadratic.FiberDichotomyData
import DiophCompression.SemanticQuadratic.PellOrbitOfXPos

namespace DiophCompression.SemanticQuadratic

open MPUP

theorem dichotomy_pell_data (A B C : ℤ) (h : 0 < disc A B C) (hns : ¬ IsSquare (disc A B C)) :
    DichotomyOneWitnessData A B C := by
  obtain ⟨D, hDdef⟩ : ∃ D : ℤ, D = disc A B C := ⟨_, rfl⟩
  have hDpos : 0 < D := by rw [hDdef]; exact h
  -- K and the fiber
  refine ⟨(2 * |B| + 4 * |C|).toNat, ?_⟩
  have hK : (((2 * |B| + 4 * |C|).toNat : ℕ) : ℤ) = 2 * |B| + 4 * |C| := Int.toNat_of_nonneg (by positivity)
  intro l m q
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, β = 2 * B * m - 4 * C * l := ⟨_, rfl⟩
  have hl := abs_nonneg l; have hm := abs_nonneg m; have hq' := abs_nonneg q
  have hβb : |β| ≤ (2 * |B| + 4 * |C|) * (1 + |l| + |m|) := by
    rw [hβ]
    calc |2 * B * m - 4 * C * l| ≤ |2 * B * m| + |4 * C * l| := abs_sub _ _
      _ = 2 * |B| * |m| + 4 * |C| * |l| := by simp [abs_mul]
      _ ≤ (2 * |B| + 4 * |C|) * (1 + |l| + |m|) := by
        nlinarith [mul_nonneg (abs_nonneg B) hl, mul_nonneg (abs_nonneg C) hm, abs_nonneg B, abs_nonneg C]
  by_cases hall : ∀ c ∈ fiberSet A B C l m q, 2 * D * (c : ℤ) + β ≤ 0
  · right
    intro c hc
    have hX := hall c hc
    have hc0 : (0 : ℤ) ≤ c := by exact_mod_cast Nat.zero_le c
    have h1 : (c : ℤ) ≤ 2 * D * c := le_mul_of_one_le_left hc0 (by linarith)
    have h2 : 2 * D * (c : ℤ) ≤ |β| := by linarith [neg_le_abs β]
    have hx0 : (1 : ℤ) ≤ 1 + |l| + |m| := by linarith
    have hx1 : 1 + |l| + |m| ≤ (1 + |l| + |m|) ^ 2 := le_self_pow₀ hx0 (by norm_num)
    unfold fbound; rw [hK]
    have h3 : (2 * |B| + 4 * |C|) * (1 + |l| + |m|) ≤ (2 * |B| + 4 * |C|) * ((1 + |l| + |m|) ^ 2 + |q|) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · left
    push_neg at hall
    obtain ⟨c₀, hc₀, hX₀⟩ := hall
    rw [hβ, hDdef] at hX₀
    obtain ⟨P, Q, Y₀, pt, unit, hP2, hpt0, hmem, hout, hmono⟩ :=
      pell_orbit_of_X_pos A B C l m q h hns c₀ hc₀ hX₀
    -- the outputs are naturals: they start at c₀ and increase
    have hge : ∀ k : ℕ, (c₀ : ℤ) ≤ (pt k).1 := by
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [hpt0]
      · have := hmono (Nat.pos_of_ne_zero (by omega) : 0 < k)
        simp only at this
        rw [hpt0] at this
        linarith
    have hnn : ∀ k : ℕ, 0 ≤ (pt k).1 := fun k =>
      le_trans (by exact_mod_cast Nat.zero_le c₀) (hge k)
    have hD2 : (2 * disc A B C : ℤ) ≠ 0 := by positivity
    refine ⟨OneWitnessFamilyData.pell P Q
      (fun k => (DiophCompression.pellOrbit (disc A B C) P Q
        (2 * disc A B C * (c₀ : ℤ) + (2 * B * m - 4 * C * l)) Y₀ k).1)
      (fun k => (DiophCompression.pellOrbit (disc A B C) P Q
        (2 * disc A B C * (c₀ : ℤ) + (2 * B * m - 4 * C * l)) Y₀ k).2)
      (fun k => DiophCompression.pellOrbit_succ_fst _ _ _ _ _ k)
      (fun k => DiophCompression.pellOrbit_succ_snd _ _ _ _ _ k)
      (2 * disc A B C) 1 (-(2 * B * m - 4 * C * l)) hD2
      (fun k => ((pt k).1).toNat) (fun k => (pt k).2) (fun k => ?_) unit hP2 ?_ ?_⟩
    · rw [Int.toNat_of_nonneg (hnn k)]
      linarith [hout k]
    · intro k
      rw [Int.toNat_of_nonneg (hnn k)]
      exact hmem k
    · intro i j hij
      have h1 := hmono hij
      simp only at h1
      have hb : 0 < (pt j).1 := lt_of_le_of_lt (hnn i) h1
      simp only
      exact (Int.toNat_lt_toNat hb).mpr h1

end DiophCompression.SemanticQuadratic

#print axioms DiophCompression.SemanticQuadratic.dichotomy_pell_data
