import DiophCompression.SemanticQuadratic.FiberDefs
namespace DiophCompression.SemanticQuadratic
open MPUP

theorem fiberSet_infinite_of_family' (A B C l m q : ℤ) (c₀ : ℕ) (s : ℕ) (hs : 1 ≤ s)
    (ut : ℕ → ℤ) (hfam : ∀ t : ℕ, fq A B C l m q ((c₀ + s * t : ℕ) : ℤ) (ut t) = 0) :
    (fiberSet A B C l m q).Infinite := by
  apply Set.infinite_of_not_bddAbove
  intro ⟨M, hM⟩
  have hmem : c₀ + s * (M + 1) ∈ fiberSet A B C l m q := ⟨ut (M + 1), hfam (M + 1)⟩
  have := hM hmem
  nlinarith

theorem dichotomy_square_C_zero (A B C : ℤ) (h : 0 < disc A B C) (hC : C = 0) : Dichotomy A B C := by
  subst hC
  have hB : B ≠ 0 := by
    intro hB0; subst hB0; unfold disc at h; norm_num at h
  have hB1 : 1 ≤ |B| := Int.one_le_abs hB
  refine ⟨(B ^ 2 + |B| + |A| + 1).toNat, ?_⟩
  have hK : (((B ^ 2 + |B| + |A| + 1).toNat : ℕ) : ℤ) = B ^ 2 + |B| + |A| + 1 := by
    rw [Int.toNat_of_nonneg]; have := abs_nonneg A; have := abs_nonneg B; have := sq_nonneg B; omega
  intro l m q
  have hl := abs_nonneg l; have hm := abs_nonneg m; have hq := abs_nonneg q; have hA := abs_nonneg A
  have hBsq : (0 : ℤ) ≤ B ^ 2 := sq_nonneg B
  -- bound of a c with B c + m = 0
  have hzero_bound : ∀ c : ℕ, B * (c : ℤ) + m = 0 → (c : ℤ) ≤ |m| := by
    intro c hc
    have hc0 : (0 : ℤ) ≤ c := by exact_mod_cast Nat.zero_le c
    have : |B| * (c : ℤ) = |m| := by
      rw [← abs_of_nonneg hc0, ← abs_mul, show B * (c : ℤ) = -m by linarith, abs_neg]
    nlinarith
  have hfb : ∀ c : ℕ, (c : ℤ) ≤ |m| → (c : ℤ) ≤ fbound (B ^ 2 + |B| + |A| + 1).toNat l m q := by
    intro c hc; unfold fbound; rw [hK]
    nlinarith [sq_nonneg (1 + |l| + |m|), mul_nonneg hBsq hq, mul_nonneg hBsq (sq_nonneg (1 + |l| + |m|)),
      mul_nonneg (abs_nonneg B) (sq_nonneg (1 + |l| + |m|)), mul_nonneg hA (sq_nonneg (1 + |l| + |m|)),
      mul_nonneg hBsq hq, mul_nonneg (abs_nonneg B) hq, mul_nonneg hA hq]
  by_cases hall : ∀ c ∈ fiberSet A B 0 l m q, B * (c : ℤ) + m = 0
  · right
    intro c hc
    exact hfb c (hzero_bound c (hall c hc))
  · push Not at hall
    obtain ⟨c₁, ⟨u₁, hu₁⟩, hne⟩ := hall
    simp only [fq] at hu₁
    set R := B ^ 2 * q - B * l * m + A * m ^ 2 with hR
    -- (B c₁ + m) * (B² u₁ + A B c₁ + B l - A m) = -R
    have hkey : (B * (c₁ : ℤ) + m) * (B ^ 2 * u₁ + A * B * c₁ + B * l - A * m) = -R := by
      rw [hR]; linear_combination B ^ 2 * hu₁
    by_cases hR0 : R = 0
    · left
      have hu₁' : B ^ 2 * u₁ = -(A * B * (c₁ : ℤ) + B * l - A * m) := by
        have h0 : (B * (c₁ : ℤ) + m) * (B ^ 2 * u₁ + A * B * c₁ + B * l - A * m) = 0 := by
          rw [hkey, hR0, neg_zero]
        rcases mul_eq_zero.mp h0 with h1 | h1
        · exact absurd h1 hne
        · linarith
      have hs : 1 ≤ (B ^ 2).toNat := by
        have : 1 ≤ B ^ 2 := by nlinarith [sq_abs B]
        omega
      refine fiberSet_infinite_of_family' A B 0 l m q c₁ (B ^ 2).toNat hs (fun t => u₁ - A * B * t) ?_
      intro t
      have hB2 : (((B ^ 2).toNat : ℕ) : ℤ) = B ^ 2 := Int.toNat_of_nonneg hBsq
      push_cast
      rw [hB2]
      simp only [fq]
      have hB2ne : B ^ 2 ≠ 0 := pow_ne_zero 2 hB
      apply mul_left_cancel₀ hB2ne
      rw [mul_zero]
      linear_combination (B * (c₁ : ℤ) + m + B ^ 2 * B * t) * hu₁' + hR0 + B ^ 2 * hu₁
        - B ^ 2 * hu₁
    · right
      intro c hc
      obtain ⟨u, hu⟩ := hc
      simp only [fq] at hu
      by_cases hz : B * (c : ℤ) + m = 0
      · exact hfb c (hzero_bound c hz)
      · have hdvd : (B * (c : ℤ) + m) ∣ R := by
          refine ⟨-(B ^ 2 * u + A * B * c + B * l - A * m), ?_⟩
          rw [hR]; linear_combination B ^ 2 * hu
        have hle : |B * (c : ℤ) + m| ≤ |R| :=
          Int.le_of_dvd (abs_pos.mpr hR0) ((abs_dvd_abs _ _).mpr hdvd)
        have hc0 : (0 : ℤ) ≤ c := by exact_mod_cast Nat.zero_le c
        have h1 : |B| * (c : ℤ) ≤ |R| + |m| := by
          have : |B * (c : ℤ)| ≤ |B * c + m| + |m| := by
            calc |B * (c : ℤ)| = |(B * c + m) - m| := by ring_nf
              _ ≤ |B * (c : ℤ) + m| + |m| := abs_sub _ _
          rw [abs_mul, abs_of_nonneg hc0] at this
          linarith
        have h2 : (c : ℤ) ≤ |R| + |m| := by nlinarith [abs_nonneg R]
        have hRb : |R| ≤ B ^ 2 * |q| + |B| * |l| * |m| + |A| * |m| ^ 2 := by
          rw [hR]
          calc |B ^ 2 * q - B * l * m + A * m ^ 2|
              ≤ |B ^ 2 * q - B * l * m| + |A * m ^ 2| := abs_add_le _ _
            _ ≤ |B ^ 2 * q| + |B * l * m| + |A * m ^ 2| := by linarith [abs_sub (B ^ 2 * q) (B * l * m)]
            _ = B ^ 2 * |q| + |B| * |l| * |m| + |A| * |m| ^ 2 := by simp [abs_mul, sq_abs]
        unfold fbound; rw [hK]
        set S := (1 + |l| + |m|) ^ 2 with hS
        have hS0 : 0 ≤ S := sq_nonneg _
        have e1 : |l| * |m| ≤ S := by rw [hS]; nlinarith
        have e2 : |m| ^ 2 ≤ S := by rw [hS]; nlinarith
        have e3 : |m| ≤ S := by rw [hS]; nlinarith
        have f1 : B ^ 2 * |q| ≤ B ^ 2 * (S + |q|) := by nlinarith
        have f2 : |B| * |l| * |m| ≤ |B| * (S + |q|) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg B)
        have f3 : |A| * |m| ^ 2 ≤ |A| * (S + |q|) :=
          mul_le_mul_of_nonneg_left (by linarith) hA
        have f4 : |m| ≤ 1 * (S + |q|) := by rw [one_mul]; linarith
        have hR2 : (c : ℤ) ≤ B ^ 2 * (S + |q|) + |B| * (S + |q|) + |A| * (S + |q|) + 1 * (S + |q|) := by
          linarith [h2, hRb, f1, f2, f3, f4]
        calc (c : ℤ) ≤ B ^ 2 * (S + |q|) + |B| * (S + |q|) + |A| * (S + |q|) + 1 * (S + |q|) := hR2
          _ = (B ^ 2 + |B| + |A| + 1) * (S + |q|) := by ring

end DiophCompression.SemanticQuadratic
#print axioms DiophCompression.SemanticQuadratic.dichotomy_square_C_zero
