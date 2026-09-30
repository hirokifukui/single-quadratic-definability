import DiophCompression.SemanticQuadratic.FiberDefs
namespace DiophCompression.SemanticQuadratic
open MPUP

theorem fiberSet_infinite_of_family'' (A B C l m q : ℤ) (c₀ : ℕ) (s : ℕ) (hs : 1 ≤ s)
    (ut : ℕ → ℤ) (hfam : ∀ t : ℕ, fq A B C l m q ((c₀ + s * t : ℕ) : ℤ) (ut t) = 0) :
    (fiberSet A B C l m q).Infinite := by
  apply Set.infinite_of_not_bddAbove
  intro ⟨M, hM⟩
  have hmem : c₀ + s * (M + 1) ∈ fiberSet A B C l m q := ⟨ut (M + 1), hfam (M + 1)⟩
  have := hM hmem
  nlinarith

/-- The square-class family, as one polynomial identity: s = ±1 is the sign in Y₀ = s X₀, σ is any integer
(used as the sign of C to make the step positive). -/
theorem square_family_identity (A B C l m q δ s σ c₀ u₀ t : ℤ)
    (hs : s * s = 1) (hδ : δ ^ 2 = B ^ 2 - 4 * A * C)
    (hN : (2 * B * m - 4 * C * l) ^ 2 - 4 * δ ^ 2 * (m ^ 2 - 4 * C * q) = 0)
    (hY : 2 * δ * (2 * C * u₀ + B * c₀ + m) = s * (2 * δ ^ 2 * c₀ + (2 * B * m - 4 * C * l))) :
    4 * δ ^ 2 * (4 * C * fq A B C l m q (c₀ + 2 * σ * C * δ * t) (u₀ + σ * (s * δ ^ 2 - B * δ) * t)) = 0 := by
  unfold fq
  linear_combination
    (2 * δ * (2 * C * (u₀ + σ * (s * δ ^ 2 - B * δ) * t) + B * (c₀ + 2 * σ * C * δ * t) + m)
      + s * (2 * δ ^ 2 * (c₀ + 2 * σ * C * δ * t) + (2 * B * m - 4 * C * l))) * hY
    + (2 * δ ^ 2 * (c₀ + 2 * σ * C * δ * t) + (2 * B * m - 4 * C * l)) ^ 2 * hs
    + hN + 4 * δ ^ 2 * (c₀ + 2 * σ * C * δ * t) ^ 2 * hδ

theorem dichotomy_square_C_ne (A B C : ℤ) (h : 0 < disc A B C) (hs : IsSquare (disc A B C)) (hC : C ≠ 0) :
    Dichotomy A B C := by
  obtain ⟨r, hr⟩ := hs
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℤ, δ = |r| := ⟨_, rfl⟩
  have hδsq : δ ^ 2 = B ^ 2 - 4 * A * C := by rw [hδdef, sq_abs, sq, ← hr]; rfl
  have hδpos : 1 ≤ δ := by
    have : r ≠ 0 := by rintro rfl; simp at hr; rw [hr] at h; exact lt_irrefl _ h
    rw [hδdef]; exact Int.one_le_abs this
  have hC1 : 1 ≤ |C| := Int.one_le_abs hC
  have hl' := abs_nonneg B; have hC' := abs_nonneg C
  refine ⟨((2 * |B| + 4 * |C|) ^ 2 + 4 * disc A B C * (1 + 4 * |C|) + 2 * |B| + 4 * |C|).toNat, ?_⟩
  have hK : ((((2 * |B| + 4 * |C|) ^ 2 + 4 * disc A B C * (1 + 4 * |C|) + 2 * |B| + 4 * |C|).toNat : ℕ) : ℤ)
      = (2 * |B| + 4 * |C|) ^ 2 + 4 * disc A B C * (1 + 4 * |C|) + 2 * |B| + 4 * |C| := by
    rw [Int.toNat_of_nonneg]; have := sq_nonneg (2 * |B| + 4 * |C|); positivity
  intro l m q
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, β = 2 * B * m - 4 * C * l := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℤ, γ = m ^ 2 - 4 * C * q := ⟨_, rfl⟩
  obtain ⟨N', hN'⟩ : ∃ N' : ℤ, N' = β ^ 2 - 4 * δ ^ 2 * γ := ⟨_, rfl⟩
  have hl := abs_nonneg l; have hm := abs_nonneg m; have hq := abs_nonneg q
  -- shared bounds
  have hβb : |β| ≤ (2 * |B| + 4 * |C|) * (1 + |l| + |m|) := by
    rw [hβ]
    calc |2 * B * m - 4 * C * l| ≤ |2 * B * m| + |4 * C * l| := abs_sub _ _
      _ = 2 * |B| * |m| + 4 * |C| * |l| := by simp [abs_mul]
      _ ≤ (2 * |B| + 4 * |C|) * (1 + |l| + |m|) := by nlinarith [mul_nonneg hl' hl, mul_nonneg hC' hm]
  have hγb : |γ| ≤ |m| ^ 2 + 4 * |C| * |q| := by
    rw [hγ]
    calc |m ^ 2 - 4 * C * q| ≤ |m ^ 2| + |4 * C * q| := abs_sub _ _
      _ = |m| ^ 2 + 4 * |C| * |q| := by simp [abs_mul, sq_abs]
  by_cases hN0 : N' = 0
  · -- infinite (if nonempty)
    by_cases hne : ∃ c ∈ fiberSet A B C l m q, True
    · left
      obtain ⟨c₀, ⟨u₀, hu₀⟩, -⟩ := hne
      -- from the key identity: (2δ w₀)^2 = X₀^2 (N' = 0)
      have hkey : 4 * C * fq A B C l m q c₀ u₀
          = (2 * C * u₀ + B * c₀ + m) ^ 2 - (disc A B C * (c₀ : ℤ) ^ 2 + β * c₀ + γ) := by
        unfold fq disc; rw [hβ, hγ]; ring
      rw [hu₀, mul_zero] at hkey
      have hsq : (2 * δ * (2 * C * u₀ + B * c₀ + m)) ^ 2 = (2 * δ ^ 2 * c₀ + β) ^ 2 := by
        have hd : disc A B C = δ ^ 2 := by unfold disc; rw [hδsq]
        rw [hd] at hkey
        have : N' = 0 := hN0
        rw [hN'] at this
        nlinarith [hkey, this]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hY | hY
      · -- s = 1
        exact square_branch A B C l m q δ 1 c₀ u₀ (by norm_num) hδsq hδpos hC (by rw [hN', hβ, hγ] at hN0; exact hN0)
          (by rw [one_mul, ← hβ]; exact hY)
      · exact square_branch A B C l m q δ (-1) c₀ u₀ (by norm_num) hδsq hδpos hC (by rw [hN', hβ, hγ] at hN0; exact hN0)
          (by rw [neg_one_mul, ← hβ]; exact hY)
    · right; intro c hc; exact absurd ⟨c, hc, trivial⟩ hne
  · right
    intro c hc
    obtain ⟨u, hu⟩ := hc
    have hkey : 4 * C * fq A B C l m q c u
        = (2 * C * u + B * c + m) ^ 2 - (disc A B C * (c : ℤ) ^ 2 + β * c + γ) := by
      unfold fq disc; rw [hβ, hγ]; ring
    rw [hu, mul_zero] at hkey
    have hd : disc A B C = δ ^ 2 := by unfold disc; rw [hδsq]
    rw [hd] at hkey
    have hfac0 : ((2 * δ ^ 2 * (c : ℤ) + β) - 2 * δ * (2 * C * u + B * c + m))
        * ((2 * δ ^ 2 * (c : ℤ) + β) + 2 * δ * (2 * C * u + B * c + m)) = N' := by
      rw [hN']; linear_combination 4 * δ ^ 2 * hkey
    obtain ⟨X, hX⟩ : ∃ X : ℤ, X = 2 * δ ^ 2 * (c : ℤ) + β := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = 2 * δ * (2 * C * u + B * c + m) := ⟨_, rfl⟩
    have hfac : (X - Y) * (X + Y) = N' := by rw [hX, hY]; exact hfac0
    have hXY1 : X - Y ≠ 0 := by intro h0; apply hN0; rw [← hfac, h0, zero_mul]
    have hXY2 : X + Y ≠ 0 := by intro h0; apply hN0; rw [← hfac, h0, mul_zero]
    have hd1 : |X - Y| ≤ |N'| := Int.le_of_dvd (abs_pos.mpr hN0) ((abs_dvd_abs _ _).mpr ⟨X + Y, hfac.symm⟩)
    have hd2 : |X + Y| ≤ |N'| := Int.le_of_dvd (abs_pos.mpr hN0) ((abs_dvd_abs _ _).mpr ⟨X - Y, by rw [← hfac]; ring⟩)
    have hXle : |X| ≤ |N'| := by
      have : |2 * X| ≤ |X - Y| + |X + Y| := by
        calc |2 * X| = |(X - Y) + (X + Y)| := by ring_nf
          _ ≤ |X - Y| + |X + Y| := abs_add_le _ _
      rw [abs_mul, abs_two] at this; linarith
    have hc0 : (0 : ℤ) ≤ c := by exact_mod_cast Nat.zero_le c
    have hcX : 2 * δ ^ 2 * (c : ℤ) ≤ |N'| + |β| := by
      have : 2 * δ ^ 2 * (c : ℤ) = X - β := by rw [hX]; ring
      rw [this]; linarith [le_abs_self (X - β), abs_sub X β, hXle]
    have hδ2 : (1 : ℤ) ≤ δ ^ 2 := one_le_pow₀ hδpos
    have hc1 : (c : ℤ) ≤ |N'| + |β| := by
      have : (c : ℤ) ≤ 2 * δ ^ 2 * c := le_mul_of_one_le_left hc0 (by linarith)
      linarith
    have hN'b : |N'| ≤ β ^ 2 + 4 * δ ^ 2 * |γ| := by
      rw [hN']
      calc |β ^ 2 - 4 * δ ^ 2 * γ| ≤ |β ^ 2| + |4 * δ ^ 2 * γ| := abs_sub _ _
        _ = β ^ 2 + 4 * δ ^ 2 * |γ| := by
          rw [abs_of_nonneg (sq_nonneg β), abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ 4 * δ ^ 2)]
    unfold fbound; rw [hK, hd]
    obtain ⟨S, hS⟩ : ∃ S : ℤ, S = (1 + |l| + |m|) ^ 2 := ⟨_, rfl⟩
    rw [← hS]
    have hS0 : 0 ≤ S := by rw [hS]; exact sq_nonneg _
    have hx0 : (1 : ℤ) ≤ 1 + |l| + |m| := by linarith
    have hx1 : 1 + |l| + |m| ≤ S := by rw [hS]; exact le_self_pow₀ hx0 (by norm_num)
    have hβ0 := abs_nonneg β
    have hb1 : β ^ 2 ≤ (2 * |B| + 4 * |C|) ^ 2 * S := by
      rw [← sq_abs β, hS, ← mul_pow]
      exact pow_le_pow_left₀ hβ0 hβb 2
    have hb2 : |β| ≤ (2 * |B| + 4 * |C|) * S := by
      calc |β| ≤ (2 * |B| + 4 * |C|) * (1 + |l| + |m|) := hβb
        _ ≤ (2 * |B| + 4 * |C|) * S := mul_le_mul_of_nonneg_left hx1 (by positivity)
    have hm2 : |m| ^ 2 ≤ S := by rw [hS]; exact pow_le_pow_left₀ hm (by linarith) 2
    have hb3 : 4 * δ ^ 2 * |γ| ≤ 4 * δ ^ 2 * (1 + 4 * |C|) * (S + |q|) := by
      have h1 : |γ| ≤ (1 + 4 * |C|) * (S + |q|) := by
        have g1 : 4 * |C| * |q| ≤ 4 * |C| * (S + |q|) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have g2 : |m| ^ 2 ≤ 1 * (S + |q|) := by rw [one_mul]; linarith
        linarith [hγb]
      calc 4 * δ ^ 2 * |γ| ≤ 4 * δ ^ 2 * ((1 + 4 * |C|) * (S + |q|)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 4 * δ ^ 2 * (1 + 4 * |C|) * (S + |q|) := by ring
    have hfin : (c : ℤ) ≤ (2 * |B| + 4 * |C|) ^ 2 * (S + |q|) + 4 * δ ^ 2 * (1 + 4 * |C|) * (S + |q|)
        + (2 * |B| + 4 * |C|) * (S + |q|) := by
      have hSq : S ≤ S + |q| := by linarith
      have e1 : (2 * |B| + 4 * |C|) ^ 2 * S ≤ (2 * |B| + 4 * |C|) ^ 2 * (S + |q|) :=
        mul_le_mul_of_nonneg_left hSq (sq_nonneg _)
      have e2 : (2 * |B| + 4 * |C|) * S ≤ (2 * |B| + 4 * |C|) * (S + |q|) :=
        mul_le_mul_of_nonneg_left hSq (by linarith)
      linarith only [hc1, hN'b, hb1, hb2, hb3, e1, e2]
    calc (c : ℤ) ≤ _ := hfin
      _ = ((2 * |B| + 4 * |C|) ^ 2 + 4 * δ ^ 2 * (1 + 4 * |C|) + 2 * |B| + 4 * |C|) * (S + |q|) := by ring
where
  /-- The infinite branch for a given sign s ∈ {1, −1}. -/
  square_branch (A B C l m q δ s : ℤ) (c₀ : ℕ) (u₀ : ℤ) (hs : s * s = 1) (hδsq : δ ^ 2 = B ^ 2 - 4 * A * C)
      (hδpos : 1 ≤ δ) (hC : C ≠ 0)
      (hN : (2 * B * m - 4 * C * l) ^ 2 - 4 * δ ^ 2 * (m ^ 2 - 4 * C * q) = 0)
      (hY : 2 * δ * (2 * C * u₀ + B * c₀ + m) = s * (2 * δ ^ 2 * c₀ + (2 * B * m - 4 * C * l))) :
      (fiberSet A B C l m q).Infinite := by
    -- σ = sign of C, so that 2 σ C δ = 2 |C| δ ≥ 2
    obtain ⟨σ, hσ⟩ : ∃ σ : ℤ, σ * C = |C| := by
      rcases lt_or_gt_of_ne hC with hneg | hpos
      · exact ⟨-1, by rw [abs_of_neg hneg]; ring⟩
      · exact ⟨1, by rw [abs_of_pos hpos]; ring⟩
    have hC1 : 1 ≤ |C| := Int.one_le_abs hC
    have hstep : 1 ≤ (2 * |C| * δ).toNat := by
      have : 1 ≤ 2 * |C| * δ := by nlinarith
      omega
    refine fiberSet_infinite_of_family'' A B C l m q c₀ (2 * |C| * δ).toNat hstep
      (fun t => u₀ + σ * (s * δ ^ 2 - B * δ) * t) ?_
    intro t
    have hcast : (((2 * |C| * δ).toNat : ℕ) : ℤ) = 2 * σ * C * δ := by
      rw [Int.toNat_of_nonneg (by positivity), ← hσ]; ring
    push_cast
    rw [hcast]
    have hid := square_family_identity A B C l m q δ s σ c₀ u₀ t hs hδsq hN hY
    have hne : 4 * δ ^ 2 * (4 * C) ≠ 0 := by positivity
    have : 4 * δ ^ 2 * (4 * C) * fq A B C l m q (↑c₀ + 2 * σ * C * δ * ↑t) (u₀ + σ * (s * δ ^ 2 - B * δ) * ↑t) = 0 := by
      rw [mul_assoc]; exact hid
    exact (mul_eq_zero.mp this).resolve_left hne

end DiophCompression.SemanticQuadratic
#print axioms DiophCompression.SemanticQuadratic.dichotomy_square_C_ne
