import DiophCompression.SemanticQuadratic.PellPow
namespace DiophCompression.SemanticQuadratic
open MPUP

theorem pell_step_identity (A B C l m q D c u P Q a b σ : ℤ)
    (hD : D = B ^ 2 - 4 * A * C) (hunit : P ^ 2 - D * Q ^ 2 = 1)
    (h0 : fq A B C l m q c u = 0)
    (ha : (2 * D * c + (2 * B * m - 4 * C * l)) * P + D * (2 * (2 * C * u + B * c + m)) * Q
        - (2 * D * c + (2 * B * m - 4 * C * l)) = 8 * D * σ * C * a)
    (hb : (2 * D * c + (2 * B * m - 4 * C * l)) * Q + (2 * (2 * C * u + B * c + m)) * P
        - 2 * (2 * C * u + B * c + m) = 8 * D * σ * C * b) :
    16 * D * C * fq A B C l m q (c + 4 * σ * C * a) (u + 2 * σ * (D * b - B * a)) = 0 := by
  unfold fq at h0 ⊢
  linear_combination
    (16 * D * C * (P ^ 2 - D * Q ^ 2)) * h0
    - ((2 * B * m - 4 * C * l) ^ 2 - 4 * D * (m ^ 2 - 4 * C * q)) * hunit
    + (2 * ((2 * D * c + (2 * B * m - 4 * C * l)) * P + D * (2 * (2 * C * u + B * c + m)) * Q)
        - ((2 * D * c + (2 * B * m - 4 * C * l)) * P + D * (2 * (2 * C * u + B * c + m)) * Q
            - (2 * D * c + (2 * B * m - 4 * C * l)) - 8 * D * σ * C * a)) * ha
    - (2 * D * ((2 * D * c + (2 * B * m - 4 * C * l)) * Q + (2 * (2 * C * u + B * c + m)) * P)
        - D * ((2 * D * c + (2 * B * m - 4 * C * l)) * Q + (2 * (2 * C * u + B * c + m)) * P
            - 2 * (2 * C * u + B * c + m) - 8 * D * σ * C * b)) * hb
    + (4 * D * (c ^ 2 * (1 - P ^ 2 + D * Q ^ 2) + 8 * C * c * σ * a + 16 * C ^ 2 * σ ^ 2 * a ^ 2)) * hD

/-- Pell class: disc > 0, not a square. -/
theorem dichotomy_pell (A B C : ℤ) (h : 0 < disc A B C) (hns : ¬ IsSquare (disc A B C)) : Dichotomy A B C := by
  obtain ⟨D, hDdef⟩ : ∃ D : ℤ, D = disc A B C := ⟨_, rfl⟩
  have hD : D = B ^ 2 - 4 * A * C := by rw [hDdef]; rfl
  have hDpos : 0 < D := by rw [hDdef]; exact h
  have hnsD : ¬ IsSquare D := by rw [hDdef]; exact hns
  have hC : C ≠ 0 := by
    intro h0; apply hns; refine ⟨B, ?_⟩; unfold disc; rw [h0]; ring
  have hC1 : 1 ≤ |C| := Int.one_le_abs hC
  -- a nontrivial unit, made nonnegative
  obtain ⟨p0, q0, hpq0, hq0⟩ := Pell.exists_of_not_isSquare hDpos hnsD
  obtain ⟨p, hp⟩ : ∃ p : ℤ, p = |p0| := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℤ, q = |q0| := ⟨_, rfl⟩
  have hpq : p ^ 2 - D * q ^ 2 = 1 := by rw [hp, hq, sq_abs, sq_abs]; exact hpq0
  have hq1 : 1 ≤ q := by rw [hq]; exact Int.one_le_abs hq0
  have hp1 : 1 ≤ p := by
    have h0 : 0 ≤ p := by rw [hp]; exact abs_nonneg _
    by_contra hcon; push Not at hcon
    have : p = 0 := by omega
    rw [this] at hpq; nlinarith
  -- sign of C and the modulus M = 8 D |C|
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤ, σ * C = |C| := by
    rcases lt_or_gt_of_ne hC with hneg | hpos
    · exact ⟨-1, by rw [abs_of_neg hneg]; ring⟩
    · exact ⟨1, by rw [abs_of_pos hpos]; ring⟩
  obtain ⟨Mn, hMn⟩ : ∃ Mn : ℕ, (Mn : ℤ) = 8 * D * |C| :=
    ⟨(8 * D * |C|).toNat, Int.toNat_of_nonneg (by positivity)⟩
  have hMpos : 0 < Mn := by have : (0 : ℤ) < Mn := by rw [hMn]; positivity
                            exact_mod_cast this
  obtain ⟨T, hT, hT1, hT2⟩ := pellPow_periodic D p q hpq Mn hMpos
  obtain ⟨P, hP⟩ : ∃ P : ℤ, P = (pellPow D p q T).1 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = (pellPow D p q T).2 := ⟨_, rfl⟩
  have hPQ : P ^ 2 - D * Q ^ 2 = 1 := by rw [hP, hQ]; exact pellPow_norm D p q hpq T
  have hPQpos := pellPow_pos D p q hDpos hp1 hq1 T
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact hPQpos.2.2 (by omega)
  have hP2 : 2 ≤ P := by
    have hP1 : 1 ≤ P := by rw [hP]; exact hPQpos.1
    by_contra hcon; push Not at hcon
    have : P = 1 := by omega
    rw [this] at hPQ; nlinarith
  rw [← hP] at hT1; rw [← hQ] at hT2
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
    push Not at hall
    obtain ⟨c₀, hc₀, hX₀⟩ := hall
    -- the step: from any c with X > 0 to a larger one
    have step : ∀ c ∈ fiberSet A B C l m q, 0 < 2 * D * (c : ℤ) + β →
        ∃ c' ∈ fiberSet A B C l m q, c < c' := by
      intro c hc hX
      obtain ⟨u, hu⟩ := hc
      obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = 2 * (2 * C * u + B * c + m) := ⟨_, rfl⟩
      obtain ⟨X, hX'⟩ : ∃ X : ℤ, X = 2 * D * (c : ℤ) + β := ⟨_, rfl⟩
      -- sign choice
      obtain ⟨Q', hQ'n, hQ'dvd, hYQ⟩ : ∃ Q' : ℤ, P ^ 2 - D * Q' ^ 2 = 1 ∧ (Mn : ℤ) ∣ Q' ∧ 0 ≤ Y * Q' := by
        rcases le_or_gt 0 Y with hY0 | hY0
        · exact ⟨Q, hPQ, hT2, mul_nonneg hY0 (by linarith)⟩
        · exact ⟨-Q, by rw [neg_sq]; exact hPQ, (dvd_neg).mpr hT2, by nlinarith⟩
      have hXpos : 0 < X := by rw [hX']; exact hX
      -- new pair
      have hda : (Mn : ℤ) ∣ (X * P + D * Y * Q') - X := by
        have : (X * P + D * Y * Q') - X = X * (P - 1) + D * Y * Q' := by ring
        rw [this]; exact dvd_add (dvd_mul_of_dvd_right hT1 _) (dvd_mul_of_dvd_right hQ'dvd _)
      have hdb : (Mn : ℤ) ∣ (X * Q' + Y * P) - Y := by
        have : (X * Q' + Y * P) - Y = X * Q' + Y * (P - 1) := by ring
        rw [this]; exact dvd_add (dvd_mul_of_dvd_right hQ'dvd _) (dvd_mul_of_dvd_right hT1 _)
      obtain ⟨a, ha⟩ := hda
      obtain ⟨b, hb⟩ := hdb
      -- a ≥ 1 since X' - X ≥ X (P - 1) > 0
      have hgrow : X < X * P + D * Y * Q' := by
        have e1 : X * 2 ≤ X * P := mul_le_mul_of_nonneg_left hP2 (le_of_lt hXpos)
        have e2 : 0 ≤ D * (Y * Q') := mul_nonneg (le_of_lt hDpos) hYQ
        have e3 : D * Y * Q' = D * (Y * Q') := by ring
        linarith only [e1, e2, e3, hXpos]
      have ha1 : 1 ≤ a := by
        have hM0 : (0 : ℤ) < Mn := by rw [hMn]; positivity
        by_contra hcon; push Not at hcon
        have : (Mn : ℤ) * a ≤ (Mn : ℤ) * 0 := mul_le_mul_of_nonneg_left (by omega) (le_of_lt hM0)
        rw [mul_zero] at this
        linarith only [this, ha, hgrow]
      have ha' : (2 * D * (c : ℤ) + (2 * B * m - 4 * C * l)) * P + D * (2 * (2 * C * u + B * c + m)) * Q'
          - (2 * D * (c : ℤ) + (2 * B * m - 4 * C * l)) = 8 * D * σ * C * a := by
        rw [← hβ, ← hY, ← hX']; rw [hMn, ← hσ] at ha; linear_combination ha
      have hb' : (2 * D * (c : ℤ) + (2 * B * m - 4 * C * l)) * Q' + (2 * (2 * C * u + B * c + m)) * P
          - 2 * (2 * C * u + B * c + m) = 8 * D * σ * C * b := by
        rw [← hβ, ← hY, ← hX']; rw [hMn, ← hσ] at hb; linear_combination hb
      -- apply the step identity
      have hid := pell_step_identity A B C l m q D c u P Q' a b σ hD hQ'n hu ha' hb'
      have h16 : (16 : ℤ) * D * C ≠ 0 := by positivity
      have hfq : fq A B C l m q ((c : ℤ) + 4 * σ * C * a) (u + 2 * σ * (D * b - B * a)) = 0 :=
        (mul_eq_zero.mp hid).resolve_left h16
      refine ⟨c + (4 * |C| * a).toNat, ⟨u + 2 * σ * (D * b - B * a), ?_⟩, ?_⟩
      · have hcast : (((4 * |C| * a).toNat : ℕ) : ℤ) = 4 * σ * C * a := by
          rw [Int.toNat_of_nonneg (by positivity), ← hσ]; ring
        push_cast; rw [hcast]; exact hfq
      · have : 1 ≤ (4 * |C| * a).toNat := by
          have h4 : 1 * 1 ≤ |C| * a := mul_le_mul hC1 ha1 zero_le_one (abs_nonneg C)
          have h5 : 4 * |C| * a = 4 * (|C| * a) := by ring
          have : (1 : ℤ) ≤ 4 * |C| * a := by linarith only [h4, h5]
          omega
        omega
    -- iterate: for every k there is an element ≥ k
    have hk : ∀ k : ℕ, ∃ c ∈ fiberSet A B C l m q, 0 < 2 * D * (c : ℤ) + β ∧ k ≤ c := by
      intro k
      induction k with
      | zero => exact ⟨c₀, hc₀, hX₀, Nat.zero_le _⟩
      | succ k ih =>
        obtain ⟨c, hc, hX, hkc⟩ := ih
        obtain ⟨c', hc', hlt⟩ := step c hc hX
        refine ⟨c', hc', ?_, by omega⟩
        have hcc : (c : ℤ) ≤ c' := by exact_mod_cast le_of_lt hlt
        have := mul_le_mul_of_nonneg_left hcc (by linarith : (0 : ℤ) ≤ 2 * D)
        linarith only [this, hX]
    apply Set.infinite_of_not_bddAbove
    rintro ⟨M0, hM0⟩
    obtain ⟨c, hc, -, hkc⟩ := hk (M0 + 1)
    have := hM0 hc
    omega

end DiophCompression.SemanticQuadratic
#print axioms DiophCompression.SemanticQuadratic.dichotomy_pell
