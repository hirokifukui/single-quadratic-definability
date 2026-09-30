/-
  DiophCompression/SemanticQuadraticTwoWitness/PellStep.lean — s8: the Pell step of `Class_D7.dichotomy_pell`
  extracted as a reusable lemma (verbatim transcription of Class_D7.lean lines 27–65 and 94–165, r07 layer
  md5 7eaccd60; Class_D7.lean itself is untouched). From one fiber element with X = 2·disc·c + (2Bm − 4Cl) > 0
  the one-witness fiber set is infinite. Used by the scaled-line generic theorem (GPT r07 必須6).
-/
import DiophCompression.SemanticQuadratic.Class_D7

namespace DiophCompression.SemanticQuadratic

theorem pell_infinite_of_X_pos (A B C l m q : ℤ) (h : 0 < disc A B C) (hns : ¬ IsSquare (disc A B C))
    (c₀ : ℕ) (hc₀ : c₀ ∈ fiberSet A B C l m q)
    (hX₀ : 0 < 2 * disc A B C * (c₀ : ℤ) + (2 * B * m - 4 * C * l)) :
    (fiberSet A B C l m q).Infinite := by
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
  obtain ⟨qU, hq⟩ : ∃ qU : ℤ, qU = |q0| := ⟨_, rfl⟩
  have hpq : p ^ 2 - D * qU ^ 2 = 1 := by rw [hp, hq, sq_abs, sq_abs]; exact hpq0
  have hq1 : 1 ≤ qU := by rw [hq]; exact Int.one_le_abs hq0
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
  obtain ⟨T, hT, hT1, hT2⟩ := pellPow_periodic D p qU hpq Mn hMpos
  obtain ⟨P, hP⟩ : ∃ P : ℤ, P = (pellPow D p qU T).1 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = (pellPow D p qU T).2 := ⟨_, rfl⟩
  have hPQ : P ^ 2 - D * Q ^ 2 = 1 := by rw [hP, hQ]; exact pellPow_norm D p qU hpq T
  have hPQpos := pellPow_pos D p qU hDpos hp1 hq1 T
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact hPQpos.2.2 (by omega)
  have hP2 : 2 ≤ P := by
    have hP1 : 1 ≤ P := by rw [hP]; exact hPQpos.1
    by_contra hcon; push Not at hcon
    have : P = 1 := by omega
    rw [this] at hPQ; nlinarith
  rw [← hP] at hT1; rw [← hQ] at hT2
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, β = 2 * B * m - 4 * C * l := ⟨_, rfl⟩
  rw [← hDdef, ← hβ] at hX₀
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
#print axioms DiophCompression.SemanticQuadratic.pell_infinite_of_X_pos
