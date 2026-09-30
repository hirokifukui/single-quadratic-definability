/-
  RayCounting.lean — Gate-18 research program, Packet A5-2 / A5-3 (conditional layer).
  From a fixed-base prime ray in S and the A5-1 input `FixedAPPrimeLowerBound` (hypothesis, not
  axiom): `N_S(X) ≥ κ·X/log X` for X ≥ X₁, with κ = c/(4|α|) and X₁ explicit. The finitely many
  primes ≤ M and the affine offset/denominator are handled; no uniformity in the base point.
  Consequence: `LogLowerBound S` (weaker) also follows on the same hypothesis.
-/
import ResearchUpgrade.PrimeRay

namespace DiophCompression.ResearchUpgrade

/-- `log x ≤ 2√x` for `x ≥ 0`. -/
theorem log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at h
  linarith

/-- A5-2/A5-3 (CONDITIONAL on `FixedAPPrimeLowerBound`): a fixed-base prime ray in `S` gives
`N_S(X) ≥ κ X / log X` for all large `X`. -/
theorem fiberCountZZ_xlog_of_ray {S : Set ℤ} (R : FixedBasePrimeRay S)
    (hAP : FixedAPPrimeLowerBound) :
    ∃ (κ : ℝ) (X₁ : ℕ), 0 < κ ∧ 2 ≤ X₁ ∧
      ∀ X : ℕ, X₁ ≤ X → κ * X / Real.log X ≤ (fiberCountZZ S X : ℝ) := by
  obtain ⟨c, Y₀, hc, hY₀, hAPM⟩ := hAP R.M R.hM
  set a : ℕ := R.α.natAbs with ha
  set b' : ℕ := R.β.natAbs with hb'
  have ha0 : 0 < a := Int.natAbs_pos.mpr R.hα
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0
  set κ : ℝ := c / (4 * a) with hκ
  have hκpos : 0 < κ := by positivity
  set T : ℝ := (8 * a * R.M / c) ^ 2 with hT
  refine ⟨κ, max (max 2 (2 * (b' + a))) (max (2 * a * Y₀) (⌈T⌉₊ + 1)), hκpos,
    le_max_of_le_left (le_max_left _ _), ?_⟩
  intro X hX
  have hX2 : 2 ≤ X := le_trans (le_max_of_le_left (le_max_left _ _)) hX
  have hXba : 2 * (b' + a) ≤ X := le_trans (le_max_of_le_left (le_max_right _ _)) hX
  have hXY₀ : 2 * a * Y₀ ≤ X := le_trans (le_max_of_le_right (le_max_left _ _)) hX
  have hXT : ⌈T⌉₊ + 1 ≤ X := le_trans (le_max_of_le_right (le_max_right _ _)) hX
  have hbX : b' ≤ X := by omega
  set Y : ℕ := (X - b') / a with hY
  -- a·Y + b' ≤ X
  have hYle : Y * a + b' ≤ X := by
    have h1 : Y * a ≤ X - b' := Nat.div_mul_le_self _ _
    have := Nat.add_le_add_right h1 b'
    rwa [Nat.sub_add_cancel hbX] at this
  -- X < a·(Y+1) + b'
  have hYlt : X - b' < a * (Y + 1) := Nat.lt_mul_div_succ (X - b') ha0
  -- real versions
  have hYleR : (Y : ℝ) * a + b' ≤ X := by exact_mod_cast hYle
  have hYltR : (X : ℝ) - b' < a * (Y + 1) := by
    have : ((X - b' : ℕ) : ℝ) < a * (Y + 1) := by exact_mod_cast hYlt
    rwa [Nat.cast_sub hbX] at this
  have hXbaR : (2 : ℝ) * (b' + a) ≤ X := by exact_mod_cast hXba
  have hXY₀R : (2 : ℝ) * a * Y₀ ≤ X := by exact_mod_cast hXY₀
  -- X ≤ 2·a·Y
  have hX2aY : (X : ℝ) ≤ 2 * a * Y := by nlinarith
  have hYY₀ : Y₀ ≤ Y := by
    have : (Y₀ : ℝ) ≤ Y := by
      have h := le_trans hXY₀R hX2aY
      nlinarith
    exact_mod_cast this
  have hY2 : 2 ≤ Y := le_trans hY₀ hYY₀
  have hYX : Y ≤ X := by
    have : Y ≤ Y * a := Nat.le_mul_of_pos_right _ ha0
    omega
  -- the ray count (Finset form)
  have hXY : |R.α| * Y + |R.β| ≤ (X : ℤ) := by
    have h1 : |R.α| = (a : ℤ) := by rw [ha, Int.natCast_natAbs]
    have h2 : |R.β| = (b' : ℤ) := by rw [hb', Int.natCast_natAbs]
    rw [h1, h2]
    have := hYle
    have : ((Y * a + b' : ℕ) : ℤ) ≤ X := by exact_mod_cast this
    push_cast at this
    linarith
  have hcount := fiberCountZZ_ge_primeCountAP R X Y hXY
  have hcountR : (primeCountAP R.M Y : ℝ) ≤ (fiberCountZZ S X : ℝ) + R.M := by exact_mod_cast hcount
  -- the analytic input at Y
  have hpi := hAPM Y hYY₀
  -- logs
  have hYR1 : (1 : ℝ) < Y := by exact_mod_cast (by omega : 1 < Y)
  have hXR1 : (1 : ℝ) < X := by exact_mod_cast (by omega : 1 < X)
  have hlogY : 0 < Real.log Y := Real.log_pos hYR1
  have hlogX : 0 < Real.log X := Real.log_pos hXR1
  have hlogYX : Real.log Y ≤ Real.log X :=
    Real.log_le_log (by positivity) (by exact_mod_cast hYX)
  set L := Real.log X with hL
  -- c·Y ≤ (N + M)·L
  have h1 : c * Y / L ≤ c * Y / Real.log Y :=
    div_le_div_of_nonneg_left (by positivity) hlogY hlogYX
  have h2 : c * Y ≤ ((fiberCountZZ S X : ℝ) + R.M) * L := by
    have := le_trans h1 (le_trans hpi hcountR)
    rwa [div_le_iff₀ hlogX] at this
  -- M·L ≤ κ·X
  have hsqrt : 8 * a * R.M / c ≤ Real.sqrt X := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have hTX : T ≤ X := by
      have : (⌈T⌉₊ : ℝ) ≤ X := by exact_mod_cast (by omega : ⌈T⌉₊ ≤ X)
      exact le_trans (Nat.le_ceil T) this
    rw [hT] at hTX
    exact hTX
  have hκ8 : κ * (8 * a * R.M / c) = 2 * R.M := by
    rw [hκ]; field_simp; ring
  have h3 : (R.M : ℝ) * L ≤ κ * X := by
    have hL2 : L ≤ 2 * Real.sqrt X := log_le_two_sqrt (by positivity)
    have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt (by positivity)
    have hs0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
    have h2M : 2 * (R.M : ℝ) ≤ κ * Real.sqrt X := by
      rw [← hκ8]; exact mul_le_mul_of_nonneg_left hsqrt hκpos.le
    calc (R.M : ℝ) * L ≤ R.M * (2 * Real.sqrt X) :=
          mul_le_mul_of_nonneg_left hL2 (by positivity)
      _ = (2 * R.M) * Real.sqrt X := by ring
      _ ≤ (κ * Real.sqrt X) * Real.sqrt X := mul_le_mul_of_nonneg_right h2M hs0
      _ = κ * X := by rw [mul_assoc, hsq]
  -- assemble: κ X = c X/(4a) ≤ c Y/2 ... precisely 2·κ·X ≤ c·Y
  have h4 : 2 * (κ * X) ≤ c * Y := by
    have : κ * (2 * a * Y) = c * Y / 2 := by rw [hκ]; field_simp; ring
    have := mul_le_mul_of_nonneg_left hX2aY hκpos.le
    linarith
  rw [div_le_iff₀ hlogX]
  nlinarith

/-- The weaker `LogLowerBound` also follows (conditional on the same input), with `κ/4`. -/
theorem logLowerBound_of_ray {S : Set ℤ} (R : FixedBasePrimeRay S) (hAP : FixedAPPrimeLowerBound) :
    LogLowerBound S := by
  obtain ⟨κ, X₁, hκ, hX₁, h⟩ := fiberCountZZ_xlog_of_ray R hAP
  refine ⟨κ / 4, X₁, by positivity, hX₁, fun X hX => ?_⟩
  have hX2 : 2 ≤ X := le_trans hX₁ hX
  have hXR1 : (1 : ℝ) < X := by exact_mod_cast (by omega : 1 < X)
  have hlogX : 0 < Real.log X := Real.log_pos hXR1
  have hL2 : Real.log X ≤ 2 * Real.sqrt X := log_le_two_sqrt (by positivity)
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  have hlog2 : Real.log X * Real.log X ≤ 4 * X := by nlinarith
  calc κ / 4 * Real.log X = κ * (Real.log X * Real.log X) / (4 * Real.log X) := by
        field_simp
    _ ≤ κ * (4 * X) / (4 * Real.log X) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hlog2 hκ.le
    _ = κ * X / Real.log X := by field_simp
    _ ≤ _ := h X hX

end DiophCompression.ResearchUpgrade
