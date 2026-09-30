/-
  SharpnessUnconditional.lean — A6-3 / A6-4 with NO analytic hypothesis: the two Sharpness.lean theorems
  re-run on `logBarrier_of_quadratic_unconditional` (the B2/B3 route). Proof bodies are verbatim copies.
-/
import ResearchUpgrade.Sharpness

namespace DiophCompression.ResearchUpgrade
open MvPolynomial MPUP

theorem E_not_quadratic_fiber_unconditional :
    ∀ (n r : ℕ) (P : Poly (n + 1) r) (_ : P.totalDegree ≤ 2) (a : Fin n → ℤ),
      fiberZZ P a ≠ expTowerSet := by
  intro n r P hP a hEq
  rcases logBarrier_of_quadratic_unconditional P hP a with hbdd | hlog
  · obtain ⟨B, hB⟩ := hbdd
    rw [hEq] at hB
    have hfin : expTowerSet.Finite := by
      apply Set.Finite.subset (Set.finite_Icc (-(B : ℤ)) (B : ℤ))
      intro c hc
      rw [Set.mem_Icc]; exact abs_le.mp (hB c hc)
    exact expTowerSet_infinite hfin
  · rw [hEq] at hlog
    obtain ⟨κ, X₀, hκ, hX₀, hbound⟩ := hlog
    obtain ⟨m, hmN, hgrow⟩ := exists_growth κ hκ X₀
    set Xm : ℕ := 2 ^ (2 ^ m) with hXm
    have hXmX₀ : X₀ ≤ Xm := by
      rw [hXm]
      calc X₀ ≤ m := hmN
        _ ≤ 2 ^ m := (Nat.lt_two_pow_self).le
        _ ≤ 2 ^ (2 ^ m) := Nat.pow_le_pow_right (by norm_num) (Nat.lt_two_pow_self).le
    have hXm2 : 2 ≤ Xm := by
      rw [hXm]; exact Nat.le_self_pow (pow_ne_zero m (by norm_num)) 2
    have hb := hbound Xm hXmX₀
    have hcount := fiberCountZZ_expTower_le Xm hXm2
    have hLm : Nat.log 2 (Nat.log 2 Xm) = m := by
      rw [hXm, Nat.log_pow (show (1 : ℕ) < 2 by norm_num), Nat.log_pow (show (1 : ℕ) < 2 by norm_num)]
    rw [hLm] at hcount
    have hlogXm : Real.log (Xm : ℝ) = (2 : ℝ) ^ m * Real.log 2 := by
      rw [hXm]; push_cast; rw [Real.log_pow]; push_cast; ring
    have hR : κ * Real.log (Xm : ℝ) ≤ (m : ℝ) + 2 := by
      calc κ * Real.log (Xm : ℝ) ≤ (fiberCountZZ expTowerSet Xm : ℝ) := hb
        _ ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast hcount
        _ = (m : ℝ) + 2 := by push_cast; ring
    rw [hlogXm] at hR
    have hcontra : κ * 2 ^ m * Real.log 2 ≤ (m : ℝ) + 2 := by
      have heq : κ * 2 ^ m * Real.log 2 = κ * ((2 : ℝ) ^ m * Real.log 2) := by ring
      rw [heq]; exact hR
    linarith [hgrow, hcontra]

/-! ### A6-4 : the separator -/

theorem not_quadratic_fiber_of_sublog_unconditional (S : Set ℤ)
    (hinf : S.Infinite)
    (hsub : ∀ κ : ℝ, 0 < κ →
      ∃ᶠ X : ℕ in Filter.atTop, (fiberCountZZ S X : ℝ) < κ * Real.log X) :
    ∀ (n r : ℕ) (P : Poly (n + 1) r) (_ : P.totalDegree ≤ 2) (a : Fin n → ℤ),
      fiberZZ P a ≠ S := by
  intro n r P hP a hEq
  rcases logBarrier_of_quadratic_unconditional P hP a with hbdd | hlog
  · obtain ⟨B, hB⟩ := hbdd
    rw [hEq] at hB
    have hfin : S.Finite := by
      apply Set.Finite.subset (Set.finite_Icc (-(B : ℤ)) (B : ℤ))
      intro c hc
      rw [Set.mem_Icc]; exact abs_le.mp (hB c hc)
    exact hinf hfin
  · rw [hEq] at hlog
    obtain ⟨κ, X₀, hκ, hX₀, hbound⟩ := hlog
    have hfreq := hsub κ hκ
    have hev : ∀ᶠ X : ℕ in Filter.atTop, X₀ ≤ X := Filter.eventually_atTop.2 ⟨X₀, fun X h => h⟩
    obtain ⟨X, hlt, hge⟩ := (hfreq.and_eventually hev).exists
    have hb := hbound X hge
    linarith [hb, hlt]

/-! ### CONTROLS : the descent on the standard chain `(17,12) → (3,2) → (1,0)` -/

end DiophCompression.ResearchUpgrade
