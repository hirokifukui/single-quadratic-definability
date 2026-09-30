/-
  PellStep.lean — Gate-20 Packets 4 and 5, tasks T14 (square step), T15 (congruence-preserving
  positive unit) and T17 (two-step output obstruction).

  These are the algebraic core of the reviewer's delivery item 5, "congruence-preserving Pell
  three-point collision".  They are independent of the rational-complement machinery (T06/T07),
  which is why they can be closed now: the s47 mathlib probe found `Pell.exists_of_not_isSquare`
  and the `Zsqrtd` ring already in place.

  What is NOT here: the geometric embedding of the Pell plane into the solution set (T13, T16,
  T18) needs the centre `h(a)` and the rational complement.  The reviewer's pass condition for
  T17 — "大域的軌道分類・実数漸近・等分布なし" — is met: nothing below classifies orbits or takes
  a limit; two points and one determinant.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Ineq

namespace DiophCompression.ResearchUpgrade

/-! ### T14 — the square of a Pell unit -/

/-- The square of `(T, S)` is `(2T² − 1, 2TS)` — the reviewer's §5.3 formulas, derived from the
Pell relation rather than quoted. -/
theorem pell_square {d T S : ℤ} (h : T * T - d * (S * S) = 1) :
    (T * T + d * (S * S)) = 2 * T ^ 2 - 1 ∧
      (T * T + d * (S * S)) * (T * T + d * (S * S)) - d * ((2 * T * S) * (2 * T * S)) = 1 := by
  constructor
  · nlinarith [h]
  · nlinarith [h]

/-! ### T15 — a congruence-preserving positive unit -/

/-- Norm of a power of a norm-one element. -/
private theorem norm_pow_eq_one {d : ℤ} {α : Zsqrtd d}
    (h : α.re * α.re - d * (α.im * α.im) = 1) (k : ℕ) :
    (α ^ k).re * (α ^ k).re - d * ((α ^ k).im * (α ^ k).im) = 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
      have hre : (α ^ (n + 1)).re = (α ^ n).re * α.re + d * ((α ^ n).im * α.im) := by
        rw [pow_succ]; simp; try ring
      have him : (α ^ (n + 1)).im = (α ^ n).re * α.im + (α ^ n).im * α.re := by
        rw [pow_succ]; simp; try ring
      rw [hre, him]; nlinarith [ih, h]

/-- The core step: a repetition mod `N` yields a unit congruent to 1. -/
private theorem pell_congr_core {d : ℤ} {N : ℕ} [NeZero N] {α : Zsqrtd d}
    (hnorm1 : α.re * α.re - d * (α.im * α.im) = 1)
    (hstar : star α * α = 1)
    (hpos : ∀ k : ℕ, 1 < (α ^ (k + 1)).re ∧ 0 < (α ^ (k + 1)).im)
    {i j : ℕ} (hlt : i < j)
    (h1 : ((α ^ i).re : ZMod N) = ((α ^ j).re : ZMod N))
    (h2 : ((α ^ i).im : ZMod N) = ((α ^ j).im : ZMod N)) :
    ∃ T S : ℤ, T * T - d * (S * S) = 1 ∧ 1 < T ∧ 0 < S ∧ (N : ℤ) ∣ (T - 1) ∧ (N : ℤ) ∣ S := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, j = i + (k + 1) := ⟨j - i - 1, by omega⟩
  set K : ℕ := k + 1 with hK
  obtain ⟨hTgt, hSpos⟩ := hpos k
  refine ⟨(α ^ K).re, (α ^ K).im, norm_pow_eq_one hnorm1 K, hTgt, hSpos, ?_, ?_⟩
  all_goals {
    have hsplit : α ^ j = α ^ i * α ^ K := by rw [hk, pow_add]
    have hinv : (star α) ^ i * α ^ i = 1 := by
      rw [← mul_pow, hstar, one_pow]
    have hkey : (star α) ^ i * (α ^ j - α ^ i) = α ^ K - 1 := by
      rw [hsplit, mul_sub, ← mul_assoc, hinv, one_mul]
    have hdre : (N : ℤ) ∣ ((α ^ j).re - (α ^ i).re) := by
      have hz : (((α ^ j).re - (α ^ i).re : ℤ) : ZMod N) = 0 := by push_cast; rw [← h1]; ring
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hz
    have hdim : (N : ℤ) ∣ ((α ^ j).im - (α ^ i).im) := by
      have hz : (((α ^ j).im - (α ^ i).im : ℤ) : ZMod N) = 0 := by push_cast; rw [← h2]; ring
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hz
    set β : Zsqrtd d := (star α) ^ i with hβ
    set γ : Zsqrtd d := α ^ j - α ^ i with hγ
    have hγre : γ.re = (α ^ j).re - (α ^ i).re := by simp [hγ]
    have hγim : γ.im = (α ^ j).im - (α ^ i).im := by simp [hγ]
    have hprodre : (β * γ).re = β.re * γ.re + d * (β.im * γ.im) := by simp; try ring
    have hprodim : (β * γ).im = β.re * γ.im + β.im * γ.re := by simp; try ring
    have hbre : (N : ℤ) ∣ (β * γ).re := by
      rw [hprodre, hγre, hγim]
      exact dvd_add (Dvd.dvd.mul_left hdre _) (Dvd.dvd.mul_left (Dvd.dvd.mul_left hdim _) _)
    have hbim : (N : ℤ) ∣ (β * γ).im := by
      rw [hprodim, hγre, hγim]
      exact dvd_add (Dvd.dvd.mul_left hdim _) (Dvd.dvd.mul_left hdre _)
    have hfin : β * γ = α ^ K - 1 := hkey
    rw [hfin] at hbre hbim
    have hre1 : ((α ^ K : Zsqrtd d) - 1).re = (α ^ K).re - 1 := by simp
    have him1 : ((α ^ K : Zsqrtd d) - 1).im = (α ^ K).im := by simp
    rw [hre1] at hbre
    rw [him1] at hbim
    first
      | exact hbre
      | exact hbim }

/-- **T15.**  For `d > 0` not a square and any modulus `N ≥ 1` there is a nontrivial POSITIVE Pell
solution congruent to the identity mod `N`.  No fundamental-unit computation is required — the
argument is pigeonhole in the finite ring `ZMod N × ZMod N` plus cancellation by the conjugate. -/
theorem exists_pell_unit_congr {d : ℤ} (hd : 0 < d) (hns : ¬ IsSquare d) (N : ℕ) (hN : 0 < N) :
    ∃ T S : ℤ, T * T - d * (S * S) = 1 ∧ 1 < T ∧ 0 < S ∧ (N : ℤ) ∣ (T - 1) ∧ (N : ℤ) ∣ S := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare hd hns
  -- normalise to a positive solution
  set x' : ℤ := |x| with hx'
  set y' : ℤ := |y| with hy'
  have hnorm : x' * x' - d * (y' * y') = 1 := by
    have h1 : x' * x' = x ^ 2 := by rw [hx', ← sq_abs]; ring
    have h2 : y' * y' = y ^ 2 := by rw [hy', ← sq_abs]; ring
    rw [h1, h2]; linarith [hxy]
  have hy'pos : 0 < y' := abs_pos.mpr hy
  have hx'nonneg : 0 ≤ x' := abs_nonneg x
  have hd1 : 1 ≤ d := hd
  have hx'gt : 1 < x' := by nlinarith [hnorm, hy'pos, hd1, hx'nonneg]
  -- the unit in ℤ√d
  set α : Zsqrtd d := ⟨x', y'⟩ with hα
  have hre : α.re = x' := rfl
  have him : α.im = y' := rfl
  have hstar : star α * α = 1 := by
    ext <;> simp [hα] <;> ring_nf <;> linarith [hnorm]
  -- powers are positive and grow
  have hpos : ∀ k : ℕ, 1 < (α ^ (k + 1)).re ∧ 0 < (α ^ (k + 1)).im := by
    intro k
    induction k with
    | zero => simp [hα]; exact ⟨hx'gt, hy'pos⟩
    | succ n ih =>
        obtain ⟨h1, h2⟩ := ih
        rw [pow_succ]
        constructor
        · have : (α ^ (n + 1) * α).re = (α ^ (n+1)).re * x' + d * ((α ^ (n+1)).im * y') := by
            simp [hα]; try ring
          rw [this]
          have hprod : 0 < ((α ^ (n+1)).re - 1) * (x' - 1) :=
            mul_pos (by linarith) (by linarith)
          have hB : 0 < d * ((α ^ (n+1)).im * y') :=
            mul_pos (by linarith) (mul_pos h2 hy'pos)
          nlinarith [hprod, hB]
        · have : (α ^ (n + 1) * α).im = (α ^ (n+1)).re * y' + (α ^ (n+1)).im * x' := by
            simp [hα]; try ring
          rw [this]
          have hA : 0 < (α ^ (n+1)).re * y' := mul_pos (by linarith) hy'pos
          have hB : 0 < (α ^ (n+1)).im * x' := mul_pos h2 (by linarith)
          linarith
  -- pigeonhole in ZMod N × ZMod N
  obtain ⟨i, j, hij, hfe⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun k : ℕ => (((α ^ k).re : ZMod N), ((α ^ k).im : ZMod N)))
  -- wlog i < j
  have hnorm1 : α.re * α.re - d * (α.im * α.im) = 1 := hnorm
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact pell_congr_core hnorm1 hstar hpos hlt
      (congrArg Prod.fst hfe) (congrArg Prod.snd hfe)
  · exact pell_congr_core hnorm1 hstar hpos hlt
      (congrArg Prod.fst hfe.symm) (congrArg Prod.snd hfe.symm)


/-! ### T17 — the two-step output obstruction -/

/-- **T17.**  If the outputs at `z₀`, `z₁` and `z₂` agree, the coefficient matrix of the two
resulting relations has determinant `2S₁(1 − T₁) ≠ 0`, so both output vectors vanish.  Stated for
an arbitrary index type, so it applies coordinate-wise to a vector output. -/
theorem pell_two_step_obstruction {ι : Type*} {T₁ S₁ : ℤ} (hT : 1 < T₁) (hS : 0 < S₁)
    {U V : ι → ℤ}
    (h1 : ∀ i, (T₁ - 1) * U i + S₁ * V i = 0)
    (h2 : ∀ i, (2 * T₁ ^ 2 - 1 - 1) * U i + (2 * T₁ * S₁) * V i = 0) :
    (∀ i, U i = 0) ∧ (∀ i, V i = 0) := by
  have hdet : 2 * S₁ * (1 - T₁) ≠ 0 := by
    have hp : 0 < S₁ * (T₁ - 1) := mul_pos hS (by omega)
    have heq : 2 * S₁ * (1 - T₁) = -(2 * (S₁ * (T₁ - 1))) := by ring
    have hneg : 2 * S₁ * (1 - T₁) < 0 := by rw [heq]; linarith
    exact ne_of_lt hneg
  have hU : ∀ i, U i = 0 := by
    intro i
    have e1 := h1 i
    have e2 := h2 i
    have hz : (2 * S₁ * (1 - T₁)) * U i = 0 := by linear_combination (2 * T₁ * S₁) * e1 - S₁ * e2
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h hdet
    · exact h
  refine ⟨hU, fun i => ?_⟩
  have e1 := h1 i
  rw [hU i, mul_zero, zero_add] at e1
  rcases mul_eq_zero.mp e1 with h | h
  · exact absurd h (by omega)
  · exact h

end DiophCompression.ResearchUpgrade
