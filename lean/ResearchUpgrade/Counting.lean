/-
  Counting.lean — Gate-18 research program, Packet A0-2 / A4-1.
  Definitions: fiberCountZZ (N_S(X)), ExponentialInjection, LogLowerBound.
  The count is over OUTPUTS c ∈ S (a set), never over witnessed solutions.
  Constants (κ, X₀, A, B) are existential per S — no uniformity across sets is claimed.
  Baseline (mpup-lean r39) is untouched; nothing here is imported by the baseline.
-/
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.Star
import Mathlib.Data.Set.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.SetNotationForOrder

namespace DiophCompression.ResearchUpgrade

open Classical

/-- `N_S(X) = #{c ∈ S : |c| ≤ X}` for `S ⊆ ℤ`, `X : ℕ`. -/
noncomputable def fiberCountZZ (S : Set ℤ) (X : ℕ) : ℕ :=
  ((Finset.Icc (-(X : ℤ)) (X : ℤ)).filter (fun c => c ∈ S)).card

/-- Existence of an injective sequence in `S` with exponential envelope `|g n| ≤ A·Bⁿ`. -/
def ExponentialInjection (S : Set ℤ) : Prop :=
  ∃ (A B : ℕ) (g : ℕ → ℤ), 1 ≤ A ∧ 2 ≤ B ∧ Function.Injective g ∧
    (∀ n, g n ∈ S) ∧ ∀ n, |g n| ≤ (A : ℤ) * (B : ℤ) ^ n

/-- `∃ κ > 0, X₀ ≥ 2, ∀ X ≥ X₀, κ log X ≤ N_S(X)`. -/
def LogLowerBound (S : Set ℤ) : Prop :=
  ∃ (κ : ℝ) (X₀ : ℕ), 0 < κ ∧ 2 ≤ X₀ ∧
    ∀ X : ℕ, X₀ ≤ X → κ * Real.log X ≤ (fiberCountZZ S X : ℝ)

/-- The negation image `-S`. -/
def negSet (S : Set ℤ) : Set ℤ := {c | -c ∈ S}

/-! ### A0-2 sanity checks: empty, singleton, all of ℤ, sign reversal, monotonicity -/

theorem fiberCountZZ_empty (X : ℕ) : fiberCountZZ ∅ X = 0 := by
  simp [fiberCountZZ]

theorem fiberCountZZ_univ (X : ℕ) : fiberCountZZ Set.univ X = 2 * X + 1 := by
  simp [fiberCountZZ, Int.card_Icc]
  omega

theorem fiberCountZZ_singleton (c : ℤ) (X : ℕ) :
    fiberCountZZ {c} X = if |c| ≤ (X : ℤ) then 1 else 0 := by
  simp only [fiberCountZZ, Set.mem_singleton_iff]
  rw [Finset.filter_eq']
  by_cases h : |c| ≤ (X : ℤ)
  · have : c ∈ Finset.Icc (-(X : ℤ)) (X : ℤ) := by
      rw [Finset.mem_Icc]; exact abs_le.mp h
    simp [this, h]
  · have : c ∉ Finset.Icc (-(X : ℤ)) (X : ℤ) := by
      rw [Finset.mem_Icc]; intro hc; exact h (abs_le.mpr hc)
    simp [this, h]

theorem fiberCountZZ_neg (S : Set ℤ) (X : ℕ) : fiberCountZZ (negSet S) X = fiberCountZZ S X := by
  unfold fiberCountZZ
  refine Finset.card_bij' (fun c _ => -c) (fun c _ => -c) ?_ ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_Icc, negSet, Set.mem_setOf_eq] at hc ⊢
    exact ⟨⟨by linarith [hc.1.2], by linarith [hc.1.1]⟩, hc.2⟩
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_Icc, negSet, Set.mem_setOf_eq] at hc ⊢
    exact ⟨⟨by linarith [hc.1.2], by linarith [hc.1.1]⟩, by simpa using hc.2⟩
  · intro c _; simp
  · intro c _; simp

theorem fiberCountZZ_mono (S : Set ℤ) {X Y : ℕ} (h : X ≤ Y) :
    fiberCountZZ S X ≤ fiberCountZZ S Y := by
  unfold fiberCountZZ
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  apply Finset.Icc_subset_Icc <;> omega

theorem not_exponentialInjection_empty : ¬ ExponentialInjection (∅ : Set ℤ) := by
  rintro ⟨A, B, g, -, -, -, hmem, -⟩
  exact hmem 0

theorem exponentialInjection_univ : ExponentialInjection (Set.univ : Set ℤ) := by
  refine ⟨1, 2, fun n => (n : ℤ), le_refl _, le_refl _, ?_, fun _ => Set.mem_univ _, ?_⟩
  · intro a b h; exact_mod_cast (show ((a : ℕ) : ℤ) = (b : ℕ) from h)
  · intro n
    rw [abs_of_nonneg (by positivity)]
    have : n < 2 ^ n := Nat.lt_two_pow_self
    have : (n : ℤ) ≤ 2 ^ n := by exact_mod_cast this.le
    simpa using this

theorem exponentialInjection_neg {S : Set ℤ} (h : ExponentialInjection S) :
    ExponentialInjection (negSet S) := by
  obtain ⟨A, B, g, hA, hB, hinj, hmem, hbd⟩ := h
  refine ⟨A, B, fun n => -g n, hA, hB, ?_, ?_, ?_⟩
  · intro a b hab; exact hinj (neg_inj.mp hab)
  · intro n; simp [negSet, hmem n]
  · intro n; simpa using hbd n

/-! ### A4-1: injective exponential sequence ⇒ `N_S(A·Bⁿ) ≥ n + 1` -/

theorem fiberCountZZ_ge_of_injection (S : Set ℤ) (A B : ℕ) (g : ℕ → ℤ)
    (hB : 1 ≤ B) (hinj : Function.Injective g) (hmem : ∀ n, g n ∈ S)
    (hbd : ∀ n, |g n| ≤ (A : ℤ) * (B : ℤ) ^ n) (n : ℕ) :
    n + 1 ≤ fiberCountZZ S (A * B ^ n) := by
  unfold fiberCountZZ
  have hsub : (Finset.range (n + 1)).image g ⊆
      (Finset.Icc (-((A * B ^ n : ℕ) : ℤ)) ((A * B ^ n : ℕ) : ℤ)).filter (fun c => c ∈ S) := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    rw [Finset.mem_range] at hk
    have hk' : k ≤ n := by omega
    have hpow : (B : ℤ) ^ k ≤ (B : ℤ) ^ n :=
      pow_le_pow_right₀ (by exact_mod_cast hB) hk'
    have hbk : |g k| ≤ (A : ℤ) * (B : ℤ) ^ n :=
      (hbd k).trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    rw [Finset.mem_filter, Finset.mem_Icc]
    push_cast
    exact ⟨abs_le.mp hbk, hmem k⟩
  calc n + 1 = ((Finset.range (n + 1)).image g).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    _ ≤ _ := Finset.card_le_card hsub

theorem fiberCountZZ_ge_of_exponentialInjection {S : Set ℤ} (h : ExponentialInjection S) :
    ∃ A B : ℕ, 1 ≤ A ∧ 2 ≤ B ∧ ∀ n, n + 1 ≤ fiberCountZZ S (A * B ^ n) := by
  obtain ⟨A, B, g, hA, hB, hinj, hmem, hbd⟩ := h
  exact ⟨A, B, hA, hB, fiberCountZZ_ge_of_injection S A B g (by omega) hinj hmem hbd⟩

/-! ### A4-1 (log form): `ExponentialInjection S → LogLowerBound S`
with `κ = 1/(2 log B)` and `X₀ = max 2 (4A²)` made explicit. -/

theorem logLowerBound_of_exponentialInjection {S : Set ℤ} (h : ExponentialInjection S) :
    LogLowerBound S := by
  obtain ⟨A, B, g, hA, hB, hinj, hmem, hbd⟩ := h
  have hcount := fiberCountZZ_ge_of_injection S A B g (by omega) hinj hmem hbd
  have hB1 : 1 < B := by omega
  have hlogB : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB1)
  refine ⟨1 / (2 * Real.log B), max 2 (4 * A * A), by positivity, le_max_left _ _, ?_⟩
  intro X hX
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hXA : 4 * A * A ≤ X := le_trans (le_max_right _ _) hX
  have hXA1 : A ≤ X := by nlinarith
  set n := Nat.log B (X / A) with hn
  -- lower: A * B^n ≤ X, hence n + 1 ≤ N_S(X)
  have hXdivA : X / A ≠ 0 := by
    have : 1 ≤ X / A := (Nat.one_le_div_iff (by omega)).mpr hXA1
    omega
  have hpow_le : B ^ n ≤ X / A := Nat.pow_log_le_self B hXdivA
  have hABn : A * B ^ n ≤ X :=
    le_trans (Nat.mul_le_mul_left A hpow_le) (Nat.mul_div_le X A)
  have hN : n + 1 ≤ fiberCountZZ S X := le_trans (hcount n) (fiberCountZZ_mono S hABn)
  -- upper: X < A * B^(n+1)
  have hlt : X / A < B ^ (n + 1) := Nat.lt_pow_succ_log_self hB1 (X / A)
  have hXlt : X < A * B ^ (n + 1) := by
    have h1 : X < A * (X / A + 1) := by
      have := Nat.lt_mul_div_succ X (by omega : 0 < A)
      linarith
    have h2 : A * (X / A + 1) ≤ A * B ^ (n + 1) := Nat.mul_le_mul_left A hlt
    omega
  -- pass to ℝ
  have hXposR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hAposR : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hBposR : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hXltR : (X : ℝ) < (A : ℝ) * (B : ℝ) ^ (n + 1) := by exact_mod_cast hXlt
  have hlog1 : Real.log X < Real.log A + ((n + 1 : ℕ) : ℝ) * Real.log B := by
    have := Real.log_lt_log hXposR hXltR
    rwa [Real.log_mul hAposR.ne' (by positivity), Real.log_pow] at this
  have hA2 : (A : ℝ) ^ 2 ≤ X := by
    have : A * A ≤ X := by nlinarith
    have : ((A * A : ℕ) : ℝ) ≤ X := by exact_mod_cast this
    push_cast at this; nlinarith
  have hlog2 : 2 * Real.log A ≤ Real.log X := by
    have := Real.log_le_log (by positivity) hA2
    rwa [Real.log_pow] at this
  have hNR : ((n + 1 : ℕ) : ℝ) ≤ (fiberCountZZ S X : ℝ) := by exact_mod_cast hN
  have hkey : Real.log X ≤ 2 * ((n + 1 : ℕ) : ℝ) * Real.log B := by nlinarith
  calc 1 / (2 * Real.log B) * Real.log X
      ≤ 1 / (2 * Real.log B) * (2 * ((n + 1 : ℕ) : ℝ) * Real.log B) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = ((n + 1 : ℕ) : ℝ) := by field_simp
    _ ≤ _ := hNR

end DiophCompression.ResearchUpgrade
