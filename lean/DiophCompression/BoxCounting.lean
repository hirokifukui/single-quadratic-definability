/-
  DiophCompression/BoxCounting.lean — r04 Task 1, abstract core (session 4, 2026-08-26, claude.ai direct).
  If F : ℕ^n → ℤ^ι is injective and |F a j| ≤ K·N^{e j} on the box [0,N]^n for every N ≥ 1,
  then n ≤ Σ_j e j.  Pure counting: (N+1)^n ≤ ∏_j (2K N^{e j}+1) ≤ (2K+1)^{|ι|} N^{Σ e}.
  Generalizes MPUP.aux_arith / aux_counting (uniform exponent) to a degree profile.
-/
import Mathlib

namespace DiophCompression

/-- Arithmetic core of the box-counting argument. -/
theorem box_arith (n S M K : ℕ) (h : S + 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ (2 * K + 1) ^ M * N ^ S < (N + 1) ^ n := by
  refine ⟨(2 * K + 1) ^ M + 1, by omega, ?_⟩
  set N := (2 * K + 1) ^ M + 1 with hN
  have hlt : (2 * K + 1) ^ M < N := by omega
  have hpos : 0 < N ^ S := pow_pos (by omega) _
  calc (2 * K + 1) ^ M * N ^ S < N * N ^ S := (Nat.mul_lt_mul_right hpos).mpr hlt
    _ = N ^ (S + 1) := by rw [pow_succ]; ring
    _ ≤ N ^ n := Nat.pow_le_pow_right (by omega) h
    _ < (N + 1) ^ n := Nat.pow_lt_pow_left (by omega) (by omega)

/-- ∏_j (2K N^{e j} + 1) ≤ (2K+1)^{|ι|} N^{Σ e}  for N ≥ 1. -/
theorem prod_box_le {ι : Type} [Fintype ι] (e : ι → ℕ) (K N : ℕ) (h1 : 1 ≤ N) :
    ∏ j, (2 * K * N ^ e j + 1) ≤ (2 * K + 1) ^ Fintype.card ι * N ^ (∑ j, e j) := by
  have hstep : ∀ j, 2 * K * N ^ e j + 1 ≤ (2 * K + 1) * N ^ e j := by
    intro j
    have : 1 ≤ N ^ e j := Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc ∏ j, (2 * K * N ^ e j + 1) ≤ ∏ j, ((2 * K + 1) * N ^ e j) :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun j _ => hstep j)
    _ = (∏ _j : ι, (2 * K + 1)) * ∏ j, N ^ e j := Finset.prod_mul_distrib
    _ = (2 * K + 1) ^ Fintype.card ι * N ^ (∑ j, e j) := by
        rw [Finset.prod_const, Finset.card_univ, Finset.prod_pow_eq_pow_sum]

/-- THE ABSTRACT BOX-COUNTING BOUND (degree profile version). -/
theorem box_counting_bound {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : (Fin n → ℕ) → ι → ℤ) (hF : Function.Injective F) (e : ι → ℕ) (K : ℕ)
    (hb : ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℕ, (∀ i, a i ≤ N) →
      ∀ j, |F a j| ≤ (K : ℤ) * (N : ℤ) ^ e j) :
    n ≤ ∑ j, e j := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨N, h1, hlt⟩ := box_arith n (∑ j, e j) (Fintype.card ι) K (by omega)
  -- the box and the target
  let a : (Fin n → Fin (N + 1)) → (Fin n → ℕ) := fun g i => (g i : ℕ)
  have haN : ∀ g i, a g i ≤ N := fun g i => Nat.lt_succ_iff.1 (g i).isLt
  let B : ι → ℕ := fun j => K * N ^ e j
  have habs : ∀ g j, -(B j : ℤ) ≤ F (a g) j ∧ F (a g) j ≤ (B j : ℤ) := by
    intro g j
    have h := hb N h1 (a g) (haN g) j
    have hB : ((B j : ℕ) : ℤ) = (K : ℤ) * (N : ℤ) ^ e j := by simp [B]
    rw [← hB] at h
    exact abs_le.1 h
  let f : (Fin n → Fin (N + 1)) → (∀ j : ι, Fin (2 * B j + 1)) :=
    fun g j => ⟨(F (a g) j + B j).toNat, by
      rw [Int.toNat_lt' (by omega)]
      have := (habs g j).2
      push_cast
      omega⟩
  have hinj : Function.Injective f := by
    intro g g' hgg
    have hcoord : ∀ j, F (a g) j = F (a g') j := by
      intro j
      have hc := congrFun hgg j
      simp only [f] at hc
      have hv := Fin.val_eq_of_eq hc
      have hnn1 : 0 ≤ F (a g) j + B j := by have := (habs g j).1; omega
      have hnn2 : 0 ≤ F (a g') j + B j := by have := (habs g' j).1; omega
      have : F (a g) j + B j = F (a g') j + B j := by
        rw [← Int.toNat_of_nonneg hnn1, ← Int.toNat_of_nonneg hnn2]
        exact_mod_cast hv
      omega
    have hFa : F (a g) = F (a g') := funext hcoord
    have haa : a g = a g' := hF hFa
    funext i
    exact Fin.ext (congrFun haa i)
  have hcard := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_pi] at hcard
  simp only [Fintype.card_fin] at hcard
  have hprod := prod_box_le e K N h1
  simp only [B] at hcard
  have : (N + 1) ^ n ≤ (2 * K + 1) ^ Fintype.card ι * N ^ (∑ j, e j) := by
    calc (N + 1) ^ n ≤ ∏ j, (2 * (K * N ^ e j) + 1) := hcard
      _ = ∏ j, (2 * K * N ^ e j + 1) := by
          apply Finset.prod_congr rfl; intro j _; ring
      _ ≤ _ := hprod
  omega

end DiophCompression

#print axioms DiophCompression.box_counting_bound
