/-
  DiophCompression/Counting.lean — r04 Task 3 combinatorial layer (session 4, 2026-08-26, claude.ai direct).
  degLE d k = exponent vectors in k variables of total degree ≤ d;  |degLE d k| = C(d+k, k);
  wCount d k = Σ_{|m|≤d} (d − |m|) = C(d+k, k+1)   (GPT r03 Task 3: the identity in Lean, not by Sage).
-/
import Mathlib

namespace DiophCompression

/-- Hockey stick in range form: Σ_{t=0}^{d} C(t+k, k) = C(d+k+1, k+1). -/
theorem sum_range_choose_add (d k : ℕ) :
    ∑ t ∈ Finset.range (d + 1), (t + k).choose k = (d + k + 1).choose (k + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, show d + 1 + k + 1 = (d + k + 1) + 1 by ring,
      Nat.choose_succ_succ' (d + k + 1) k, show d + 1 + k = d + k + 1 by ring]
    ring

/-- Exponent vectors in `k` variables of total degree ≤ `d`. -/
def degLE (d k : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => Finset.range (d + 1)).filter (fun m => ∑ i, m i ≤ d)

theorem mem_degLE {d k : ℕ} {m : Fin k → ℕ} : m ∈ degLE d k ↔ ∑ i, m i ≤ d := by
  unfold degLE
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    rw [Finset.mem_range]
    have : m i ≤ ∑ j, m j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

theorem degLE_zero_right (d : ℕ) : degLE d 0 = {fun _ => 0} := by
  ext m
  rw [mem_degLE, Finset.mem_singleton]
  constructor
  · intro _; exact Subsingleton.elim _ _
  · intro _; simp

/-- The fibre of `degLE d (k+1)` over `m 0 = m0` is the image of `degLE (d - m0) k` under `Fin.cons m0`. -/
theorem degLE_fiber (d k m0 : ℕ) (hm0 : m0 ≤ d) :
    (degLE d (k + 1)).filter (fun m => m 0 = m0)
      = (degLE (d - m0) k).image (Fin.cons m0) := by
  ext m
  rw [Finset.mem_filter, Finset.mem_image, mem_degLE]
  constructor
  · rintro ⟨hs, h0⟩
    refine ⟨Fin.tail m, ?_, ?_⟩
    · rw [mem_degLE]
      rw [Fin.sum_univ_succ] at hs
      have : m 0 + ∑ i : Fin k, Fin.tail m i ≤ d := hs
      omega
    · rw [← h0]; exact Fin.cons_self_tail m
  · rintro ⟨m', hm', rfl⟩
    rw [mem_degLE] at hm'
    refine ⟨?_, by simp⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega

theorem card_degLE (k : ℕ) : ∀ d, (degLE d k).card = (d + k).choose k := by
  induction k with
  | zero =>
    intro d
    rw [degLE_zero_right, Finset.card_singleton]
    simp
  | succ k ih =>
    intro d
    have hmaps : Set.MapsTo (fun m : Fin (k + 1) → ℕ => m 0) (degLE d (k + 1)) (Finset.range (d + 1)) := by
      intro m hm
      rw [Finset.mem_coe, mem_degLE] at hm
      rw [Finset.mem_coe, Finset.mem_range]
      show m 0 < d + 1
      have : m 0 ≤ ∑ j, m j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      omega
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfib : ∀ m0 ∈ Finset.range (d + 1),
        ((degLE d (k + 1)).filter (fun m => m 0 = m0)).card = (d - m0 + k).choose k := by
      intro m0 hm0
      rw [Finset.mem_range] at hm0
      rw [degLE_fiber d k m0 (by omega), Finset.card_image_of_injective _
        (Fin.cons_right_injective (α := fun _ : Fin (k + 1) => ℕ) m0), ih]
    rw [Finset.sum_congr rfl hfib]
    have hr := Finset.sum_range_reflect (fun t => (t + k).choose k) (d + 1)
    simp only [Nat.add_sub_cancel] at hr
    rw [hr, sum_range_choose_add, show d + (k + 1) = d + k + 1 by ring]

/-- Weighted count Σ_{|m| ≤ d} (d − |m|). -/
def wCount (d k : ℕ) : ℕ := ∑ m ∈ degLE d k, (d - ∑ i, m i)

theorem wCount_succ (d k : ℕ) : wCount (d + 1) k = wCount d k + (degLE d k).card := by
  unfold wCount
  rw [← Finset.sum_filter_add_sum_filter_not (degLE (d + 1) k) (fun m => ∑ i, m i ≤ d)]
  have h1 : (degLE (d + 1) k).filter (fun m => ∑ i, m i ≤ d) = degLE d k := by
    ext m; rw [Finset.mem_filter, mem_degLE, mem_degLE]; constructor
    · exact fun h => h.2
    · exact fun h => ⟨by omega, h⟩
  have h2 : ∑ m ∈ (degLE (d + 1) k).filter (fun m => ¬ ∑ i, m i ≤ d), (d + 1 - ∑ i, m i) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_filter, mem_degLE] at hm
    omega
  rw [h1, h2, add_zero, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [mem_degLE] at hm
  omega

theorem wCount_eq_choose (k : ℕ) : ∀ d, wCount d k = (d + k).choose (k + 1) := by
  intro d
  induction d with
  | zero =>
    unfold wCount
    rw [Finset.sum_eq_zero (fun _ _ => Nat.zero_sub _)]
    simp
  | succ d ih =>
    rw [wCount_succ, ih, card_degLE, show d + 1 + k = (d + k) + 1 by ring, Nat.choose_succ_succ' (d + k) k]
    ring

/-- Corollary (GPT r03 §3.1 / Task 4 form): Σ_{|β|≤d, q variables} (d − |β|) = C(d+q, q+1). -/
theorem wCount_eq_choose' (d q : ℕ) : wCount d q = (d + q).choose (q + 1) := wCount_eq_choose q d

end DiophCompression

#print axioms DiophCompression.card_degLE
#print axioms DiophCompression.wCount_eq_choose
