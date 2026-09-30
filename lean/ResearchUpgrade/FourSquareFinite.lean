/-
  FourSquareFinite.lean — s54.  R42-B1..B3: the four-square family, a REAL finite criterion
  (the s52 `BoxCriterion.total_and_outputUnique_iff` is only pointwise).

  * Lattice level (`FourSquareFinite`): for a residue vector `η ∈ [0,k)ᵐ`, `m > 0`,
    `#S_η = 1 ↔ d_η ≤ R0 < d_η + g_η` (`existsUnique_iff_gap`), with `d_η = Σ δ_j²`,
    `g_η = min_j k(k − 2δ_j)`, `δ_j = min(η_j, k − η_j)`; the unique point is the coordinatewise
    nearest one (`nearest_mem`); an explicit finite box and the cardinality form
    (`mem_boxFinset_of_le`, `existsUnique_iff_card`).  All residues:
    `full_residue_iff` — k odd and `m·h² ≤ R0 < (h+1)²` (k = 2h+1); controls k=3,m=3,R0=3 (yes),
    k=3,m=4 (no R0), k=5,m=2,R0=8 (yes).
  * `IntQuad.eval_eq_c_iff`: constancy of a degree-≤2 integer polynomial is the finite coefficient
    condition `l = 0 ∧ Q + Qᵀ = 0` (not "every entry of Q is 0").
  * Family level: `total_and_outputUnique_iff_finite` (R42-B1) — under the explicit hR, total ∧ OU
    iff the coefficient condition and exactly one point for each of the FINITELY many reachable
    residues `resid ρ`, `ρ ∈ {0,…,k−1}ⁿ` (n = 0 included); no quantifier over inputs remains.
    `…_iff_thresholds`, `graph_iff_table` (f read off: `⌊lin/k⌋ + nearest`), and
    `…_iff_of_surjective` under the EXTRA hypothesis that every residue is reached (R42-B3).
  * Controls: `ExNeg` (k = 2, R = a(a−1)): representatives 0, 1 pass, output-uniqueness fails at
    a = 3, the residual is not constant.  `Ex` passes through the finite criterion.

  Not claimed: a decision procedure for general SE₂, any complexity bound, or anything for a
  residual not carried by a degree-≤2 integer polynomial.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.BoxCriterion

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace FourSquareFinite

/-- Distance from a residue `e ∈ [0,k)` to the nearest multiple of `k`. -/
def dlt (k e : ℤ) : ℤ := min e (k - e)

/-- Squared distance of the nearest lattice point: `d_η = Σ δ_j²`. -/
def dist0 {m : ℕ} (k : ℤ) (η : Fin m → ℤ) : ℤ := ∑ j, dlt k (η j) ^ 2

/-- The gap to the second point: `g_η = min_j k(k − 2δ_j)`, as a fold seeded with `k²` (the largest
possible term, so the seed never wins when `m > 0`). -/
def gap {m : ℕ} (k : ℤ) (η : Fin m → ℤ) : ℤ :=
  Finset.univ.fold min (k * k) fun j => k * (k - 2 * dlt k (η j))

/-- The nearest multiple, as a shift: `0` if `2e < k`, else `1`. -/
def nearest (k e : ℤ) : ℤ := if 2 * e < k then 0 else 1

/-! ### One coordinate -/

section coord

set_option linter.unusedSectionVars false

variable {k e : ℤ} (hk : 1 ≤ k) (he0 : 0 ≤ e) (hek : e < k)
include hk he0 hek

theorem dlt_nonneg : 0 ≤ dlt k e := by unfold dlt; omega

theorem two_dlt_le : 2 * dlt k e ≤ k := by unfold dlt; omega

theorem nearest_err : (k * nearest k e - e) ^ 2 = dlt k e ^ 2 := by
  unfold nearest dlt
  split_ifs with h
  · rw [min_eq_left (by omega)]; ring
  · rw [min_eq_right (by omega)]; ring

theorem other_err : (k * (1 - nearest k e) - e) ^ 2 = (k - dlt k e) ^ 2 := by
  unfold nearest dlt
  split_ifs with h
  · rw [min_eq_left (by omega)]; ring
  · rw [min_eq_right (by omega)]; ring

theorem dlt_le_err (s : ℤ) : dlt k e ^ 2 ≤ (k * s - e) ^ 2 := by
  have h0 := dlt_nonneg hk he0 hek
  rw [sq_le_sq, abs_of_nonneg h0]
  unfold dlt
  rcases le_or_gt s 0 with hs | hs
  · rw [abs_of_nonpos (by nlinarith)]
    have : k * s ≤ 0 := by nlinarith
    omega
  · rw [abs_of_nonneg (by nlinarith)]
    have : k ≤ k * s := by nlinarith
    omega

theorem other_le_err (s : ℤ) (hs : s ≠ nearest k e) : (k - dlt k e) ^ 2 ≤ (k * s - e) ^ 2 := by
  have h2 := two_dlt_le hk he0 hek
  rw [sq_le_sq, abs_of_nonneg (by omega)]
  unfold nearest at hs
  unfold dlt
  split_ifs at hs with h
  · rcases lt_or_gt_of_ne hs with hs | hs
    · rw [abs_of_nonpos (by nlinarith)]
      have : k * s ≤ -k := by nlinarith
      omega
    · rw [abs_of_nonneg (by nlinarith)]
      have : k ≤ k * s := by nlinarith
      omega
  · rcases lt_or_gt_of_ne hs with hs | hs
    · rw [abs_of_nonpos (by nlinarith)]
      have : k * s ≤ 0 := by nlinarith
      omega
    · rw [abs_of_nonneg (by nlinarith)]
      have : 2 * k ≤ k * s := by nlinarith
      omega

theorem term_le_sq : k * (k - 2 * dlt k e) ≤ k * k := by
  have := dlt_nonneg hk he0 hek
  nlinarith

end coord

theorem nearest_ne_other (k e : ℤ) : 1 - nearest k e ≠ nearest k e := by
  unfold nearest; split_ifs <;> omega

/-! ### The gap as a minimum -/

theorem gap_le {m : ℕ} (k : ℤ) (η : Fin m → ℤ) (j : Fin m) :
    gap k η ≤ k * (k - 2 * dlt k (η j)) :=
  (Finset.fold_min_le _).mpr (Or.inr ⟨j, Finset.mem_univ _, le_rfl⟩)

theorem exists_term_le_gap {m : ℕ} (hm : 0 < m) {k : ℤ} (hk : 1 ≤ k) {η : Fin m → ℤ}
    (hη : ∀ j, 0 ≤ η j ∧ η j < k) : ∃ j, k * (k - 2 * dlt k (η j)) ≤ gap k η := by
  rcases (Finset.fold_min_le (gap k η)).mp (le_refl (gap k η)) with h | ⟨j, -, hj⟩
  · exact ⟨⟨0, hm⟩, le_trans (term_le_sq hk (hη _).1 (hη _).2) h⟩
  · exact ⟨j, hj⟩

theorem exists_term_eq_gap {m : ℕ} (hm : 0 < m) {k : ℤ} (hk : 1 ≤ k) {η : Fin m → ℤ}
    (hη : ∀ j, 0 ≤ η j ∧ η j < k) : ∃ j, gap k η = k * (k - 2 * dlt k (η j)) := by
  obtain ⟨j, hj⟩ := exists_term_le_gap hm hk hη
  exact ⟨j, le_antisymm (gap_le k η j) hj⟩

/-! ### The whole box -/

section box

variable {m : ℕ} {k : ℤ} (hk : 1 ≤ k) {η : Fin m → ℤ} (hη : ∀ j, 0 ≤ η j ∧ η j < k)
include hk hη

/-- The coordinatewise nearest point. -/
def nearVec (k : ℤ) (η : Fin m → ℤ) : Fin m → ℤ := fun j => nearest k (η j)

theorem nearVec_err : ∑ j, (k * nearVec k η j - η j) ^ 2 = dist0 k η :=
  Finset.sum_congr rfl fun j _ => nearest_err hk (hη j).1 (hη j).2

theorem dist0_le (s : Fin m → ℤ) : dist0 k η ≤ ∑ j, (k * s j - η j) ^ 2 :=
  Finset.sum_le_sum fun j _ => dlt_le_err hk (hη j).1 (hη j).2 (s j)

theorem far_of_ne (s : Fin m → ℤ) (hs : s ≠ nearVec k η) :
    ∃ j, dist0 k η + k * (k - 2 * dlt k (η j)) ≤ ∑ j, (k * s j - η j) ^ 2 := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hs
  refine ⟨j, ?_⟩
  have h1 := Finset.add_sum_erase Finset.univ (fun i => (k * s i - η i) ^ 2) (Finset.mem_univ j)
  have h2 := Finset.add_sum_erase Finset.univ (fun i => dlt k (η i) ^ 2) (Finset.mem_univ j)
  have h3 : ∑ i ∈ Finset.univ.erase j, dlt k (η i) ^ 2
      ≤ ∑ i ∈ Finset.univ.erase j, (k * s i - η i) ^ 2 :=
    Finset.sum_le_sum fun i _ => dlt_le_err hk (hη i).1 (hη i).2 (s i)
  have h4 := other_le_err hk (hη j).1 (hη j).2 (s j) hj
  unfold dist0
  nlinarith

theorem second_point (j : Fin m) :
    ∑ i, (k * Function.update (nearVec k η) j (1 - nearest k (η j)) i - η i) ^ 2
      = dist0 k η + k * (k - 2 * dlt k (η j)) := by
  classical
  have h1 := Finset.add_sum_erase Finset.univ
    (fun i => (k * Function.update (nearVec k η) j (1 - nearest k (η j)) i - η i) ^ 2)
    (Finset.mem_univ j)
  have h2 := Finset.add_sum_erase Finset.univ (fun i => dlt k (η i) ^ 2) (Finset.mem_univ j)
  have h3 : ∑ i ∈ Finset.univ.erase j,
      (k * Function.update (nearVec k η) j (1 - nearest k (η j)) i - η i) ^ 2
      = ∑ i ∈ Finset.univ.erase j, dlt k (η i) ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    exact nearest_err hk (hη i).1 (hη i).2
  have h4 := other_err hk (hη j).1 (hη j).2
  simp only [Function.update_self] at h1
  unfold dist0
  rw [← h1, ← h2, h3, h4]
  ring

end box

/-- **R42-B2 (GAP).**  `#S_η = 1 ↔ d_η ≤ R0 < d_η + g_η`. -/
theorem existsUnique_iff_gap {m : ℕ} (hm : 0 < m) {k : ℤ} (hk : 1 ≤ k) {η : Fin m → ℤ}
    (hη : ∀ j, 0 ≤ η j ∧ η j < k) (R0 : ℤ) :
    (∃! s : Fin m → ℤ, ∑ j, (k * s j - η j) ^ 2 ≤ R0) ↔
      dist0 k η ≤ R0 ∧ R0 < dist0 k η + gap k η := by
  classical
  constructor
  · rintro ⟨s, hs, huniq⟩
    refine ⟨le_trans (dist0_le hk hη s) hs, ?_⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨j, hj⟩ := exists_term_le_gap hm hk hη
    have hA : nearVec k η = s := huniq _ (by
      show ∑ j, (k * nearVec k η j - η j) ^ 2 ≤ R0
      rw [nearVec_err hk hη]; exact le_trans (dist0_le hk hη s) hs)
    have hB : Function.update (nearVec k η) j (1 - nearest k (η j)) = s :=
      huniq _ (by
        show ∑ i, (k * Function.update (nearVec k η) j (1 - nearest k (η j)) i - η i) ^ 2 ≤ R0
        rw [second_point hk hη j]; linarith)
    have := congrFun (hB.trans hA.symm) j
    rw [Function.update_self] at this
    exact nearest_ne_other k (η j) this
  · rintro ⟨h1, h2⟩
    refine ⟨nearVec k η, by
      show ∑ j, (k * nearVec k η j - η j) ^ 2 ≤ R0
      rw [nearVec_err hk hη]; exact h1, fun y hy => ?_⟩
    have hy' : ∑ j, (k * y j - η j) ^ 2 ≤ R0 := hy
    by_contra hne
    obtain ⟨j, hj⟩ := far_of_ne hk hη y hne
    linarith [gap_le k η j]

/-- **R42-B2 (the point).**  When the box has a point, the coordinatewise nearest one is in it. -/
theorem nearest_mem {m : ℕ} {k : ℤ} (hk : 1 ≤ k) {η : Fin m → ℤ}
    (hη : ∀ j, 0 ≤ η j ∧ η j < k) {R0 : ℤ}
    (h : ∃! s : Fin m → ℤ, ∑ j, (k * s j - η j) ^ 2 ≤ R0) :
    ∑ j, (k * nearest k (η j) - η j) ^ 2 ≤ R0 := by
  obtain ⟨s, hs, -⟩ := h
  have := nearVec_err hk hη
  simp only [nearVec] at this
  rw [this]
  exact le_trans (dist0_le hk hη s) hs


/-! ### An explicit finite box and the decidable form -/

/-- An explicit finite box that contains every point of `S_η`. -/
def boxFinset (m : ℕ) (R0 : ℤ) : Finset (Fin m → ℤ) :=
  Fintype.piFinset fun _ =>
    (Finset.range (2 * R0.natAbs + 3)).image fun i : ℕ => (i : ℤ) - ((R0.natAbs : ℤ) + 1)

theorem mem_boxFinset_iff {m : ℕ} {R0 : ℤ} {s : Fin m → ℤ} :
    s ∈ boxFinset m R0 ↔
      ∀ j, -((R0.natAbs : ℤ) + 1) ≤ s j ∧ s j ≤ (R0.natAbs : ℤ) + 1 := by
  simp only [boxFinset, Fintype.mem_piFinset, Finset.mem_image, Finset.mem_range]
  refine forall_congr' fun j => ⟨?_, ?_⟩
  · rintro ⟨i, hi, hij⟩; omega
  · intro h; exact ⟨(s j + ((R0.natAbs : ℤ) + 1)).toNat, by omega, by omega⟩

/-- **B (finite box).**  Every point of `S_η` lies in `boxFinset`. -/
theorem mem_boxFinset_of_le {m : ℕ} {k : ℤ} (hk : 1 ≤ k) {η : Fin m → ℤ}
    (hη : ∀ j, 0 ≤ η j ∧ η j < k) {R0 : ℤ} {s : Fin m → ℤ}
    (h : ∑ j, (k * s j - η j) ^ 2 ≤ R0) : s ∈ boxFinset m R0 := by
  rw [mem_boxFinset_iff]
  intro j
  have hj : (k * s j - η j) ^ 2 ≤ R0 :=
    le_trans (Finset.single_le_sum (f := fun i => (k * s i - η i) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)) h
  have hN : R0 ≤ (R0.natAbs : ℤ) := Int.le_natAbs
  have h1 := Int.le_self_sq (k * s j - η j)
  have h2 := Int.le_self_sq (-(k * s j - η j))
  rw [neg_sq] at h2
  have hηj := hη j
  set N : ℤ := (R0.natAbs : ℤ) with hNdef
  have hN0 : 0 ≤ N := by omega
  constructor
  · by_contra hc
    push Not at hc
    have : k * s j ≤ s j := by nlinarith
    omega
  · by_contra hc
    push Not at hc
    have : k * (N + 2) ≤ k * s j := by nlinarith
    have : N + 2 * k ≤ k * (N + 2) := by nlinarith
    omega

/-- **B (decidable form).**  "Exactly one point" is a cardinality of an explicit finite set. -/
theorem existsUnique_iff_card {m : ℕ} {k : ℤ} (hk : 1 ≤ k) {η : Fin m → ℤ}
    (hη : ∀ j, 0 ≤ η j ∧ η j < k) (R0 : ℤ) :
    (∃! s : Fin m → ℤ, ∑ j, (k * s j - η j) ^ 2 ≤ R0) ↔
      ((boxFinset m R0).filter fun s => ∑ j, (k * s j - η j) ^ 2 ≤ R0).card = 1 := by
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨s, hs, hu⟩
    refine ⟨s, ?_⟩
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hy⟩; exact hu y hy
    · rintro rfl; exact ⟨mem_boxFinset_of_le hk hη hs, hs⟩
  · rintro ⟨s, hs⟩
    have hmem : s ∈ (boxFinset m R0).filter fun s => ∑ j, (k * s j - η j) ^ 2 ≤ R0 := by
      rw [hs]; exact Finset.mem_singleton_self s
    refine ⟨s, (Finset.mem_filter.mp hmem).2, fun y hy => ?_⟩
    have : y ∈ (boxFinset m R0).filter fun s => ∑ j, (k * s j - η j) ^ 2 ≤ R0 :=
      Finset.mem_filter.mpr ⟨mem_boxFinset_of_le hk hη hy, hy⟩
    rw [hs] at this
    exact Finset.mem_singleton.mp this

/-! ### All residues -/

theorem dist0_single {m : ℕ} (k : ℤ) (j0 : Fin m) (h : ℤ) (hk : 0 ≤ k) :
    dist0 k (fun j => if j = j0 then h else 0) = dlt k h ^ 2 := by
  classical
  unfold dist0
  rw [Finset.sum_eq_single j0]
  · simp
  · intro b _ hb
    simp only [if_neg hb, dlt]
    rw [sub_zero, min_eq_left hk]; ring
  · intro h'; exact absurd (Finset.mem_univ j0) h'

/-- **R42-B3 (all residues).**  Every residue class has exactly one point iff `k` is odd and
`m·h² ≤ R0 < (h+1)²` with `k = 2h+1` (this covers `k = 1`, where it reads `R0 = 0`). -/
theorem full_residue_iff {m : ℕ} (hm : 0 < m) {k : ℤ} (hk : 1 ≤ k) (R0 : ℤ) :
    (∀ η : Fin m → ℤ, (∀ j, 0 ≤ η j ∧ η j < k) →
        ∃! s : Fin m → ℤ, ∑ j, (k * s j - η j) ^ 2 ≤ R0) ↔
      k % 2 = 1 ∧ (m : ℤ) * ((k - 1) / 2) ^ 2 ≤ R0 ∧ R0 < ((k + 1) / 2) ^ 2 := by
  classical
  set j0 : Fin m := ⟨0, hm⟩
  constructor
  · intro H
    have hodd : k % 2 = 1 := by
      by_contra hev
      have hη : ∀ j, 0 ≤ (fun j => if j = j0 then k / 2 else 0) j ∧
          (fun j => if j = j0 then k / 2 else 0) j < k := fun j => by
        simp only; split_ifs <;> omega
      obtain ⟨h1, h2⟩ := (existsUnique_iff_gap hm hk hη R0).mp (H _ hη)
      have hg := gap_le k (fun j => if j = j0 then k / 2 else 0) j0
      simp only [↓reduceIte, dlt] at hg
      rw [min_eq_left (by omega)] at hg
      have h0 : k - 2 * (k / 2) = 0 := by omega
      rw [h0, mul_zero] at hg
      linarith
    set h := (k - 1) / 2 with hh
    have hk2 : k = 2 * h + 1 := by omega
    refine ⟨hodd, ?_, ?_⟩
    · have hη : ∀ j : Fin m, 0 ≤ (fun _ => h) j ∧ (fun _ => h) j < k :=
        fun j => ⟨by show 0 ≤ h; omega, by show h < k; omega⟩
      obtain ⟨h1, -⟩ := (existsUnique_iff_gap hm hk hη R0).mp (H _ hη)
      have hd : dist0 k (fun _ : Fin m => h) = (m : ℤ) * h ^ 2 := by
        simp only [dist0, dlt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [min_eq_left (by omega)]
      linarith
    · have hη : ∀ j, 0 ≤ (fun j => if j = j0 then h else 0) j ∧
          (fun j => if j = j0 then h else 0) j < k := fun j => by
        simp only; split_ifs <;> omega
      obtain ⟨-, h2⟩ := (existsUnique_iff_gap hm hk hη R0).mp (H _ hη)
      rw [dist0_single k j0 h (by omega)] at h2
      have hg := gap_le k (fun j => if j = j0 then h else 0) j0
      simp only [↓reduceIte] at hg
      have hdh : dlt k h = h := by unfold dlt; rw [min_eq_left (by omega)]
      rw [hdh] at hg h2
      have hh1 : (k + 1) / 2 = h + 1 := by omega
      rw [hh1]
      nlinarith
  · rintro ⟨hodd, h1, h2⟩ η hη
    rw [existsUnique_iff_gap hm hk hη]
    set h := (k - 1) / 2 with hh
    have hk2 : k = 2 * h + 1 := by omega
    have hh1 : (k + 1) / 2 = h + 1 := by omega
    rw [hh1] at h2
    have hδ : ∀ j, dlt k (η j) ≤ h := fun j => by
      have := two_dlt_le hk (hη j).1 (hη j).2; omega
    have hδ0 : ∀ j, 0 ≤ dlt k (η j) := fun j => dlt_nonneg hk (hη j).1 (hη j).2
    constructor
    · have : dist0 k η ≤ ∑ _j : Fin m, h ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (hδ0 j) (hδ j) 2
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      linarith
    · obtain ⟨j, hj⟩ := exists_term_eq_gap hm hk hη
      rw [hj]
      have hd : dlt k (η j) ^ 2 ≤ dist0 k η :=
        Finset.single_le_sum (f := fun i => dlt k (η i) ^ 2) (fun i _ => sq_nonneg _)
          (Finset.mem_univ j)
      have := hδ j
      have := hδ0 j
      nlinarith

theorem full_residue_k3_m3 : ∀ η : Fin 3 → ℤ, (∀ j, 0 ≤ η j ∧ η j < 3) →
    ∃! s : Fin 3 → ℤ, ∑ j, (3 * s j - η j) ^ 2 ≤ 3 :=
  (full_residue_iff (m := 3) (by norm_num) (k := 3) (by norm_num) 3).mpr (by norm_num)

theorem not_full_residue_k3_m4 (R0 : ℤ) : ¬ ∀ η : Fin 4 → ℤ, (∀ j, 0 ≤ η j ∧ η j < 3) →
    ∃! s : Fin 4 → ℤ, ∑ j, (3 * s j - η j) ^ 2 ≤ R0 := fun H => by
  have := (full_residue_iff (m := 4) (by norm_num) (k := 3) (by norm_num) R0).mp H
  norm_num at this
  omega

theorem full_residue_k5_m2 : ∀ η : Fin 2 → ℤ, (∀ j, 0 ≤ η j ∧ η j < 5) →
    ∃! s : Fin 2 → ℤ, ∑ j, (5 * s j - η j) ^ 2 ≤ 8 :=
  (full_residue_iff (m := 2) (by norm_num) (k := 5) (by norm_num) 8).mpr (by norm_num)

end FourSquareFinite

/-- A degree-≤2 integer polynomial is constant iff its coefficients say so — a finite condition on
the coefficients (the symmetric part of `Q`, not every entry of `Q`). -/
theorem IntQuad.eval_eq_c_iff {n : ℕ} (P : IntQuad (Fin n)) :
    (∀ x, P.eval x = P.c) ↔ (∀ i, P.l i = 0) ∧ ∀ i j, P.Q i j + P.Q j i = 0 := by
  classical
  constructor
  · intro h
    have hlq : ∀ x : Fin n → ℤ, P.l ⬝ᵥ x = 0 ∧ x ⬝ᵥ (P.Q *ᵥ x) = 0 := by
      intro x
      have h1 := h x
      have h2 := h (-x)
      simp only [IntQuad.eval, dotProduct_neg, mulVec_neg, neg_dotProduct, neg_neg] at h1 h2
      constructor <;> linarith
    have hform : ∀ i j : Fin n, Pi.single i (1 : ℤ) ⬝ᵥ (P.Q *ᵥ Pi.single j 1) = P.Q i j := by
      intro i j
      rw [mulVec_single_one, single_dotProduct, one_mul]
      rfl
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · have := (hlq (Pi.single i 1)).1
      rwa [dotProduct_single, mul_one] at this
    · have h3 := (hlq (Pi.single i 1 + Pi.single j 1)).2
      have hi := (hlq (Pi.single i 1)).2
      have hj := (hlq (Pi.single j 1)).2
      rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hform, hform, hform,
        hform] at h3
      rw [hform] at hi
      rw [hform] at hj
      linarith
  · rintro ⟨hl, hQ⟩ x
    have h1 : x ⬝ᵥ (P.Q *ᵥ x) = ∑ a, ∑ b, x a * (P.Q a b * x b) := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
    have h2 : (∑ a, ∑ b, x a * (P.Q a b * x b)) = ∑ a, ∑ b, x b * (P.Q b a * x a) :=
      Finset.sum_comm
    have h3 : (∑ a, ∑ b, x a * (P.Q a b * x b)) + ∑ a, ∑ b, x b * (P.Q b a * x a) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun b _ => ?_
      linear_combination (x a * x b) * hQ a b
    have hS : x ⬝ᵥ (P.Q *ᵥ x) = 0 := by linarith
    have hl0 : P.l ⬝ᵥ x = 0 := by
      simp [dotProduct, hl]
    simp only [IntQuad.eval]
    rw [hl0]
    linarith

namespace FourSquareSlack
namespace Family

variable {n m : ℕ} (F : Family n m)

open FourSquareFinite

/-- The reachable residue vector of the representative `ρ ∈ {0,…,k−1}ⁿ`. -/
def resid (ρ : Fin n → Fin F.k.toNat) (j : Fin m) : ℤ :=
  F.lin (fun i => ((ρ i : ℕ) : ℤ)) j % F.k

theorem resid_bounds (ρ : Fin n → Fin F.k.toNat) (j : Fin m) :
    0 ≤ F.resid ρ j ∧ F.resid ρ j < F.k := by
  have := F.hk
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩

/-- The representative of an input. -/
def rep (a : Fin n → ℤ) : Fin n → Fin F.k.toNat := fun i =>
  ⟨(a i % F.k).toNat, by
    have := F.hk
    have h1 := Int.emod_lt_of_pos (a i) (show 0 < F.k by omega)
    have h2 := Int.emod_nonneg (a i) (show F.k ≠ 0 by omega)
    omega⟩

theorem resid_rep (a : Fin n → ℤ) (j : Fin m) : F.resid (F.rep a) j = F.lin a j % F.k := by
  have hk0 : 0 < F.k := by have := F.hk; omega
  have hcast : (fun i => (((F.rep a i : Fin F.k.toNat) : ℕ) : ℤ)) = fun i => a i % F.k := by
    funext i
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ hk0.ne')
  unfold resid
  rw [hcast]
  show Int.ModEq F.k _ _
  rw [Int.modEq_iff_dvd]
  have : F.lin a j - F.lin (fun i => a i % F.k) j = ∑ i, F.B j i * (F.k * (a i / F.k)) := by
    simp only [lin]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.emod_def]
    ring
  rw [this]
  exact Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (dvd_mul_right _ _) _

omit F in
theorem shift_existsUnique {m : ℕ} (k : ℤ) (L : Fin m → ℤ) (R0 : ℤ) :
    (∃! b : Fin m → ℤ, ∑ j, (k * b j - L j) ^ 2 ≤ R0) ↔
      ∃! s : Fin m → ℤ, ∑ j, (k * s j - L j % k) ^ 2 ≤ R0 := by
  refine Equiv.existsUnique_congr (Equiv.subRight (fun j => L j / k)) fun b => ?_
  have e : ∀ j, k * b j - L j = k * (b - fun j => L j / k) j - L j % k := by
    intro j
    simp only [Pi.sub_apply]
    rw [Int.emod_def]
    ring
  simp only [Equiv.subRight_apply]
  rw [Finset.sum_congr rfl fun j _ => by rw [e j]]

theorem R_const_c (hm : 0 < m) (hT : F.Total) (hU : F.OutputUnique) {P : IntQuad (Fin n)}
    (hR : ∀ a, F.R a = P.eval a) (x : Fin n → ℤ) : P.eval x = P.c := by
  have := F.R_const hm hT hU hR x
  rw [hR, hR] at this
  rw [this]
  simp [IntQuad.eval]

/-- **R42-B1.**  No quantifier over integer inputs remains on the right. -/
theorem total_and_outputUnique_iff_finite (hm : 0 < m) {P : IntQuad (Fin n)}
    (hR : ∀ a, F.R a = P.eval a) :
    (F.Total ∧ F.OutputUnique) ↔
      ((∀ i, P.l i = 0) ∧ (∀ i j, P.Q i j + P.Q j i = 0) ∧
        ∀ ρ : Fin n → Fin F.k.toNat,
          ∃! s : Fin m → ℤ, ∑ j, (F.k * s j - F.resid ρ j) ^ 2 ≤ P.c) := by
  constructor
  · intro hTU
    have hconst := F.R_const_c hm hTU.1 hTU.2 hR
    obtain ⟨hl, hQ⟩ := (IntQuad.eval_eq_c_iff P).mp hconst
    refine ⟨hl, hQ, fun ρ => ?_⟩
    have H := (F.total_and_outputUnique_iff).mp hTU (fun i => ((ρ i : ℕ) : ℤ))
    rw [hR, hconst] at H
    exact (shift_existsUnique F.k _ P.c).mp H
  · rintro ⟨hl, hQ, H⟩
    have hconst := (IntQuad.eval_eq_c_iff P).mpr ⟨hl, hQ⟩
    refine (F.total_and_outputUnique_iff).mpr fun a => ?_
    rw [hR, hconst]
    refine (shift_existsUnique F.k _ P.c).mpr ?_
    have := H (F.rep a)
    simp only [F.resid_rep] at this
    exact this

/-- **R42-B3 (two thresholds).** -/
theorem total_and_outputUnique_iff_thresholds (hm : 0 < m) {P : IntQuad (Fin n)}
    (hR : ∀ a, F.R a = P.eval a) :
    (F.Total ∧ F.OutputUnique) ↔
      ((∀ i, P.l i = 0) ∧ (∀ i j, P.Q i j + P.Q j i = 0) ∧
        ∀ ρ : Fin n → Fin F.k.toNat,
          FourSquareFinite.dist0 F.k (F.resid ρ) ≤ P.c ∧
            P.c < FourSquareFinite.dist0 F.k (F.resid ρ) + FourSquareFinite.gap F.k (F.resid ρ)) := by
  rw [F.total_and_outputUnique_iff_finite hm hR]
  exact and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun ρ =>
    existsUnique_iff_gap hm F.hk (F.resid_bounds ρ) P.c

/-- **R42-B3 (the table).**  The defined function, read off coordinatewise. -/
theorem graph_iff_table (hm : 0 < m) {P : IntQuad (Fin n)} (hR : ∀ a, F.R a = P.eval a)
    (hT : F.Total) (hU : F.OutputUnique) (a : Fin n → ℤ) (b : Fin m → ℤ) :
    F.Graph a b ↔
      b = fun j => F.lin a j / F.k + FourSquareFinite.nearest F.k (F.lin a j % F.k) := by
  have hconst := F.R_const_c hm hT hU hR
  obtain ⟨-, -, H⟩ := (F.total_and_outputUnique_iff_finite hm hR).mp ⟨hT, hU⟩
  have Hs := H (F.rep a)
  simp only [F.resid_rep] at Hs
  have hbd : ∀ j, 0 ≤ F.lin a j % F.k ∧ F.lin a j % F.k < F.k := by
    intro j; have := F.hk
    exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  have hnear := nearest_mem F.hk hbd Hs
  have hbox : ∀ b : Fin m → ℤ, (∑ j, (F.k * b j - F.lin a j) ^ 2)
      = ∑ j, (F.k * (b j - F.lin a j / F.k) - F.lin a j % F.k) ^ 2 := fun b =>
    Finset.sum_congr rfl fun j _ => by rw [Int.emod_def]; ring
  rw [F.graph_iff_box, hR, hconst, hbox]
  obtain ⟨s, -, hsu⟩ := Hs
  constructor
  · intro hb
    have e1 := hsu (fun j => b j - F.lin a j / F.k) hb
    have e2 := hsu (fun j => nearest F.k (F.lin a j % F.k)) hnear
    funext j
    have := congrFun (e1.trans e2.symm) j
    change b j = F.lin a j / F.k + nearest F.k (F.lin a j % F.k)
    linarith
  · rintro rfl
    simpa using hnear

/-- **R42-B3 (surjective residues).**  Under the EXTRA hypothesis that every residue is reached. -/
theorem total_and_outputUnique_iff_of_surjective (hm : 0 < m) {P : IntQuad (Fin n)}
    (hR : ∀ a, F.R a = P.eval a)
    (hsurj : ∀ η : Fin m → ℤ, (∀ j, 0 ≤ η j ∧ η j < F.k) → ∃ ρ, F.resid ρ = η) :
    (F.Total ∧ F.OutputUnique) ↔
      ((∀ i, P.l i = 0) ∧ (∀ i j, P.Q i j + P.Q j i = 0) ∧
        F.k % 2 = 1 ∧ (m : ℤ) * ((F.k - 1) / 2) ^ 2 ≤ P.c ∧ P.c < ((F.k + 1) / 2) ^ 2) := by
  rw [F.total_and_outputUnique_iff_finite hm hR, ← full_residue_iff hm F.hk P.c]
  refine and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun H η hη => ?_, fun H ρ => H _ (F.resid_bounds ρ)⟩
  obtain ⟨ρ, rfl⟩ := hsurj η hη
  exact H ρ

end Family

/-- **Negative control.**  `k = 2`, `R(a) = a(a−1)`: the representatives `a = 0, 1` pass, yet the
family is not output-unique (`a = 3`), and the residual is not constant. -/
def ExNeg : Family 1 1 := ⟨2, by norm_num, fun _ => 0, fun _ _ => 0, fun a => a 0 * (a 0 - 1)⟩

theorem ExNeg_box (a b : Fin 1 → ℤ) : ExNeg.Graph a b ↔ (2 * b 0) ^ 2 ≤ a 0 * (a 0 - 1) := by
  rw [Family.graph_iff_box]
  simp [ExNeg, Family.lin]

theorem ExNeg_representatives (a0 : ℤ) (h : a0 = 0 ∨ a0 = 1) :
    ∃! b : Fin 1 → ℤ, ExNeg.Graph (fun _ => a0) b := by
  have h0 : a0 * (a0 - 1) = 0 := by rcases h with rfl | rfl <;> norm_num
  refine ⟨0, ?_, fun y hy => ?_⟩
  · show ExNeg.Graph (fun _ => a0) 0
    rw [ExNeg_box]; simp [h0]
  · have hy' : ExNeg.Graph (fun _ => a0) y := hy
    rw [ExNeg_box] at hy'
    simp only [h0] at hy'
    funext j
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    simp only [Pi.zero_apply]
    nlinarith [sq_nonneg (y 0), hy']

theorem ExNeg_not_outputUnique : ¬ ExNeg.OutputUnique := by
  intro h
  have := h (fun _ => 3) (fun _ => 0) (fun _ => 1)
    (by rw [ExNeg_box]; norm_num) (by rw [ExNeg_box]; norm_num)
  have := congrFun this 0
  simp at this

theorem ExNeg_residual_not_const : ¬ ∀ a, ExNeg.R a = ExNeg.R 0 := fun h => by
  have := h (fun _ => 3)
  simp [ExNeg] at this

/-- `Ex` passes the finite criterion through its three reachable residues. -/
theorem Ex_total_outputUnique_via_finite : Ex.Total ∧ Ex.OutputUnique := by
  have hR : ∀ a, Ex.R a = (⟨1, 0, 0⟩ : IntQuad (Fin 1)).eval a := fun a => by
    simp [Ex, IntQuad.eval]
  rw [Ex.total_and_outputUnique_iff_finite Nat.one_pos hR]
  refine ⟨fun i => rfl, fun i j => by simp, fun ρ => ?_⟩
  exact (FourSquareFinite.full_residue_iff Nat.one_pos Ex.hk 1).mpr (by
    show (3 : ℤ) % 2 = 1 ∧ ((1 : ℕ) : ℤ) * ((3 - 1) / 2) ^ 2 ≤ 1 ∧ (1 : ℤ) < ((3 + 1) / 2) ^ 2
    decide) _ (Ex.resid_bounds ρ)

end FourSquareSlack

end DiophCompression.ResearchUpgrade
