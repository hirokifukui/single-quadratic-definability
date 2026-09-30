/-
  C2DeltaZero.lean — Gate-18 research program, Packet c2_delta_zero_ofmv.
  Three deliverables (all honestly labelled):
    1. General-`n` converse `QuadForm.ofMv`: every `MvPolynomial (Fin n) ℚ` of total degree ≤ 2
       is realised by a `QuadForm n`.  The engine is the classification lemma
       `degree_le_two_cases`: a monomial exponent `d : Fin n →₀ ℕ` with `d.sum ≤ 2` is one of
       `0`, `single i 1`, `single i 2`, `single i 1 + single j 1` (`i ≠ j`).
    2. C2-2 parabolic case δ = 0, one input / one linear witness `u`:
       (a) NO-WITNESS-after-change reduction: the relation with the `u`-column killed is exactly
           the C1 relation `R1`, so `oneInputNoWitness_full` gives `FullCosetNF`.
       (b) LINEAR-WITNESS obstruction: if the witness `u` survives with a nonzero coefficient `m`,
           the relation is invariant under `y ↦ y + m`, hence NEVER total-unique; `FullCosetNF`
           follows vacuously.  (This is the "witness only imposes a congruence" phenomenon.)
    3. Split case δ > 0 square, trivial sub-branch `β₁ = β₂ = 0`, `a₁ = 1`: one branch is always
       integral, so total-uniqueness pins the output to that affine branch, giving `FullCosetNF`.

  Baseline (mpup-lean r39) is read-only.  No sorry, no new axiom.
-/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Notation
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Core
import ResearchUpgrade.C2Partial
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.OneInputNoWitness

namespace DiophCompression.ResearchUpgrade

open Matrix MvPolynomial
open scoped Classical

namespace QuadForm

/-! ## Part 1 — general-`n` converse `ofMv`

The candidate `QuadForm` extracted from a polynomial `p`: constant `coeff 0 p`, linear part
`coeff (single i 1) p`, symmetric quadratic part with diagonal `coeff (single i 2) p` and
off-diagonal split `(1/2)·coeff (single i 1 + single j 1) p`. -/

/-- The `QuadForm` read off the low-degree coefficients of `p`. -/
noncomputable def mkQ {n : ℕ} (p : MvPolynomial (Fin n) ℚ) : QuadForm n where
  c := coeff 0 p
  l := fun i => coeff (Finsupp.single i 1) p
  Q := fun i j => if i = j then coeff (Finsupp.single i 2) p
                  else (1/2 : ℚ) * coeff (Finsupp.single i 1 + Finsupp.single j 1) p

/-- The explicit expansion of `(mkQ p).eval t`. -/
theorem mkQ_eval {n : ℕ} (p : MvPolynomial (Fin n) ℚ) (t : Fin n → ℚ) :
    (mkQ p).eval t
      = coeff 0 p + ∑ i, coeff (Finsupp.single i 1) p * t i
        + ∑ i, t i * ∑ j, (if i = j then coeff (Finsupp.single i 2) p
            else (1/2 : ℚ) * coeff (Finsupp.single i 1 + Finsupp.single j 1) p) * t j := by
  simp only [QuadForm.eval, mkQ, dotProduct, Matrix.mulVec]

/-! ### Classification of degree-≤2 monomial exponents. -/

/-- The total-degree functional of `single i m`. -/
private theorem tdeg_single {n : ℕ} (i : Fin n) (m : ℕ) :
    ((Finsupp.single i m : Fin n →₀ ℕ).sum fun _ e => e) = m :=
  Finsupp.sum_single_index rfl

/-- The total-degree functional is additive. -/
private theorem tdeg_add {n : ℕ} (a b : Fin n →₀ ℕ) :
    ((a + b).sum fun _ e => e) = (a.sum fun _ e => e) + (b.sum fun _ e => e) :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- **Classification lemma** (`degree_le_two_cases`).  A monomial exponent of total degree ≤ 2 is
`0`, `single i 1`, `single i 2`, or `single i 1 + single j 1` with `i ≠ j`. -/
theorem degree_le_two_cases {n : ℕ} (d : Fin n →₀ ℕ) (hd : (d.sum fun _ e => e) ≤ 2) :
    d = 0 ∨ (∃ i, d = Finsupp.single i 1) ∨ (∃ i, d = Finsupp.single i 2)
      ∨ (∃ i j, i ≠ j ∧ d = Finsupp.single i 1 + Finsupp.single j 1) := by
  classical
  have hcard : d.support.card ≤ 2 := by
    have h1 : d.support.card ≤ ∑ i ∈ d.support, d i := by
      have := Finset.card_nsmul_le_sum d.support d 1
        (fun i hi => Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi))
      simpa using this
    calc d.support.card ≤ ∑ i ∈ d.support, d i := h1
      _ = d.sum (fun _ e => e) := rfl
      _ ≤ 2 := hd
  rcases Nat.lt_or_ge d.support.card 1 with h0 | h1
  · -- card = 0
    have hs : d.support = ∅ := Finset.card_eq_zero.1 (by omega)
    exact Or.inl (Finsupp.support_eq_empty.1 hs)
  · rcases Nat.lt_or_ge d.support.card 2 with h1' | h2
    · -- card = 1
      obtain ⟨a, hne, heq⟩ := Finsupp.card_support_eq_one.1
        (Nat.le_antisymm (Nat.lt_succ_iff.1 h1') h1)
      have htot : (d.sum fun _ e => e) = d a := by
        conv_lhs => rw [heq]
        exact tdeg_single a (d a)
      have hpos : 1 ≤ d a := Nat.one_le_iff_ne_zero.2 hne
      have hle : d a ≤ 2 := by omega
      have : d a = 1 ∨ d a = 2 := by omega
      rcases this with h | h
      · exact Or.inr (Or.inl ⟨a, by rw [heq, h]⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨a, by rw [heq, h]⟩))
    · -- card = 2
      have hc2 : d.support.card = 2 := le_antisymm hcard h2
      obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.1 hc2
      have hamem : a ∈ d.support := by rw [hs]; exact Finset.mem_insert_self a {b}
      have hbmem : b ∈ d.support := by
        rw [hs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      have hapos : 1 ≤ d a := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hamem)
      have hbpos : 1 ≤ d b := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hbmem)
      have htot : (d.sum fun _ e => e) = d a + d b := by
        rw [Finsupp.sum, hs, Finset.sum_pair hab]
      have hda : d a = 1 := by omega
      have hdb : d b = 1 := by omega
      refine Or.inr (Or.inr (Or.inr ⟨a, b, hab, ?_⟩))
      ext i
      by_cases hia : i = a
      · subst hia
        rw [Finsupp.add_apply, Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne hab, add_zero, hda]
      · by_cases hib : i = b
        · subst hib
          rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm hab), Finsupp.single_eq_same,
            zero_add, hdb]
        · have hnotin : i ∉ d.support := by rw [hs]; simp [hia, hib]
          rw [Finsupp.notMem_support_iff.1 hnotin, Finsupp.add_apply,
            Finsupp.single_eq_of_ne hia, Finsupp.single_eq_of_ne hib, add_zero]

/-! ### Additivity of `p ↦ (mkQ p).eval t` and reduction to monomials. -/

theorem mkQ_eval_add {n : ℕ} (x y : MvPolynomial (Fin n) ℚ) (t : Fin n → ℚ) :
    (mkQ (x + y)).eval t = (mkQ x).eval t + (mkQ y).eval t := by
  rw [mkQ_eval, mkQ_eval, mkQ_eval, coeff_add]
  have e1 : ∑ i, coeff (Finsupp.single i 1) (x + y) * t i
      = (∑ i, coeff (Finsupp.single i 1) x * t i) + ∑ i, coeff (Finsupp.single i 1) y * t i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [coeff_add]; ring)
  have e2 : (∑ i, t i * ∑ j, (if i = j then coeff (Finsupp.single i 2) (x + y)
        else (1/2 : ℚ) * coeff (Finsupp.single i 1 + Finsupp.single j 1) (x + y)) * t j)
      = (∑ i, t i * ∑ j, (if i = j then coeff (Finsupp.single i 2) x
        else (1/2 : ℚ) * coeff (Finsupp.single i 1 + Finsupp.single j 1) x) * t j)
      + ∑ i, t i * ∑ j, (if i = j then coeff (Finsupp.single i 2) y
        else (1/2 : ℚ) * coeff (Finsupp.single i 1 + Finsupp.single j 1) y) * t j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← mul_add]; congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← add_mul]; congr 1
    split_ifs <;> rw [coeff_add] <;> ring
  rw [e1, e2]; ring

theorem mkQ_eval_zero {n : ℕ} (t : Fin n → ℚ) :
    (mkQ (0 : MvPolynomial (Fin n) ℚ)).eval t = 0 := by
  rw [mkQ_eval]; simp

theorem mkQ_eval_sum {n : ℕ} (s : Finset (Fin n →₀ ℕ))
    (F : (Fin n →₀ ℕ) → MvPolynomial (Fin n) ℚ) (t : Fin n → ℚ) :
    (mkQ (∑ d ∈ s, F d)).eval t = ∑ d ∈ s, (mkQ (F d)).eval t := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [mkQ_eval_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, mkQ_eval_add, ih]

/-! ### Auxiliary Finsupp facts for the classification of the monomial cases. -/

private theorem tdeg_zero {n : ℕ} :
    ((0 : Fin n →₀ ℕ).sum fun _ e => e) = 0 := Finsupp.sum_zero_index

/-- `single a 2` is never a two-distinct-variable exponent. -/
private theorem single_two_ne_pair {n : ℕ} (a k l : Fin n) (hkl : k ≠ l) :
    (Finsupp.single a 2 : Fin n →₀ ℕ) ≠ Finsupp.single k 1 + Finsupp.single l 1 := by
  intro h
  have hk := DFunLike.congr_fun h k
  simp only [Finsupp.add_apply, Finsupp.single_apply] at hk
  rw [if_neg (Ne.symm hkl)] at hk
  split_ifs at hk <;> omega

/-- `single i 1 + single i 1 = single i 2`. -/
private theorem single_one_add_self {n : ℕ} (i : Fin n) :
    (Finsupp.single i 1 + Finsupp.single i 1 : Fin n →₀ ℕ) = Finsupp.single i 2 := by
  rw [← Finsupp.single_add]

/-- Equality of two-variable exponents (`k ≠ l`) forces the index pair to match up to swap. -/
private theorem pair_eq_pair_iff {n : ℕ} {i j k l : Fin n} (hkl : k ≠ l) :
    (Finsupp.single k 1 + Finsupp.single l 1 : Fin n →₀ ℕ)
        = Finsupp.single i 1 + Finsupp.single j 1
      ↔ (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  constructor
  · intro h
    have hk := DFunLike.congr_fun h k
    have hl := DFunLike.congr_fun h l
    simp only [Finsupp.add_apply, Finsupp.single_apply, if_true] at hk hl
    rw [if_neg (Ne.symm hkl)] at hk
    rw [if_neg hkl] at hl
    by_cases hik : i = k
    · subst hik
      refine Or.inl ⟨rfl, ?_⟩
      by_contra hjl
      rw [if_neg hkl, if_neg hjl] at hl
      omega
    · rw [if_neg hik, zero_add] at hk
      have hjk : j = k := by by_contra hc; rw [if_neg hc] at hk; omega
      subst hjk
      refine Or.inr ⟨?_, rfl⟩
      rw [if_neg hkl] at hl
      by_contra hil; rw [if_neg hil] at hl; omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [add_comm]

/-! ### The per-monomial identity. -/

/-- On a single degree-≤2 monomial the constructed `QuadForm` reproduces the evaluation. -/
theorem mkQ_eval_monomial {n : ℕ} (d : Fin n →₀ ℕ) (a : ℚ) (t : Fin n → ℚ)
    (hd : (d.sum fun _ e => e) ≤ 2) :
    (mkQ (monomial d a)).eval t = MvPolynomial.eval t (monomial d a) := by
  classical
  rw [mkQ_eval, eval_monomial]
  rcases degree_le_two_cases d hd with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, l, hkl, rfl⟩
  · -- d = 0
    have hlin : (∑ i, coeff (Finsupp.single i 1) (monomial (0 : Fin n →₀ ℕ) a) * t i) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [coeff_monomial, if_neg (fun hcon => by
        have h := congrArg (fun z : Fin n →₀ ℕ => z.sum fun _ e => e) hcon
        simp only [tdeg_single, tdeg_zero] at h; omega), zero_mul]
    have hquad : (∑ i, t i * ∑ j, (if i = j then coeff (Finsupp.single i 2) (monomial (0 : Fin n →₀ ℕ) a)
          else (1/2 : ℚ) * coeff (Finsupp.single i 1 + Finsupp.single j 1) (monomial (0 : Fin n →₀ ℕ) a)) * t j) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Finset.mul_sum]; refine (Finset.sum_eq_zero (fun j _ => ?_))
      rw [coeff_monomial, coeff_monomial]
      by_cases h : i = j
      · rw [if_pos h, if_neg (fun hcon => by
          have h := congrArg (fun z : Fin n →₀ ℕ => z.sum fun _ e => e) hcon
          simp only [tdeg_single, tdeg_zero] at h; omega), zero_mul, mul_zero]
      · rw [if_neg h, if_neg (fun hcon => by
          have h := congrArg (fun z : Fin n →₀ ℕ => z.sum fun _ e => e) hcon
          simp only [tdeg_add, tdeg_single, tdeg_zero] at h; omega), mul_zero, zero_mul, mul_zero]
    rw [hlin, hquad, coeff_monomial, if_pos rfl, Finsupp.prod_zero_index, mul_one]
    ring
  · -- d = single k 1
    have hc0 : coeff 0 (monomial (Finsupp.single k 1) a) = 0 := by
      rw [coeff_monomial, if_neg (fun hcon => by
        have h := congrArg (fun z : Fin n →₀ ℕ => z.sum fun _ e => e) hcon
        simp only [tdeg_single, tdeg_zero] at h; omega)]
    have hlin : (∑ i, coeff (Finsupp.single i 1) (monomial (Finsupp.single k 1) a) * t i)
        = a * t k := by
      rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
      · rw [coeff_monomial, if_pos rfl]
      · intro i _ hik
        rw [coeff_monomial, if_neg (by
          rw [Finsupp.single_left_inj (by norm_num : (1:ℕ) ≠ 0)]; exact fun h => hik h.symm), zero_mul]
    have hquad : (∑ i, t i * ∑ j, (if i = j then coeff (Finsupp.single i 2) (monomial (Finsupp.single k 1) a)
          else (1/2 : ℚ) * coeff (Finsupp.single i 1 + Finsupp.single j 1) (monomial (Finsupp.single k 1) a)) * t j) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Finset.mul_sum]; refine (Finset.sum_eq_zero (fun j _ => ?_))
      rw [coeff_monomial, coeff_monomial]
      by_cases h : i = j
      · rw [if_pos h, if_neg (fun hcon => by
          have h := congrArg (fun z : Fin n →₀ ℕ => z.sum fun _ e => e) hcon
          simp only [tdeg_single] at h; omega), zero_mul, mul_zero]
      · rw [if_neg h, if_neg (fun hcon => by
          have h := congrArg (fun z : Fin n →₀ ℕ => z.sum fun _ e => e) hcon
          simp only [tdeg_add, tdeg_single] at h; omega), mul_zero, zero_mul, mul_zero]
    rw [hc0, hlin, hquad, Finsupp.prod_single_index (by simp), pow_one]
    ring
  · -- d = single k 2
    have hc0 : coeff 0 (monomial (Finsupp.single k 2) a) = 0 := by
      rw [coeff_monomial, if_neg (fun hcon => by
        have h := congrArg (fun z : Fin n →₀ ℕ => z.sum fun _ e => e) hcon
        simp only [tdeg_single, tdeg_zero] at h; omega)]
    have hlin : (∑ i, coeff (Finsupp.single i 1) (monomial (Finsupp.single k 2) a) * t i) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [coeff_monomial, if_neg (fun hcon => by
        have h := congrArg (fun z : Fin n →₀ ℕ => z.sum fun _ e => e) hcon
        simp only [tdeg_single] at h; omega), zero_mul]
    have hquad : (∑ i, t i * ∑ j, (if i = j then coeff (Finsupp.single i 2) (monomial (Finsupp.single k 2) a)
          else (1/2 : ℚ) * coeff (Finsupp.single i 1 + Finsupp.single j 1) (monomial (Finsupp.single k 2) a)) * t j)
        = a * t k ^ 2 := by
      rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
      · rw [Finset.mul_sum, Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
        · rw [if_pos rfl, coeff_monomial, if_pos rfl]; ring
        · intro j _ hkj
          rw [if_neg (Ne.symm hkj), coeff_monomial,
            if_neg (single_two_ne_pair k k j (Ne.symm hkj)), mul_zero, zero_mul, mul_zero]
      · intro i _ hik
        rw [Finset.mul_sum]; refine (Finset.sum_eq_zero (fun j _ => ?_))
        by_cases h : i = j
        · rw [if_pos h, coeff_monomial, if_neg (fun hcon =>
            hik ((Finsupp.single_left_inj (by norm_num : (2:ℕ) ≠ 0)).1 hcon).symm),
            zero_mul, mul_zero]
        · rw [if_neg h, coeff_monomial, if_neg (single_two_ne_pair k i j h),
            mul_zero, zero_mul, mul_zero]
    rw [hc0, hlin, hquad, Finsupp.prod_single_index (by simp)]
    ring
  · -- d = single k 1 + single l 1, k ≠ l
    have hprod : (Finsupp.single k 1 + Finsupp.single l 1 : Fin n →₀ ℕ).prod
        (fun n e => t n ^ e) = t k * t l := by
      rw [Finsupp.prod_add_index' (fun a => by simp) (fun a b c => by rw [pow_add])]
      rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp), pow_one, pow_one]
    have hc0 : coeff 0 (monomial (Finsupp.single k 1 + Finsupp.single l 1) a) = 0 := by
      rw [coeff_monomial, if_neg (fun hcon => by
        have h := congrArg (fun z : Fin n →₀ ℕ => z.sum fun _ e => e) hcon
        simp only [tdeg_add, tdeg_single, tdeg_zero] at h; omega)]
    have hlin : (∑ i, coeff (Finsupp.single i 1)
        (monomial (Finsupp.single k 1 + Finsupp.single l 1) a) * t i) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [coeff_monomial, if_neg (fun hcon => by
        have h := congrArg (fun z : Fin n →₀ ℕ => z.sum fun _ e => e) hcon
        simp only [tdeg_add, tdeg_single] at h; omega), zero_mul]
    have hquad : (∑ i, t i * ∑ j, (if i = j then coeff (Finsupp.single i 2)
          (monomial (Finsupp.single k 1 + Finsupp.single l 1) a)
          else (1/2 : ℚ) * coeff (Finsupp.single i 1 + Finsupp.single j 1)
          (monomial (Finsupp.single k 1 + Finsupp.single l 1) a)) * t j) = a * (t k * t l) := by
      set mono := monomial (Finsupp.single k 1 + Finsupp.single l 1) a with hmono
      -- The diagonal coefficient vanishes, so the whole entry is the off-diagonal one.
      have hAll : ∀ i j, (if i = j then coeff (Finsupp.single i 2) mono
            else (1/2 : ℚ) * coeff (Finsupp.single i 1 + Finsupp.single j 1) mono)
          = (1/2 : ℚ) * coeff (Finsupp.single i 1 + Finsupp.single j 1) mono := by
        intro i j
        by_cases h : i = j
        · subst h
          rw [if_pos rfl]
          have hz : coeff (Finsupp.single i 2) mono = 0 := by
            rw [hmono, coeff_monomial, if_neg (fun hh => single_two_ne_pair i k l hkl hh.symm)]
          rw [single_one_add_self i, hz]; ring
        · rw [if_neg h]
      -- The off-diagonal coefficient is `a` exactly on the two matching index pairs.
      have hcoeff : ∀ i j, coeff (Finsupp.single i 1 + Finsupp.single j 1) mono
          = if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then a else 0 := by
        intro i j
        rw [hmono, coeff_monomial]
        by_cases h : (i = k ∧ j = l) ∨ (i = l ∧ j = k)
        · rw [if_pos ((pair_eq_pair_iff hkl).2 h), if_pos h]
        · rw [if_neg (fun hh => h ((pair_eq_pair_iff hkl).1 hh)), if_neg h]
      have hsplit : ∀ i j : Fin n, (if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then a else 0)
          = (if i = k ∧ j = l then a else 0) + (if i = l ∧ j = k then a else 0) := by
        intro i j
        by_cases h1 : i = k ∧ j = l
        · by_cases h2 : i = l ∧ j = k
          · exact absurd (h1.1.symm.trans h2.1) hkl
          · rw [if_pos (Or.inl h1), if_pos h1, if_neg h2, add_zero]
        · by_cases h2 : i = l ∧ j = k
          · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2, zero_add]
          · rw [if_neg (fun hh => hh.elim h1 h2), if_neg h1, if_neg h2, add_zero]
      have D1 : (∑ i, t i * ∑ j, ((1/2:ℚ) * (if i = k ∧ j = l then a else 0)) * t j)
          = (1/2:ℚ) * a * (t k * t l) := by
        rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
        · have hinner : (∑ j, ((1/2:ℚ) * (if k = k ∧ j = l then a else 0)) * t j)
              = (1/2:ℚ) * a * t l := by
            rw [Finset.sum_eq_single_of_mem l (Finset.mem_univ l)]
            · rw [if_pos ⟨rfl, rfl⟩]
            · intro j _ hjl; rw [if_neg (fun hh => hjl hh.2), mul_zero, zero_mul]
          rw [hinner]; ring
        · intro i _ hik
          refine mul_eq_zero.2 (Or.inr (Finset.sum_eq_zero (fun j _ => ?_)))
          rw [if_neg (fun hh => hik hh.1), mul_zero, zero_mul]
      have D2 : (∑ i, t i * ∑ j, ((1/2:ℚ) * (if i = l ∧ j = k then a else 0)) * t j)
          = (1/2:ℚ) * a * (t l * t k) := by
        rw [Finset.sum_eq_single_of_mem l (Finset.mem_univ l)]
        · have hinner : (∑ j, ((1/2:ℚ) * (if l = l ∧ j = k then a else 0)) * t j)
              = (1/2:ℚ) * a * t k := by
            rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
            · rw [if_pos ⟨rfl, rfl⟩]
            · intro j _ hjk; rw [if_neg (fun hh => hjk hh.2), mul_zero, zero_mul]
          rw [hinner]; ring
        · intro i _ hil
          refine mul_eq_zero.2 (Or.inr (Finset.sum_eq_zero (fun j _ => ?_)))
          rw [if_neg (fun hh => hil hh.1), mul_zero, zero_mul]
      calc (∑ i, t i * ∑ j, (if i = j then coeff (Finsupp.single i 2) mono
              else (1/2 : ℚ) * coeff (Finsupp.single i 1 + Finsupp.single j 1) mono) * t j)
          = ∑ i, t i * ∑ j, ((1/2:ℚ) * ((if i = k ∧ j = l then a else 0)
              + (if i = l ∧ j = k then a else 0))) * t j := by
            refine Finset.sum_congr rfl (fun i _ => ?_); congr 1
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [hAll i j, hcoeff i j, hsplit i j]
        _ = (∑ i, t i * ∑ j, ((1/2:ℚ) * (if i = k ∧ j = l then a else 0)) * t j)
              + (∑ i, t i * ∑ j, ((1/2:ℚ) * (if i = l ∧ j = k then a else 0)) * t j) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [← mul_add]; congr 1
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [mul_add, add_mul]
        _ = a * (t k * t l) := by rw [D1, D2]; ring
    rw [hc0, hlin, hquad, hprod]
    ring

/-- **General-`n` converse `ofMv`.** Every degree-≤2 polynomial in `n` variables is a `QuadForm`. -/
theorem ofMv {n : ℕ} (p : MvPolynomial (Fin n) ℚ) (hp : p.totalDegree ≤ 2) :
    ∃ q : QuadForm n, ∀ t : Fin n → ℚ, MvPolynomial.eval t p = q.eval t := by
  classical
  refine ⟨mkQ p, fun t => ?_⟩
  have hL : MvPolynomial.eval t p = ∑ d ∈ p.support, MvPolynomial.eval t (monomial d (coeff d p)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  have hR : (mkQ p).eval t = ∑ d ∈ p.support, (mkQ (monomial d (coeff d p))).eval t := by
    conv_lhs => rw [p.as_sum]
    rw [mkQ_eval_sum]
  rw [hL, hR]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdeg : (d.sum fun _ e => e) ≤ 2 := le_trans (le_totalDegree hd) hp
  exact (mkQ_eval_monomial d (coeff d p) t hdeg).symm

end QuadForm

/-! ## Part 2 — C2-2 parabolic case δ = 0, one input `x`, one witness `u`

The `(y,u)`-quadratic part is a perfect square `λ w²` (`δ = 0`).  After the unimodular change of
`(y,u)`-coordinates, two honest sub-cases arise.

**(a) No witness after the change.**  When the change kills the `u`-column, the relation is exactly
the C1 relation `R1`, so `oneInputNoWitness_full` already delivers `FullCosetNF`. -/

/-- The parabolic δ = 0 case with the witness column killed is literally the C1 relation, so the
output function has the full-residue coset normal form. -/
theorem c22_noWitness_fullCoset (a b d e f g : ℤ) (hT : RelTotal (R1 a b d e f g))
    (hU : RelUnique (R1 a b d e f g)) : FullCosetNF (f1 a b d e f g hT) :=
  oneInputNoWitness_full a b d e f g hT hU

/-! **(b) Linear witness survives.**  If the witness `u` keeps a nonzero coefficient `m`, the
relation `∃ u, a y² + (b x + d) y + (e x² + f x + g) + m u = 0` is equivalent to a congruence
`… ≡ 0 (mod m)`, hence invariant under `y ↦ y + m`.  With `m ≠ 0` this destroys uniqueness. -/

/-- The parabolic relation with a linearly-appearing witness `u` of coefficient `m`. -/
def Puw (a b d e f g m : ℤ) (x y : ℤ) : Prop :=
  ∃ u : ℤ, a * y ^ 2 + (b * x + d) * y + (e * x ^ 2 + f * x + g) + m * u = 0

/-- The relation is invariant under `y ↦ y + m` (the witness only imposes a congruence mod `m`). -/
theorem Puw_shift (a b d e f g m : ℤ) (x y : ℤ) (h : Puw a b d e f g m x y) :
    Puw a b d e f g m x (y + m) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u - (2 * a * y + a * m + b * x + d), by linear_combination hu⟩

/-- **Linear-witness obstruction.** With `m ≠ 0` the relation is never simultaneously total and
unique: any output `y` at an input forces the distinct output `y + m` at the same input. -/
theorem c22_witnessLinear_not_totalUnique (a b d e f g m : ℤ) (hm : m ≠ 0) :
    ¬ (RelTotal (Puw a b d e f g m) ∧ RelUnique (Puw a b d e f g m)) := by
  rintro ⟨hT, hU⟩
  obtain ⟨y0, hy0⟩ := hT 0
  have hshift := Puw_shift a b d e f g m 0 y0 hy0
  have heq : y0 = y0 + m := hU 0 y0 (y0 + m) hy0 hshift
  exact hm (by linarith)

/-- The (choice-extracted) output function of the linear-witness relation. -/
noncomputable def fuw (a b d e f g m : ℤ) (hT : RelTotal (Puw a b d e f g m)) :
    (Fin 1 → ℤ) → ℤ := fun x => Classical.choose (hT (x 0))

/-- Consequently `FullCosetNF` holds **vacuously** for a (non-existent) total-unique linear-witness
family with `m ≠ 0`. -/
theorem c22_witnessLinear_fullCoset (a b d e f g m : ℤ) (hm : m ≠ 0)
    (hT : RelTotal (Puw a b d e f g m)) (hU : RelUnique (Puw a b d e f g m)) :
    FullCosetNF (fuw a b d e f g m hT) :=
  absurd ⟨hT, hU⟩ (c22_witnessLinear_not_totalUnique a b d e f g m hm)

/-- `m = 1`: the witness is free, so every `y` is an output — uniqueness fails. -/
example (a b d e f g : ℤ) :
    ¬ (RelTotal (Puw a b d e f g 1) ∧ RelUnique (Puw a b d e f g 1)) :=
  c22_witnessLinear_not_totalUnique a b d e f g 1 (by norm_num)

/-- `m = 2`, `a = 1`, `b = 0`: `y² + d y + (e x² + f x + g) ≡ 0 (mod 2)` cannot single out a unique
`y`, so no total-unique family exists (and `FullCosetNF` holds vacuously). -/
example (d e f g : ℤ) :
    ¬ (RelTotal (Puw 1 0 d e f g 2) ∧ RelUnique (Puw 1 0 d e f g 2)) :=
  c22_witnessLinear_not_totalUnique 1 0 d e f g 2 (by norm_num)

/-! ## Part 3 — split case δ > 0 (perfect square), trivial sub-branch

The `(y,u)`-form factors as two affine lines.  With `β₁ = β₂ = 0` the two branches are C1-type in
`y`.  We prove the honest trivial sub-case `a₁ = 1`: branch 1 (`y + (p₁ x + q₁)`) is always
integral, so total-uniqueness pins the output to that affine branch and `FullCosetNF` follows. -/

/-- The split relation `(y + (p₁ x + q₁)) · (a₂ y + (p₂ x + q₂)) = 0` (`β₁ = β₂ = 0`, `a₁ = 1`). -/
def Psplit (a2 p1 q1 p2 q2 : ℤ) (x y : ℤ) : Prop :=
  (y + (p1 * x + q1)) * (a2 * y + (p2 * x + q2)) = 0

/-- Branch 1 is always available, so the relation is total. -/
theorem Psplit_total (a2 p1 q1 p2 q2 : ℤ) : RelTotal (Psplit a2 p1 q1 p2 q2) :=
  fun x => ⟨-(p1 * x + q1), by simp only [Psplit]; ring⟩

/-- The (choice-extracted) output function of the split relation. -/
noncomputable def fsplit (a2 p1 q1 p2 q2 : ℤ) (hT : RelTotal (Psplit a2 p1 q1 p2 q2)) :
    (Fin 1 → ℤ) → ℤ := fun x => Classical.choose (hT (x 0))

/-- **Split trivial sub-case.** A total-unique split family (`β₁ = β₂ = 0`, `a₁ = 1`) has its output
pinned to the affine branch `y = −(p₁ x + q₁)`, hence lands in the full-residue coset normal form. -/
theorem c33_split_fullCoset (a2 p1 q1 p2 q2 : ℤ)
    (hT : RelTotal (Psplit a2 p1 q1 p2 q2)) (hU : RelUnique (Psplit a2 p1 q1 p2 q2)) :
    FullCosetNF (fsplit a2 p1 q1 p2 q2 hT) := by
  have hval : ∀ x : Fin 1 → ℤ, fsplit a2 p1 q1 p2 q2 hT x = -(p1 * x 0 + q1) := by
    intro x
    have hout : Psplit a2 p1 q1 p2 q2 (x 0) (Classical.choose (hT (x 0))) :=
      Classical.choose_spec (hT (x 0))
    have hbr : Psplit a2 p1 q1 p2 q2 (x 0) (-(p1 * x 0 + q1)) := by simp only [Psplit]; ring
    exact hU (x 0) _ _ hout hbr
  apply globalQuadratic_imp_fullCoset_one
  refine ⟨⟨-(q1 : ℚ), fun _ => -(p1 : ℚ), fun _ _ => 0⟩, fun x => ?_⟩
  rw [hval x]
  simp only [QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
  push_cast
  ring

end DiophCompression.ResearchUpgrade
