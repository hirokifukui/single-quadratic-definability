/-
  frozen_statements/WeightedBound_STATEMENTS.lean — s34 (2026-09-04, agora, claude.ai direct).

  Verbatim freeze of every declaration of MPUP/WeightedBound.lean: the weighted counting
  obstruction of Appendix C, its two closed forms, and the two final no-go theorems.
  Created in answer to Gate-8 F01: before s34 this module carried thirteen theorems and two
  definitions and none of them were frozen, so the manuscript's claim that every theorem
  statement is frozen and diffed did not hold of the load-bearing Appendix C theorem.
  Statements only; the proofs live in the production tree and are checked by the kernel there.
-/
import MPUP.Obstruction

namespace MPUP

def wtCount (d k : ℕ) : ℕ := sorry

theorem wtCount_le_crude (d k : ℕ) : wtCount d k ≤ d * monoCount d k := by sorry

theorem wtCount_mono {d d' k k' : ℕ} (hd : d ≤ d') (hk : k ≤ k') :
    wtCount d k ≤ wtCount d' k' := by sorry

theorem aux_arith_weighted (n W A : ℕ) (h : W + 1 ≤ n) :
    ∃ N, 1 ≤ N ∧ A * N ^ W < (N + 1) ^ n := by sorry

def pval {n r : ℕ} (v : Fin (n+1) ⊕ Fin r) (k : ℕ) : ℕ := sorry

theorem pval_efac {n r : ℕ} (v : Fin (n+1) ⊕ Fin r) (k : ℕ) :
    pval v k + (efac v k).sum (fun _ x => x) = k := by sorry

theorem deg_finset_sum {ι : Type*} {σ : Type*} (s : Finset ι) (g : ι → (σ →₀ ℕ)) :
    (∑ i ∈ s, g i).sum (fun _ k => k) = ∑ i ∈ s, (g i).sum (fun _ k => k) := by sorry

theorem aux_kappa_bound_weighted {n r N : ℕ} (C0 : Poly (n+1) r) (a : Fin n → ℕ)
    (hN : ∀ i, a i ≤ N) (h1 : 1 ≤ N)
    (β : (Fin (n+1) ⊕ Fin r) →₀ ℕ) (hβ : β ∈ C0.support)
    (m : (Fin 1 ⊕ Fin r) →₀ ℕ) (hm : (∑ v ∈ β.support, efac v (β v)) = m) :
    |∏ v ∈ β.support, cfac a v (β v)| ≤ (N : ℤ) ^ (C0.totalDegree - (m.sum fun _ k => k)) := by sorry

theorem aux_coeff_bound_weighted {n r N : ℕ} (C0 : Poly (n + 1) r) (a : Fin n → ℕ)
    (hN : ∀ i, a i ≤ N) (h1 : 1 ≤ N) (m : (Fin 1 ⊕ Fin r) →₀ ℕ) :
    |(Phi C0 a).coeff m|
      ≤ (∑ β ∈ C0.support, |C0.coeff β|)
          * (N : ℤ) ^ (C0.totalDegree - (m.sum fun _ k => k)) := by sorry

theorem aux_coeff_nat_weighted {n r N : ℕ} (C0 : Poly (n+1) r) (a : Fin n → ℕ)
    (hN : ∀ i, a i ≤ N) (h1 : 1 ≤ N) (m : (Fin 1 ⊕ Fin r) →₀ ℕ) :
    ((Phi C0 a).coeff m).natAbs
      ≤ (∑ β ∈ C0.support, (C0.coeff β).natAbs)
          * N ^ (C0.totalDegree - (m.sum fun _ k => k)) := by sorry

theorem aux_counting_weighted {n r : ℕ} {W : Set (Fin r → ℤ)} (C0 : Poly (n + 1) r)
    {e : (Fin n → ℕ) → ℕ} (he : Function.Injective e)
    (hC : RepresentsIn W C0 (graph e)) (N : ℕ) (h1 : 1 ≤ N) :
    (N + 1) ^ n
      ≤ (2 * (∑ β ∈ C0.support, (C0.coeff β).natAbs) + 1) ^ (monoCount C0.totalDegree (r + 1))
          * N ^ (wtCount C0.totalDegree (r + 1)) := by sorry

theorem coder_counting_bound_weighted {n r : ℕ} (W : Set (Fin r → ℤ)) (C : Poly (n + 1) r)
    (e : (Fin n → ℕ) → ℕ) (he : Function.Injective e) (hC : RepresentsIn W C (graph e)) :
    n ≤ wtCount C.totalDegree (r + 1) := by sorry

theorem multiUniversalN_bound_weighted {ν δ : ℕ → ℕ} (h : MultiUniversalN ν δ) (n : ℕ) :
    n ≤ wtCount (δ (n + 1)) (ν (n + 1) + 1) := by sorry

theorem multiUniversalZ_bound_weighted {ν δ : ℕ → ℕ} (h : MultiUniversalZ ν δ) (n : ℕ) :
    n ≤ wtCount (δ (n + 1)) (ν (n + 1) + 1) := by sorry

theorem not_MPUP_N_of_weighted_bound : ¬ MPUP_N := by sorry

theorem monoCount_widen {e d k : ℕ} (h : e ≤ d) :
    ((Finset.univ : Finset (Fin k → Fin (d + 1))).filter
      (fun m => ∑ i, (m i : ℕ) ≤ e)).card = monoCount e k := by sorry

theorem monoCount_succ_right (d k : ℕ) :
    monoCount d (k + 1) = ∑ t ∈ Finset.range (d + 1), monoCount (d - t) k := by sorry

theorem monoCount_closed_form (d k : ℕ) : monoCount d k = (d + k).choose k := by sorry

theorem wtCount_eq_sum_monoCount (d k : ℕ) :
    wtCount d k = ∑ e ∈ Finset.range d, monoCount e k := by sorry

theorem wtCount_closed_form (d k : ℕ) : wtCount d k = (d + k).choose (k + 1) := by sorry

theorem not_MPUP_Z_of_weighted_bound : ¬ MPUP_Z := by sorry

end MPUP
