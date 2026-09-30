/-
  DimensionFromCoset.lean — Gate-18 research program, Packet C4-3 / C4-4 (upper half).
  C4-3: a vector polynomial q : ℤⁿ → ℚᵐ with components of degree ≤ 2 and n > m has an
        integer v ≠ 0 with q(v) = q(−v) (common ℚ-kernel of the linear parts, cleared to ℤ).
  C4-4 (upper half, CONDITIONAL on the normal form): a function f : ℤⁿ → ℤᵐ with a weak
        vector coset normal form and n > m is not injective.
  The iff (existence direction n ≤ m via sum of squares) needs the baseline definability
  vocabulary and is a separate leaf. Nothing here touches the baseline.
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import ResearchUpgrade.CosetNormalForm

namespace DiophCompression.ResearchUpgrade

open Matrix

/-- Clear denominators: a nonzero rational vector is a positive multiple of an integer vector. -/
theorem exists_int_vec_of_rat {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0) :
    ∃ (w : Fin n → ℤ) (d : ℕ), 0 < d ∧ w ≠ 0 ∧ castQ w = (d : ℚ) • v := by
  set d : ℕ := ∏ i, (v i).den with hd
  have hdpos : 0 < d := Finset.prod_pos (fun i _ => (v i).den_pos)
  have hint : ∀ i, ∃ z : ℤ, (z : ℚ) = v i * d := by
    intro i
    have hsplit := Finset.mul_prod_erase Finset.univ (fun i => (v i).den) (Finset.mem_univ i)
    refine ⟨(v i).num * ((∏ j ∈ Finset.univ.erase i, (v j).den : ℕ) : ℤ), ?_⟩
    rw [hd, ← hsplit]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose w hw using hint
  refine ⟨w, d, hdpos, ?_, ?_⟩
  · intro hw0
    apply hv
    funext i
    have := hw i
    rw [hw0] at this
    simp only [Pi.zero_apply, Int.cast_zero] at this
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
    have : v i * d = 0 := this.symm
    exact (mul_eq_zero.mp this).resolve_right hdq
  · funext i
    simp only [castQ, Pi.smul_apply, smul_eq_mul, hw i]
    ring

/-- C4-3: for `n > m`, every family of `m` quadratic forms in `n` variables has a nonzero
integer vector `v` with `q_j(v) = q_j(−v)` for all `j`. -/
theorem exists_collision_vector {n m : ℕ} (hnm : m < n) (q : Fin m → QuadForm n) :
    ∃ v : Fin n → ℤ, v ≠ 0 ∧ ∀ j, (q j).eval (castQ v) = (q j).eval (castQ (-v)) := by
  -- the linear parts as a matrix / linear map ℚⁿ → ℚᵐ
  set L : Matrix (Fin m) (Fin n) ℚ := Matrix.of fun j i => (q j).l i with hL
  have hker : (Matrix.mulVecLin L).ker ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
    exact hnm
  obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hlin : ∀ j, (q j).l ⬝ᵥ v = 0 := by
    intro j
    have h := congrFun (LinearMap.mem_ker.mp hvker) j
    simpa [hL, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using h
  obtain ⟨w, d, hd, hw0, hwv⟩ := exists_int_vec_of_rat v hv0
  refine ⟨w, hw0, fun j => ?_⟩
  have hneg : castQ (-w) = -castQ w := by funext i; simp [castQ]
  rw [hneg, hwv]
  simp only [QuadForm.eval, dotProduct_smul, smul_dotProduct, dotProduct_neg, neg_dotProduct,
    mulVec_neg, mulVec_smul, hlin j, smul_eq_mul, mul_zero, neg_zero]
  ring

/-- C4-4 (upper half, conditional on the normal form): a weak vector coset normal form with
`n > m` forbids injectivity. -/
theorem not_injective_of_weakVectorCosetNF {n m : ℕ} (hnm : m < n)
    (f : (Fin n → ℤ) → (Fin m → ℤ)) (h : WeakVectorCosetNF f) : ¬ Function.Injective f := by
  obtain ⟨M, ρ, q, hM, hq⟩ := h
  obtain ⟨w, hw0, hcol⟩ := exists_collision_vector hnm q
  intro hinj
  have hfeq : f (ρ + (M : ℤ) • w) = f (ρ + (M : ℤ) • (-w)) := by
    funext j
    apply Int.cast_injective (α := ℚ)
    rw [hq, hq, hcol j]
  have := hinj hfeq
  apply hw0
  have h2 : (2 * (M : ℤ)) • w = 0 := by
    have := sub_eq_zero.mpr this
    rw [add_sub_add_left_eq_sub, smul_neg, sub_neg_eq_add, ← two_smul ℤ, smul_smul] at this
    exact this
  have hM0 : (2 * (M : ℤ)) ≠ 0 := by omega
  exact (smul_eq_zero.mp h2).resolve_left hM0

end DiophCompression.ResearchUpgrade
