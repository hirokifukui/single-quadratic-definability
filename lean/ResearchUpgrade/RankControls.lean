/-
  RankControls.lean — s55.  R43 D1 (GATE25 #70): totality alone does not produce an affine
  section in rank three.

  * `d1_no_affine_section` — no rational affine family `p + L t` solves
    `b² + u² + v² = 1 + 8 Σ aᵢ²` along a full lattice coset (the quadratic parts force
    `LᵀL = 8M²·I₄`, of rank four, while `LᵀL` has rank at most three; `rc_gram`, `rc_rank_contra`).
  * `d1_total_of_threeSquares`, `ctlD1_total_of_threeSquares` — totality, CONDITIONAL on the
    three-square theorem for `N ≡ 1 (mod 8)` taken as a hypothesis (no Lean proof at this pin; no
    axiom is added).  `d1_outputs_zero`, `ctlD1_not_outputUnique` — outputs `−1, 0, 1` at `a = 0`:
    a counter-example to the totality-only strategy, not to a normal form.
  * Rank four, unconditional: `d1r4_total` (four squares), `d1r4_no_affine_section`,
    `ctlD1r4_total`, `ctlD1r4_not_outputUnique`.

  Not claimed: non-existence of degree-two sections.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.GraphVocabulary
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.SumFourSquares

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace RankControl

theorem rc_mulVec_castQ {a b : ℕ} (L : Matrix (Fin b) (Fin a) ℚ) (u : Fin a → ℤ) (k : Fin b) :
    (L *ᵥ castQ u) k = ∑ i, L k i * (u i : ℚ) := rfl

theorem rc_gram {a b : ℕ} (M : ℕ) (lam : ℚ) (ρ : Fin a → ℤ) (p : Fin b → ℚ)
    (L : Matrix (Fin b) (Fin a) ℚ)
    (h : ∀ t : Fin a → ℤ, ∑ k, (p k + (L *ᵥ castQ t) k) ^ 2
      = 1 + lam * ∑ i, ((ρ i : ℚ) + (M : ℚ) * (t i : ℚ)) ^ 2) :
    Lᵀ * L = (lam * (M : ℚ) ^ 2) • (1 : Matrix (Fin a) (Fin a) ℚ) := by
  classical
  have hbil : ∀ s t : Fin a → ℤ,
      ∑ k, (L *ᵥ castQ s) k * (L *ᵥ castQ t) k
        = lam * (M : ℚ) ^ 2 * ∑ i, (s i : ℚ) * (t i : ℚ) := by
    intro s t
    have h1 := h (s + t)
    have h2 := h s
    have h3 := h t
    have h4 := h 0
    have hk : ∀ k, (p k + (L *ᵥ castQ (s + t)) k) ^ 2
        = (p k + (L *ᵥ castQ s) k) ^ 2 + (p k + (L *ᵥ castQ t) k) ^ 2 - (p k + (L *ᵥ castQ 0) k) ^ 2
          + 2 * ((L *ᵥ castQ s) k * (L *ᵥ castQ t) k) := by
      intro k
      simp only [rc_mulVec_castQ, Pi.add_apply, Pi.zero_apply, Int.cast_add, Int.cast_zero,
        mul_zero, Finset.sum_const_zero, mul_add, Finset.sum_add_distrib]
      ring
    have hi : ∀ i, ((ρ i : ℚ) + (M : ℚ) * (((s + t) i : ℤ) : ℚ)) ^ 2
        = ((ρ i : ℚ) + (M : ℚ) * (s i : ℚ)) ^ 2 + ((ρ i : ℚ) + (M : ℚ) * (t i : ℚ)) ^ 2
          - ((ρ i : ℚ) + (M : ℚ) * (((0 : Fin a → ℤ) i : ℤ) : ℚ)) ^ 2
          + 2 * ((M : ℚ) ^ 2 * ((s i : ℚ) * (t i : ℚ))) := by
      intro i
      simp only [Pi.add_apply, Pi.zero_apply, Int.cast_add, Int.cast_zero]
      ring
    rw [Finset.sum_congr rfl fun k _ => hk k] at h1
    rw [Finset.sum_congr rfl fun i _ => hi i] at h1
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
    rw [h2, h3, h4] at h1
    linarith
  ext i j
  have := hbil (Pi.single i 1) (Pi.single j 1)
  simp only [rc_mulVec_castQ] at this
  simp only [Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, smul_eq_mul]
  rw [this]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem rc_rank_contra {a b : ℕ} (hab : b < a) (c : ℚ) (hc : c ≠ 0)
    (L : Matrix (Fin b) (Fin a) ℚ) (h : Lᵀ * L = c • (1 : Matrix (Fin a) (Fin a) ℚ)) : False := by
  classical
  have h1 : (Lᵀ * L).rank ≤ b := by
    have := Matrix.rank_mul_le_right Lᵀ L
    have h2 := Matrix.rank_le_card_height L
    simp only [Fintype.card_fin] at h2
    omega
  have hu : IsUnit (c • (1 : Matrix (Fin a) (Fin a) ℚ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hc)
  have h3 := Matrix.rank_of_isUnit _ hu
  simp only [Fintype.card_fin] at h3
  rw [h, h3] at h1
  omega

theorem d1_no_affine_section (M : ℕ) (hM : 1 ≤ M) (ρ : Fin 4 → ℤ) (p : Fin 3 → ℚ)
    (L : Matrix (Fin 3) (Fin 4) ℚ) :
    ¬ ∀ t : Fin 4 → ℤ, ∑ k, (p k + (L *ᵥ castQ t) k) ^ 2
        = 1 + 8 * ∑ i, ((ρ i : ℚ) + (M : ℚ) * (t i : ℚ)) ^ 2 := by
  intro hall
  have hg := rc_gram M 8 ρ p L hall
  have hM0 : (M : ℚ) ≠ 0 := by
    have : (0 : ℚ) < M := by exact_mod_cast hM
    exact ne_of_gt this
  exact rc_rank_contra (by norm_num) _ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hM0)) L hg

theorem d1_total_of_threeSquares
    (h3 : ∀ N : ℤ, 0 ≤ N → N % 8 = 1 → ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = N)
    (a : Fin 4 → ℤ) : ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = 1 + 8 * ∑ i, a i ^ 2 := by
  apply h3
  · have : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  · generalize ∑ i, a i ^ 2 = S
    omega

theorem d1_outputs_zero (b : ℤ) :
    (∃ u v : ℤ, b ^ 2 + u ^ 2 + v ^ 2 = 1 + 8 * ∑ i, (0 : Fin 4 → ℤ) i ^ 2) ↔
      b = -1 ∨ b = 0 ∨ b = 1 := by
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, mul_zero, add_zero]
  constructor
  · rintro ⟨u, v, h⟩
    have h1 : -1 ≤ b := by nlinarith [sq_nonneg u, sq_nonneg v]
    have h2 : b ≤ 1 := by nlinarith [sq_nonneg u, sq_nonneg v]
    omega
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, 0, by norm_num⟩
    · exact ⟨1, 0, by norm_num⟩
    · exact ⟨0, 0, by norm_num⟩

def ctlD1 : QuadraticGraphData 4 1 2 where
  P :=
    { c := -1
      l := 0
      Q := fun p q => match p, q with
        | Sum.inl i, Sum.inl i' => if i = i' then -8 else 0
        | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 1
        | Sum.inr (Sum.inr i), Sum.inr (Sum.inr i') => if i = i' then 1 else 0
        | _, _ => 0 }

theorem ctlD1_eval (a : Fin 4 → ℤ) (b : Fin 1 → ℤ) (u : Fin 2 → ℤ) :
    ctlD1.P.eval (pt a b u) = b 0 ^ 2 + u 0 ^ 2 + u 1 ^ 2 - 1 - 8 * ∑ i, a i ^ 2 := by
  simp [ctlD1, IntQuad.eval, pt, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Fin.sum_univ_two, Fin.sum_univ_four]
  ring

theorem ctlD1_total_of_threeSquares
    (h3 : ∀ N : ℤ, 0 ≤ N → N % 8 = 1 → ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = N) :
    ctlD1.Total := by
  intro a
  obtain ⟨x, y, z, h⟩ := d1_total_of_threeSquares h3 a
  refine ⟨![x], ![y, z], ?_⟩
  unfold QuadraticGraphData.Sol
  rw [ctlD1_eval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  linarith

theorem ctlD1_not_outputUnique : ¬ ctlD1.OutputUnique := by
  intro hU
  have g1 : ctlD1.Graph 0 ![1] := ⟨0, by unfold QuadraticGraphData.Sol; rw [ctlD1_eval]; simp⟩
  have g0 : ctlD1.Graph 0 ![0] := ⟨![1, 0], by unfold QuadraticGraphData.Sol; rw [ctlD1_eval]; simp⟩
  have := congrFun (hU 0 _ _ g1 g0) 0
  simp at this

theorem d1r4_total (a : Fin 5 → ℤ) : ∃ z : Fin 4 → ℤ, ∑ k, z k ^ 2 = 1 + ∑ i, a i ^ 2 := by
  have hN : 0 ≤ 1 + ∑ i, a i ^ 2 := by
    have : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  obtain ⟨w, x, y, z, h⟩ := Nat.sum_four_squares (1 + ∑ i, a i ^ 2).toNat
  refine ⟨![w, x, y, z], ?_⟩
  have h' : ((w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 : ℕ) : ℤ) = ((1 + ∑ i, a i ^ 2).toNat : ℤ) := by
    rw [h]
  rw [Int.toNat_of_nonneg hN] at h'
  push_cast at h'
  simp [Fin.sum_univ_four]
  linarith

theorem d1r4_no_affine_section (M : ℕ) (hM : 1 ≤ M) (ρ : Fin 5 → ℤ) (p : Fin 4 → ℚ)
    (L : Matrix (Fin 4) (Fin 5) ℚ) :
    ¬ ∀ t : Fin 5 → ℤ, ∑ k, (p k + (L *ᵥ castQ t) k) ^ 2
        = 1 + ∑ i, ((ρ i : ℚ) + (M : ℚ) * (t i : ℚ)) ^ 2 := by
  intro hall
  have hg := rc_gram M 1 ρ p L (fun t => by rw [one_mul]; exact hall t)
  have hM0 : (M : ℚ) ≠ 0 := by
    have : (0 : ℚ) < M := by exact_mod_cast hM
    exact ne_of_gt this
  exact rc_rank_contra (by norm_num) _ (mul_ne_zero one_ne_zero (pow_ne_zero 2 hM0)) L hg

def ctlD1r4 : QuadraticGraphData 5 1 3 where
  P :=
    { c := -1
      l := 0
      Q := fun p q => match p, q with
        | Sum.inl i, Sum.inl i' => if i = i' then -1 else 0
        | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 1
        | Sum.inr (Sum.inr i), Sum.inr (Sum.inr i') => if i = i' then 1 else 0
        | _, _ => 0 }

theorem ctlD1r4_eval (a : Fin 5 → ℤ) (b : Fin 1 → ℤ) (u : Fin 3 → ℤ) :
    ctlD1r4.P.eval (pt a b u) = b 0 ^ 2 + u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 - 1 - ∑ i, a i ^ 2 := by
  simp [ctlD1r4, IntQuad.eval, pt, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Fin.sum_univ_three, Fin.sum_univ_five]
  ring

theorem ctlD1r4_total : ctlD1r4.Total := by
  intro a
  obtain ⟨z, h⟩ := d1r4_total a
  refine ⟨![z 0], ![z 1, z 2, z 3], ?_⟩
  unfold QuadraticGraphData.Sol
  rw [ctlD1r4_eval]
  simp only [Fin.sum_univ_four] at h
  have f0 : (![z 0] : Fin 1 → ℤ) 0 = z 0 := rfl
  have f1 : (![z 1, z 2, z 3] : Fin 3 → ℤ) 0 = z 1 := rfl
  have f2 : (![z 1, z 2, z 3] : Fin 3 → ℤ) 1 = z 2 := rfl
  have f3 : (![z 1, z 2, z 3] : Fin 3 → ℤ) 2 = z 3 := rfl
  rw [f0, f1, f2, f3]
  linarith

theorem ctlD1r4_not_outputUnique : ¬ ctlD1r4.OutputUnique := by
  intro hU
  have g1 : ctlD1r4.Graph 0 ![1] := ⟨0, by unfold QuadraticGraphData.Sol; rw [ctlD1r4_eval]; simp⟩
  have g0 : ctlD1r4.Graph 0 ![0] :=
    ⟨![1, 0, 0], by unfold QuadraticGraphData.Sol; rw [ctlD1r4_eval]; simp⟩
  have := congrFun (hU 0 _ _ g1 g0) 0
  simp at this

end RankControl

end DiophCompression.ResearchUpgrade
