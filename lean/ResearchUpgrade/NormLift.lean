/-
  NormLift.lean — s54.  R42-C1..C3: the multi-input norm lift.

  * `square_values_rigidity` (C1): a rational quadratic form that is a square at EVERY integer point
    is `h(x)²` for one rational linear form `h` (via `c21_affine_square` after clearing
    denominators; extended from ℤⁿ to ℚⁿ by homogeneity).  A test on basis vectors alone would not
    suffice (`x₁² + x₂²`).
  * `direction_discriminant_square` (C2): if `c + 2ℓ(x) + H(x)` is a rational value of
    `X² + D·Y²` (`D > 0`) at every integer `x`, then `(c·H(v) − ℓ(v)²)/D` is a rational square for
    every integer direction `v`.  `H(v) ≠ 0`: `rat_discriminant_of_total'`; `H(v) = 0`:
    `not_total_of_linear` forces `ℓ(v) = 0`.
  * `norm_section` (C3): with the base value written as `r0² + D·s0² > 0`, one rational AFFINE
    pair `(r, s)` with `r(0) = r0`, `s(0) = s0` represents the whole polynomial over ℚⁿ
    (C1 on `(cH − ℓℓᵀ)/D`, then Brahmagupta's identity, `norm_identity`).
  No class-number hypothesis, no witness uniqueness.  The base representation is PRESCRIBED, not
  chosen.  `c = 0` is not covered here.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.C2Partial
import ResearchUpgrade.Unconditional

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace NormLift

/-- Every rational vector is an integer vector divided by a positive integer. -/
theorem exists_int_scale {n : ℕ} (x : Fin n → ℚ) :
    ∃ (d : ℕ) (y : Fin n → ℤ), 0 < d ∧ castQ y = (d : ℚ) • x := by
  classical
  set P : ℕ := ∏ k, (x k).den with hP
  refine ⟨P, fun i => (x i).num * ((P / (x i).den : ℕ) : ℤ),
    Finset.prod_pos fun i _ => (x i).den_pos, ?_⟩
  funext i
  have hdvd : (x i).den ∣ P := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hq : (P : ℚ) = ((P / (x i).den : ℕ) : ℚ) * (x i).den := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  have h := Rat.mul_den_eq_num (x i)
  simp only [castQ, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
  rw [hq]
  linear_combination (-(((P / (x i).den : ℕ) : ℚ))) * h

/-- Clearing denominators of a rational matrix: `A = N² T` with `A` integral. -/
theorem exists_int_scale_matrix {n : ℕ} (T : Matrix (Fin n) (Fin n) ℚ) :
    ∃ (N : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), 0 < N ∧
      ∀ i j, (A i j : ℚ) = (N : ℚ) ^ 2 * T i j := by
  classical
  set P : ℕ := ∏ p : Fin n × Fin n, (T p.1 p.2).den with hP
  refine ⟨P, fun i j => (T i j).num * ((P / (T i j).den : ℕ) : ℤ) * (P : ℤ),
    Finset.prod_pos fun p _ => (T p.1 p.2).den_pos, ?_⟩
  intro i j
  have hdvd : (T i j).den ∣ P :=
    Finset.dvd_prod_of_mem (fun p : Fin n × Fin n => (T p.1 p.2).den) (Finset.mem_univ (i, j))
  have hq : (P : ℚ) = ((P / (T i j).den : ℕ) : ℚ) * (T i j).den := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  have h := Rat.mul_den_eq_num (T i j)
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [hq]
  linear_combination (-((((P / (T i j).den : ℕ) : ℚ)) ^ 2 * ((T i j).den : ℚ))) * h

theorem castQ_zero {n : ℕ} : castQ (0 : Fin n → ℤ) = 0 := by
  funext i; simp [castQ]

/-- **R42-C1.**  A rational quadratic form that is a square at every integer point is the square of
one rational linear form. -/
theorem square_values_rigidity {n : ℕ} (T : Matrix (Fin n) (Fin n) ℚ)
    (hsq : ∀ v : Fin n → ℤ, IsSquare (castQ v ⬝ᵥ (T *ᵥ castQ v))) :
    ∃ h : Fin n → ℚ, ∀ x : Fin n → ℚ, x ⬝ᵥ (T *ᵥ x) = (h ⬝ᵥ x) ^ 2 := by
  obtain ⟨N, A, hN, hA⟩ := exists_int_scale_matrix T
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdelta : ∀ x : Fin n → ℤ,
      ((deltaQ A 0 0 x : ℤ) : ℚ) = (N : ℚ) ^ 2 * (castQ x ⬝ᵥ (T *ᵥ castQ x)) := by
    intro x
    simp only [deltaQ, add_zero, dotProduct, mulVec, castQ]
    push_cast
    simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hA]
    ring
  have hsqZ : ∀ x : Fin n → ℤ, IsSquare (deltaQ A 0 0 x) := by
    intro x
    rw [← Rat.isSquare_intCast_iff]
    obtain ⟨r, hr⟩ := hsq x
    exact ⟨(N : ℚ) * r, by rw [hdelta, hr]; ring⟩
  obtain ⟨ℓ, s, hℓ⟩ := c21_affine_square A 0 0 hsqZ
  have hs : s = 0 := by
    have h0 := hℓ 0
    have hd0 : deltaQ A 0 0 (0 : Fin n → ℤ) = 0 := by
      simp [deltaQ]
    rw [hd0, castQ_zero, dotProduct_zero, zero_add] at h0
    push_cast at h0
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0.symm
  subst hs
  refine ⟨(1 / (N : ℚ)) • ℓ, ?_⟩
  -- integer points
  have hint : ∀ y : Fin n → ℤ,
      castQ y ⬝ᵥ (T *ᵥ castQ y) = (((1 / (N : ℚ)) • ℓ) ⬝ᵥ castQ y) ^ 2 := by
    intro y
    have h1 := hℓ y
    rw [hdelta, add_zero] at h1
    rw [smul_dotProduct, smul_eq_mul]
    have hN2 : ((N : ℚ) ^ 2) ≠ 0 := pow_ne_zero 2 hNq
    field_simp
    linear_combination h1
  intro x
  obtain ⟨d, y, hd, hy⟩ := exists_int_scale x
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have h2 := hint y
  rw [hy, mulVec_smul, dotProduct_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul] at h2
  have hd2 : (d : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hdq
  have : (d : ℚ) ^ 2 * (x ⬝ᵥ (T *ᵥ x)) = (d : ℚ) ^ 2 * ((((1 / (N : ℚ)) • ℓ) ⬝ᵥ x) ^ 2) := by
    linear_combination h2
  exact mul_left_cancel₀ hd2 this


theorem castQ_intSmul {n : ℕ} (t : ℤ) (v : Fin n → ℤ) : castQ (t • v) = (t : ℚ) • castQ v := by
  funext i; simp [castQ]

/-- **R42-C2.**  Norm representability at every integer point forces the direction discriminant to
be `D` times a square, in every integer direction (the `H(v) = 0` directions included). -/
theorem direction_discriminant_square {n : ℕ} (D c : ℚ) (hD : 0 < D) (ell : Fin n → ℚ)
    (H : Matrix (Fin n) (Fin n) ℚ)
    (hrep : ∀ x : Fin n → ℤ, ∃ X Y : ℚ,
      c + 2 * (ell ⬝ᵥ castQ x) + castQ x ⬝ᵥ (H *ᵥ castQ x) = X ^ 2 + D * Y ^ 2)
    (v : Fin n → ℤ) :
    IsSquare ((c * (castQ v ⬝ᵥ (H *ᵥ castQ v)) - (ell ⬝ᵥ castQ v) ^ 2) / D) := by
  set A' := castQ v ⬝ᵥ (H *ᵥ castQ v) with hA'
  set L := ell ⬝ᵥ castQ v with hL
  have hline : ∀ t : ℤ, ∃ X Y : ℚ,
      A' * (t : ℚ) ^ 2 + (2 * L) * (t : ℚ) + c = X ^ 2 + D * Y ^ 2 := by
    intro t
    obtain ⟨X, Y, h⟩ := hrep (t • v)
    refine ⟨X, Y, ?_⟩
    rw [castQ_intSmul, mulVec_smul, dotProduct_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul] at h
    rw [← h, hA', hL]
    ring
  have hD0 : D ≠ 0 := hD.ne'
  by_cases hA0 : A' = 0
  · have hL0 : L = 0 := by
      by_contra hL0
      apply not_total_of_linear (2 * L) c D hD (by
        intro h; apply hL0; linarith)
      intro t
      obtain ⟨X, Y, h⟩ := hline t
      exact ⟨X, Y, by rw [← h, hA0]⟩
    refine ⟨0, ?_⟩
    rw [hA0, hL0]
    simp
  · obtain ⟨h', hh'⟩ := rat_discriminant_of_total' A' (2 * L) c D hD hA0 hline
    refine ⟨h' / 2, ?_⟩
    field_simp
    linear_combination (-1 : ℚ) * hh'

/-- The discriminant matrix `(c·H − ℓℓᵀ)/D`, entrywise. -/
def discMatrix {n : ℕ} (D c : ℚ) (ell : Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => (c * H i j - ell i * ell j) / D

theorem discMatrix_form {n : ℕ} (D c : ℚ) (hD : D ≠ 0) (ell : Fin n → ℚ)
    (H : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    x ⬝ᵥ (discMatrix D c ell H *ᵥ x) = (c * (x ⬝ᵥ (H *ᵥ x)) - (ell ⬝ᵥ x) ^ 2) / D := by
  rw [eq_div_iff hD]
  simp only [discMatrix, dotProduct, mulVec, Matrix.of_apply]
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- The algebra of the section: Brahmagupta's identity after `cH − ℓ² = Dh²`. -/
theorem norm_identity (D r0 s0 L K Q : ℚ) (hc : r0 ^ 2 + D * s0 ^ 2 ≠ 0)
    (hx : (r0 ^ 2 + D * s0 ^ 2) * Q - L ^ 2 = D * K ^ 2) :
    (r0 ^ 2 + D * s0 ^ 2) + 2 * L + Q
      = (r0 + 1 / (r0 ^ 2 + D * s0 ^ 2) * (r0 * L - D * s0 * K)) ^ 2
        + D * (s0 + 1 / (r0 ^ 2 + D * s0 ^ 2) * (s0 * L + r0 * K)) ^ 2 := by
  field_simp
  linear_combination (r0 ^ 2 + D * s0 ^ 2) * hx

/-- **R42-C3.**  The affine norm section through a PRESCRIBED representation `(r0, s0)` of the base
value `c = r0² + D s0² > 0`. -/
theorem norm_section {n : ℕ} (D r0 s0 : ℚ) (hD : 0 < D) (hc : 0 < r0 ^ 2 + D * s0 ^ 2)
    (ell : Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ)
    (hrep : ∀ x : Fin n → ℤ, ∃ X Y : ℚ,
      (r0 ^ 2 + D * s0 ^ 2) + 2 * (ell ⬝ᵥ castQ x) + castQ x ⬝ᵥ (H *ᵥ castQ x) = X ^ 2 + D * Y ^ 2) :
    ∃ rl sl : Fin n → ℚ, ∀ x : Fin n → ℚ,
      (r0 ^ 2 + D * s0 ^ 2) + 2 * (ell ⬝ᵥ x) + x ⬝ᵥ (H *ᵥ x)
        = (r0 + rl ⬝ᵥ x) ^ 2 + D * (s0 + sl ⬝ᵥ x) ^ 2 := by
  set c := r0 ^ 2 + D * s0 ^ 2 with hcdef
  have hD0 : D ≠ 0 := hD.ne'
  have hc0 : c ≠ 0 := hc.ne'
  obtain ⟨h, hh⟩ := square_values_rigidity (discMatrix D c ell H) (fun v => by
    rw [discMatrix_form D c hD0]
    exact direction_discriminant_square D c hD ell H hrep v)
  have rel : ∀ x : Fin n → ℚ, c * (x ⬝ᵥ (H *ᵥ x)) - (ell ⬝ᵥ x) ^ 2 = D * (h ⬝ᵥ x) ^ 2 := by
    intro x
    have := hh x
    rw [discMatrix_form D c hD0] at this
    field_simp at this
    linear_combination this
  refine ⟨(1 / c) • (r0 • ell - (D * s0) • h), (1 / c) • (s0 • ell + r0 • h), fun x => ?_⟩
  have hx := rel x
  simp only [smul_dotProduct, sub_dotProduct, add_dotProduct, smul_eq_mul]
  exact norm_identity D r0 s0 _ _ _ hc0 hx

end NormLift

end DiophCompression.ResearchUpgrade
