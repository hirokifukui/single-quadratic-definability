/-
  DiophCompression/PolynomialMapCapacity.lean — r04 Task 1 (session 4, 2026-08-26, claude.ai direct).
  An injective polynomial map F = (F_j)_{j∈ι} : ℕ^n → ℤ^ι with totalDegree F_j ≤ e_j satisfies
  n ≤ Σ_j e_j (degree-sum version, GPT r03 Task 1). Uniform-degree corollary n ≤ |ι|·d.
  Domain is ℕ^n (parameters), values in ℤ; the ℤ^n-domain variant is NOT stated (GPT Task 1 homework).
-/
import DiophCompression.BoxCounting

namespace DiophCompression

open MvPolynomial

/-- Evaluation bound on the box: |p(a)| ≤ (Σ|coeff|) · N^{deg p} for 0 ≤ a_i ≤ N, N ≥ 1. -/
theorem eval_abs_le {n : ℕ} (p : MvPolynomial (Fin n) ℤ) {N : ℕ} (h1 : 1 ≤ N)
    (a : Fin n → ℕ) (ha : ∀ i, a i ≤ N) :
    |eval (fun i => (a i : ℤ)) p|
      ≤ (∑ β ∈ p.support, |coeff β p|) * (N : ℤ) ^ p.totalDegree := by
  rw [eval_eq]
  calc |∑ β ∈ p.support, coeff β p * ∏ i ∈ β.support, ((a i : ℤ)) ^ β i|
      ≤ ∑ β ∈ p.support, |coeff β p * ∏ i ∈ β.support, ((a i : ℤ)) ^ β i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ β ∈ p.support, |coeff β p| * (N : ℤ) ^ p.totalDegree := by
        apply Finset.sum_le_sum
        intro β hβ
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [Finset.abs_prod]
        calc ∏ i ∈ β.support, |((a i : ℤ)) ^ β i| ≤ ∏ i ∈ β.support, (N : ℤ) ^ β i := by
              apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
              intro i _
              rw [abs_pow, abs_of_nonneg (by positivity)]
              exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast ha i) _
          _ = (N : ℤ) ^ (∑ i ∈ β.support, β i) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ (N : ℤ) ^ p.totalDegree :=
              pow_le_pow_right₀ (by exact_mod_cast h1) (le_totalDegree hβ)
    _ = _ := by rw [Finset.sum_mul]

/-- The polynomial map `a ↦ (F_j(a))_j` on ℕ^n. -/
noncomputable def polyMap {n : ℕ} {ι : Type} (F : ι → MvPolynomial (Fin n) ℤ) :
    (Fin n → ℕ) → ι → ℤ :=
  fun a j => eval (fun i => (a i : ℤ)) (F j)

/-- DEGREE-SUM CAPACITY: injective polynomial map with degree profile `e` ⟹ n ≤ Σ e. -/
theorem injective_polyMap_dimension_le_degreeSum {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → MvPolynomial (Fin n) ℤ) (e : ι → ℕ) (he : ∀ j, (F j).totalDegree ≤ e j)
    (hinj : Function.Injective (polyMap F)) :
    n ≤ ∑ j, e j := by
  classical
  let K : ℕ := ∑ j, ∑ β ∈ (F j).support, (coeff β (F j)).natAbs
  apply box_counting_bound (polyMap F) hinj e K
  intro N h1 a ha j
  have hb := eval_abs_le (F j) h1 a ha
  have hKj : (∑ β ∈ (F j).support, |coeff β (F j)|) ≤ (K : ℤ) := by
    have h0 : (∑ β ∈ (F j).support, (coeff β (F j)).natAbs) ≤ K :=
      Finset.single_le_sum (f := fun j => ∑ β ∈ (F j).support, (coeff β (F j)).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h0' : ((∑ β ∈ (F j).support, (coeff β (F j)).natAbs : ℕ) : ℤ) ≤ (K : ℤ) := by
      exact_mod_cast h0
    simpa only [Nat.cast_sum, Int.natCast_natAbs] using h0'
  calc |polyMap F a j|
      = |eval (fun i => (a i : ℤ)) (F j)| := rfl
    _ ≤ (∑ β ∈ (F j).support, |coeff β (F j)|) * (N : ℤ) ^ (F j).totalDegree := hb
    _ ≤ (K : ℤ) * (N : ℤ) ^ (F j).totalDegree :=
        mul_le_mul_of_nonneg_right hKj (by positivity)
    _ ≤ (K : ℤ) * (N : ℤ) ^ e j :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by exact_mod_cast h1) (he j)) (by positivity)

/-- Uniform-degree corollary: all coordinates of degree ≤ d ⟹ n ≤ |ι| · d. -/
theorem injective_polyMap_uniformDegree_bound {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → MvPolynomial (Fin n) ℤ) (d : ℕ) (hd : ∀ j, (F j).totalDegree ≤ d)
    (hinj : Function.Injective (polyMap F)) :
    n ≤ Fintype.card ι * d := by
  have h := injective_polyMap_dimension_le_degreeSum F (fun _ => d) hd hinj
  simpa [Finset.sum_const, Finset.card_univ] using h

/-- Standard-box special case, one coordinate (m = 1): an injective polynomial ℕ^n → ℤ of degree
    ≤ d forces n ≤ d. -/
theorem injective_poly_dimension_le_degree {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (d : ℕ)
    (hd : p.totalDegree ≤ d)
    (hinj : Function.Injective (fun a : Fin n → ℕ => eval (fun i => (a i : ℤ)) p)) :
    n ≤ d := by
  have h := injective_polyMap_uniformDegree_bound (ι := Fin 1) (fun _ => p) d (fun _ => hd) ?_
  · simpa using h
  · intro a a' h
    apply hinj
    exact congrFun h 0

end DiophCompression

#print axioms DiophCompression.injective_polyMap_dimension_le_degreeSum
#print axioms DiophCompression.injective_polyMap_uniformDegree_bound
#print axioms DiophCompression.injective_poly_dimension_le_degree
