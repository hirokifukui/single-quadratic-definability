/-
  SlopeStructure.lean — s59.  GPT R47 Packets D2, D3 (GATE29): stable sub-results around the common slope.

  * `padZero`, `commonSlope_padZero_iff` [P], `singleQuadratic_padZero_iff_of_TCER` [C] (D2) — appending one zero output
    keeps a function in the class iff it has a common slope (every m; no SE₂ hypothesis on f).
  * `sqPadFn_eq_padZero`, `sqFn_not_commonSlope`, `sqPadFn_not_singleQuadratic_of_padding` — the R47 example a ↦ (a², 0)
    as an instance of the padding criterion.
  * `commonSlope_comp_data`, `commonSlope_comp` [P] (D2) — common slopes compose (modulus M N, slope C B).  This is NOT
    closure of SE₂ under composition.
  * `slopeUnknownQuad`, `slopeEncoder_eval_scale`, `slopeUnknownQuad_nonneg`, `slopeUnknownQuad_eq_zero`,
    `commonSlope_posDef_presentation` [P] (D3) — the quadratic part of the R47 encoder in its unknowns is positive
    definite; a common-slope function has a positive-definite, unique-witness presentation (that presentation only).

  Statements frozen before proof (`~/lean/s59_evidence/freeze/H3_FREEZE_s59.lean` 5fbf651e, ruling of Dr. Fukui
  2026-09-27 15:56).  TCER only in `singleQuadratic_padZero_iff_of_TCER` and its corollary, as an explicit hypothesis.
-/
import ResearchUpgrade.ScalarClassification

namespace DiophCompression.ResearchUpgrade

open Matrix MvPolynomial

def padZero {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : (Fin n → ℤ) → (Fin (m + 1) → ℤ) :=
  fun a => Fin.snoc (α := fun _ => ℤ) (f a) 0

theorem commonSlope_padZero_iff {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) :
    CommonSlopeIntNF (padZero f) ↔ CommonSlopeIntNF f := by
  constructor
  · rintro ⟨M, B, hM, h⟩
    refine ⟨M, Matrix.of fun j i => B (Fin.castSucc j) i, hM, fun a t => funext fun j => ?_⟩
    have hj := congrFun (h a t) (Fin.castSucc j)
    simp only [padZero, Fin.snoc_castSucc, Pi.add_apply] at hj
    rw [hj]
    simp [Matrix.mulVec, dotProduct]
  · rintro ⟨M, B, hM, h⟩
    refine ⟨M, Matrix.of fun j i => Fin.snoc (α := fun _ => ℤ) (fun j' => B j' i) 0 j, hM,
      fun a t => funext fun j => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [padZero, Matrix.mulVec, dotProduct]
    · simp only [padZero, Fin.snoc_castSucc, Pi.add_apply]
      rw [h a t]
      simp [Matrix.mulVec, dotProduct]

theorem singleQuadratic_padZero_iff_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      DiophCompression.SingleQuadraticDefinableFunctionZZ (padZero f) ↔ CommonSlopeIntNF f := by
  intro n m f
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨fun _ => commonSlopeIntNF_of_zero_outputs f,
      fun h => singleQuadratic_of_commonSlope ((commonSlope_padZero_iff f).mpr h)⟩
  · rw [singleQuadratic_iff_commonSlope_of_TCER hT n (m + 1) (padZero f) (by omega)]
    exact commonSlope_padZero_iff f

theorem sqPadFn_eq_padZero : sqPadFn = padZero sqFn := by
  funext a j
  fin_cases j
  · show a 0 ^ 2 = Fin.snoc (α := fun _ => ℤ) (sqFn a) 0 (Fin.castSucc 0)
    rw [Fin.snoc_castSucc]; rfl
  · show (0 : ℤ) = Fin.snoc (α := fun _ => ℤ) (sqFn a) 0 (Fin.last 1)
    rw [Fin.snoc_last]

theorem sqFn_not_commonSlope : ¬ CommonSlopeIntNF sqFn := by
  rintro ⟨M, B, hM, h⟩
  have h0 := congrFun (h (fun _ => 0) (fun _ => 1)) 0
  have h1 := congrFun (h (fun _ => 1) (fun _ => 1)) 0
  simp only [sqFn, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Fin.sum_univ_one] at h0 h1
  have hM' : (1 : ℤ) ≤ M := by exact_mod_cast hM
  nlinarith [h0, h1]

theorem sqPadFn_not_singleQuadratic_of_padding (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ¬ DiophCompression.SingleQuadraticDefinableFunctionZZ sqPadFn := by
  rw [sqPadFn_eq_padZero, singleQuadratic_padZero_iff_of_TCER hT]
  exact sqFn_not_commonSlope

theorem commonSlope_comp_data {n m k : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} {g : (Fin m → ℤ) → (Fin k → ℤ)}
    (M N : ℕ) (B : Matrix (Fin m) (Fin n) ℤ) (C : Matrix (Fin k) (Fin m) ℤ)
    (hf : ∀ a t : Fin n → ℤ, f (a + (M : ℤ) • t) = f a + B *ᵥ t)
    (hg : ∀ y s : Fin m → ℤ, g (y + (N : ℤ) • s) = g y + C *ᵥ s) :
    ∀ a t : Fin n → ℤ, g (f (a + ((M * N : ℕ) : ℤ) • t)) = g (f a) + (C * B) *ᵥ t := by
  intro a t
  rw [show ((M * N : ℕ) : ℤ) • t = (M : ℤ) • ((N : ℤ) • t) by rw [smul_smul, Nat.cast_mul], hf,
    Matrix.mulVec_smul, hg, Matrix.mulVec_mulVec]

theorem commonSlope_comp {n m k : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} {g : (Fin m → ℤ) → (Fin k → ℤ)}
    (hf : CommonSlopeIntNF f) (hg : CommonSlopeIntNF g) : CommonSlopeIntNF (g ∘ f) := by
  obtain ⟨M, B, hM, hf⟩ := hf
  obtain ⟨N, C, hN, hg⟩ := hg
  exact ⟨M * N, C * B, Nat.one_le_iff_ne_zero.mpr (by positivity),
    fun a t => commonSlope_comp_data M N B C hf hg a t⟩

def slopeUnknownQuad {R : Type*} [CommRing R] {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) (b : Fin m → R) (u : Fin n → R) (e : (Fin n → Fin M) → R) : R :=
  (∑ ρ, e ρ) ^ 2 + ∑ ρ, e ρ ^ 2 + ∑ i, ((M : R) * u i + ∑ ρ, ((((ρ i : ℕ) : ℤ)) : R) * e ρ) ^ 2
    + ∑ j, ((M : R) * b j - ∑ ρ, ((((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) : ℤ) : R) * e ρ) ^ 2

theorem slopeEncoder_eval_scale {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin n → ℤ)
    (e : (Fin n → Fin M) → ℤ) (t : ℤ) :
    MvPolynomial.eval (Sum.elim (pairVec a (t • b)) (Sum.elim (t • u) (t • e))) (slopeEncoder M B β)
      = t ^ 2 * slopeUnknownQuad M B β b u e
        + t * (-3 * ∑ ρ, e ρ - 2 * ∑ i, a i * ((M : ℤ) * u i + ∑ ρ, ((ρ i : ℕ) : ℤ) * e ρ)
          - 2 * ∑ j, (∑ i, B j i * a i)
              * ((M : ℤ) * b j - ∑ ρ, ((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) * e ρ))
        + MvPolynomial.eval (Sum.elim (pairVec a 0) (Sum.elim 0 0)) (slopeEncoder M B β) := by
  rw [slopeEncoder_eval, slopeEncoder_eval]
  simp only [slopeUnknownQuad, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Int.cast_id, Int.cast_natCast]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, sub_zero, zero_sub, neg_sq]
  have h1 : ∑ x, t * e x = t * ∑ ρ, e ρ := (Finset.mul_sum _ _ _).symm
  have h2 : ∑ x, t * e x * (t * e x - 1) = t ^ 2 * ∑ ρ, e ρ ^ 2 - t * ∑ ρ, e ρ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  have h3 : ∑ x, (a x - (M : ℤ) * (t * u x) - ∑ x_1, ((x_1 x : ℕ) : ℤ) * (t * e x_1)) ^ 2
      = t ^ 2 * ∑ x, ((M : ℤ) * u x + ∑ x_1, ((x_1 x : ℕ) : ℤ) * e x_1) ^ 2
        - t * (2 * ∑ i, a i * ((M : ℤ) * u i + ∑ ρ, ((ρ i : ℕ) : ℤ) * e ρ)) + ∑ x, a x ^ 2 := by
    have hterm : ∀ i, (a i - (M : ℤ) * (t * u i) - ∑ x_1, ((x_1 i : ℕ) : ℤ) * (t * e x_1)) ^ 2
        = t ^ 2 * ((M : ℤ) * u i + ∑ x_1, ((x_1 i : ℕ) : ℤ) * e x_1) ^ 2
          - t * (2 * (a i * ((M : ℤ) * u i + ∑ ρ, ((ρ i : ℕ) : ℤ) * e ρ))) + a i ^ 2 := by
      intro i
      have hs : ∑ x_1, ((x_1 i : ℕ) : ℤ) * (t * e x_1) = t * ∑ x_1, ((x_1 i : ℕ) : ℤ) * e x_1 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      rw [hs]; ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.mul_sum]
  have h4 : ∑ x, ((M : ℤ) * (t * b x) - ∑ i, B x i * a i
        - ∑ x_1, ((M : ℤ) * β x_1 x - ∑ i, B x i * ((x_1 i : ℕ) : ℤ)) * (t * e x_1)) ^ 2
      = t ^ 2 * ∑ x, ((M : ℤ) * b x - ∑ x_1, ((M : ℤ) * β x_1 x - ∑ i, B x i * ((x_1 i : ℕ) : ℤ)) * e x_1) ^ 2
        - t * (2 * ∑ j, (∑ i, B j i * a i)
            * ((M : ℤ) * b j - ∑ ρ, ((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) * e ρ))
        + ∑ x, (∑ i, B x i * a i) ^ 2 := by
    have hterm : ∀ j, ((M : ℤ) * (t * b j) - ∑ i, B j i * a i
          - ∑ x_1, ((M : ℤ) * β x_1 j - ∑ i, B j i * ((x_1 i : ℕ) : ℤ)) * (t * e x_1)) ^ 2
        = t ^ 2 * ((M : ℤ) * b j - ∑ x_1, ((M : ℤ) * β x_1 j - ∑ i, B j i * ((x_1 i : ℕ) : ℤ)) * e x_1) ^ 2
          - t * (2 * ((∑ i, B j i * a i)
            * ((M : ℤ) * b j - ∑ ρ, ((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) * e ρ)))
          + (∑ i, B j i * a i) ^ 2 := by
      intro j
      have hs : ∑ x_1, ((M : ℤ) * β x_1 j - ∑ i, B j i * ((x_1 i : ℕ) : ℤ)) * (t * e x_1)
          = t * ∑ x_1, ((M : ℤ) * β x_1 j - ∑ i, B j i * ((x_1 i : ℕ) : ℤ)) * e x_1 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      rw [hs]; ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.mul_sum]
  rw [h1, h2, h3, h4]
  ring

theorem slopeUnknownQuad_nonneg {n m : ℕ} (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) (b : Fin m → ℚ) (u : Fin n → ℚ) (e : (Fin n → Fin M) → ℚ) :
    0 ≤ slopeUnknownQuad M B β b u e := by
  unfold slopeUnknownQuad
  have hA : 0 ≤ (∑ ρ, e ρ) ^ 2 := sq_nonneg _
  have hB : 0 ≤ ∑ ρ, e ρ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hC : 0 ≤ ∑ i, ((M : ℚ) * u i + ∑ ρ, ((((ρ i : ℕ) : ℤ)) : ℚ) * e ρ) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 ≤ ∑ j, ((M : ℚ) * b j
      - ∑ ρ, ((((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) : ℤ) : ℚ) * e ρ) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

theorem slopeUnknownQuad_eq_zero {n m : ℕ} (M : ℕ) (hM : 1 ≤ M) (B : Matrix (Fin m) (Fin n) ℤ)
    (β : (Fin n → Fin M) → Fin m → ℤ) (b : Fin m → ℚ) (u : Fin n → ℚ) (e : (Fin n → Fin M) → ℚ)
    (h : slopeUnknownQuad M B β b u e = 0) : b = 0 ∧ u = 0 ∧ e = 0 := by
  unfold slopeUnknownQuad at h
  have hMQ : (0 : ℚ) < M := by exact_mod_cast hM
  have hA : 0 ≤ (∑ ρ, e ρ) ^ 2 := sq_nonneg _
  have hB : 0 ≤ ∑ ρ, e ρ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hC : 0 ≤ ∑ i, ((M : ℚ) * u i + ∑ ρ, ((((ρ i : ℕ) : ℤ)) : ℚ) * e ρ) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 ≤ ∑ j, ((M : ℚ) * b j
      - ∑ ρ, ((((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) : ℤ) : ℚ) * e ρ) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB0 : ∑ ρ, e ρ ^ 2 = 0 := by linarith
  have hC0 : ∑ i, ((M : ℚ) * u i + ∑ ρ, ((((ρ i : ℕ) : ℤ)) : ℚ) * e ρ) ^ 2 = 0 := by linarith
  have hD0 : ∑ j, ((M : ℚ) * b j
      - ∑ ρ, ((((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) : ℤ) : ℚ) * e ρ) ^ 2 = 0 := by linarith
  have he : e = 0 := funext fun ρ => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hB0 ρ (Finset.mem_univ _)
    exact (pow_eq_zero_iff two_ne_zero).mp this
  refine ⟨funext fun j => ?_, funext fun i => ?_, he⟩
  · have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hD0 j (Finset.mem_univ _)
    have hsq := (pow_eq_zero_iff two_ne_zero).mp hj
    have hz : ∑ ρ, ((((M : ℤ) * β ρ j - ∑ i, B j i * ((ρ i : ℕ) : ℤ)) : ℤ) : ℚ) * e ρ = 0 := by
      rw [he]; simp
    rw [hz, sub_zero] at hsq
    exact (mul_eq_zero.mp hsq).resolve_left (ne_of_gt hMQ)
  · have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hC0 i (Finset.mem_univ _)
    have hsq := (pow_eq_zero_iff two_ne_zero).mp hi
    have hz : ∑ ρ, ((((ρ i : ℕ) : ℤ)) : ℚ) * e ρ = 0 := by rw [he]; simp
    rw [hz, add_zero] at hsq
    exact (mul_eq_zero.mp hsq).resolve_left (ne_of_gt hMQ)

theorem commonSlope_posDef_presentation {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (h : CommonSlopeIntNF f) :
    ∃ (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ) (β : (Fin n → Fin M) → Fin m → ℤ), 1 ≤ M ∧
      (∀ (a : Fin n → ℤ) (b : Fin m → ℤ), b = f a ↔
        ∃ (u : Fin n → ℤ) (e : (Fin n → Fin M) → ℤ),
          MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u e)) (slopeEncoder M B β) = 0) ∧
      (∀ (a : Fin n → ℤ) (b : Fin m → ℤ) (u u' : Fin n → ℤ) (e e' : (Fin n → Fin M) → ℤ),
        MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u e)) (slopeEncoder M B β) = 0 →
        MvPolynomial.eval (Sum.elim (pairVec a b) (Sum.elim u' e')) (slopeEncoder M B β) = 0 → u = u' ∧ e = e') ∧
      (∀ (b : Fin m → ℚ) (u : Fin n → ℚ) (e : (Fin n → Fin M) → ℚ),
        slopeUnknownQuad M B β b u e = 0 → b = 0 ∧ u = 0 ∧ e = 0) := by
  obtain ⟨M, B, hM, hcs⟩ := h
  refine ⟨M, B, fun ρ => f fun i => ((ρ i : ℕ) : ℤ), hM, slopeEncoder_graph_iff M B hM hcs,
    fun a b u u' e e' h1 h2 => slopeEncoder_witness_unique M B _ hM h1 h2,
    fun b u e hq => slopeUnknownQuad_eq_zero M hM B _ b u e hq⟩

end DiophCompression.ResearchUpgrade
