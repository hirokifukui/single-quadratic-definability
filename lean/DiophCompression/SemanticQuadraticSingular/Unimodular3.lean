/-
  DiophCompression/SemanticQuadraticSingular/Unimodular3.lean — r10 必須B (GPT r09 §4.3, §8): GL_r(ℤ) transfer of
  DichotomyM, primitive kernel vectors and unimodular completion in ℤ³, congruent block form (U^T G U, NOT Smith
  normal form). Statements frozen in `Singular_STATEMENTS.lean` (md5 281708fb). Session 10, 2026-08-27, Claude Code.
-/
import DiophCompression.SemanticQuadraticSingular.DefsSingular
import DiophCompression.SemanticQuadraticTwoWitness.RankOneNormalForm

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticTwoWitness
  DiophCompression.SemanticQuadraticGeneral

/-- Substitution identity: applying `u ↦ U *ᵥ u` to `fqM` with original coefficients equals `fqM` with the
    transformed coefficients (B ↦ Uᵀ B, C ↦ Uᵀ C U, m ↦ Uᵀ m). -/
theorem fqM_mulVec {r : ℕ} (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ) (m : Fin r → ℤ)
    (q : ℤ) (U : Matrix (Fin r) (Fin r) ℤ) (c : ℤ) (u : Fin r → ℤ) :
    fqM A B C l m q c (U *ᵥ u) = fqM A (Uᵀ *ᵥ B) (Uᵀ * C * U) l (Uᵀ *ᵥ m) q c u := by
  unfold fqM witnessQuad
  have hB : B ⬝ᵥ (U *ᵥ u) = (Uᵀ *ᵥ B) ⬝ᵥ u := by
    rw [dotProduct_mulVec, mulVec_transpose]
  have hm : m ⬝ᵥ (U *ᵥ u) = (Uᵀ *ᵥ m) ⬝ᵥ u := by
    rw [dotProduct_mulVec, mulVec_transpose]
  have e1 : (Uᵀ * C * U) *ᵥ u = Uᵀ *ᵥ (C *ᵥ (U *ᵥ u)) := by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have e2 : u ⬝ᵥ (Uᵀ *ᵥ (C *ᵥ (U *ᵥ u))) = (U *ᵥ u) ⬝ᵥ (C *ᵥ (U *ᵥ u)) := by
    rw [dotProduct_mulVec, vecMul_transpose]
  have hC : (U *ᵥ u) ⬝ᵥ (C *ᵥ (U *ᵥ u)) = u ⬝ᵥ ((Uᵀ * C * U) *ᵥ u) := by
    rw [e1, e2]
  rw [hB, hm, hC]

/-- Conjugation commutes with the Gram operator: `witnessGram (Uᵀ C U) = Uᵀ (witnessGram C) U`. -/
theorem witnessGram_conj {r : ℕ} (C U : Matrix (Fin r) (Fin r) ℤ) :
    witnessGram (Uᵀ * C * U) = Uᵀ * witnessGram C * U := by
  unfold witnessGram
  rw [transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc, Matrix.mul_assoc]

/-- A unimodular witness change (det U = ±1) preserves the fiber set (with transformed coefficients). -/
theorem witness_change_preserves_fiberSet {r : ℕ} (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (l : ℤ) (m : Fin r → ℤ) (q : ℤ) (U : Matrix (Fin r) (Fin r) ℤ) (hU : U.det = 1 ∨ U.det = -1) :
    fiberSetM A B C l m q = fiberSetM A (Uᵀ *ᵥ B) (Uᵀ * C * U) l (Uᵀ *ᵥ m) q := by
  set V : Matrix (Fin r) (Fin r) ℤ := U.det • U.adjugate with hV
  have hdd : U.det * U.det = 1 := by rcases hU with h | h <;> rw [h] <;> ring
  have hUV : U * V = 1 := by
    rw [hV, Matrix.mul_smul, mul_adjugate, smul_smul, hdd, one_smul]
  ext c
  simp only [fiberSetM, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨V *ᵥ u, ?_⟩
    rw [← fqM_mulVec, mulVec_mulVec, hUV, one_mulVec]
    exact hu
  · rintro ⟨u, hu⟩
    refine ⟨U *ᵥ u, ?_⟩
    rw [fqM_mulVec]
    exact hu

/-- `∑ᵢ |(Uᵀ m)ᵢ| ≤ (∑ₐᵦ |Uₐᵦ|)·∑ⱼ|mⱼ|`. -/
private lemma aux_sum_mulVec_bound {r : ℕ} (U : Matrix (Fin r) (Fin r) ℤ) (m : Fin r → ℤ) :
    ∑ i, |(Uᵀ *ᵥ m) i| ≤ (∑ a, ∑ b, |U a b|) * ∑ j, |m j| := by
  have h1 : ∀ i, |(Uᵀ *ᵥ m) i| ≤ ∑ j, |U j i| * |m j| := by
    intro i
    have he : (Uᵀ *ᵥ m) i = ∑ j, U j i * m j := by
      simp [Matrix.mulVec, Matrix.transpose_apply, dotProduct]
    rw [he]
    calc |∑ j, U j i * m j| ≤ ∑ j, |U j i * m j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |U j i| * |m j| := by simp_rw [abs_mul]
  calc ∑ i, |(Uᵀ *ᵥ m) i|
      ≤ ∑ i, ∑ j, |U j i| * |m j| := Finset.sum_le_sum (fun i _ => h1 i)
    _ = ∑ j, ∑ i, |U j i| * |m j| := Finset.sum_comm
    _ = ∑ j, (∑ i, |U j i|) * |m j| := by simp_rw [Finset.sum_mul]
    _ ≤ ∑ j, (∑ a, ∑ b, |U a b|) * |m j| := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact Finset.single_le_sum (f := fun a => ∑ b, |U a b|)
          (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg _)) (Finset.mem_univ j)
    _ = (∑ a, ∑ b, |U a b|) * ∑ j, |m j| := by rw [← Finset.mul_sum]

/-- Monotonicity of `fboundM` under the induced change of the linear part `m ↦ Uᵀ m`. -/
private lemma aux_fboundM_mono {r : ℕ} (K : ℕ) (U : Matrix (Fin r) (Fin r) ℤ) (l : ℤ) (m : Fin r → ℤ)
    (q : ℤ) :
    fboundM K l (Uᵀ *ᵥ m) q ≤ fboundM (K * (1 + ∑ i, ∑ j, (U i j).natAbs) ^ 2) l m q := by
  unfold fboundM
  set S : ℤ := ∑ a, ∑ b, |U a b| with hS
  set T : ℤ := ∑ j, |m j| with hT
  have hS0 : (0:ℤ) ≤ S := Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg _))
  have hT0 : (0:ℤ) ≤ T := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hScast : ((∑ i, ∑ j, (U i j).natAbs : ℕ) : ℤ) = S := by
    rw [hS]; push_cast; rfl
  have hcast : ((K * (1 + ∑ i, ∑ j, (U i j).natAbs) ^ 2 : ℕ) : ℤ) = (K:ℤ) * (1 + S) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, hScast]
  rw [hcast]
  set X : ℤ := 1 + |l| + ∑ i, |(Uᵀ *ᵥ m) i| with hX
  have hsum : (∑ i, |(Uᵀ *ᵥ m) i|) ≤ S * T := by rw [hS, hT]; exact aux_sum_mulVec_bound U m
  have hK0 : (0:ℤ) ≤ (K:ℤ) := by positivity
  have hX0 : (0:ℤ) ≤ X := by rw [hX]; positivity
  set Y : ℤ := 1 + |l| + T with hY
  have hY0 : (0:ℤ) ≤ Y := by rw [hY]; positivity
  have hM0 : (0:ℤ) ≤ 1 + S := by linarith
  have hMY0 : (0:ℤ) ≤ (1 + S) * Y := mul_nonneg hM0 hY0
  have hXMY : X ≤ (1 + S) * Y := by
    rw [hX, hY]; nlinarith [hsum, hS0, hT0, abs_nonneg l]
  have hXsq : X ^ 2 ≤ (1 + S) ^ 2 * Y ^ 2 := by
    nlinarith [mul_le_mul hXMY hXMY hX0 hMY0]
  have hM1 : (1:ℤ) ≤ (1 + S) ^ 2 := by nlinarith [hS0]
  have hqnn : (0:ℤ) ≤ |q| := abs_nonneg q
  have hInner : X ^ 2 + |q| ≤ (1 + S) ^ 2 * (Y ^ 2 + |q|) := by
    nlinarith [hXsq, mul_nonneg (by linarith [hM1] : (0:ℤ) ≤ (1 + S) ^ 2 - 1) hqnn]
  calc (K:ℤ) * (X ^ 2 + |q|) ≤ (K:ℤ) * ((1 + S) ^ 2 * (Y ^ 2 + |q|)) :=
        mul_le_mul_of_nonneg_left hInner hK0
    _ = (K:ℤ) * (1 + S) ^ 2 * (Y ^ 2 + |q|) := by ring

/-- If the transformed data satisfies `DichotomyM`, so does the original data. -/
theorem dichotomyM_of_change {r : ℕ} (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (U : Matrix (Fin r) (Fin r) ℤ) (hU : U.det = 1 ∨ U.det = -1)
    (h : DichotomyM A (Uᵀ *ᵥ B) (Uᵀ * C * U)) : DichotomyM A B C := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K * (1 + ∑ i, ∑ j, (U i j).natAbs) ^ 2, ?_⟩
  intro l m q
  have hEq : fiberSetM A B C l m q = fiberSetM A (Uᵀ *ᵥ B) (Uᵀ * C * U) l (Uᵀ *ᵥ m) q :=
    witness_change_preserves_fiberSet A B C l m q U hU
  rcases hK l (Uᵀ *ᵥ m) q with hInf | hBd
  · left; rw [hEq]; exact hInf
  · right; intro c hc
    rw [hEq] at hc
    exact le_trans (hBd c hc) (aux_fboundM_mono K U l m q)

/-- The integral radical is saturated: if `d • v` is in the radical for `d ≠ 0`, so is `v`. -/
theorem kernel_is_saturated (G : Matrix (Fin 3) (Fin 3) ℤ) (d : ℤ) (hd : d ≠ 0) (v : Fin 3 → ℤ)
    (h : d • v ∈ IntegralRadical G) : v ∈ IntegralRadical G := by
  unfold IntegralRadical at h ⊢
  simp only [Set.mem_setOf_eq] at h ⊢
  rw [mulVec_smul] at h
  exact (smul_eq_zero.mp h).resolve_left hd

/-- A singular integer 3×3 matrix has a primitive integral kernel vector. -/
theorem primitive_kernel_vector_of_det_zero (G : Matrix (Fin 3) (Fin 3) ℤ) (hG : G.det = 0) :
    ∃ v : Fin 3 → ℤ, IsPrimitiveVector v ∧ v ∈ IntegralRadical G := by
  obtain ⟨v, hv0, hvk⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hG
  set g : ℤ := Finset.univ.gcd v with hg
  have hgne : g ≠ 0 := by
    rw [hg]; intro hzero
    apply hv0; funext i
    exact Finset.gcd_eq_zero_iff.mp hzero i (Finset.mem_univ i)
  have hg0 : 0 ≤ g := Finset.Int.finsetGcd_nonneg
  set w : Fin 3 → ℤ := fun i => v i / g with hw
  have hdvd : ∀ i, g ∣ v i := fun i => Finset.gcd_dvd (Finset.mem_univ i)
  have hvw : v = g • w := by
    funext i
    simp only [hw, Pi.smul_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdvd i)).symm
  have hprim : IsPrimitiveVector w := by
    unfold IsPrimitiveVector
    have hfun : (v : Fin 3 → ℤ) = fun x => g * w x := by
      funext i; simp only [hw]; exact (Int.mul_ediv_cancel' (hdvd i)).symm
    have hgw : Finset.univ.gcd v = g * Finset.univ.gcd w := by
      rw [hfun, Finset.gcd_mul_left, Int.normalize_of_nonneg hg0]
    have h1 : g * Finset.univ.gcd w = g * 1 := by rw [← hgw, ← hg, mul_one]
    exact mul_left_cancel₀ hgne h1
  refine ⟨w, hprim, ?_⟩
  apply kernel_is_saturated G g hgne w
  rw [← hvw]
  unfold IntegralRadical; simp only [Set.mem_setOf_eq]; exact hvk

/-- A primitive vector in ℤ³ is the last column of a unimodular matrix. -/
theorem primitive_vector_unimodular_completion (v : Fin 3 → ℤ) (hv : IsPrimitiveVector v) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℤ, U.det = 1 ∧ ∀ i, U i 2 = v i := by
  set a := v 0 with ha_def
  set b := v 1 with hb_def
  set c := v 2 with hc_def
  unfold IsPrimitiveVector at hv
  by_cases hdn : Int.gcd a b = 0
  · -- a = b = 0, so c = ±1
    rw [Int.gcd_eq_zero_iff] at hdn
    obtain ⟨ha0, hb0⟩ := hdn
    have e0 : v 0 = 0 := by rw [← ha_def]; exact ha0
    have e1 : v 1 = 0 := by rw [← hb_def]; exact hb0
    have hcdvd : c ∣ (1 : ℤ) := by
      rw [← hv]
      apply Finset.dvd_gcd
      intro i _
      fin_cases i
      · show c ∣ a; rw [ha0]; exact dvd_zero c
      · show c ∣ b; rw [hb0]; exact dvd_zero c
      · show c ∣ c; exact dvd_rfl
    have hc1 : c = 1 ∨ c = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one hcdvd)
    refine ⟨!![1, 0, 0; 0, c, 0; 0, 0, c], ?_, ?_⟩
    · rcases hc1 with h | h <;> rw [h] <;> simp [Matrix.det_fin_three]
    · intro i
      fin_cases i <;> simp [e0, e1, hc_def]
  · -- d = gcd(a,b) ≠ 0
    set d : ℤ := (Int.gcd a b : ℤ) with hd_def
    have hd : d ≠ 0 := by rw [hd_def]; exact_mod_cast hdn
    have hda : d ∣ a := Int.gcd_dvd_left a b
    have hdb : d ∣ b := Int.gcd_dvd_right a b
    set a' : ℤ := a / d with ha'_def
    set b' : ℤ := b / d with hb'_def
    have haa' : a = d * a' := (Int.mul_ediv_cancel' hda).symm
    have hbb' : b = d * b' := (Int.mul_ediv_cancel' hdb).symm
    set x : ℤ := Int.gcdA a b with hx_def
    set y : ℤ := Int.gcdB a b with hy_def
    have hbez : d = a * x + b * y := Int.gcd_eq_gcd_ab a b
    have hkey : d * (a' * x + b' * y) = d := by
      have hexp : d * (a' * x + b' * y) = (d * a') * x + (d * b') * y := by ring
      rw [hexp, ← haa', ← hbb', ← hbez]
    have hab : a' * x + b' * y = 1 := by
      apply mul_left_cancel₀ hd
      rw [hkey, mul_one]
    -- gcd(d, c) = 1
    set e : ℤ := (Int.gcd d c : ℤ) with he_def
    have he_d : e ∣ d := Int.gcd_dvd_left d c
    have he_c : e ∣ c := Int.gcd_dvd_right d c
    have he1 : e = 1 := by
      apply Int.eq_one_of_dvd_one (by rw [he_def]; exact_mod_cast Nat.zero_le _)
      rw [← hv]
      apply Finset.dvd_gcd
      intro i _
      fin_cases i
      · show e ∣ a; exact dvd_trans he_d hda
      · show e ∣ b; exact dvd_trans he_d hdb
      · show e ∣ c; exact he_c
    set z : ℤ := Int.gcdA d c with hz_def
    set w : ℤ := Int.gcdB d c with hw_def
    have hdc : d * z + c * w = 1 := by
      rw [← he1, he_def]; exact (Int.gcd_eq_gcd_ab d c).symm
    refine ⟨!![-y, -w * a', a; x, -w * b', b; 0, z, c], ?_, ?_⟩
    · rw [Matrix.det_fin_three]
      simp only [Matrix.of_apply]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      rw [haa', hbb']
      linear_combination (a' * x + b' * y) * hdc + hab
    · intro i
      fin_cases i <;> simp [ha_def, hb_def, hc_def]

/-- Any symmetric singular integer 3×3 Gram matrix is congruent (via a unimodular `U`) to one whose
    last row and column vanish. -/
theorem congruent_block_form_rank_two (G : Matrix (Fin 3) (Fin 3) ℤ) (hs : Gᵀ = G) (hG : G.det = 0) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℤ, U.det = 1 ∧ (∀ i, (Uᵀ * G * U) i 2 = 0) ∧ (∀ j, (Uᵀ * G * U) 2 j = 0) := by
  obtain ⟨v, hprim, hker⟩ := primitive_kernel_vector_of_det_zero G hG
  obtain ⟨U, hdet, hcol⟩ := primitive_vector_unimodular_completion v hprim
  have hkv : G *ᵥ v = 0 := hker
  have hUe : U *ᵥ Pi.single (2 : Fin 3) (1 : ℤ) = v := by
    funext i; have := hcol i; simpa [Matrix.mulVec_single] using this
  have hMe : (Uᵀ * G * U) *ᵥ Pi.single (2 : Fin 3) (1 : ℤ) = 0 := by
    rw [← mulVec_mulVec, hUe, ← mulVec_mulVec, hkv, mulVec_zero]
  have hcolz : ∀ i, (Uᵀ * G * U) i 2 = 0 := by
    intro i
    have h := congrFun hMe i
    simpa [Matrix.mulVec_single] using h
  have hsymm : (Uᵀ * G * U)ᵀ = Uᵀ * G * U := by
    rw [transpose_mul, transpose_mul, transpose_transpose, hs, Matrix.mul_assoc]
  refine ⟨U, hdet, hcolz, ?_⟩
  intro j
  have hrw : (Uᵀ * G * U) 2 j = (Uᵀ * G * U) j 2 := by
    conv_lhs => rw [← hsymm]
    rw [Matrix.transpose_apply]
  rw [hrw]; exact hcolz j

set_option maxHeartbeats 800000 in
/-- A symmetric singular integer 3×3 Gram matrix with vanishing adjugate (rank ≤ 1) is congruent (via a
    unimodular `U`) to one supported only at the top-left corner. -/
theorem congruent_block_form_rank_one (G : Matrix (Fin 3) (Fin 3) ℤ) (hs : Gᵀ = G) (hG : G.det = 0)
    (hadj : G.adjugate = 0) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℤ, (U.det = 1 ∨ U.det = -1) ∧
      ∀ i j, ¬ (i = 0 ∧ j = 0) → (Uᵀ * G * U) i j = 0 := by
  obtain ⟨U, hdet, hcolz, hrowz⟩ := congruent_block_form_rank_two G hs hG
  set G' : Matrix (Fin 3) (Fin 3) ℤ := Uᵀ * G * U with hG'
  have hsymm : G'ᵀ = G' := by
    rw [hG', transpose_mul, transpose_mul, transpose_transpose, hs, Matrix.mul_assoc]
  have hsym01 : G' 1 0 = G' 0 1 := by
    have := congrFun (congrFun hsymm 0) 1
    rwa [Matrix.transpose_apply] at this
  obtain ⟨a, ha_def⟩ : ∃ a : ℤ, a = G' 0 0 := ⟨_, rfl⟩
  obtain ⟨e, he_def⟩ : ∃ e : ℤ, e = G' 0 1 := ⟨_, rfl⟩
  obtain ⟨f, hf_def⟩ : ∃ f : ℤ, f = G' 1 1 := ⟨_, rfl⟩
  have hG'eq : G' = !![a, e, 0; e, f, 0; 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply]
    · exact ha_def.symm
    · exact he_def.symm
    · exact hcolz 0
    · exact hsym01.trans he_def.symm
    · exact hf_def.symm
    · exact hcolz 1
    · exact hrowz 0
    · exact hrowz 1
    · exact hrowz 2
  have hadjG' : G'.adjugate = 0 := by
    rw [hG', Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hadj]; simp
  have hdisc0 : a * f - e * e = 0 := by
    have h1 : (G'.adjugate) 2 2 = 0 := by rw [hadjG']; rfl
    rw [Matrix.adjugate_fin_three] at h1
    simp only [Matrix.of_apply, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at h1
    rw [hsym01, ← ha_def, ← he_def, ← hf_def] at h1
    linear_combination h1
  by_cases haef : a = 0 ∧ e = 0 ∧ f = 0
  · -- G' = 0
    obtain ⟨ha0, he0, hf0⟩ := haef
    have hz : G' = 0 := by
      rw [hG'eq, ha0, he0, hf0]; ext i j; fin_cases i <;> fin_cases j <;> simp
    exact ⟨U, Or.inl hdet, fun i j _ => by rw [← hG', hz, Matrix.zero_apply]⟩
  · -- rank exactly one: use rank_one_normal_form
    have hdiscW : discW a (2 * e) f = 0 := by unfold discW; linear_combination -4 * hdisc0
    have hne : ¬ (a = 0 ∧ 2 * e = 0 ∧ f = 0) := by
      rintro ⟨ha0, he0, hf0⟩; exact haef ⟨ha0, by linarith, hf0⟩
    obtain ⟨p, r, s, t, k, hpm, hk, id1, id2, id3⟩ := rank_one_normal_form a (2 * e) f hdiscW hne
    set V : Matrix (Fin 3) (Fin 3) ℤ := !![p, r, 0; s, t, 0; 0, 0, 1] with hVdef
    have hdetV : V.det = p * t - r * s := by
      rw [hVdef, Matrix.det_fin_three]; simp only [Matrix.of_apply]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]; ring
    refine ⟨U * V, ?_, ?_⟩
    · rw [Matrix.det_mul, hdet, one_mul, hdetV]; exact hpm
    · intro i j hij
      have hconj : (U * V)ᵀ * G * (U * V) = Vᵀ * G' * V := by
        rw [hG', transpose_mul]; simp only [Matrix.mul_assoc]
      rw [hconj, hG'eq, hVdef]
      fin_cases i <;> fin_cases j <;>
        first
        | exact absurd ⟨rfl, rfl⟩ hij
        | (simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
           try (first
                | linear_combination id3
                | (have h2 : (2 : ℤ) * (a * p * r + e * (p * t + r * s) + f * s * t) = 0 := by
                     linear_combination id2
                   linarith [h2])
                | ring))

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.fqM_mulVec
#print axioms DiophCompression.SemanticQuadraticSingular.witnessGram_conj
#print axioms DiophCompression.SemanticQuadraticSingular.witness_change_preserves_fiberSet
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomyM_of_change
#print axioms DiophCompression.SemanticQuadraticSingular.kernel_is_saturated
#print axioms DiophCompression.SemanticQuadraticSingular.primitive_kernel_vector_of_det_zero
#print axioms DiophCompression.SemanticQuadraticSingular.primitive_vector_unimodular_completion
#print axioms DiophCompression.SemanticQuadraticSingular.congruent_block_form_rank_two
#print axioms DiophCompression.SemanticQuadraticSingular.congruent_block_form_rank_one
