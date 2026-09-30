/-
  BridgeGeneral.lean — r11 (GPT r10 必須D): the arbitrary-r degree-2 bridge from MvPolynomial to
  explicit matrix data. Statements frozen in BridgeGeneral_STATEMENTS.lean (md5 67507c7c) before
  proofs; fidelity gate: s11_bridge_general_gate.sage (16,000 identity checks r = 1..8, 0 bad,
  planted control 200/200). Part 1 (s11, claude.ai direct): the three defs and the general
  support classification — no per-r monomial enumeration.
-/
import DiophCompression.SemanticQuadraticMatrix.FullRankGeneric
import DiophCompression.SemanticQuadraticThreeWitness.Bridge3W

namespace DiophCompression.SemanticQuadraticMatrix

open Matrix MvPolynomial DiophCompression.SemanticQuadraticGeneral

variable {r : ℕ}

/-- GPT r10 必須D def 1 (name verbatim): the c² coefficient of H. -/
noncomputable def aOfGeneral (H : MvPolynomial (Fin (r + 1)) ℤ) : ℤ :=
  coeff (Finsupp.single 0 2) H

/-- GPT r10 必須D def 2 (name verbatim): the cross vector of c·u_k coefficients. -/
noncomputable def bVectorOfGeneral (H : MvPolynomial (Fin (r + 1)) ℤ) : Fin r → ℤ :=
  fun k => coeff (Finsupp.single 0 1 + Finsupp.single k.succ 1) H

/-- GPT r10 必須D def 3 (name verbatim): the upper-triangular witness coefficient matrix. -/
noncomputable def witnessMatrixOfGeneral (H : MvPolynomial (Fin (r + 1)) ℤ) :
    Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun i j =>
    if i = j then coeff (Finsupp.single i.succ 2) H
    else if (i : ℕ) < (j : ℕ) then coeff (Finsupp.single i.succ 1 + Finsupp.single j.succ 1) H
    else 0

/-- GPT r10 必須D theorem 1 (name verbatim, 合格条件): a degree-2 exponent vector is a square
or a product of two distinct variables — over an arbitrary index type, no enumeration. -/
theorem homogeneous_degree_two_support_classification {ι : Type*} (d : ι →₀ ℕ)
    (hd : d.sum (fun _ n => n) = 2) :
    (∃ i, d = Finsupp.single i 2) ∨
      ∃ i j, i ≠ j ∧ d = Finsupp.single i 1 + Finsupp.single j 1 := by
  have hne : d ≠ 0 := by
    rintro rfl
    simp at hd
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  have hi' : d i ≠ 0 := by simpa using hi
  have hdec : Finsupp.single i (d i) + d.erase i = d := Finsupp.single_add_erase i d
  have hsplit : d i + (d.erase i).sum (fun _ n => n) = 2 := by
    have h1 : (Finsupp.single i (d i) + d.erase i).sum (fun _ n => n) =
        (Finsupp.single i (d i)).sum (fun _ n => n) + (d.erase i).sum (fun _ n => n) :=
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
    have h2 : (Finsupp.single i (d i)).sum (fun _ n => n) = d i :=
      Finsupp.sum_single_index rfl
    rw [hdec] at h1
    rw [h2] at h1
    omega
  have hge : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr hi'
  have hle : d i ≤ 2 := by omega
  interval_cases h : d i
  · -- d i = 1: erase has sum 1
    have h1 : (d.erase i).sum (fun _ n => n) = 1 := by omega
    obtain ⟨j, hj⟩ := (Finsupp.sum_eq_one_iff _).mp h1
    have hij : i ≠ j := by
      rintro rfl
      have : (d.erase i) i = 0 := Finsupp.erase_same
      rw [hj] at this
      simp at this
    right
    refine ⟨i, j, hij, ?_⟩
    have hd2 := hdec
    rw [hj] at hd2
    exact hd2.symm
  · -- d i = 2: erase has sum 0, hence erase = 0
    have h0 : (d.erase i).sum (fun _ n => n) = 0 := by omega
    have hz : d.erase i = 0 := by
      ext a
      by_contra ha
      have hmem : a ∈ (d.erase i).support := Finsupp.mem_support_iff.mpr ha
      have hone : 1 ≤ (d.erase i) a := Nat.one_le_iff_ne_zero.mpr ha
      have hles : (d.erase i) a ≤ ∑ b ∈ (d.erase i).support, (d.erase i) b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le _) hmem
      have : (d.erase i).sum (fun _ n => n) = ∑ b ∈ (d.erase i).support, (d.erase i) b := rfl
      omega
    left
    refine ⟨i, ?_⟩
    have hd2 := hdec
    rw [hz, add_zero] at hd2
    exact hd2.symm

/-- Evaluate a single-variable monomial exponent: `∏ k, x k ^ (single i n) k = x i ^ n`. -/
private lemma prod_single (x : Fin (r + 1) → ℤ) (i : Fin (r + 1)) (n : ℕ) :
    ∏ k, x k ^ ((Finsupp.single i n) k) = x i ^ n := by
  rw [Finset.prod_eq_single i]
  · rw [Finsupp.single_eq_same]
  · intro j _ hj; rw [Finsupp.single_apply, if_neg (Ne.symm hj), pow_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Evaluate a two-variable degree-2 monomial exponent. -/
private lemma prod_cross (x : Fin (r + 1) → ℤ) (i j : Fin (r + 1)) :
    ∏ k, x k ^ ((Finsupp.single i 1 + Finsupp.single j 1 : Fin (r + 1) →₀ ℕ) k) = x i * x j := by
  simp_rw [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib, prod_single, pow_one]

/-- Support of a two-distinct-variable degree-2 monomial exponent. -/
private lemma cross_support (i j : Fin (r + 1)) (hij : i ≠ j) :
    (Finsupp.single i 1 + Finsupp.single j 1 : Fin (r + 1) →₀ ℕ).support = {i, j} := by
  rw [Finsupp.support_add_eq]
  · rw [Finsupp.support_single_ne_zero _ (by norm_num),
        Finsupp.support_single_ne_zero _ (by norm_num)]
    rfl
  · rw [Finsupp.support_single_ne_zero _ (by norm_num),
        Finsupp.support_single_ne_zero _ (by norm_num)]
    simp [hij]

/-- Two ordered pairs `(i,j)`, `(i',j')` with `i<j`, `i'<j'` producing the same unordered pair
of indices are equal. -/
private lemma pair_ext (i j i' j' : Fin (r + 1)) (hij : i < j) (hij' : i' < j')
    (h : ({i, j} : Finset (Fin (r + 1))) = {i', j'}) : i = i' ∧ j = j' := by
  have h1 : i' ∈ ({i, j} : Finset (Fin (r + 1))) := by rw [h]; simp
  have h2 : j' ∈ ({i, j} : Finset (Fin (r + 1))) := by rw [h]; simp
  have h3 : i ∈ ({i', j'} : Finset (Fin (r + 1))) := by rw [← h]; simp
  have h4 : j ∈ ({i', j'} : Finset (Fin (r + 1))) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3 h4
  constructor <;> omega

/-- Reindex an `Ioi 0` sum on `Fin (r+1)` along `Fin.succ`. -/
private lemma sum_Ioi_zero_succ (g : Fin (r + 1) → ℤ) :
    ∑ j ∈ Finset.Ioi (0 : Fin (r + 1)), g j = ∑ k : Fin r, g k.succ := by
  rw [← Finset.filter_lt_eq_Ioi, Finset.sum_filter, Fin.sum_univ_succ]
  simp [Fin.succ_pos]

/-- Reindex an `Ioi (i.succ)` sum on `Fin (r+1)` along `Fin.succ`. -/
private lemma sum_Ioi_succ_succ (i : Fin r) (g : Fin (r + 1) → ℤ) :
    ∑ j ∈ Finset.Ioi (i.succ), g j = ∑ k ∈ Finset.Ioi i, g k.succ := by
  rw [← Finset.filter_lt_eq_Ioi, Finset.sum_filter, Fin.sum_univ_succ,
      ← Finset.filter_lt_eq_Ioi, Finset.sum_filter]
  simp [Fin.succ_lt_succ_iff]

/-- Core expansion: evaluate a homogeneous degree-2 polynomial as a sum over squares and
upper-triangular cross terms, in the original `Fin (r+1)` coordinates. -/
private lemma core (H : MvPolynomial (Fin (r + 1)) ℤ) (hH : H.IsHomogeneous 2)
    (c : ℤ) (u : Fin r → ℤ) :
    eval (Fin.cons c u) H =
      (∑ i : Fin (r + 1), coeff (Finsupp.single i 2) H * ((Fin.cons c u : Fin (r + 1) → ℤ) i) ^ 2)
      + ∑ i : Fin (r + 1), ∑ j ∈ Finset.Ioi i,
          coeff (Finsupp.single i 1 + Finsupp.single j 1) H
            * ((Fin.cons c u : Fin (r + 1) → ℤ) i) * ((Fin.cons c u : Fin (r + 1) → ℤ) j) := by
  classical
  set x : Fin (r + 1) → ℤ := Fin.cons c u with hxdef
  rw [eval_eq']
  -- support ⊆ Diag ∪ Cross
  have hsub : H.support ⊆
      (Finset.univ.image (fun i : Fin (r + 1) => (Finsupp.single i 2 : Fin (r + 1) →₀ ℕ)))
        ∪ (Finset.univ.sigma (fun i : Fin (r + 1) => Finset.Ioi i)).image
            (fun p => (Finsupp.single p.1 1 + Finsupp.single p.2 1 : Fin (r + 1) →₀ ℕ)) := by
    intro d hd
    have hcoeff : coeff d H ≠ 0 := mem_support_iff.mp hd
    have hdeg : Finsupp.degree d = 2 := by
      by_contra hne
      exact hcoeff (hH.coeff_eq_zero hne)
    have hsum : d.sum (fun _ n => n) = 2 := by
      have hbridge : d.sum (fun _ n => n) = Finsupp.degree d := rfl
      rw [hbridge]; exact hdeg
    rcases homogeneous_degree_two_support_classification d hsum with ⟨i, hi⟩ | ⟨i, j, hij, hij2⟩
    · refine Finset.mem_union_left _ ?_
      rw [hi]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    · refine Finset.mem_union_right _ ?_
      rcases lt_or_gt_of_ne hij with h | h
      · have hmem : (⟨i, j⟩ : (_ : Fin (r + 1)) × Fin (r + 1)) ∈
            Finset.univ.sigma (fun i : Fin (r + 1) => Finset.Ioi i) :=
          Finset.mem_sigma.mpr ⟨Finset.mem_univ i, Finset.mem_Ioi.mpr h⟩
        rw [hij2]
        exact Finset.mem_image_of_mem _ hmem
      · have hmem : (⟨j, i⟩ : (_ : Fin (r + 1)) × Fin (r + 1)) ∈
            Finset.univ.sigma (fun i : Fin (r + 1) => Finset.Ioi i) :=
          Finset.mem_sigma.mpr ⟨Finset.mem_univ j, Finset.mem_Ioi.mpr h⟩
        rw [hij2, add_comm (Finsupp.single i 1) (Finsupp.single j 1)]
        exact Finset.mem_image_of_mem _ hmem
  -- terms outside the support vanish
  have hzero : ∀ d ∈ (Finset.univ.image
        (fun i : Fin (r + 1) => (Finsupp.single i 2 : Fin (r + 1) →₀ ℕ)))
        ∪ (Finset.univ.sigma (fun i : Fin (r + 1) => Finset.Ioi i)).image
            (fun p => (Finsupp.single p.1 1 + Finsupp.single p.2 1 : Fin (r + 1) →₀ ℕ)),
      d ∉ H.support → coeff d H * ∏ k, x k ^ (d k) = 0 := by
    intro d _ hd
    have : coeff d H = 0 := by rw [MvPolynomial.mem_support_iff] at hd; exact not_not.mp hd
    rw [this, zero_mul]
  -- disjointness of Diag and Cross
  have hdisj : Disjoint
      (Finset.univ.image (fun i : Fin (r + 1) => (Finsupp.single i 2 : Fin (r + 1) →₀ ℕ)))
      ((Finset.univ.sigma (fun i : Fin (r + 1) => Finset.Ioi i)).image
          (fun p => (Finsupp.single p.1 1 + Finsupp.single p.2 1 : Fin (r + 1) →₀ ℕ))) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_image] at ha hb
    obtain ⟨i, _, rfl⟩ := ha
    obtain ⟨p, hp, hpe⟩ := hb
    rw [Finset.mem_sigma, Finset.mem_Ioi] at hp
    have hne : p.1 ≠ p.2 := ne_of_lt hp.2
    have h2 : (Finsupp.single i 2 : Fin (r + 1) →₀ ℕ).support.card = 1 := by
      rw [Finsupp.support_single_ne_zero _ (by norm_num), Finset.card_singleton]
    rw [← hpe, cross_support _ _ hne, Finset.card_insert_of_notMem (by simp [hne]),
        Finset.card_singleton] at h2
    omega
  -- injectivity of the two parametrizations
  have hinjDiag : Set.InjOn (fun i : Fin (r + 1) => (Finsupp.single i 2 : Fin (r + 1) →₀ ℕ))
      ↑(Finset.univ : Finset (Fin (r + 1))) := by
    intro a _ b _ h
    exact Finsupp.single_left_injective (by norm_num) h
  have hinjCross : Set.InjOn
      (fun p : (_ : Fin (r + 1)) × Fin (r + 1) =>
        (Finsupp.single p.1 1 + Finsupp.single p.2 1 : Fin (r + 1) →₀ ℕ))
      ↑(Finset.univ.sigma (fun i : Fin (r + 1) => Finset.Ioi i)) := by
    intro p hp q hq h
    rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Ioi] at hp hq
    have h' : (Finsupp.single p.1 1 + Finsupp.single p.2 1 : Fin (r + 1) →₀ ℕ)
        = Finsupp.single q.1 1 + Finsupp.single q.2 1 := h
    have hsp : ({p.1, p.2} : Finset (Fin (r + 1))) = {q.1, q.2} := by
      rw [← cross_support p.1 p.2 (ne_of_lt hp.2), ← cross_support q.1 q.2 (ne_of_lt hq.2), h']
    obtain ⟨e1, e2⟩ := pair_ext p.1 p.2 q.1 q.2 hp.2 hq.2 hsp
    exact Sigma.ext e1 (heq_of_eq e2)
  rw [Finset.sum_subset hsub hzero, Finset.sum_union hdisj,
      Finset.sum_image hinjDiag, Finset.sum_image hinjCross, Finset.sum_sigma]
  simp only [prod_single, prod_cross, mul_assoc]

/-- The witness quadratic form of `witnessMatrixOfGeneral H`, expanded into diagonal squares and
upper-triangular cross terms. -/
private lemma witnessQuad_expand (H : MvPolynomial (Fin (r + 1)) ℤ) (u : Fin r → ℤ) :
    witnessQuad (witnessMatrixOfGeneral H) u =
      (∑ i : Fin r, coeff (Finsupp.single i.succ 2) H * (u i) ^ 2)
      + ∑ i : Fin r, ∑ j ∈ Finset.Ioi i,
          coeff (Finsupp.single i.succ 1 + Finsupp.single j.succ 1) H * u i * u j := by
  have hdouble : witnessQuad (witnessMatrixOfGeneral H) u
      = ∑ i, ∑ j, (witnessMatrixOfGeneral H) i j * u i * u j := by
    unfold witnessQuad
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    congr 1; ext i; congr 1; ext j; ring
  rw [hdouble, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · -- diagonal term
    have hii : (witnessMatrixOfGeneral H) i i = coeff (Finsupp.single i.succ 2) H := by
      simp [witnessMatrixOfGeneral]
    rw [hii]; ring
  · -- off-diagonal terms
    rw [← Finset.sum_subset (s₁ := Finset.Ioi i) (s₂ := Finset.univ.erase i)]
    · apply Finset.sum_congr rfl
      intro j hj
      have hlt : i < j := Finset.mem_Ioi.mp hj
      simp only [witnessMatrixOfGeneral, Matrix.of_apply, if_neg (ne_of_lt hlt),
        if_pos (show (i : ℕ) < (j : ℕ) from hlt)]
    · intro j hj
      exact Finset.mem_erase.mpr ⟨(ne_of_lt (Finset.mem_Ioi.mp hj)).symm, Finset.mem_univ j⟩
    · intro j hj hj'
      rw [Finset.mem_erase] at hj
      have hne : i ≠ j := (hj.1).symm
      have hnlt : ¬ i < j := by
        rw [Finset.mem_Ioi] at hj'; exact hj'
      simp only [witnessMatrixOfGeneral, Matrix.of_apply, if_neg hne,
        if_neg (show ¬ (i : ℕ) < (j : ℕ) from hnlt)]
      ring

/-- GPT r10 必須D theorem 2 (name verbatim): the evaluation identity for homogeneous quadratic H
in the (c, u) split, uniformly in r. -/
theorem homogeneous_degree_two_eval_general (H : MvPolynomial (Fin (r + 1)) ℤ)
    (hH : H.IsHomogeneous 2) (c : ℤ) (u : Fin r → ℤ) :
    eval (Fin.cons c u) H =
      aOfGeneral H * c ^ 2 + c * (bVectorOfGeneral H ⬝ᵥ u)
        + witnessQuad (witnessMatrixOfGeneral H) u := by
  have hSum1 : (∑ i : Fin (r + 1),
        coeff (Finsupp.single i 2) H * ((Fin.cons c u : Fin (r + 1) → ℤ) i) ^ 2)
      = aOfGeneral H * c ^ 2 + ∑ i : Fin r, coeff (Finsupp.single i.succ 2) H * (u i) ^ 2 := by
    rw [Fin.sum_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ, aOfGeneral]
  have hSum2 : (∑ i : Fin (r + 1), ∑ j ∈ Finset.Ioi i,
        coeff (Finsupp.single i 1 + Finsupp.single j 1) H
          * ((Fin.cons c u : Fin (r + 1) → ℤ) i) * ((Fin.cons c u : Fin (r + 1) → ℤ) j))
      = c * (bVectorOfGeneral H ⬝ᵥ u)
        + ∑ i : Fin r, ∑ j ∈ Finset.Ioi i,
            coeff (Finsupp.single i.succ 1 + Finsupp.single j.succ 1) H * u i * u j := by
    rw [Fin.sum_univ_succ]
    congr 1
    · -- the i = 0 outer term
      simp only [Fin.cons_zero]
      rw [sum_Ioi_zero_succ]
      simp only [Fin.cons_succ]
      rw [dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [bVectorOfGeneral]
      ring
    · -- the i = i'.succ outer terms
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.cons_succ]
      rw [sum_Ioi_succ_succ]
      simp only [Fin.cons_succ]
  rw [core H hH c u, hSum1, hSum2, witnessQuad_expand]
  ring

/-- GPT r10 必須D theorem 4 (name verbatim). -/
theorem fboundG_eq_fboundM_general (K : ℕ) (ℓ : Fin (r + 1) → ℤ) (q : ℤ) :
    fboundG K ℓ q = fboundM K (ℓ 0) (fun k => ℓ k.succ) q := by
  simp only [fboundG, fboundM]
  rw [Fin.sum_univ_succ]
  ring

/-- The fiber value in the (c, u) split equals the matrix fiber polynomial. -/
theorem fiberVal_eq_fqM_general (H : MvPolynomial (Fin (r + 1)) ℤ) (hH : H.IsHomogeneous 2)
    (ℓ : Fin (r + 1) → ℤ) (q : ℤ) (c : ℤ) (u : Fin r → ℤ) :
    fiberVal H ℓ q (Fin.cons c u) =
      fqM (aOfGeneral H) (bVectorOfGeneral H) (witnessMatrixOfGeneral H)
        (ℓ 0) (fun k => ℓ k.succ) q c u := by
  simp only [fiberVal, fqM]
  rw [homogeneous_degree_two_eval_general H hH]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, dotProduct]
  ring

/-- GPT r10 必須D theorem 3 (name verbatim): the fiber sets agree, uniformly in r. -/
theorem fiberSetG_eq_fiberSetM_general (H : MvPolynomial (Fin (r + 1)) ℤ)
    (hH : H.IsHomogeneous 2) (ℓ : Fin (r + 1) → ℤ) (q : ℤ) :
    fiberSetG H ℓ q =
      fiberSetM (aOfGeneral H) (bVectorOfGeneral H) (witnessMatrixOfGeneral H)
        (ℓ 0) (fun k => ℓ k.succ) q := by
  ext c
  simp only [fiberSetG, fiberSetM, Set.mem_setOf_eq, fiberVal_eq_fqM_general H hH]

/-- GPT r10 必須D theorem 5 (name verbatim): the transfer of the matrix dichotomy to the
polynomial dichotomy, uniformly in r. -/
theorem dichotomyG_of_dichotomyM_general (H : MvPolynomial (Fin (r + 1)) ℤ)
    (hH : H.IsHomogeneous 2) :
    DichotomyM (aOfGeneral H) (bVectorOfGeneral H) (witnessMatrixOfGeneral H) → DichotomyG H := by
  rintro ⟨K, hK⟩
  refine ⟨K, fun ℓ q => ?_⟩
  rw [fiberSetG_eq_fiberSetM_general H hH, fboundG_eq_fboundM_general]
  exact hK (ℓ 0) (fun k => ℓ k.succ) q

/-- 宿題群 3.13 anchor: at r = 3 the general extraction is definitionally the r10 bridge (a). -/
theorem aOfGeneral_three (H : MvPolynomial (Fin 4) ℤ) :
    aOfGeneral H = DiophCompression.SemanticQuadraticThreeWitness.aOf H := rfl

/-- 宿題群 3.13 anchor (B). -/
theorem bVectorOfGeneral_three (H : MvPolynomial (Fin 4) ℤ) :
    bVectorOfGeneral H = DiophCompression.SemanticQuadraticThreeWitness.bVectorOf H := by
  funext k
  fin_cases k <;> rfl

/-- 宿題群 3.13 anchor (C). -/
theorem witnessMatrixOfGeneral_three (H : MvPolynomial (Fin 4) ℤ) :
    witnessMatrixOfGeneral H = DiophCompression.SemanticQuadraticThreeWitness.witnessMatrixOf H := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end DiophCompression.SemanticQuadraticMatrix

section AxiomAudit
open DiophCompression.SemanticQuadraticMatrix
#print axioms homogeneous_degree_two_support_classification
#print axioms homogeneous_degree_two_eval_general
#print axioms fiberSetG_eq_fiberSetM_general
#print axioms fboundG_eq_fboundM_general
#print axioms dichotomyG_of_dichotomyM_general
#print axioms aOfGeneral_three
#print axioms bVectorOfGeneral_three
#print axioms witnessMatrixOfGeneral_three
end AxiomAudit
