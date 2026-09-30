/-
  MPUP/Obstruction.lean — the counting obstruction (spec/OBSTRUCTION_THEOREM.md), statements FROZEN 2026-08-26.
  Main: any polynomial of total degree d in n parameters, one code parameter c and r unknowns (over ℕ or ℤ)
  that represents the graph of an injective e : ℕ^n → ℕ satisfies  n ≤ d · monoCount d (r+1),
  where monoCount d k = C(d+k, k) = number of monomials of total degree ≤ d in k variables.
  Corollaries: ¬ TupleCoderN r d, ¬ TupleCoderZ r d, and (with Task 1) ¬ MPUP_N, ¬ MPUP_Z.
-/
import MPUP.Spec
import MPUP.Task1

namespace MPUP
open MvPolynomial

/-- Number of monomials of total degree ≤ d in k variables, counted directly as exponent vectors
    (each exponent ≤ d, sum ≤ d). Numerically this is `Nat.choose (d + k) k`; that identity is
    not needed for the obstruction and is left as a remark. -/
def monoCount (d k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (d + 1))).filter (fun m => ∑ i, (m i : ℕ) ≤ d)).card

theorem monoCount_mono {d d' k k' : ℕ} (hd : d ≤ d') (hk : k ≤ k') :
    monoCount d k ≤ monoCount d' k' := by
  rw [monoCount, monoCount]
  refine Finset.card_le_card_of_injOn
    (fun m i => if h : (i:ℕ) < k then (⟨(m ⟨i,h⟩ : ℕ), by omega⟩ : Fin (d'+1)) else 0) ?_ ?_
  · intro m hm
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm ⊢
    have key : ∑ i : Fin k', ((if h : (i:ℕ) < k then (⟨(m ⟨i,h⟩ : ℕ), by omega⟩ : Fin (d'+1)) else 0) : ℕ)
        = ∑ j : Fin k, ((m j : ℕ)) := by
      set F : ℕ → ℕ := fun j => if h : j < k then (m ⟨j,h⟩ : ℕ) else 0 with hF
      have hL : ∑ i : Fin k', ((if h : (i:ℕ) < k then (⟨(m ⟨i,h⟩ : ℕ), by omega⟩ : Fin (d'+1)) else 0) : ℕ)
          = ∑ i ∈ Finset.range k', F i := by
        rw [← Fin.sum_univ_eq_sum_range F k']
      have hR : ∑ j : Fin k, ((m j : ℕ)) = ∑ j ∈ Finset.range k, F j := by
        rw [← Fin.sum_univ_eq_sum_range F k]
        apply Finset.sum_congr rfl
        intro j _
        show (m j : ℕ) = F j
        simp only [hF]; rw [dif_pos j.isLt]
      rw [hL, hR]
      apply (Finset.sum_subset (Finset.range_subset_range.mpr hk) _).symm
      intro x _ hx
      simp only [hF, Finset.mem_range] at hx ⊢
      rw [dif_neg hx]
    simp only [apply_dite Fin.val, Fin.val_zero] at *
    rw [key]
    exact le_trans hm hd
  · intro m1 _ m2 _ heq
    funext j
    have hj : (Fin.castLE hk j : ℕ) < k := by simpa using j.isLt
    have h2 := congrFun heq (Fin.castLE hk j)
    simp only [dif_pos hj] at h2
    apply Fin.ext
    have h3 := Fin.val_eq_of_eq h2
    simpa using h3

/-- Representation with witnesses restricted to a set `W` of integer vectors (ℕ^r or ℤ^r are instances). -/
def RepresentsIn {n r : ℕ} (W : Set (Fin r → ℤ)) (P : Poly n r) (A : Set (Fin n → ℕ)) : Prop :=
  ∀ a, a ∈ A ↔ ∃ y ∈ W, evalAt P a y = 0

theorem representsN_iff_representsIn {n r : ℕ} (P : Poly n r) (A : Set (Fin n → ℕ)) :
    RepresentsN P A ↔ RepresentsIn {y | ∀ i, 0 ≤ y i} P A := by
  constructor
  · intro h a
    rw [h a]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨fun i => (y i : ℤ), fun i => Int.natCast_nonneg _, hy⟩
    · rintro ⟨y, hy, hy0⟩
      refine ⟨fun i => (y i).toNat, ?_⟩
      have : (fun i => ((y i).toNat : ℤ)) = y := by
        funext i; exact Int.toNat_of_nonneg (hy i)
      rw [this]; exact hy0
  · intro h a
    rw [h a]
    constructor
    · rintro ⟨y, hy, hy0⟩
      refine ⟨fun i => (y i).toNat, ?_⟩
      have : (fun i => ((y i).toNat : ℤ)) = y := by
        funext i; exact Int.toNat_of_nonneg (hy i)
      rw [this]; exact hy0
    · rintro ⟨y, hy⟩
      exact ⟨fun i => (y i : ℤ), fun i => Int.natCast_nonneg _, hy⟩

theorem representsZ_iff_representsIn {n r : ℕ} (P : Poly n r) (A : Set (Fin n → ℕ)) :
    RepresentsZ P A ↔ RepresentsIn Set.univ P A := by
  simp [RepresentsZ, RepresentsIn]

theorem aux_arith (n d M K : ℕ) (h : d * M + 1 ≤ n) :
    ∃ N, 1 ≤ N ∧ (2 * K * N ^ d + 1) ^ M < (N + 1) ^ n := by
  set K' := K + 1 with hK'
  set N := (3 * K') ^ M + 1 with hN
  have hN1 : 1 ≤ N := by rw [hN]; omega
  have hNd : 1 ≤ N ^ d := Nat.one_le_pow d N (by omega)
  refine ⟨N, hN1, ?_⟩
  have s1 : 2 * K * N ^ d + 1 ≤ 3 * K' * N ^ d := by
    have h3 : 3 * K' * N ^ d = 3 * K * N ^ d + 3 * N ^ d := by rw [hK']; ring
    nlinarith [hNd]
  calc (2 * K * N ^ d + 1) ^ M
      ≤ (3 * K' * N ^ d) ^ M := Nat.pow_le_pow_left s1 M
    _ = (3 * K') ^ M * N ^ (d * M) := by rw [Nat.mul_pow, ← Nat.pow_mul]
    _ < N * N ^ (d * M) := by
        have hpos : 0 < N ^ (d * M) := Nat.one_le_pow _ _ (by omega)
        have hlt : (3 * K') ^ M < N := by rw [hN]; omega
        exact (Nat.mul_lt_mul_right hpos).mpr hlt
    _ = N ^ (d * M + 1) := by rw [pow_succ]; ring
    _ ≤ N ^ n := Nat.pow_le_pow_right (by omega) h
    _ < (N + 1) ^ n := Nat.pow_lt_pow_left (by omega) (by omega)

noncomputable def fsub {n r : ℕ} (a : Fin n → ℕ) :
    (Fin (n+1) ⊕ Fin r) → MvPolynomial (Fin 1 ⊕ Fin r) ℤ :=
  fun v => match v with
    | Sum.inl i => if h : (i:ℕ) < n then C ((a ⟨i,h⟩ : ℕ) : ℤ) else X (Sum.inl 0)
    | Sum.inr j => X (Sum.inr j)

noncomputable def Phi {n r : ℕ} (C0 : Poly (n+1) r) (a : Fin n → ℕ) :
    MvPolynomial (Fin 1 ⊕ Fin r) ℤ :=
  aeval (fsub a) C0

theorem aux_L1 {n r : ℕ} (C0 : Poly (n+1) r) (a : Fin n → ℕ) (c : ℕ) (y : Fin r → ℤ) :
    evalAt C0 (Fin.snoc a c) y
      = eval (Sum.elim (fun _ : Fin 1 => (c : ℤ)) y) (Phi C0 a) := by
  unfold evalAt Phi
  rw [map_aeval]
  have hcomp : (eval (Sum.elim (fun _ : Fin 1 => (c : ℤ)) y)).comp
      (algebraMap ℤ (MvPolynomial (Fin 1 ⊕ Fin r) ℤ)) = RingHom.id ℤ := by
    rw [algebraMap_eq]
    ext z
    simp
  rw [hcomp]
  -- now eval₂Hom (RingHom.id ℤ) ρ C0 = eval ρ' C0
  have : (eval₂Hom (RingHom.id ℤ) (fun v => (eval (Sum.elim (fun _ : Fin 1 => (c:ℤ)) y)) (fsub a v))) C0
      = eval (fun v => (eval (Sum.elim (fun _ : Fin 1 => (c:ℤ)) y)) (fsub a v)) C0 := rfl
  rw [this]
  apply congrArg (fun σ => eval σ C0)
  funext v
  cases v with
  | inl i =>
    simp only [Sum.elim_inl]
    show (Fin.snoc a c : Fin (n+1) → ℕ) i = (eval _) (fsub a (Sum.inl i))
    simp only [fsub]
    by_cases h : (i:ℕ) < n
    · rw [dif_pos h, eval_C]
      have hval : (Fin.snoc a c : Fin (n+1) → ℕ) i = a ⟨↑i, h⟩ := by
        have key := Fin.snoc_castSucc (α := fun _ => ℕ) (p := a) (x := c) (i := ⟨(i:ℕ), h⟩)
        have hc : (Fin.castSucc ⟨(i:ℕ), h⟩ : Fin (n+1)) = i := by ext; simp
        rw [hc] at key
        exact key
      exact_mod_cast hval
    · rw [dif_neg h]
      have hlast : i = Fin.last n := Fin.eq_last_of_not_lt h
      simp [eval_X, hlast, Fin.snoc_last]
  | inr j =>
    simp only [Sum.elim_inr]
    show y j = (eval _) (fsub a (Sum.inr j))
    simp only [fsub, eval_X, Sum.elim_inr]

theorem aux_td_aeval {n r : ℕ}
    (g : (Fin (n+1) ⊕ Fin r) → MvPolynomial (Fin 1 ⊕ Fin r) ℤ)
    (p : Poly (n+1) r) (hg : ∀ v, (g v).totalDegree ≤ 1) :
    (aeval g p).totalDegree ≤ p.totalDegree := by
  rw [aeval_def, eval₂_eq]
  apply totalDegree_finsetSum_le
  intro β hβ
  rw [algebraMap_eq]
  calc (C (coeff β p) * ∏ v ∈ β.support, (g v) ^ (β v)).totalDegree
      ≤ (C (coeff β p)).totalDegree + (∏ v ∈ β.support, (g v) ^ (β v)).totalDegree :=
        totalDegree_mul _ _
    _ = (∏ v ∈ β.support, (g v) ^ (β v)).totalDegree := by rw [totalDegree_C]; ring
    _ ≤ ∑ v ∈ β.support, ((g v) ^ (β v)).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ v ∈ β.support, (β v) * 1 := by
        apply Finset.sum_le_sum
        intro v _
        calc ((g v) ^ (β v)).totalDegree ≤ (β v) * (g v).totalDegree := totalDegree_pow _ _
          _ ≤ (β v) * 1 := by apply Nat.mul_le_mul_left; exact hg v
    _ = ∑ v ∈ β.support, β v := by simp
    _ ≤ p.totalDegree := le_totalDegree hβ

theorem aux_Phi_totalDegree {n r : ℕ} (C0 : Poly (n+1) r) (a : Fin n → ℕ) :
    (Phi C0 a).totalDegree ≤ C0.totalDegree := by
  apply aux_td_aeval
  intro v
  cases v with
  | inl i =>
    simp only [fsub]
    by_cases h : (i:ℕ) < n
    · rw [dif_pos h, totalDegree_C]; omega
    · rw [dif_neg h]; exact le_of_eq (totalDegree_X _)
  | inr j => simp only [fsub]; exact le_of_eq (totalDegree_X _)


theorem aux_prod_monomial {σ ι R : Type*} [DecidableEq σ] [CommRing R]
    (s : Finset ι) (e : ι → σ →₀ ℕ) (c : ι → R) :
    ∏ i ∈ s, (monomial (e i) (c i) : MvPolynomial σ R)
      = monomial (∑ i ∈ s, e i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x t hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx, ih, monomial_mul]

noncomputable def efac {n r : ℕ} (v : Fin (n+1) ⊕ Fin r) (k : ℕ) :
    (Fin 1 ⊕ Fin r) →₀ ℕ :=
  match v with
  | Sum.inl i => if _ : (i:ℕ) < n then 0 else Finsupp.single (Sum.inl 0) k
  | Sum.inr j => Finsupp.single (Sum.inr j) k

noncomputable def cfac {n r : ℕ} (a : Fin n → ℕ) (v : Fin (n+1) ⊕ Fin r) (k : ℕ) : ℤ :=
  match v with
  | Sum.inl i => if h : (i:ℕ) < n then ((a ⟨i,h⟩ : ℕ) : ℤ) ^ k else 1
  | Sum.inr j => 1

theorem aux_factor {n r : ℕ} (a : Fin n → ℕ) (v : Fin (n+1) ⊕ Fin r) (k : ℕ) :
    (fsub a v) ^ k = monomial (efac v k) (cfac a v k) := by
  cases v with
  | inl i =>
    simp only [fsub, efac, cfac]
    by_cases h : (i:ℕ) < n
    · rw [dif_pos h, dif_pos h, dif_pos h, ← C_pow, C_apply]
    · rw [dif_neg h, dif_neg h, dif_neg h, X_pow_eq_monomial]
  | inr j =>
    simp only [fsub, efac, cfac]
    rw [X_pow_eq_monomial]

theorem aux_kappa_bound {n r N : ℕ} (C0 : Poly (n+1) r) (a : Fin n → ℕ)
    (hN : ∀ i, a i ≤ N) (h1 : 1 ≤ N)
    (β : (Fin (n+1) ⊕ Fin r) →₀ ℕ) (hβ : β ∈ C0.support) :
    |∏ v ∈ β.support, cfac a v (β v)| ≤ (N : ℤ) ^ C0.totalDegree := by
  rw [Finset.abs_prod]
  have step1 : ∏ v ∈ β.support, |cfac a v (β v)| ≤ ∏ v ∈ β.support, (N : ℤ) ^ (β v) := by
    apply Finset.prod_le_prod
    · intro v _; exact abs_nonneg _
    · intro v _
      cases v with
      | inl i =>
        simp only [cfac]
        by_cases h : (i:ℕ) < n
        · rw [dif_pos h, abs_pow]
          apply pow_le_pow_left₀ (abs_nonneg _)
          rw [abs_of_nonneg (by positivity)]
          exact_mod_cast hN _
        · rw [dif_neg h, abs_one]
          exact one_le_pow₀ (by exact_mod_cast h1)
      | inr j =>
        simp only [cfac, abs_one]
        exact one_le_pow₀ (by exact_mod_cast h1)
  calc ∏ v ∈ β.support, |cfac a v (β v)|
      ≤ ∏ v ∈ β.support, (N : ℤ) ^ (β v) := step1
    _ = (N : ℤ) ^ (∑ v ∈ β.support, β v) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (N : ℤ) ^ C0.totalDegree := by
        apply pow_le_pow_right₀ (by exact_mod_cast h1)
        exact le_totalDegree hβ

theorem aux_G_monomial {n r : ℕ} (a : Fin n → ℕ)
    (β : (Fin (n+1) ⊕ Fin r) →₀ ℕ) :
    (∏ v ∈ β.support, (fsub a v) ^ (β v))
      = monomial (∑ v ∈ β.support, efac v (β v)) (∏ v ∈ β.support, cfac a v (β v)) := by
  have h : ∀ v ∈ β.support, (fsub a v) ^ (β v)
      = monomial (efac v (β v)) (cfac a v (β v)) := fun v _ => aux_factor a v (β v)
  rw [Finset.prod_congr rfl h, aux_prod_monomial]

theorem aux_coeff_bound {n r N : ℕ} (C0 : Poly (n+1) r) (a : Fin n → ℕ)
    (hN : ∀ i, a i ≤ N) (h1 : 1 ≤ N) (m : (Fin 1 ⊕ Fin r) →₀ ℕ) :
    |(Phi C0 a).coeff m|
      ≤ (∑ β ∈ C0.support, |C0.coeff β|) * (N : ℤ) ^ C0.totalDegree := by
  have hexp : Phi C0 a
      = ∑ β ∈ C0.support, C (C0.coeff β) * (∏ v ∈ β.support, (fsub a v) ^ (β v)) := by
    rw [Phi, aeval_def, eval₂_eq, algebraMap_eq]
  rw [hexp, coeff_sum]
  have hterm : ∀ β ∈ C0.support,
      |coeff m (C (C0.coeff β) * (∏ v ∈ β.support, (fsub a v) ^ (β v)))|
        ≤ |C0.coeff β| * (N : ℤ) ^ C0.totalDegree := by
    intro β hβ
    rw [coeff_C_mul, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [aux_G_monomial, coeff_monomial]
    by_cases hν : (∑ v ∈ β.support, efac v (β v)) = m
    · rw [if_pos hν]; exact aux_kappa_bound C0 a hN h1 β hβ
    · rw [if_neg hν, abs_zero]; positivity
  calc |∑ β ∈ C0.support, coeff m (C (C0.coeff β) * (∏ v ∈ β.support, (fsub a v) ^ (β v)))|
      ≤ ∑ β ∈ C0.support, |coeff m (C (C0.coeff β) * (∏ v ∈ β.support, (fsub a v) ^ (β v)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ β ∈ C0.support, |C0.coeff β| * (N : ℤ) ^ C0.totalDegree := Finset.sum_le_sum hterm
    _ = (∑ β ∈ C0.support, |C0.coeff β|) * (N : ℤ) ^ C0.totalDegree := by
        rw [Finset.sum_mul]

theorem aux_Phi_injective {n r : ℕ} {W : Set (Fin r → ℤ)} (C0 : Poly (n+1) r)
    {e : (Fin n → ℕ) → ℕ} (he : Function.Injective e)
    (hC : RepresentsIn W C0 (graph e)) : Function.Injective (Phi C0) := by
  intro a a' hEq
  have hmem : (Fin.snoc a (e a) : Fin (n+1) → ℕ) ∈ graph e := by
    show (Fin.snoc a (e a) : Fin (n+1) → ℕ) (Fin.last n)
        = e (Fin.init (Fin.snoc a (e a) : Fin (n+1) → ℕ))
    rw [Fin.snoc_last, Fin.init_snoc]
  obtain ⟨y, hyW, hy0⟩ := (hC _).1 hmem
  rw [aux_L1 C0 a (e a) y, hEq, ← aux_L1 C0 a' (e a) y] at hy0
  have hmem' : (Fin.snoc a' (e a) : Fin (n+1) → ℕ) ∈ graph e := (hC _).2 ⟨y, hyW, hy0⟩
  have hg : (Fin.snoc a' (e a) : Fin (n+1) → ℕ) (Fin.last n)
      = e (Fin.init (Fin.snoc a' (e a) : Fin (n+1) → ℕ)) := hmem'
  rw [Fin.snoc_last, Fin.init_snoc] at hg
  exact he hg

noncomputable def e2 (r : ℕ) : (Fin 1 ⊕ Fin r) ≃ Fin (r+1) :=
  finSumFinEquiv.trans (finCongr (by omega))

noncomputable def muMon {r : ℕ} (idx : Fin (r+1) → ℕ) : (Fin 1 ⊕ Fin r) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v => idx (e2 r v))

theorem muMon_apply {r : ℕ} (idx : Fin (r+1) → ℕ) (v : Fin 1 ⊕ Fin r) :
    (muMon idx) v = idx (e2 r v) := rfl

theorem muMon_idxOf {r : ℕ} (m : (Fin 1 ⊕ Fin r) →₀ ℕ) :
    muMon (fun i => m ((e2 r).symm i)) = m := by
  ext v
  rw [muMon_apply]
  simp

theorem aux_coeff_nat {n r N : ℕ} (C0 : Poly (n+1) r) (a : Fin n → ℕ)
    (hN : ∀ i, a i ≤ N) (h1 : 1 ≤ N) (m : (Fin 1 ⊕ Fin r) →₀ ℕ) :
    ((Phi C0 a).coeff m).natAbs
      ≤ (∑ β ∈ C0.support, (C0.coeff β).natAbs) * N ^ C0.totalDegree := by
  have hb := aux_coeff_bound C0 a hN h1 m
  rw [Int.abs_eq_natAbs] at hb
  have hrhs : (∑ β ∈ C0.support, |C0.coeff β|) * (N : ℤ) ^ C0.totalDegree
      = (((∑ β ∈ C0.support, (C0.coeff β).natAbs) * N ^ C0.totalDegree : ℕ) : ℤ) := by
    push_cast
    simp only [Int.abs_eq_natAbs]
  rw [hrhs] at hb
  exact_mod_cast hb

theorem aux_counting {n r : ℕ} {W : Set (Fin r → ℤ)} (C0 : Poly (n+1) r)
    {e : (Fin n → ℕ) → ℕ} (he : Function.Injective e)
    (hC : RepresentsIn W C0 (graph e)) (N : ℕ) (h1 : 1 ≤ N) :
    (N + 1) ^ n
      ≤ (2 * (∑ β ∈ C0.support, (C0.coeff β).natAbs) * N ^ C0.totalDegree + 1)
          ^ (monoCount C0.totalDegree (r + 1)) := by
  classical
  set d := C0.totalDegree with hd
  set Knat := ∑ β ∈ C0.support, (C0.coeff β).natAbs with hK
  set B0 := Knat * N ^ d with hB0
  set Bnd := 2 * B0 + 1 with hBnd
  -- Predicate
  let P : (Fin (r+1) → Fin (d+1)) → Prop := fun idx => ∑ i, (idx i : ℕ) ≤ d
  -- Coefficient two-sided bound
  have habs : ∀ (a' : Fin n → ℕ), (∀ i, a' i ≤ N) → ∀ m : (Fin 1 ⊕ Fin r) →₀ ℕ,
      -(B0 : ℤ) ≤ (Phi C0 a').coeff m ∧ (Phi C0 a').coeff m ≤ (B0 : ℤ) := by
    intro a' ha' m
    have hcb := aux_coeff_nat C0 a' ha' h1 m
    rw [← hd, ← hK, ← hB0] at hcb
    have hcbz : (((Phi C0 a').coeff m).natAbs : ℤ) ≤ (B0 : ℤ) := by exact_mod_cast hcb
    have h1' := Int.le_natAbs (a := (Phi C0 a').coeff m)
    have h2' := Int.le_natAbs (a := -((Phi C0 a').coeff m))
    rw [Int.natAbs_neg] at h2'
    omega
  -- entry / degree bound helper
  have hentry : ∀ (m : (Fin 1 ⊕ Fin r) →₀ ℕ) (v : Fin 1 ⊕ Fin r),
      m v ≤ ∑ w ∈ m.support, m w := by
    intro m v
    by_cases hv : v ∈ m.support
    · exact Finset.single_le_sum (by intro w _; exact Nat.zero_le _) hv
    · rw [Finsupp.notMem_support_iff.1 hv]; exact Nat.zero_le _
  have hsumfull : ∀ (m : (Fin 1 ⊕ Fin r) →₀ ℕ),
      ∑ i : Fin (r+1), m ((e2 r).symm i) = ∑ w ∈ m.support, m w := by
    intro m
    rw [Equiv.sum_comp (e2 r).symm (fun v => m v)]
    rw [← Finset.sum_subset (Finset.subset_univ m.support)]
    intro w _ hw
    exact Finsupp.notMem_support_iff.1 hw
  -- define f
  let a : (Fin n → Fin (N+1)) → (Fin n → ℕ) := fun g i => (g i : ℕ)
  have haN : ∀ g i, a g i ≤ N := by intro g i; exact Nat.lt_succ_iff.1 (g i).isLt
  let f : (Fin n → Fin (N+1)) → ({idx : Fin (r+1) → Fin (d+1) // P idx} → Fin Bnd) :=
    fun g s => ⟨((Phi C0 (a g)).coeff (muMon (fun i => (s.1 i : ℕ))) + B0).toNat, by
      rw [Int.toNat_lt' (by omega)]
      have hb := (habs (a g) (haN g) (muMon (fun i => (s.1 i : ℕ)))).2
      have : ((Bnd : ℕ) : ℤ) = 2 * (B0 : ℤ) + 1 := by rw [hBnd]; push_cast; ring
      rw [this]; omega⟩
  have hinj : Function.Injective f := by
    intro g g' hgg
    -- coeffs agree on all low-degree monomials
    have hcoeff : ∀ s : {idx : Fin (r+1) → Fin (d+1) // P idx},
        (Phi C0 (a g)).coeff (muMon (fun i => (s.1 i : ℕ)))
          = (Phi C0 (a g')).coeff (muMon (fun i => (s.1 i : ℕ))) := by
      intro s
      have hcong := congrFun hgg s
      simp only [f] at hcong
      have hv := Fin.val_eq_of_eq hcong
      have hb1 := (habs (a g) (haN g) (muMon (fun i => (s.1 i : ℕ)))).1
      have hb2 := (habs (a g') (haN g') (muMon (fun i => (s.1 i : ℕ)))).1
      have hnn1 : 0 ≤ (Phi C0 (a g)).coeff (muMon (fun i => (s.1 i : ℕ))) + B0 := by omega
      have hnn2 : 0 ≤ (Phi C0 (a g')).coeff (muMon (fun i => (s.1 i : ℕ))) + B0 := by omega
      have heqz : (Phi C0 (a g)).coeff (muMon (fun i => (s.1 i : ℕ))) + B0
          = (Phi C0 (a g')).coeff (muMon (fun i => (s.1 i : ℕ))) + B0 := by
        rw [← Int.toNat_of_nonneg hnn1, ← Int.toNat_of_nonneg hnn2]
        exact_mod_cast hv
      omega
    -- Phi equal
    have hPhi : Phi C0 (a g) = Phi C0 (a g') := by
      ext m
      by_cases hdeg : ∑ w ∈ m.support, m w ≤ d
      · -- build s
        have hlt : ∀ i : Fin (r+1), m ((e2 r).symm i) < d + 1 := by
          intro i
          have := hentry m ((e2 r).symm i)
          omega
        let s : {idx : Fin (r+1) → Fin (d+1) // P idx} :=
          ⟨fun i => ⟨m ((e2 r).symm i), hlt i⟩, by
            show ∑ i, ((⟨m ((e2 r).symm i), hlt i⟩ : Fin (d+1)) : ℕ) ≤ d
            simp only [Fin.val_mk]
            rw [hsumfull m]; exact hdeg⟩
        have hmu : muMon (fun i => ((s.1 i : ℕ))) = m := by
          show muMon (fun i => m ((e2 r).symm i)) = m
          exact muMon_idxOf m
        have := hcoeff s
        rw [hmu] at this
        exact this
      · have hdeg' : d < ∑ w ∈ m.support, m w := not_le.1 hdeg
        rw [coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt (aux_Phi_totalDegree C0 (a g)) hdeg'),
            coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt (aux_Phi_totalDegree C0 (a g')) hdeg')]
    have haa : a g = a g' := aux_Phi_injective C0 he hC hPhi
    funext i
    have : (g i : ℕ) = (g' i : ℕ) := congrFun haa i
    exact Fin.ext this
  -- cards
  have hcardD : Fintype.card (Fin n → Fin (N+1)) = (N+1)^n := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hcardC : Fintype.card ({idx : Fin (r+1) → Fin (d+1) // P idx} → Fin Bnd)
      = Bnd ^ (monoCount d (r+1)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype]
    rfl
  have hfin := Fintype.card_le_of_injective f hinj
  rw [hcardD, hcardC] at hfin
  have hBe : Bnd = 2 * Knat * N ^ d + 1 := by rw [hBnd, hB0]; ring
  rw [hBe] at hfin
  exact hfin


/-- THE COUNTING BOUND. -/
theorem coder_counting_bound {n r : ℕ} (W : Set (Fin r → ℤ)) (C : Poly (n + 1) r)
    (e : (Fin n → ℕ) → ℕ) (he : Function.Injective e) (hC : RepresentsIn W C (graph e)) :
    n ≤ C.totalDegree * monoCount C.totalDegree (r + 1) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨N, hN1, hlt⟩ := aux_arith n C.totalDegree (monoCount C.totalDegree (r + 1))
    (∑ β ∈ C.support, (C.coeff β).natAbs) (by omega)
  have hcount := aux_counting C he hC N hN1
  exact absurd hcount (not_le.2 hlt)

theorem not_tupleCoderN (r d : ℕ) : ¬ TupleCoderN r d := by
  intro h
  obtain ⟨e, he, r', hr', C, hCd, hC⟩ := h (d * monoCount d (r + 1) + 1)
  have h1 := coder_counting_bound _ C e he ((representsN_iff_representsIn C _).1 hC)
  have h2 : C.totalDegree * monoCount C.totalDegree (r' + 1) ≤ d * monoCount d (r + 1) :=
    Nat.mul_le_mul hCd (monoCount_mono hCd (by omega))
  omega

theorem not_tupleCoderZ (r d : ℕ) : ¬ TupleCoderZ r d := by
  intro h
  obtain ⟨e, he, r', hr', C, hCd, hC⟩ := h (d * monoCount d (r + 1) + 1)
  have h1 := coder_counting_bound _ C e he ((representsZ_iff_representsIn C _).1 hC)
  have h2 : C.totalDegree * monoCount C.totalDegree (r' + 1) ≤ d * monoCount d (r + 1) :=
    Nat.mul_le_mul hCd (monoCount_mono hCd (by omega))
  omega

theorem coder_of_multiUniversalZ {ν δ : ℕ} (h : MultiUniversalZ (fun _ => ν) (fun _ => δ)) :
    TupleCoderZ ν δ := by
  intro n
  exact ⟨code, code_injective n, h (n + 1) _ (diophN_graph_code n)⟩

/-- The §6.2 open question, ℕ-unknowns: NO. -/
theorem not_MPUP_N : ¬ MPUP_N := by
  rintro ⟨ν, δ, h⟩
  exact not_tupleCoderN ν δ (coder_of_multiUniversal h)

/-- The §6.2 open question, ℤ-unknowns: NO. -/
theorem not_MPUP_Z : ¬ MPUP_Z := by
  rintro ⟨ν, δ, h⟩
  exact not_tupleCoderZ ν δ (coder_of_multiUniversalZ h)

end MPUP

#print axioms MPUP.not_tupleCoderN
#print axioms MPUP.not_MPUP_N
#print axioms MPUP.not_MPUP_Z
