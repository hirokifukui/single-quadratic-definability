/-
  MPUP/WeightedBound.lean — session 32 (2026-09-03, agora).

  The graded refinement of the counting obstruction. `MPUP/Obstruction.lean` is NOT modified:
  every statement there keeps its bytes, and this file only imports it.

  Obstruction.lean bounds every coefficient of the specialised polynomial by K * N^d, uniformly
  in the monomial, and so pays d for each of the monoCount d (r+1) monomials:  n <= d * M.
  A monomial m of fibre degree |m| can only receive contributions from those beta whose parameter
  part has degree at most d - |m|, so its coefficient is bounded by K * N^(d - |m|).  Adding the
  exponents instead of multiplying gives the weighted bound

      n <= wtCount d (r+1) = sum over monomials m of (d - |m|),

  which is <= d * M and is the form the paper's Appendix C states.

  s34 (2026-09-04): both closed forms are now KERNEL FACTS in this file, not remarks --
  `monoCount_closed_form : monoCount d k = (d + k).choose k` and
  `wtCount_closed_form  : wtCount  d k = (d + k).choose (k + 1)`.  The earlier docstring here
  deferred them to the paper; that deferral is withdrawn.  Obstruction.lean's own docstring still
  defers the monoCount identity, because the five frozen modules keep their bytes; the identity
  itself is proved here.  A claim in a docstring is not a claim of the kernel: that is exactly why
  these two were promoted to theorems.

  STATEMENTS FROZEN BY claude.ai BEFORE ANY PROOF WAS ATTEMPTED.  Tactic search may be delegated;
  the statements may not be edited to make a proof go through.  Any change to a statement below
  invalidates the delegation and must come back here first.
-/
import MPUP.Obstruction

namespace MPUP
open MvPolynomial

/-- Weighted count of monomials of total degree `≤ d` in `k` variables: each monomial `m` is
    counted with weight `d - |m|`, the degree still available to the parameters.  Counted
    directly as exponent vectors, in the same concrete style as `monoCount`. -/
def wtCount (d k : ℕ) : ℕ :=
  ∑ m ∈ (Finset.univ : Finset (Fin k → Fin (d + 1))).filter (fun m => ∑ i, (m i : ℕ) ≤ d),
    (d - ∑ i, (m i : ℕ))

/-- The weighted count never exceeds the crude count `d * M` of `Obstruction.lean`: the weighted
    bound is a refinement of the published one, not a different claim. -/
theorem wtCount_le_crude (d k : ℕ) : wtCount d k ≤ d * monoCount d k := by
  classical
  have h := Finset.sum_le_card_nsmul
    ((Finset.univ : Finset (Fin k → Fin (d + 1))).filter (fun m => ∑ i, (m i : ℕ) ≤ d))
    (fun m => d - ∑ i, (m i : ℕ)) d (fun m _ => Nat.sub_le _ _)
  simpa [wtCount, monoCount, smul_eq_mul, mul_comm] using h

theorem wtCount_mono {d d' k k' : ℕ} (hd : d ≤ d') (hk : k ≤ k') :
    wtCount d k ≤ wtCount d' k' := by
  classical
  rw [wtCount, wtCount]
  set S := (Finset.univ : Finset (Fin k → Fin (d + 1))).filter (fun m => ∑ i, (m i : ℕ) ≤ d)
    with hS
  set T := (Finset.univ : Finset (Fin k' → Fin (d' + 1))).filter (fun m => ∑ i, (m i : ℕ) ≤ d')
    with hT
  set φ : (Fin k → Fin (d+1)) → (Fin k' → Fin (d'+1)) :=
    fun m i => if h : (i:ℕ) < k then (⟨(m ⟨i,h⟩ : ℕ), by omega⟩ : Fin (d'+1)) else 0 with hφ
  have key : ∀ m : Fin k → Fin (d+1), ∑ i : Fin k', ((φ m i : ℕ)) = ∑ j : Fin k, ((m j : ℕ)) := by
    intro m
    set F : ℕ → ℕ := fun j => if h : j < k then (m ⟨j,h⟩ : ℕ) else 0 with hF
    have hL : ∑ i : Fin k', ((φ m i : ℕ)) = ∑ i ∈ Finset.range k', F i := by
      rw [← Fin.sum_univ_eq_sum_range F k']
      apply Finset.sum_congr rfl
      intro i _
      simp only [hφ, hF]
      rw [apply_dite Fin.val]
      simp
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
  have hφinj : ∀ m1 ∈ S, ∀ m2 ∈ S, φ m1 = φ m2 → m1 = m2 := by
    intro m1 _ m2 _ heq
    funext j
    have hj : (Fin.castLE hk j : ℕ) < k := by simpa using j.isLt
    have h2 := congrFun heq (Fin.castLE hk j)
    simp only [hφ, dif_pos hj] at h2
    apply Fin.ext
    have h3 := Fin.val_eq_of_eq h2
    simpa using h3
  have hmap : ∀ m ∈ S, φ m ∈ T := by
    intro m hm
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [key m]
    exact le_trans hm hd
  calc ∑ m ∈ S, (d - ∑ i, (m i:ℕ))
      ≤ ∑ m ∈ S, (d' - ∑ i, ((φ m) i:ℕ)) := by
        apply Finset.sum_le_sum
        intro m _
        rw [key m]
        exact Nat.sub_le_sub_right hd _
    _ = ∑ m' ∈ S.image φ, (d' - ∑ i, (m' i:ℕ)) := by
        rw [Finset.sum_image hφinj]
    _ ≤ ∑ m' ∈ T, (d' - ∑ i, (m' i:ℕ)) := by
        apply Finset.sum_le_sum_of_subset
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨m, hm, rfl⟩ := hx
        exact hmap m hm

/-- Arithmetic core, weighted form.  With a constant `A` in front, `A * N^W` is beaten by
    `(N+1)^n` at some `N ≥ 1` as soon as `n ≥ W + 1`. -/
theorem aux_arith_weighted (n W A : ℕ) (h : W + 1 ≤ n) :
    ∃ N, 1 ≤ N ∧ A * N ^ W < (N + 1) ^ n := by
  refine ⟨A + 1, by omega, ?_⟩
  have hpos : 0 < (A + 1) ^ W := Nat.one_le_pow W (A + 1) (by omega)
  calc A * (A + 1) ^ W
      < (A + 1) * (A + 1) ^ W := (Nat.mul_lt_mul_right hpos).mpr (by omega)
    _ = (A + 1) ^ (W + 1) := by rw [pow_succ]; ring
    _ ≤ (A + 1) ^ n := Nat.pow_le_pow_right (by omega) h
    _ < (A + 1 + 1) ^ n := Nat.pow_lt_pow_left (by omega) (by omega)

/-- Parameter-part degree carried by a single variable `v` with exponent `k`: `k` on the
    substituted parameters `Sum.inl i` (`i < n`), zero on the fibre variables. -/
def pval {n r : ℕ} (v : Fin (n+1) ⊕ Fin r) (k : ℕ) : ℕ :=
  match v with
  | Sum.inl i => if (i:ℕ) < n then k else 0
  | Sum.inr _ => 0

/-- On each variable, the parameter degree and the fibre degree (the total degree of `efac v k`)
    add up to the full exponent `k`. -/
theorem pval_efac {n r : ℕ} (v : Fin (n+1) ⊕ Fin r) (k : ℕ) :
    pval v k + (efac v k).sum (fun _ x => x) = k := by
  cases v with
  | inl i =>
    simp only [pval, efac]
    by_cases h : (i:ℕ) < n
    · rw [if_pos h, dif_pos h, Finsupp.sum_zero_index]; omega
    · rw [if_neg h, dif_neg h, Finsupp.sum_single_index (by rfl)]; omega
  | inr j =>
    simp only [pval, efac]
    rw [Finsupp.sum_single_index (by rfl)]; omega

/-- The total-degree map `μ ↦ μ.sum (fun _ k => k)` is additive over a finite sum of `Finsupp`s. -/
theorem deg_finset_sum {ι : Type*} {σ : Type*} (s : Finset ι) (g : ι → (σ →₀ ℕ)) :
    (∑ i ∈ s, g i).sum (fun _ k => k) = ∑ i ∈ s, (g i).sum (fun _ k => k) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x t hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ih]

/-- Weighted form of `aux_kappa_bound`: when `∑ efac = m`, the product of parameter powers is
    bounded by `N` raised to `C0.totalDegree - |m|`, not just `C0.totalDegree`. -/
theorem aux_kappa_bound_weighted {n r N : ℕ} (C0 : Poly (n+1) r) (a : Fin n → ℕ)
    (hN : ∀ i, a i ≤ N) (h1 : 1 ≤ N)
    (β : (Fin (n+1) ⊕ Fin r) →₀ ℕ) (hβ : β ∈ C0.support)
    (m : (Fin 1 ⊕ Fin r) →₀ ℕ) (hm : (∑ v ∈ β.support, efac v (β v)) = m) :
    |∏ v ∈ β.support, cfac a v (β v)| ≤ (N : ℤ) ^ (C0.totalDegree - (m.sum fun _ k => k)) := by
  rw [Finset.abs_prod]
  have step1 : ∏ v ∈ β.support, |cfac a v (β v)|
      ≤ ∏ v ∈ β.support, (N : ℤ) ^ (pval v (β v)) := by
    apply Finset.prod_le_prod
    · intro v _; exact abs_nonneg _
    · intro v _
      cases v with
      | inl i =>
        simp only [cfac, pval]
        by_cases h : (i:ℕ) < n
        · rw [dif_pos h, if_pos h, abs_pow]
          apply pow_le_pow_left₀ (abs_nonneg _)
          rw [abs_of_nonneg (by positivity)]
          exact_mod_cast hN _
        · rw [dif_neg h, if_neg h, abs_one, pow_zero]
      | inr j =>
        simp only [cfac, pval, abs_one, pow_zero]
        exact le_refl _
  have hexp : (∑ v ∈ β.support, pval v (β v))
      ≤ C0.totalDegree - (m.sum fun _ k => k) := by
    have hsum : ∑ v ∈ β.support, (pval v (β v) + (efac v (β v)).sum (fun _ x => x))
        = ∑ v ∈ β.support, β v := by
      apply Finset.sum_congr rfl; intro v _; exact pval_efac v (β v)
    rw [Finset.sum_add_distrib] at hsum
    have hdeg : ∑ v ∈ β.support, (efac v (β v)).sum (fun _ x => x)
        = m.sum (fun _ k => k) := by
      rw [← hm, deg_finset_sum]
    have htd : ∑ v ∈ β.support, β v ≤ C0.totalDegree := le_totalDegree hβ
    omega
  calc ∏ v ∈ β.support, |cfac a v (β v)|
      ≤ ∏ v ∈ β.support, (N : ℤ) ^ (pval v (β v)) := step1
    _ = (N : ℤ) ^ (∑ v ∈ β.support, pval v (β v)) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (N : ℤ) ^ (C0.totalDegree - (m.sum fun _ k => k)) :=
        pow_le_pow_right₀ (by exact_mod_cast h1) hexp

/-- GRADED COEFFICIENT BOUND.  This is the single step `Obstruction.lean` does not take:
    `aux_coeff_bound` bounds every coefficient by `K * N^d`; here the exponent drops by the
    fibre degree of the monomial. -/
theorem aux_coeff_bound_weighted {n r N : ℕ} (C0 : Poly (n + 1) r) (a : Fin n → ℕ)
    (hN : ∀ i, a i ≤ N) (h1 : 1 ≤ N) (m : (Fin 1 ⊕ Fin r) →₀ ℕ) :
    |(Phi C0 a).coeff m|
      ≤ (∑ β ∈ C0.support, |C0.coeff β|)
          * (N : ℤ) ^ (C0.totalDegree - (m.sum fun _ k => k)) := by
  have hexp : Phi C0 a
      = ∑ β ∈ C0.support, C (C0.coeff β) * (∏ v ∈ β.support, (fsub a v) ^ (β v)) := by
    rw [Phi, aeval_def, eval₂_eq, algebraMap_eq]
  rw [hexp, coeff_sum]
  have hterm : ∀ β ∈ C0.support,
      |coeff m (C (C0.coeff β) * (∏ v ∈ β.support, (fsub a v) ^ (β v)))|
        ≤ |C0.coeff β| * (N : ℤ) ^ (C0.totalDegree - (m.sum fun _ k => k)) := by
    intro β hβ
    rw [coeff_C_mul, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [aux_G_monomial, coeff_monomial]
    by_cases hν : (∑ v ∈ β.support, efac v (β v)) = m
    · rw [if_pos hν]; exact aux_kappa_bound_weighted C0 a hN h1 β hβ m hν
    · rw [if_neg hν, abs_zero]; positivity
  calc |∑ β ∈ C0.support, coeff m (C (C0.coeff β) * (∏ v ∈ β.support, (fsub a v) ^ (β v)))|
      ≤ ∑ β ∈ C0.support, |coeff m (C (C0.coeff β) * (∏ v ∈ β.support, (fsub a v) ^ (β v)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ β ∈ C0.support, |C0.coeff β| * (N : ℤ) ^ (C0.totalDegree - (m.sum fun _ k => k)) :=
        Finset.sum_le_sum hterm
    _ = (∑ β ∈ C0.support, |C0.coeff β|) * (N : ℤ) ^ (C0.totalDegree - (m.sum fun _ k => k)) := by
        rw [Finset.sum_mul]

theorem aux_coeff_nat_weighted {n r N : ℕ} (C0 : Poly (n+1) r) (a : Fin n → ℕ)
    (hN : ∀ i, a i ≤ N) (h1 : 1 ≤ N) (m : (Fin 1 ⊕ Fin r) →₀ ℕ) :
    ((Phi C0 a).coeff m).natAbs
      ≤ (∑ β ∈ C0.support, (C0.coeff β).natAbs)
          * N ^ (C0.totalDegree - (m.sum fun _ k => k)) := by
  have hb := aux_coeff_bound_weighted C0 a hN h1 m
  rw [Int.abs_eq_natAbs] at hb
  have hrhs : (∑ β ∈ C0.support, |C0.coeff β|)
        * (N : ℤ) ^ (C0.totalDegree - (m.sum fun _ k => k))
      = (((∑ β ∈ C0.support, (C0.coeff β).natAbs)
          * N ^ (C0.totalDegree - (m.sum fun _ k => k)) : ℕ) : ℤ) := by
    push_cast
    simp only [Int.abs_eq_natAbs]
  rw [hrhs] at hb
  exact_mod_cast hb

/-- Box count, weighted form.  Compare `aux_counting`, whose right-hand side is
    `(2*K*N^d + 1) ^ monoCount d (r+1)`. -/
theorem aux_counting_weighted {n r : ℕ} {W : Set (Fin r → ℤ)} (C0 : Poly (n + 1) r)
    {e : (Fin n → ℕ) → ℕ} (he : Function.Injective e)
    (hC : RepresentsIn W C0 (graph e)) (N : ℕ) (h1 : 1 ≤ N) :
    (N + 1) ^ n
      ≤ (2 * (∑ β ∈ C0.support, (C0.coeff β).natAbs) + 1) ^ (monoCount C0.totalDegree (r + 1))
          * N ^ (wtCount C0.totalDegree (r + 1)) := by
  classical
  set d := C0.totalDegree with hd
  set Knat := ∑ β ∈ C0.support, (C0.coeff β).natAbs with hK
  let P : (Fin (r+1) → Fin (d+1)) → Prop := fun idx => ∑ i, (idx i : ℕ) ≤ d
  let B0 : {idx : Fin (r+1) → Fin (d+1) // P idx} → ℕ :=
    fun s => Knat * N ^ (d - ∑ i, (s.1 i : ℕ))
  -- degree of the monomial attached to s
  have hsumfull : ∀ (m : (Fin 1 ⊕ Fin r) →₀ ℕ),
      ∑ i : Fin (r+1), m ((e2 r).symm i) = ∑ w ∈ m.support, m w := by
    intro m
    rw [Equiv.sum_comp (e2 r).symm (fun v => m v)]
    rw [← Finset.sum_subset (Finset.subset_univ m.support)]
    intro w _ hw
    exact Finsupp.notMem_support_iff.1 hw
  have hdegm : ∀ s : {idx : Fin (r+1) → Fin (d+1) // P idx},
      (muMon (fun i => (s.1 i : ℕ))).sum (fun _ k => k) = ∑ i, (s.1 i : ℕ) := by
    intro s
    have h0 : (muMon (fun i => (s.1 i : ℕ))).sum (fun _ k => k)
        = ∑ w ∈ (muMon (fun i => (s.1 i : ℕ))).support, (muMon (fun i => (s.1 i : ℕ))) w := rfl
    rw [h0, ← hsumfull (muMon (fun i => (s.1 i : ℕ)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [muMon_apply]
    simp
  -- coefficient two-sided bound, in terms of B0
  have habs : ∀ (a' : Fin n → ℕ), (∀ i, a' i ≤ N) →
      ∀ s : {idx : Fin (r+1) → Fin (d+1) // P idx},
        -((B0 s : ℤ)) ≤ (Phi C0 a').coeff (muMon (fun i => (s.1 i : ℕ)))
          ∧ (Phi C0 a').coeff (muMon (fun i => (s.1 i : ℕ))) ≤ (B0 s : ℤ) := by
    intro a' ha' s
    have hcb := aux_coeff_nat_weighted C0 a' ha' h1 (muMon (fun i => (s.1 i : ℕ)))
    rw [← hd, ← hK, hdegm s] at hcb
    have hcbz : (((Phi C0 a').coeff (muMon (fun i => (s.1 i : ℕ)))).natAbs : ℤ) ≤ (B0 s : ℤ) := by
      exact_mod_cast hcb
    have h1' := Int.le_natAbs (a := (Phi C0 a').coeff (muMon (fun i => (s.1 i : ℕ))))
    have h2' := Int.le_natAbs (a := -((Phi C0 a').coeff (muMon (fun i => (s.1 i : ℕ)))))
    rw [Int.natAbs_neg] at h2'
    omega
  -- entry / degree bound helper
  have hentry : ∀ (m : (Fin 1 ⊕ Fin r) →₀ ℕ) (v : Fin 1 ⊕ Fin r),
      m v ≤ ∑ w ∈ m.support, m w := by
    intro m v
    by_cases hv : v ∈ m.support
    · exact Finset.single_le_sum (by intro w _; exact Nat.zero_le _) hv
    · rw [Finsupp.notMem_support_iff.1 hv]; exact Nat.zero_le _
  -- define f
  let a : (Fin n → Fin (N+1)) → (Fin n → ℕ) := fun g i => (g i : ℕ)
  have haN : ∀ g i, a g i ≤ N := by intro g i; exact Nat.lt_succ_iff.1 (g i).isLt
  let f : (Fin n → Fin (N+1)) →
      ((s : {idx : Fin (r+1) → Fin (d+1) // P idx}) → Fin (2 * B0 s + 1)) :=
    fun g s => ⟨((Phi C0 (a g)).coeff (muMon (fun i => (s.1 i : ℕ))) + (B0 s : ℤ)).toNat, by
      rw [Int.toNat_lt' (by omega)]
      have hb := (habs (a g) (haN g) s).2
      have hcast : (((2 * B0 s + 1 : ℕ)) : ℤ) = 2 * (B0 s : ℤ) + 1 := by push_cast; ring
      rw [hcast]; omega⟩
  have hinj : Function.Injective f := by
    intro g g' hgg
    have hcoeff : ∀ s : {idx : Fin (r+1) → Fin (d+1) // P idx},
        (Phi C0 (a g)).coeff (muMon (fun i => (s.1 i : ℕ)))
          = (Phi C0 (a g')).coeff (muMon (fun i => (s.1 i : ℕ))) := by
      intro s
      have hcong := congrFun hgg s
      simp only [f] at hcong
      have hv := Fin.val_eq_of_eq hcong
      have hb1 := (habs (a g) (haN g) s).1
      have hb2 := (habs (a g') (haN g') s).1
      have hnn1 : 0 ≤ (Phi C0 (a g)).coeff (muMon (fun i => (s.1 i : ℕ))) + (B0 s : ℤ) := by omega
      have hnn2 : 0 ≤ (Phi C0 (a g')).coeff (muMon (fun i => (s.1 i : ℕ))) + (B0 s : ℤ) := by omega
      have heqz : (Phi C0 (a g)).coeff (muMon (fun i => (s.1 i : ℕ))) + (B0 s : ℤ)
          = (Phi C0 (a g')).coeff (muMon (fun i => (s.1 i : ℕ))) + (B0 s : ℤ) := by
        rw [← Int.toNat_of_nonneg hnn1, ← Int.toNat_of_nonneg hnn2]
        exact_mod_cast hv
      omega
    have hPhi : Phi C0 (a g) = Phi C0 (a g') := by
      ext m
      by_cases hdeg : ∑ w ∈ m.support, m w ≤ d
      · have hlt : ∀ i : Fin (r+1), m ((e2 r).symm i) < d + 1 := by
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
  have hcardC : Fintype.card ((s : {idx : Fin (r+1) → Fin (d+1) // P idx}) → Fin (2 * B0 s + 1))
      = ∏ s : {idx : Fin (r+1) → Fin (d+1) // P idx}, (2 * B0 s + 1) := by
    rw [Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro s _
    rw [Fintype.card_fin]
  have hfin := Fintype.card_le_of_injective f hinj
  rw [hcardD, hcardC] at hfin
  -- product bound
  have hcardCard : Fintype.card {idx : Fin (r+1) → Fin (d+1) // P idx} = monoCount d (r+1) := by
    rw [Fintype.card_subtype]; rfl
  have hwtsum : (∑ s : {idx : Fin (r+1) → Fin (d+1) // P idx}, (d - ∑ i, ((s.1 i : ℕ))))
      = wtCount d (r+1) := by
    rw [wtCount]
    refine (Finset.sum_subtype
      ((Finset.univ : Finset (Fin (r+1) → Fin (d+1))).filter (fun m => ∑ i, (m i : ℕ) ≤ d))
      (fun x => ?_) (fun idx : Fin (r+1) → Fin (d+1) => d - ∑ i, (idx i : ℕ))).symm
    simp [P, Finset.mem_filter]
  have hprodbound : (∏ s : {idx : Fin (r+1) → Fin (d+1) // P idx}, (2 * B0 s + 1))
      ≤ (2 * Knat + 1) ^ (monoCount d (r + 1)) * N ^ (wtCount d (r + 1)) := by
    calc ∏ s : {idx : Fin (r+1) → Fin (d+1) // P idx}, (2 * B0 s + 1)
        ≤ ∏ s : {idx : Fin (r+1) → Fin (d+1) // P idx},
            ((2 * Knat + 1) * N ^ (d - ∑ i, ((s.1 i : ℕ)))) := by
          apply Finset.prod_le_prod'
          intro s _
          show 2 * (Knat * N ^ (d - ∑ i, (s.1 i : ℕ))) + 1
              ≤ (2 * Knat + 1) * N ^ (d - ∑ i, (s.1 i : ℕ))
          have hexp : (2 * Knat + 1) * N ^ (d - ∑ i, (s.1 i : ℕ))
              = 2 * (Knat * N ^ (d - ∑ i, (s.1 i : ℕ))) + N ^ (d - ∑ i, (s.1 i : ℕ)) := by ring
          rw [hexp]
          have hp : 1 ≤ N ^ (d - ∑ i, (s.1 i : ℕ)) := Nat.one_le_pow _ _ (by omega)
          omega
      _ = (∏ s : {idx : Fin (r+1) → Fin (d+1) // P idx}, (2 * Knat + 1))
            * ∏ s : {idx : Fin (r+1) → Fin (d+1) // P idx}, N ^ (d - ∑ i, ((s.1 i : ℕ))) :=
          Finset.prod_mul_distrib
      _ = (2 * Knat + 1) ^ (Fintype.card {idx : Fin (r+1) → Fin (d+1) // P idx})
            * N ^ (∑ s : {idx : Fin (r+1) → Fin (d+1) // P idx}, (d - ∑ i, ((s.1 i : ℕ)))) := by
          rw [Finset.prod_const, Finset.prod_pow_eq_pow_sum, Finset.card_univ]
      _ = (2 * Knat + 1) ^ (monoCount d (r + 1)) * N ^ (wtCount d (r + 1)) := by
          rw [hcardCard, hwtsum]
  exact le_trans hfin hprodbound

/-- THE WEIGHTED COUNTING BOUND.  Refines `coder_counting_bound`. -/
theorem coder_counting_bound_weighted {n r : ℕ} (W : Set (Fin r → ℤ)) (C : Poly (n + 1) r)
    (e : (Fin n → ℕ) → ℕ) (he : Function.Injective e) (hC : RepresentsIn W C (graph e)) :
    n ≤ wtCount C.totalDegree (r + 1) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨N, hN1, hlt⟩ := aux_arith_weighted n (wtCount C.totalDegree (r + 1))
    ((2 * (∑ β ∈ C.support, (C.coeff β).natAbs) + 1) ^ (monoCount C.totalDegree (r + 1)))
    (by omega)
  have hcount := aux_counting_weighted C he hC N hN1
  exact absurd hcount (not_le.2 hlt)

/-- Quantitative obstruction in weighted form, ℕ-unknowns.  This is the statement Appendix C
    prints; with `wtCount d k = (d+k).choose (k+1)` it reads
    `p - 1 ≤ (δ(p) + ν(p) + 1).choose (ν(p) + 2)` at `p = n + 1`. -/
theorem multiUniversalN_bound_weighted {ν δ : ℕ → ℕ} (h : MultiUniversalN ν δ) (n : ℕ) :
    n ≤ wtCount (δ (n + 1)) (ν (n + 1) + 1) := by
  obtain ⟨r', hr', C, hCd, hC⟩ := h (n + 1) _ (diophN_graph_code n)
  have h1 := coder_counting_bound_weighted _ C code (code_injective n)
    ((representsN_iff_representsIn C _).1 hC)
  have h2 : wtCount C.totalDegree (r' + 1) ≤ wtCount (δ (n + 1)) (ν (n + 1) + 1) :=
    wtCount_mono hCd (by omega)
  omega

/-- Quantitative obstruction in weighted form, ℤ-unknowns. -/
theorem multiUniversalZ_bound_weighted {ν δ : ℕ → ℕ} (h : MultiUniversalZ ν δ) (n : ℕ) :
    n ≤ wtCount (δ (n + 1)) (ν (n + 1) + 1) := by
  obtain ⟨r', hr', C, hCd, hC⟩ := h (n + 1) _ (diophN_graph_code n)
  have h1 := coder_counting_bound_weighted _ C code (code_injective n)
    ((representsZ_iff_representsIn C _).1 hC)
  have h2 : wtCount C.totalDegree (r' + 1) ≤ wtCount (δ (n + 1)) (ν (n + 1) + 1) :=
    wtCount_mono hCd (by omega)
  omega

/-- Sanity: the weighted bound still kills the constant case, so nothing is lost. -/
theorem not_MPUP_N_of_weighted_bound : ¬ MPUP_N := by
  rintro ⟨ν, δ, h⟩
  have := multiUniversalN_bound_weighted h (wtCount δ (ν + 1) + 1)
  omega

theorem monoCount_widen {e d k : ℕ} (h : e ≤ d) :
    ((Finset.univ : Finset (Fin k → Fin (d + 1))).filter
      (fun m => ∑ i, (m i : ℕ) ≤ e)).card = monoCount e k := by
  classical
  rw [monoCount]
  refine Finset.card_nbij'
    (fun m => fun i => (⟨min (m i : ℕ) e, by omega⟩ : Fin (e + 1)))
    (fun m => fun i => (⟨(m i : ℕ), by have := (m i).isLt; omega⟩ : Fin (d + 1)))
    ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm ⊢
    have hle : ∀ i, (m i : ℕ) ≤ e := by
      intro i
      have := Finset.single_le_sum (f := fun j => ((m j : ℕ))) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
      omega
    have : ∀ i, min (m i : ℕ) e = (m i : ℕ) := fun i => Nat.min_eq_left (hle i)
    simpa [this] using hm
  · intro m hm
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm ⊢
    simpa using hm
  · intro m hm
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm
    funext i
    have hle : (m i : ℕ) ≤ e := by
      have := Finset.single_le_sum (f := fun j => ((m j : ℕ))) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
      omega
    exact Fin.ext (by simpa using Nat.min_eq_left hle)
  · intro m hm
    funext i
    have := (m i).isLt
    exact Fin.ext (by simp; omega)

theorem monoCount_succ_right (d k : ℕ) :
    monoCount d (k + 1) = ∑ t ∈ Finset.range (d + 1), monoCount (d - t) k := by
  classical
  have hmaps : Set.MapsTo (fun m : Fin (k + 1) → Fin (d + 1) => ((m 0 : ℕ)))
      ↑((Finset.univ : Finset (Fin (k + 1) → Fin (d + 1))).filter
          (fun m => ∑ i, (m i : ℕ) ≤ d)) ↑(Finset.range (d + 1)) := by
    intro m _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact (m 0).isLt
  rw [monoCount, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl ?_
  intro t ht
  have ht' : t < d + 1 := Finset.mem_range.1 ht
  rw [← monoCount_widen (e := d - t) (d := d) (k := k) (by omega)]
  refine Finset.card_nbij'
    (fun m => fun i : Fin k => m i.succ)
    (fun m => (Fin.cons (⟨t, ht'⟩ : Fin (d + 1)) m : Fin (k + 1) → Fin (d + 1)))
    ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    obtain ⟨hs, h0⟩ := hm
    have hs' : ∑ i, ((m i : ℕ)) ≤ d := hs
    have h0' : ((m 0 : ℕ)) = t := h0
    have hsplit : ∑ i, ((m i : ℕ)) = ((m 0 : ℕ)) + ∑ i : Fin k, ((m i.succ : ℕ)) :=
      Fin.sum_univ_succ (fun i => ((m i : ℕ)))
    omega
  · intro m hm
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    set M : Fin (k + 1) → Fin (d + 1) := Fin.cons (⟨t, ht'⟩ : Fin (d + 1)) m with hM
    have hM0 : ((M 0 : ℕ)) = t := by simp [hM]
    have hMs : ∀ i : Fin k, ((M i.succ : ℕ)) = ((m i : ℕ)) := by
      intro i; simp [hM]
    have hsplit : ∑ i, ((M i : ℕ)) = ((M 0 : ℕ)) + ∑ i : Fin k, ((M i.succ : ℕ)) :=
      Fin.sum_univ_succ (fun i => ((M i : ℕ)))
    have hsum : ∑ i : Fin k, ((M i.succ : ℕ)) = ∑ i : Fin k, ((m i : ℕ)) :=
      Finset.sum_congr rfl (fun i _ => hMs i)
    refine ⟨?_, hM0⟩
    rw [hsplit, hM0, hsum]
    omega
  · intro m hm
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    obtain ⟨_, h0⟩ := hm
    have h0' : (⟨t, ht'⟩ : Fin (d + 1)) = m 0 := Fin.ext (by simpa using h0.symm)
    show (Fin.cons (⟨t, ht'⟩ : Fin (d + 1)) (fun i : Fin k => m i.succ)
        : Fin (k + 1) → Fin (d + 1)) = m
    rw [h0']
    exact Fin.cons_self_tail m
  · intro m _
    funext i
    simp

theorem monoCount_closed_form (d k : ℕ) : monoCount d k = (d + k).choose k := by
  induction k generalizing d with
  | zero =>
      simp [monoCount]
  | succ k ih =>
      rw [monoCount_succ_right]
      have h1 : ∀ t ∈ Finset.range (d + 1), monoCount (d - t) k = ((d - t) + k).choose k :=
        fun t _ => ih (d - t)
      rw [Finset.sum_congr rfl h1]
      have h2 := Finset.sum_range_reflect (fun j => ((j + k).choose k)) (d + 1)
      simp only [Nat.add_sub_cancel] at h2
      rw [h2, Nat.sum_range_add_choose d k]
      ring_nf

theorem wtCount_eq_sum_monoCount (d k : ℕ) :
    wtCount d k = ∑ e ∈ Finset.range d, monoCount e k := by
  classical
  rw [wtCount]
  have step : ∀ m : Fin k → Fin (d + 1),
      (d - ∑ i, (m i : ℕ)) = ∑ e ∈ Finset.range d, (if ∑ i, (m i : ℕ) ≤ e then 1 else 0) := by
    intro m
    have : (Finset.range d).filter (fun e => ∑ i, (m i : ℕ) ≤ e)
        = Finset.Ico (∑ i, (m i : ℕ)) d := by
      ext e; simp [Finset.mem_filter, Finset.mem_Ico, and_comm]
    have hc := congrArg Finset.card this
    rw [Nat.card_Ico] at hc
    rw [← hc, Finset.card_filter]
  rw [Finset.sum_congr rfl (fun m _ => step m)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro e he
  have hed : e ≤ d := by have := Finset.mem_range.1 he; omega
  rw [← monoCount_widen (e := e) (d := d) (k := k) hed]
  rw [← Finset.card_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, h2⟩; exact h2
  · intro h2; exact ⟨by omega, h2⟩

theorem wtCount_closed_form (d k : ℕ) : wtCount d k = (d + k).choose (k + 1) := by
  rw [wtCount_eq_sum_monoCount]
  rw [Finset.sum_congr rfl (fun e _ => monoCount_closed_form e k)]
  cases d with
  | zero => simp
  | succ D =>
      rw [Nat.sum_range_add_choose D k]
      ring_nf

theorem not_MPUP_Z_of_weighted_bound : ¬ MPUP_Z := by
  rintro ⟨ν, δ, h⟩
  have := multiUniversalZ_bound_weighted h (wtCount δ (ν + 1) + 1)
  omega

end MPUP
