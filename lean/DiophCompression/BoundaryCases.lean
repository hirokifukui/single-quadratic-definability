/-
  DiophCompression/BoundaryCases.lean — r04 Task 8 second target (session 4, 2026-08-26, claude.ai direct).
  G_R(0, d) = d for d ≥ 1.
  Upper bound is SEMANTIC (not from specialization counting, which only gives C(d+1,2)): with no
  witnesses, P(a, c) = 0 has the unique natural root c = e(a); the univariate polynomial P(a, ·) is
  neither zero nor a nonzero constant, its coefficients are ≤ K·N^d on the box, and an integer root
  of Σ_{k≤m} g_k c^k with g_m ≠ 0, m ≥ 1 satisfies c ≤ (max|g_k|)·m. Hence e(a) ≤ K·d·N^d and box
  counting gives n ≤ d.  Lower bound: c = d!·skolem(a), degree d, no witness.
-/
import MPUP.Obstruction
import DiophCompression.Definitions
import DiophCompression.BoxCounting
import DiophCompression.SkolemTupling

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Elementary integer root bound -/

/-- If Σ_{k<m+1} g_k c^k = 0 with |g_k| ≤ M, g_m ≠ 0 (m ≥ 1), and c ∈ ℕ, then c ≤ M·m. -/
theorem nat_root_bound (g : ℕ → ℤ) (m M : ℕ) (hm : 1 ≤ m) (hM : ∀ k ≤ m, |g k| ≤ M)
    (hlead : g m ≠ 0) (c : ℕ) (hroot : ∑ k ∈ Finset.range (m + 1), g k * (c : ℤ) ^ k = 0) :
    c ≤ M * m := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; exact Nat.zero_le _
  -- isolate the leading term
  rw [Finset.sum_range_succ] at hroot
  have hlead' : (1 : ℤ) ≤ |g m| := by
    have := abs_pos.2 hlead; omega
  have hcm : ((c : ℤ) ^ m) ≤ |g m * (c : ℤ) ^ m| := by
    rw [abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ (c : ℤ) ^ m by positivity)]
    exact le_mul_of_one_le_left (by positivity) hlead'
  have hsum : |g m * (c : ℤ) ^ m| = |∑ k ∈ Finset.range m, g k * (c : ℤ) ^ k| := by
    rw [show g m * (c : ℤ) ^ m = -(∑ k ∈ Finset.range m, g k * (c : ℤ) ^ k) by linarith, abs_neg]
  have hbound : |∑ k ∈ Finset.range m, g k * (c : ℤ) ^ k| ≤ (M : ℤ) * m * (c : ℤ) ^ (m - 1) := by
    calc |∑ k ∈ Finset.range m, g k * (c : ℤ) ^ k|
        ≤ ∑ k ∈ Finset.range m, |g k * (c : ℤ) ^ k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range m, (M : ℤ) * (c : ℤ) ^ (m - 1) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_range] at hk
          rw [abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ (c : ℤ) ^ k by positivity)]
          exact mul_le_mul (hM k (by omega))
            (pow_le_pow_right₀ (by exact_mod_cast hc) (by omega)) (by positivity) (by positivity)
      _ = (M : ℤ) * m * (c : ℤ) ^ (m - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hfinal : (c : ℤ) ^ m ≤ (M : ℤ) * m * (c : ℤ) ^ (m - 1) := by
    calc (c : ℤ) ^ m ≤ |g m * (c : ℤ) ^ m| := hcm
      _ = _ := hsum
      _ ≤ _ := hbound
  have hpow : (c : ℤ) ^ m = (c : ℤ) * (c : ℤ) ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow] at hfinal
  have hpos : (0 : ℤ) < (c : ℤ) ^ (m - 1) := pow_pos (by exact_mod_cast hc) _
  have : (c : ℤ) ≤ (M : ℤ) * m := le_of_mul_le_mul_right (by linarith) hpos
  exact_mod_cast this

/-! ### Univariate reduction of the witness-free specialization -/

theorem finsupp_eq_single (m : (Fin 1 ⊕ Fin 0) →₀ ℕ) :
    m = Finsupp.single (Sum.inl 0) (m (Sum.inl 0)) := by
  ext v
  cases v with
  | inl i =>
    have : i = 0 := Subsingleton.elim _ _
    subst this; simp
  | inr j => exact j.elim0

/-- Coefficient sequence of the witness-free specialization. -/
noncomputable def ucoeff {n : ℕ} (C0 : Poly (n + 1) 0) (a : Fin n → ℕ) (k : ℕ) : ℤ :=
  coeff (Finsupp.single (Sum.inl 0) k) (Phi C0 a)

theorem phi_eq_sum {n : ℕ} (C0 : Poly (n + 1) 0) {d : ℕ} (hd : C0.totalDegree ≤ d)
    (a : Fin n → ℕ) :
    Phi C0 a = ∑ k ∈ Finset.range (d + 1), monomial (Finsupp.single (Sum.inl 0) k) (ucoeff C0 a k) := by
  classical
  ext m
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases hk : m (Sum.inl 0) ≤ d
  · have hsingle : ∀ k ∈ Finset.range (d + 1),
        (if Finsupp.single (Sum.inl 0) k = m then ucoeff C0 a k else 0)
          = if k = m (Sum.inl 0) then ucoeff C0 a k else 0 := by
      intro k _
      congr 1
      apply propext
      constructor
      · intro h; rw [← h]; simp
      · intro h; rw [h]; exact (finsupp_eq_single m).symm
    rw [Finset.sum_congr rfl hsingle, Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_range.2 (by omega))]
    unfold ucoeff; rw [← finsupp_eq_single m]
  · push Not at hk
    have hzero : coeff m (Phi C0 a) = 0 := by
      apply coeff_eq_zero_of_totalDegree_lt
      have h1 : (aux_Phi_totalDegree C0 a) = (aux_Phi_totalDegree C0 a) := rfl
      have hdeg := aux_Phi_totalDegree C0 a
      have hm : m (Sum.inl 0) ≤ ∑ i ∈ m.support, m i := by
        by_cases hmem : Sum.inl 0 ∈ m.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
        · rw [Finsupp.notMem_support_iff.1 hmem]; exact Nat.zero_le _
      omega
    rw [hzero]
    symm
    apply Finset.sum_eq_zero
    intro k hk'
    rw [Finset.mem_range] at hk'
    rw [if_neg]
    intro h
    have := congrArg (fun f => f (Sum.inl 0)) h
    simp at this
    omega

theorem evalAt_eq_sum {n : ℕ} (C0 : Poly (n + 1) 0) {d : ℕ} (hd : C0.totalDegree ≤ d)
    (a : Fin n → ℕ) (c : ℕ) (y : Fin 0 → ℤ) :
    evalAt C0 (Fin.snoc a c) y
      = ∑ k ∈ Finset.range (d + 1), ucoeff C0 a k * (c : ℤ) ^ k := by
  rw [aux_L1 C0 a c y, phi_eq_sum C0 hd a, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [eval_monomial, Finsupp.prod_single_index (by simp)]
  simp

/-! ### Upper bound G(0, d) ≤ d -/

theorem graph_no_witness_le {n d : ℕ} (h : GraphAchievableN n 0 d) : n ≤ d := by
  classical
  obtain ⟨e, he, r', hr', C0, hC0d, hrep⟩ := h
  have hr0 : r' = 0 := by omega
  subst hr0
  -- root characterisation: c = e a ↔ Σ ucoeff C0 a k c^k = 0
  have hchar : ∀ (a : Fin n → ℕ) (c : ℕ),
      c = e a ↔ ∑ k ∈ Finset.range (d + 1), ucoeff C0 a k * (c : ℤ) ^ k = 0 := by
    intro a c
    have h1 := hrep (Fin.snoc a c)
    have hmem : ((Fin.snoc a c : Fin (n + 1) → ℕ) ∈ graph e) ↔ c = e a := by
      show (Fin.snoc a c : Fin (n + 1) → ℕ) (Fin.last n)
          = e (Fin.init (Fin.snoc a c : Fin (n + 1) → ℕ)) ↔ c = e a
      rw [Fin.snoc_last, Fin.init_snoc]
    rw [hmem] at h1
    rw [h1]
    constructor
    · rintro ⟨y, hy⟩; rw [← evalAt_eq_sum C0 hC0d a c (fun i => (y i : ℤ))]; exact hy
    · intro hz; exact ⟨Fin.elim0, by rw [evalAt_eq_sum C0 hC0d a c]; exact hz⟩
  -- coefficient bound on the box
  set K : ℕ := ∑ β ∈ C0.support, (C0.coeff β).natAbs with hK
  have hcoef : ∀ N, 1 ≤ N → ∀ a : Fin n → ℕ, (∀ i, a i ≤ N) → ∀ k, |ucoeff C0 a k| ≤ (K : ℤ) * (N : ℤ) ^ d := by
    intro N h1 a ha k
    have hb := aux_coeff_bound C0 a ha h1 (Finsupp.single (Sum.inl 0) k)
    have hKz : (∑ β ∈ C0.support, |C0.coeff β|) = (K : ℤ) := by
      simp only [hK, Nat.cast_sum, Int.natCast_natAbs]
    rw [hKz] at hb
    calc |ucoeff C0 a k| ≤ (K : ℤ) * (N : ℤ) ^ C0.totalDegree := hb
      _ ≤ (K : ℤ) * (N : ℤ) ^ d :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by exact_mod_cast h1) hC0d) (by positivity)
  -- the univariate polynomial has a nonzero coefficient in degree ≥ 1
  have hnontriv : ∀ a : Fin n → ℕ, ∃ k, 1 ≤ k ∧ k ≤ d ∧ ucoeff C0 a k ≠ 0 := by
    intro a
    by_contra hcon
    push Not at hcon
    have hconst : ∀ c : ℕ, ∑ k ∈ Finset.range (d + 1), ucoeff C0 a k * (c : ℤ) ^ k = ucoeff C0 a 0 := by
      intro c
      rw [Finset.sum_range_succ' (fun k => ucoeff C0 a k * (c : ℤ) ^ k)]
      simp only [pow_zero, mul_one]
      rw [Finset.sum_eq_zero]
      · simp
      · intro k hk; rw [Finset.mem_range] at hk; rw [hcon (k + 1) (by omega) (by omega)]; ring
    have h0 : ucoeff C0 a 0 = 0 := by
      have := (hchar a (e a)).1 rfl; rw [hconst] at this; exact this
    have h2 : e a + 1 = e a := (hchar a (e a + 1)).2 (by rw [hconst, h0])
    omega
  -- e a ≤ K d N^d on the box
  have hbox : ∀ N, 1 ≤ N → ∀ a : Fin n → ℕ, (∀ i, a i ≤ N) → e a ≤ K * N ^ d * d := by
    intro N h1 a ha
    obtain ⟨k0, hk1, hkd, hk0⟩ := hnontriv a
    -- largest nonzero index
    let S := (Finset.range (d + 1)).filter (fun k => 1 ≤ k ∧ ucoeff C0 a k ≠ 0)
    have hSne : S.Nonempty :=
      ⟨k0, by simp only [S, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hk1, hk0⟩⟩
    obtain ⟨m, hm⟩ : ∃ m, m = S.max' hSne := ⟨_, rfl⟩
    have hmS : m ∈ S := by rw [hm]; exact Finset.max'_mem S hSne
    simp only [S, Finset.mem_filter, Finset.mem_range] at hmS
    have hupper : ∀ k, m < k → k ≤ d → ucoeff C0 a k = 0 := by
      intro k hmk hkd
      by_contra hne
      have hkS : k ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by omega, hne⟩
      have := Finset.le_max' S k hkS
      rw [← hm] at this
      omega
    have hroot := (hchar a (e a)).1 rfl
    have hroot' : ∑ k ∈ Finset.range (m + 1), ucoeff C0 a k * ((e a : ℕ) : ℤ) ^ k = 0 := by
      rw [← hroot]
      apply Finset.sum_subset
      · intro k hk; rw [Finset.mem_range] at hk ⊢; omega
      · intro k hk hk'
        rw [Finset.mem_range] at hk hk'
        rw [hupper k (by omega) (by omega)]; ring
    have hM : ∀ k ≤ m, |ucoeff C0 a k| ≤ ((K * N ^ d : ℕ) : ℤ) := by
      intro k _; push_cast; exact hcoef N h1 a ha k
    have := nat_root_bound (ucoeff C0 a) m (K * N ^ d) hmS.2.1 hM hmS.2.2 (e a) hroot'
    calc e a ≤ K * N ^ d * m := this
      _ ≤ K * N ^ d * d := Nat.mul_le_mul_left _ (by omega)
  -- box counting with one coordinate of degree d
  have hbc := box_counting_bound (ι := Fin 1) (fun a _ => ((e a : ℕ) : ℤ)) ?_ (fun _ => d) (K * d) ?_
  · simpa using hbc
  · intro a a' h
    have h0 := congrFun h 0
    simp only at h0
    exact he (by exact_mod_cast h0)
  · intro N h1 a ha j
    have := hbox N h1 a ha
    rw [abs_of_nonneg (by positivity)]
    have : ((e a : ℕ) : ℤ) ≤ ((K * N ^ d * d : ℕ) : ℤ) := by exact_mod_cast this
    calc ((e a : ℕ) : ℤ) ≤ ((K * N ^ d * d : ℕ) : ℤ) := this
      _ = ((K * d : ℕ) : ℤ) * (N : ℤ) ^ d := by push_cast; ring

/-! ### Lower bound G(0, d) ≥ d (d ≥ 1): c = d!·skolem(a), no witness. -/

theorem graph_no_witness_achievable (d : ℕ) (hd : 1 ≤ d) : GraphAchievableN d 0 d := by
  refine ⟨fun a => d.factorial * skolem a, ?_, 0, le_rfl,
    X (Sum.inl (Fin.last d)) - rename (Sum.inl ∘ Fin.castSucc) (skolemPoly d), ?_, ?_⟩
  · intro a a' h
    exact skolem_injective (Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos d) h)
  · refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
    · rw [totalDegree_X]; exact hd
    · exact le_trans (totalDegree_rename_le _ _) (skolemPoly_totalDegree d)
  · intro v
    have hev : ∀ y : Fin 0 → ℤ, evalAt (X (Sum.inl (Fin.last d)) - rename (Sum.inl ∘ Fin.castSucc) (skolemPoly d)) v y
        = (v (Fin.last d) : ℤ) - ((d.factorial * skolem (Fin.init v) : ℕ) : ℤ) := by
      intro y
      unfold evalAt
      rw [map_sub, eval_X, eval_rename]
      simp only [Sum.elim_inl]
      congr 1
      have : ((Sum.elim (fun i => ((v i : ℕ) : ℤ)) y) ∘ (Sum.inl ∘ Fin.castSucc) : Fin d → ℤ)
          = fun i => ((Fin.init v i : ℕ) : ℤ) := rfl
      rw [this, eval_skolemPoly]
    constructor
    · intro hv
      have hv' : v (Fin.last d) = d.factorial * skolem (Fin.init v) := hv
      exact ⟨Fin.elim0, by rw [hev, hv']; ring⟩
    · rintro ⟨y, hy⟩
      rw [hev] at hy
      show v (Fin.last d) = d.factorial * skolem (Fin.init v)
      omega

/-- EXACT BOUNDARY CASE (Task 8 second target): G_ℕ(0, d) = d for d ≥ 1. -/
theorem graph_no_witness_exact (d : ℕ) (hd : 1 ≤ d) :
    (∀ n, GraphAchievableN n 0 d → n ≤ d) ∧ GraphAchievableN d 0 d :=
  ⟨fun _ h => graph_no_witness_le h, graph_no_witness_achievable d hd⟩

end DiophCompression

#print axioms DiophCompression.nat_root_bound
#print axioms DiophCompression.graph_no_witness_le
#print axioms DiophCompression.graph_no_witness_achievable
#print axioms DiophCompression.graph_no_witness_exact
