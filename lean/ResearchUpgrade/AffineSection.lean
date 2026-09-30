/-
  AffineSection.lean — s55.  R43 A3–A4 (GATE25 #67): integer affine sections and the integer
  affine form of the low-rank normal form.

  * Bridges (any datum): `weakIntAffine_of_section` (an integer affine family of solutions over a
    coset, plus `Defines f`), `weakIntAffine_of_affineCoset` (a rational affine law of an
    integer-valued map has integer constant and slope), `quadForm_zero_of_linearGrowth` (a rational
    quadratic polynomial of at most linear growth on the lattice has zero quadratic FORM),
    `weakIntAffine_of_weakNF_linearGrowth`.
  * A3: `binary_baseSection` — positive definite in two output/unknown coordinates, total: through
    the GIVEN solution `z0` at the GIVEN input `a0` with positive residual, an integer affine family
    of solutions on `a0 + Mℤⁿ` (output-uniqueness not assumed); `zeroResidual_section` — residual
    zero at every input: the centre is an integer affine solution family;
    `weakIntAffineCosetNF_of_binary`.
  * A4: `lowRankSemidefiniteIntAffineNF_holds` — the R43 low-rank hypotheses give the weak INTEGER
    AFFINE coset NF (route: the existing weak NF plus semidefinite linear growth; `m = 0` separate).

  Not claimed: the full-residue form, or anything in polar rank at least three.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.DefiniteShell
import ResearchUpgrade.R42Completion
import ResearchUpgrade.RadicalBridge
import ResearchUpgrade.BranchSplit

namespace DiophCompression.ResearchUpgrade

open Matrix

theorem weakIntAffine_of_affineCoset {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (M : ℕ) (hM : 1 ≤ M) (ρ : Fin n → ℤ) (c : Fin m → ℚ) (L : Matrix (Fin m) (Fin n) ℚ)
    (h : ∀ (t : Fin n → ℤ) (j : Fin m), (f (ρ + (M : ℤ) • t) j : ℚ) = c j + ∑ i, L j i * (t i : ℚ)) :
    WeakIntAffineCosetNF f := by
  refine ⟨M, ρ, f ρ, Matrix.of fun j i => f (ρ + (M : ℤ) • Pi.single i (1 : ℤ)) j - f ρ j,
    hM, fun t => ?_⟩
  funext j
  apply Int.cast_injective (α := ℚ)
  have h0 : (f ρ j : ℚ) = c j := by simpa using h 0 j
  have hi : ∀ i, (f (ρ + (M : ℤ) • Pi.single i (1 : ℤ)) j : ℚ) = c j + L j i := by
    intro i
    rw [h]
    simp [Pi.single_apply]
  simp only [Pi.add_apply, cr_mulVec_apply, Matrix.of_apply]
  push_cast
  rw [h t j, h0]
  simp only [hi, add_sub_cancel_left]

theorem weakIntAffine_of_section {n m r : ℕ} {D : QuadraticGraphData n m r}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (M : ℕ) (hM : 1 ≤ M) (a0 : Fin n → ℤ) (z0 : OutWit m r → ℤ)
    (G : Matrix (OutWit m r) (Fin n) ℤ)
    (hs : ∀ t : Fin n → ℤ, D.SolZ (a0 + (M : ℤ) • t) (z0 + G *ᵥ t)) :
    WeakIntAffineCosetNF f := by
  refine ⟨M, a0, fun j => z0 (Sum.inl j), Matrix.of fun j i => G (Sum.inl j) i, hM, fun t => ?_⟩
  rw [← (hf _ _).mp (D.graph_of_solZ (hs t))]
  funext j
  rfl

theorem ac_line_zero (A B c K S : ℚ) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (h : ∀ t : ℕ, |c + B * t + A * t ^ 2| ≤ K * (1 + t * S)) : A = 0 := by
  by_contra hA
  have hAp : 0 < |A| := abs_pos.mpr hA
  set W : ℚ := K + K * S + |B| + |c| + 1 with hW
  set T : ℕ := ⌈W / |A|⌉₊ + 1 with hTdef
  have hT1 : (1 : ℚ) ≤ T := by
    have : (1 : ℕ) ≤ T := by omega
    exact_mod_cast this
  have hT0 : (0 : ℚ) ≤ T := by linarith
  have hWle : W ≤ |A| * T := by
    have h1 : W / |A| ≤ (⌈W / |A|⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : W / |A| ≤ (T : ℚ) := by
      have : ((⌈W / |A|⌉₊ : ℕ) : ℚ) ≤ T := by exact_mod_cast (by omega : ⌈W / |A|⌉₊ ≤ T)
      linarith
    rw [div_le_iff₀ hAp] at h2
    linarith
  have hb := abs_le.mp (h T)
  have hBa := abs_le.mp (le_refl |B|)
  have hca := abs_le.mp (le_refl |c|)
  have hKT : K ≤ K * T := by nlinarith
  have hcT : |c| ≤ |c| * T := by nlinarith [abs_nonneg c]
  have hBT : |B * T| = |B| * T := by rw [abs_mul, abs_of_nonneg hT0]
  have hB1 := abs_le.mp (le_of_eq hBT)
  have hWT : W * T ≤ |A| * T * T := mul_le_mul_of_nonneg_right hWle hT0
  have hST : 0 ≤ (T : ℚ) * S := mul_nonneg hT0 hS
  rcases lt_or_gt_of_ne hA with hneg | hpos
  · rw [abs_of_neg hneg] at hWT
    nlinarith [neg_abs_le B, le_abs_self B, neg_abs_le c, le_abs_self c]
  · rw [abs_of_pos hpos] at hWT
    nlinarith [neg_abs_le B, le_abs_self B, neg_abs_le c, le_abs_self c]

theorem quadForm_zero_of_linearGrowth {n : ℕ} (q : QuadForm n) (K : ℚ)
    (h : ∀ x : Fin n → ℤ, |q.eval (castQ x)| ≤ K * (1 + ∑ i, |(x i : ℚ)|)) :
    ∀ x : Fin n → ℚ, x ⬝ᵥ q.Q *ᵥ x = 0 := by
  have hK : 0 ≤ K := by
    have := h 0
    have hz : (∑ i, |((0 : Fin n → ℤ) i : ℚ)|) = 0 := by simp
    rw [hz] at this
    linarith [abs_nonneg (q.eval (castQ 0))]
  have hint : ∀ v : Fin n → ℤ, castQ v ⬝ᵥ q.Q *ᵥ castQ v = 0 := by
    intro v
    apply ac_line_zero (castQ v ⬝ᵥ q.Q *ᵥ castQ v) (q.l ⬝ᵥ castQ v) q.c K
      (∑ i, |(v i : ℚ)|) hK (Finset.sum_nonneg fun i _ => abs_nonneg _)
    intro t
    have ht := h ((t : ℤ) • v)
    have hc : castQ ((t : ℤ) • v) = (t : ℚ) • castQ v := by
      funext i; simp [castQ]
    have hs : (∑ i, |((((t : ℤ) • v) i : ℤ) : ℚ)|) = (t : ℚ) * ∑ i, |(v i : ℚ)| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [abs_mul]
    rw [hc, hs] at ht
    have he : q.eval ((t : ℚ) • castQ v)
        = q.c + (q.l ⬝ᵥ castQ v) * t + (castQ v ⬝ᵥ q.Q *ᵥ castQ v) * t ^ 2 := by
      simp only [QuadForm.eval, dotProduct_smul, smul_dotProduct, mulVec_smul, smul_eq_mul]
      ring
    rw [he] at ht
    exact ht
  intro x
  obtain ⟨M, hM, hg⟩ := cr_exists_common_den x
  choose g hg using hg
  have hx : castQ g = (M : ℚ) • x := by
    funext i; simp [castQ, hg i]
  have := hint g
  rw [hx, smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
  have hM0 : (M : ℚ) ≠ 0 := by
    have : (0 : ℚ) < M := by exact_mod_cast hM
    exact ne_of_gt this
  have h2 : (M : ℚ) * (M : ℚ) ≠ 0 := mul_ne_zero hM0 hM0
  have : (M : ℚ) * (M : ℚ) * (x ⬝ᵥ q.Q *ᵥ x) = 0 := by linarith [this]
  rcases mul_eq_zero.mp this with h3 | h3
  · exact absurd h3 h2
  · exact h3

theorem ac_supNorm_le {ι : Type*} [Fintype ι] (a : ι → ℤ) (N : ℕ) (h : ∀ i, |a i| ≤ N) :
    supNorm a ≤ N := by
  refine Finset.sup_le fun i _ => ?_
  have := h i
  have hc : |a i| = ((a i).natAbs : ℤ) := Int.abs_eq_natAbs _
  rw [hc] at this
  exact_mod_cast this

theorem weakIntAffine_of_weakNF_linearGrowth {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hNF : WeakVectorCosetNF f) (hlin : LinearGrowth f) :
    WeakIntAffineCosetNF f := by
  obtain ⟨M, ρ, q, hM, hq⟩ := hNF
  obtain ⟨Cg, hC⟩ := hlin
  set K : ℚ := (Cg : ℚ) * (1 + supNorm ρ) + (Cg : ℚ) * M with hK
  have hbound : ∀ (j : Fin m) (t : Fin n → ℤ),
      |(q j).eval (castQ t)| ≤ K * (1 + ∑ i, |(t i : ℚ)|) := by
    intro j t
    rw [← hq t j]
    have h1 : |f (ρ + (M : ℤ) • t) j| ≤ (supNorm (f (ρ + (M : ℤ) • t)) : ℤ) := abs_le_supNorm _ j
    have h2 := hC (ρ + (M : ℤ) • t)
    have h3 : supNorm (ρ + (M : ℤ) • t) ≤ supNorm ρ + M * ∑ i, (t i).natAbs := by
      apply ac_supNorm_le
      intro i
      have hr := abs_le_supNorm ρ i
      have hti : ((t i).natAbs : ℤ) ≤ ((∑ i, (t i).natAbs : ℕ) : ℤ) := by
        exact_mod_cast Finset.single_le_sum (f := fun i => (t i).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      calc |ρ i + (M : ℤ) * t i| ≤ |ρ i| + |(M : ℤ) * t i| := abs_add_le _ _
        _ = |ρ i| + (M : ℤ) * ((t i).natAbs : ℤ) := by
            rw [abs_mul, Int.abs_eq_natAbs (t i)]; simp
        _ ≤ (supNorm ρ : ℤ) + (M : ℤ) * ((∑ i, (t i).natAbs : ℕ) : ℤ) := by
            gcongr
        _ = _ := by push_cast; ring
    have hsum : ((∑ i, (t i).natAbs : ℕ) : ℚ) = ∑ i, |(t i : ℚ)| := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.cast_natAbs, Int.cast_abs]
    have h1q : |((f (ρ + (M : ℤ) • t) j : ℤ) : ℚ)| ≤ (supNorm (f (ρ + (M : ℤ) • t)) : ℚ) := by
      rw [← Int.cast_abs]; exact_mod_cast h1
    have h2q : (supNorm (f (ρ + (M : ℤ) • t)) : ℚ) ≤ (Cg : ℚ) * (1 + supNorm (ρ + (M : ℤ) • t)) := by
      exact_mod_cast h2
    have h3q : (supNorm (ρ + (M : ℤ) • t) : ℚ) ≤ supNorm ρ + M * ∑ i, |(t i : ℚ)| := by
      rw [← hsum]; exact_mod_cast h3
    have hS : 0 ≤ ∑ i, |(t i : ℚ)| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hC0 : (0 : ℚ) ≤ Cg := Nat.cast_nonneg _
    have hr0 : (0 : ℚ) ≤ supNorm ρ := Nat.cast_nonneg _
    have hM0 : (0 : ℚ) ≤ M := Nat.cast_nonneg _
    calc |((f (ρ + (M : ℤ) • t) j : ℤ) : ℚ)| ≤ (Cg : ℚ) * (1 + supNorm (ρ + (M : ℤ) • t)) :=
          h1q.trans h2q
      _ ≤ (Cg : ℚ) * (1 + (supNorm ρ + M * ∑ i, |(t i : ℚ)|)) := by gcongr
      _ ≤ K * (1 + ∑ i, |(t i : ℚ)|) := by
          rw [hK]; nlinarith [mul_nonneg hC0 hr0, mul_nonneg (mul_nonneg hC0 hr0) hS,
            mul_nonneg (mul_nonneg hC0 hM0) hS, mul_nonneg hC0 hM0]
  have hzero : ∀ j (t : Fin n → ℤ), castQ t ⬝ᵥ (q j).Q *ᵥ castQ t = 0 :=
    fun j t => quadForm_zero_of_linearGrowth (q j) K (hbound j) (castQ t)
  refine weakIntAffine_of_affineCoset M hM ρ (fun j => (q j).c) (Matrix.of fun j i => (q j).l i)
    fun t j => ?_
  rw [hq t j]
  have hz := hzero j t
  simp only [QuadForm.eval]
  rw [hz, add_zero]
  simp only [Matrix.of_apply, dotProduct, castQ]

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

theorem ac_zPolarQ_sub_left (c c' w : OutWit m r → ℚ) :
    D.zPolarQ (c - c') w = D.zPolarQ c w - D.zPolarQ c' w := by
  simp only [zPolarQ, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k' _ => ?_
  ring

theorem ac_centre_unique (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    {a : Fin n → ℤ} {c c' : OutWit m r → ℚ} (hc : D.IsCentre a c) (hc' : D.IsCentre a c') :
    c = c' := by
  by_contra hne
  have hd : c - c' ≠ 0 := sub_ne_zero.mpr hne
  have h1 := hpos _ hd
  have h2 : D.zPolarQ (c - c') (c - c') = 0 := by
    rw [D.ac_zPolarQ_sub_left]
    have e1 := hc (c - c')
    have e2 := hc' (c - c')
    linarith
  rw [D.zPolarQ_self] at h2
  linarith

theorem binary_baseSection (e : OutWit m r ≃ Fin 2)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (hT : ∀ a, ∃ z, D.SolZ a z)
    {a0 : Fin n → ℤ} {z0 : OutWit m r → ℤ} (hz0 : D.SolZ a0 z0)
    {c : OutWit m r → ℚ} (hc : D.IsCentre a0 c) (hR : 0 < D.residual a0 c) :
    ∃ (M : ℕ) (G : Matrix (OutWit m r) (Fin n) ℤ), 1 ≤ M ∧
      ∀ t : Fin n → ℤ, D.SolZ (a0 + (M : ℤ) • t) (z0 + G *ᵥ t) := by
  classical
  obtain ⟨α, β, Δ, c0, L, Rq, hα, hΔ, hC, hRq, hdiag⟩ := binary_compiler_gen (D := D) (e := e) hpos
  have hnorm : ∀ a (z : OutWit m r → ℤ), D.SolZ a z →
      D.zQuadQ (toQ z - fun k => c0 k + ∑ i, L k i * (a i : ℚ)) = Rq.eval (castQ a) := by
    intro a z h
    rw [D.offCentre_norm (hC a) h, hRq a]
  have ha0 : Rq.eval (castQ a0) ≠ 0 := by
    have hcc := D.ac_centre_unique hpos hc (hC a0)
    rw [hcc, hRq a0] at hR
    exact ne_of_gt hR
  set cen0 : OutWit m r → ℚ := fun k => c0 k + ∑ i, L k i * (a0 i : ℚ) with hcen0
  set w0 : OutWit m r → ℚ := toQ z0 - cen0 with hw0
  set r0 := w0 (binK1 e) + β * w0 (binK2 e) with hr0
  set s0 := w0 (binK2 e) with hs0
  have hbase : α * (r0 ^ 2 + Δ * s0 ^ 2) = Rq.eval (castQ a0) := by
    rw [← hdiag, ← hnorm a0 z0 hz0]
  have hc' : 0 < r0 ^ 2 + Δ * s0 ^ 2 := by
    have hnn : 0 ≤ r0 ^ 2 + Δ * s0 ^ 2 := by positivity
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exfalso; apply ha0; rw [← hbase, ← h]; ring
  set T := Rq.translate (castQ a0) with hT'
  set ell : Fin n → ℚ := (1 / (2 * α)) • T.l with hell
  set H : Matrix (Fin n) (Fin n) ℚ := (1 / α) • T.Q with hH
  have hTc : T.c = α * (r0 ^ 2 + Δ * s0 ^ 2) := by rw [hbase]; rfl
  have hshift : ∀ x : Fin n → ℚ, Rq.eval (castQ a0 + x)
      = α * ((r0 ^ 2 + Δ * s0 ^ 2) + 2 * (ell ⬝ᵥ x) + x ⬝ᵥ (H *ᵥ x)) := by
    intro x
    rw [QuadForm.eval_translate]
    show T.c + T.l ⬝ᵥ x + x ⬝ᵥ (T.Q *ᵥ x) = _
    rw [hTc, hell, hH, smul_dotProduct, smul_mulVec, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    field_simp
  have hrep : ∀ x : Fin n → ℤ, ∃ X Y : ℚ,
      (r0 ^ 2 + Δ * s0 ^ 2) + 2 * (ell ⬝ᵥ castQ x) + castQ x ⬝ᵥ (H *ᵥ castQ x)
        = X ^ 2 + Δ * Y ^ 2 := by
    intro x
    obtain ⟨z, hz⟩ := hT (a0 + x)
    have h1 := hshift (castQ x)
    rw [← castQ_add] at h1
    have h2 := hnorm (a0 + x) z hz
    rw [hdiag] at h2
    refine ⟨_, _, mul_left_cancel₀ hα.ne' (h1.symm.trans h2.symm)⟩
  obtain ⟨rl, sl, hsec⟩ := NormLift.norm_section Δ r0 s0 hΔ hc' ell H hrep
  set G : OutWit m r → Fin n → ℚ := fun k i =>
    if k = binK1 e then L k i + rl i - β * sl i else L k i + sl i with hG
  obtain ⟨M, hM, hg⟩ := exists_common_den (fun p : OutWit m r × Fin n => G p.1 p.2)
  choose g hg using hg
  refine ⟨M, Matrix.of fun k i => g (k, i), hM, fun t => ?_⟩
  set zt : OutWit m r → ℤ := fun k => z0 k + ∑ i, g (k, i) * t i with hzt
  set x : Fin n → ℚ := castQ ((M : ℤ) • t) with hx
  have hztq : ∀ k, toQ zt k = toQ z0 k + (fun i => G k i) ⬝ᵥ x := by
    intro k
    simp only [hzt, hx, toQ, dotProduct, castQ, Pi.smul_apply, smul_eq_mul]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hg (k, i)]
    ring
  have hdiff : ∀ k, (toQ zt - fun k => c0 k + ∑ i, L k i * ((a0 + (M : ℤ) • t) i : ℚ)) k
      = w0 k + (fun i => G k i) ⬝ᵥ x - (fun i => L k i) ⬝ᵥ x := by
    intro k
    simp only [Pi.sub_apply]
    rw [hztq k, cen_add c0 L a0 M t k, hw0, hcen0]
    simp only [Pi.sub_apply]
    rw [← hx]
    ring
  have hG1 : (fun i => G (binK1 e) i) = (fun i => L (binK1 e) i) + rl - β • sl := by
    funext i; simp [hG]
  have hG2 : (fun i => G (binK2 e) i) = (fun i => L (binK2 e) i) + sl := by
    funext i; simp [hG, (k1_ne_k2 e).symm]
  have hsolt : D.SolZ (a0 + (M : ℤ) • t) zt := by
    apply solZ_of_norm (hC _)
    rw [hRq, hdiag, hdiff, hdiff, hG1, hG2]
    have hs := hsec x
    have hsh := hshift x
    rw [hx, ← castQ_add] at hsh
    rw [← hx] at hsh
    simp only [add_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [hsh, hs, hr0, hs0]
    ring
  exact hsolt

theorem zeroResidual_section (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (hT : ∀ a, ∃ z, D.SolZ a z)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = 0) :
    ∃ (g0 : OutWit m r → ℤ) (G : Matrix (OutWit m r) (Fin n) ℤ),
      ∀ a : Fin n → ℤ, D.SolZ a (g0 + G *ᵥ a) := by
  classical
  choose zf hzf using hT
  have hcz : ∀ a, toQ (zf a) = centreAt c0 C a := by
    intro a
    have h := (D.sc_solZ_iff hcen hR a (zf a)).mp (hzf a)
    by_contra hne
    have := hpos _ (sub_ne_zero.mpr hne)
    linarith
  have hz0 : ∀ k, (zf 0 k : ℚ) = c0 k := by
    intro k
    have := congrFun (hcz 0) k
    simpa [toQ, centreAt] using this
  have hzi : ∀ k i, (zf (Pi.single i 1) k : ℚ) = c0 k + C k i := by
    intro k i
    have := congrFun (hcz (Pi.single i 1)) k
    simpa [toQ, centreAt, Pi.single_apply] using this
  refine ⟨zf 0, Matrix.of fun k i => zf (Pi.single i 1) k - zf 0 k, fun a => ?_⟩
  rw [D.sc_solZ_iff hcen hR]
  have hq : toQ (zf 0 + (Matrix.of fun k i => zf (Pi.single i 1) k - zf 0 k) *ᵥ a)
      = centreAt c0 C a := by
    funext k
    simp only [toQ, Pi.add_apply, cr_mulVec_apply, Matrix.of_apply, centreAt]
    push_cast
    rw [hz0 k]
    simp only [hzi, add_sub_cancel_left]
  rw [hq, sub_self]
  simp [zQuadQ]

theorem weakIntAffineCosetNF_of_binary (e : OutWit m r ≃ Fin 2)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : WeakIntAffineCosetNF f := by
  classical
  obtain ⟨α, β, Δ, c0, L, Rq, hα, hΔ, hC, hRq, hdiag⟩ := binary_compiler_gen (D := D) (e := e) hpos
  have hT : ∀ a, ∃ z, D.SolZ a z := by
    intro a
    obtain ⟨u, hu⟩ := (hf a (f a)).mpr rfl
    exact ⟨Sum.elim (f a) u, hu⟩
  have hcen : ∀ a, D.IsCentre a (centreAt c0 L a) := hC
  by_cases h0 : ∀ a, Rq.eval (castQ a) = 0
  · obtain ⟨g0, G, hs⟩ := D.zeroResidual_section hpos hT c0 L hcen
      (fun a => (hRq a).trans (h0 a))
    refine weakIntAffine_of_section hf 1 le_rfl 0 g0 G fun t => ?_
    simpa using hs t
  · push Not at h0
    obtain ⟨a0, ha0⟩ := h0
    obtain ⟨z0, hz0⟩ := hT a0
    have hres : 0 < D.residual a0 (centreAt c0 L a0) := by
      have hn := D.offCentre_norm (hcen a0) hz0
      have hnn : 0 ≤ D.zQuadQ (toQ z0 - centreAt c0 L a0) := by
        by_cases hz : toQ z0 - centreAt c0 L a0 = 0
        · rw [hz]; simp [zQuadQ]
        · exact le_of_lt (hpos _ hz)
      have hne : D.residual a0 (centreAt c0 L a0) ≠ 0 := by
        have := hRq a0
        intro h; exact ha0 (this ▸ h)
      rw [hn] at hnn
      exact lt_of_le_of_ne hnn (Ne.symm hne)
    obtain ⟨M, G, hM, hs⟩ := D.binary_baseSection e hpos hT hz0 (hcen a0) hres
    exact weakIntAffine_of_section hf M hM a0 z0 G hs

end QuadraticGraphData

def LowRankSemidefiniteIntAffineNF : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
    (∃ v, D.zQuad v ≠ 0) →
      ((∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) ∨ ∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0) →
        D.polarRank ≤ 2 → D.Defines f → WeakIntAffineCosetNF f

theorem lowRankSemidefiniteIntAffineNF_holds : LowRankSemidefiniteIntAffineNF := by
  intro n m r D f hQ hsemi hrank hf
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨1, 0, 0, 0, le_rfl, fun t => funext fun j => j.elim0⟩
  · have hNF := lowRankSemidefiniteWeakNF_allM_holds n m r D f hQ hsemi hrank hf
    have hlin : LinearGrowth f := by
      rcases hsemi with hpos | hneg
      · exact D.linearGrowth_of_semidefinite_defines hm hpos hQ hf
      · refine D.negGraph.linearGrowth_of_semidefinite_defines hm (fun u => ?_) ?_
          (D.negGraph_defines hf)
        · rw [D.negGraph_zQuadQ]; linarith [hneg u]
        · obtain ⟨v, hv⟩ := hQ
          exact ⟨v, by rw [D.negGraph_zQuad]; omega⟩
    exact weakIntAffine_of_weakNF_linearGrowth hNF hlin

end DiophCompression.ResearchUpgrade
