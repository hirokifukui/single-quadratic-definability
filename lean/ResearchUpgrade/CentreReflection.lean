/-
  CentreReflection.lean — s55.  R43 Packet B3–B4 (GATE25 #68): reflection in a doubled centre,
  for ANY numbers of inputs, outputs and witnesses, with no sign or rank hypothesis.

  * B3: `centreReflect_solZ` — if `2c(a)` is an integer vector `h`, then `h − z` is an integer
    solution whenever `z` is; `centreReflect_output` — output-uniqueness alone forces
    `πz = πc(a)` (the witnesses may differ); `centreReflect_value` — with `Defines f`,
    `f(a) = πc(a)`.  The hypothesis is on the WHOLE vector `2c(a)`, not on its output part.
  * B4: `centreReflect_finite_iff` — some integer input has an integral doubled centre iff a
    residue `ρ ∈ (Fin N)ⁿ` solves `H0 + Hρ ≡ 0 (mod N)` (`N` a common denominator, `H0 = 2N c0`,
    `H = 2N C`); `centreReflect_coset` — one reflectable input makes a whole coset reflectable;
    capstones `centreReflect_weakIntAffineCosetNF`, `centreReflect_weakVectorCosetNF`.

  Not claimed: that the absence of a reflectable input refutes a normal form
  (`N4Control.D3_double_centre_not_integral` stays the control for this).

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.ConstResidual

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

theorem centreReflect_solZ {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    (h : OutWit m r → ℤ) (hh : toQ h = 2 • c) {z : OutWit m r → ℤ} (hz : D.SolZ a z) :
    D.SolZ a (h - z) := by
  have hq : toQ (h - z) - c = -(toQ z - c) := by
    funext k
    have hk := congrFun hh k
    simp only [toQ, Pi.smul_apply, nsmul_eq_mul] at hk
    simp only [toQ, Pi.sub_apply, Pi.neg_apply]
    push_cast
    rw [hk]
    push_cast
    ring
  have hz0 : D.P.eval (Sum.elim a z) = 0 := hz
  show D.P.eval _ = 0
  apply Int.cast_injective (α := ℚ)
  rw [D.cr_eval_cast hc, hq, D.cr_zQuadQ_neg, ← D.cr_eval_cast hc, hz0]

theorem centreReflect_output {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    (h : OutWit m r → ℤ) (hh : toQ h = 2 • c) (hU : D.OutputUnique)
    {z : OutWit m r → ℤ} (hz : D.SolZ a z) (j : Fin m) :
    (z (Sum.inl j) : ℚ) = c (Sum.inl j) := by
  have hz2 := D.centreReflect_solZ hc h hh hz
  have e := hU a _ _ (D.graph_of_solZ hz) (D.graph_of_solZ hz2)
  have ej : z (Sum.inl j) = h (Sum.inl j) - z (Sum.inl j) := congrFun e j
  have hk := congrFun hh (Sum.inl j)
  simp only [toQ, Pi.smul_apply, nsmul_eq_mul] at hk
  have ej' : (z (Sum.inl j) : ℚ) = (h (Sum.inl j) : ℚ) - z (Sum.inl j) := by exact_mod_cast ej
  push_cast at hk
  linarith

theorem centreReflect_value {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    (h : OutWit m r → ℤ) (hh : toQ h = 2 • c)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (j : Fin m) :
    (f a j : ℚ) = c (Sum.inl j) := by
  have hU : D.OutputUnique := fun a b b' hb hb' =>
    ((hf a b).mp hb).trans ((hf a b').mp hb').symm
  obtain ⟨u, hu⟩ := (hf a (f a)).mpr rfl
  have hz : D.SolZ a (Sum.elim (f a) u) := (D.solZ_iff_sol a (f a) u).mpr hu
  exact D.centreReflect_output hc h hh hU hz j

theorem centreReflect_finite_iff (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) :
    ∃ (N : ℕ) (H0 : OutWit m r → ℤ) (H : Matrix (OutWit m r) (Fin n) ℤ), 1 ≤ N ∧
      (∀ k, (H0 k : ℚ) = 2 * (N : ℚ) * c0 k) ∧
      (∀ k i, (H k i : ℚ) = 2 * (N : ℚ) * C k i) ∧
      ((∃ (a : Fin n → ℤ) (h : OutWit m r → ℤ), toQ h = 2 • centreAt c0 C a) ↔
        ∃ ρ : Fin n → Fin N, ∀ k, (N : ℤ) ∣ H0 k + ∑ i, H k i * ((ρ i : ℕ) : ℤ)) := by
  classical
  obtain ⟨N, hN, hg⟩ := cr_exists_common_den
    (Sum.elim (fun k => 2 * c0 k) (fun p : OutWit m r × Fin n => 2 * C p.1 p.2))
  choose g hg using hg
  have hg0 : ∀ k, (g (Sum.inl k) : ℚ) = (N : ℚ) * (2 * c0 k) := fun k => by simpa using hg (Sum.inl k)
  have hg1 : ∀ k i, (g (Sum.inr (k, i)) : ℚ) = (N : ℚ) * (2 * C k i) :=
    fun k i => by simpa using hg (Sum.inr (k, i))
  have hN0 : (N : ℚ) ≠ 0 := by
    have : (0 : ℚ) < N := by exact_mod_cast hN
    exact ne_of_gt this
  have hS : ∀ (a : Fin n → ℤ) k,
      ((g (Sum.inl k) + ∑ i, g (Sum.inr (k, i)) * a i : ℤ) : ℚ)
        = (N : ℚ) * (2 * centreAt c0 C a k) := by
    intro a k
    push_cast
    simp only [hg0, hg1, centreAt, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hrefl : ∀ a : Fin n → ℤ, (∃ h : OutWit m r → ℤ, toQ h = 2 • centreAt c0 C a) ↔
      ∀ k, (N : ℤ) ∣ g (Sum.inl k) + ∑ i, g (Sum.inr (k, i)) * a i := by
    intro a
    constructor
    · rintro ⟨h, hh⟩ k
      refine ⟨h k, ?_⟩
      apply Int.cast_injective (α := ℚ)
      rw [hS a k]
      have := congrFun hh k
      simp only [toQ, Pi.smul_apply, nsmul_eq_mul] at this
      push_cast
      rw [this]
      push_cast
      ring
    · intro hd
      refine ⟨fun k => (g (Sum.inl k) + ∑ i, g (Sum.inr (k, i)) * a i) / N, ?_⟩
      funext k
      simp only [toQ, Pi.smul_apply, nsmul_eq_mul]
      rw [Int.cast_div (hd k) (by push_cast; exact hN0), hS a k]
      push_cast
      field_simp
  refine ⟨N, fun k => g (Sum.inl k), Matrix.of fun k i => g (Sum.inr (k, i)), hN,
    fun k => by rw [hg0]; ring, fun k i => by simp only [Matrix.of_apply]; rw [hg1]; ring, ?_⟩
  simp only [Matrix.of_apply]
  constructor
  · rintro ⟨a, h, hh⟩
    have hd := (hrefl a).mp ⟨h, hh⟩
    have hNz : (0 : ℤ) < N := by exact_mod_cast hN
    refine ⟨fun i => ⟨(a i % N).toNat, by
      have h1 := Int.emod_lt_of_pos (a i) hNz
      have h2 := Int.emod_nonneg (a i) (ne_of_gt hNz)
      omega⟩, fun k => ?_⟩
    have hρ : ∀ i, (((a i % N).toNat : ℕ) : ℤ) = a i % N :=
      fun i => Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hNz))
    simp only [hρ]
    have hdiff : (N : ℤ) ∣ (g (Sum.inl k) + ∑ i, g (Sum.inr (k, i)) * a i)
        - (g (Sum.inl k) + ∑ i, g (Sum.inr (k, i)) * (a i % N)) := by
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      apply Finset.dvd_sum
      intro i _
      rw [← mul_sub, Int.emod_def]
      exact Dvd.dvd.mul_left ⟨a i / N, by ring⟩ _
    have := dvd_sub (hd k) hdiff
    rwa [sub_sub_cancel] at this
  · rintro ⟨ρ, hρ⟩
    exact ⟨fun i => ((ρ i : ℕ) : ℤ), (hrefl (fun i => ((ρ i : ℕ) : ℤ))).mpr hρ⟩

theorem centreReflect_coset (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (a0 : Fin n → ℤ) (h0 : ∃ h : OutWit m r → ℤ, toQ h = 2 • centreAt c0 C a0) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ t : Fin n → ℤ,
      ∃ h : OutWit m r → ℤ, toQ h = 2 • centreAt c0 C (a0 + (M : ℤ) • t) := by
  obtain ⟨M, hM, hg⟩ := cr_exists_common_den (fun p : OutWit m r × Fin n => 2 * C p.1 p.2)
  choose g hg using hg
  have hg' : ∀ k i, (g (k, i) : ℚ) = (M : ℚ) * (2 * C k i) := fun k i => by simpa using hg (k, i)
  obtain ⟨h, hh⟩ := h0
  refine ⟨M, hM, fun t => ⟨h + (Matrix.of fun k i => g (k, i)) *ᵥ t, ?_⟩⟩
  funext k
  have hk := congrFun hh k
  simp only [toQ, Pi.smul_apply, nsmul_eq_mul] at hk
  simp only [toQ, Pi.smul_apply, nsmul_eq_mul, Pi.add_apply, cr_mulVec_apply, Matrix.of_apply,
    cr_centreAt_add_smul]
  push_cast at hk ⊢
  rw [hk]
  simp only [hg']
  rw [mul_add]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem centreReflect_weakIntAffineCosetNF (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (a0 : Fin n → ℤ) (h0 : ∃ h : OutWit m r → ℤ, toQ h = 2 • centreAt c0 C a0) :
    WeakIntAffineCosetNF f := by
  obtain ⟨M, hM, hcos⟩ := centreReflect_coset c0 C a0 h0
  have hv : ∀ t j, (f (a0 + (M : ℤ) • t) j : ℚ)
      = centreAt c0 C a0 (Sum.inl j) + (M : ℚ) * ∑ i, C (Sum.inl j) i * (t i : ℚ) := by
    intro t j
    obtain ⟨h, hh⟩ := hcos t
    rw [D.centreReflect_value (hcen _) h hh hf j, cr_centreAt_add_smul]
  have h0' : ∀ j, (f a0 j : ℚ) = centreAt c0 C a0 (Sum.inl j) := by
    intro j
    have := hv 0 j
    simpa using this
  refine ⟨M, a0, f a0, Matrix.of fun j i => f (a0 + (M : ℤ) • Pi.single i (1 : ℤ)) j - f a0 j,
    hM, fun t => ?_⟩
  funext j
  apply Int.cast_injective (α := ℚ)
  simp only [Pi.add_apply, cr_mulVec_apply, Matrix.of_apply]
  push_cast
  rw [hv t j, h0' j]
  simp only [hv]
  simp [Pi.single_apply]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem centreReflect_weakVectorCosetNF (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (a0 : Fin n → ℤ) (h0 : ∃ h : OutWit m r → ℤ, toQ h = 2 • centreAt c0 C a0) :
    WeakVectorCosetNF f :=
  weakVectorCosetNF_of_weakIntAffine (D.centreReflect_weakIntAffineCosetNF c0 C hcen hf a0 h0)

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
