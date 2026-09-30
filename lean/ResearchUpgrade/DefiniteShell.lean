/-
  DefiniteShell.lean — s55.  R43 Packet C1–C4 (GATE25 #69) and the B4 Step-3 completion (#68).

  * B4-N: `centreReflect_coset_mod` — with `N` making `2N·C` integral (the `N` of
    `centreReflect_finite_iff`), one reflectable input makes the coset `a0 + Nℤⁿ` reflectable.
  * C1: for a positive definite output/witness form, `definite_coord_sq_le` gives an explicit
    rational `h ≥ 0` with `yₖ² ≤ h·Q(y)` (polar representatives + Cauchy–Schwarz, no eigenvalues);
    `definiteShell_neg`, `definiteShell_zero`, `definiteShell_bound`, `shellFinset`,
    `mem_shellFinset` — the lattice shell `Q(y) = T` is exactly a filtered box.
  * C2: `shellEquiv` — constant residual along an affine centre: integer solutions at `a` ↔ shell
    points with `y ≡ −(e0 + E a) (mod M)`, by `y = Mz − (e0 + E a)`; `shellResidue_mod` — the
    congruence depends on `a mod M` only.
  * C3: `total_outputUnique_iff_shellImage` — total ∧ output-unique iff every one of the finitely
    many residue shells has a one-point OUTPUT image (several witnesses allowed);
    `shellImage_eq_value` reads `f` off the table; `not_total_of_negResidual`.
  * C4: `DefiniteShellControl.ctlC4`, `(3b − a)² + (u + b)² + v² = 1` — positive definite, polar
    rank 3, centre `(a/3, −a/3, 0)`, residual 1, `f(a) = ⌊(a + 1)/3⌋`, four solutions at `a = 0`,
    one-point output images at `M = 3`, while the residue shell of `0` has four points.

  Statement amendment (Dr. Fukui, s55): `definiteShell_bound` and `mem_shellFinset` carry `0 ≤ h`;
  without it the frozen text was false (Q(y) = −y², h = −1).

  Not claimed: existence of an affine centre or constancy of the residual for a general datum.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.ConstResidual
import ResearchUpgrade.OutputCoercivity
import ResearchUpgrade.AffineCentre
import ResearchUpgrade.PolarAnnihilator
import ResearchUpgrade.RankExcessCompiler

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

theorem centreReflect_coset_mod (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (N : ℕ) (hN : 1 ≤ N) (H : Matrix (OutWit m r) (Fin n) ℤ)
    (hH : ∀ k i, (H k i : ℚ) = 2 * (N : ℚ) * C k i)
    (a0 : Fin n → ℤ) (h0 : ∃ h : OutWit m r → ℤ, toQ h = 2 • centreAt c0 C a0) :
    ∀ t : Fin n → ℤ, ∃ h : OutWit m r → ℤ, toQ h = 2 • centreAt c0 C (a0 + (N : ℤ) • t) := by
  have _hN := hN
  obtain ⟨h, hh⟩ := h0
  intro t
  refine ⟨h + H *ᵥ t, ?_⟩
  funext k
  have hk := congrFun hh k
  simp only [toQ, Pi.smul_apply, nsmul_eq_mul] at hk
  simp only [toQ, Pi.smul_apply, nsmul_eq_mul, Pi.add_apply, cr_mulVec_apply,
    cr_centreAt_add_smul]
  push_cast at hk ⊢
  rw [hk]
  simp only [hH]
  rw [mul_add]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sc_zQuadQ_nonneg (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (u : OutWit m r → ℚ) : 0 ≤ D.zQuadQ u := by
  by_cases hu : u = 0
  · subst hu; simp [zQuadQ]
  · exact le_of_lt (hpos u hu)

theorem definite_coord_sq_le (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) :
    ∃ h : ℚ, 0 ≤ h ∧ ∀ (y : OutWit m r → ℚ) (k : OutWit m r), (y k) ^ 2 ≤ h * D.zQuadQ y := by
  classical
  have hnn := D.sc_zQuadQ_nonneg hpos
  have hrep : ∀ k : OutWit m r, ∃ w : OutWit m r → ℚ, ∀ v, D.zPolarQ w v = v k := by
    intro k
    obtain ⟨c, hc⟩ := D.exists_polar_rep (ℓ := (LinearMap.proj k : (OutWit m r → ℚ) →ₗ[ℚ] ℚ))
      (by
        intro e he
        show e k = 0
        have h0 : D.zPolarQ e e = 0 := he e
        rw [D.zPolarQ_self] at h0
        by_contra hne
        have hne' : e ≠ 0 := fun h => hne (by rw [h]; rfl)
        have := hpos e hne'
        linarith)
    exact ⟨c, fun v => by simpa using hc v⟩
  choose w hw using hrep
  refine ⟨∑ k, 4 * D.zQuadQ (w k),
    Finset.sum_nonneg fun k _ => by have := hnn (w k); linarith, fun y k => ?_⟩
  have hc := D.semidefinite_cauchy hnn (w k) y
  rw [hw k y] at hc
  have hle : 4 * D.zQuadQ (w k) ≤ ∑ k', 4 * D.zQuadQ (w k') :=
    Finset.single_le_sum (f := fun k' => 4 * D.zQuadQ (w k'))
      (fun k' _ => by have := hnn (w k'); linarith) (Finset.mem_univ k)
  have hy := hnn y
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) hy]

theorem definiteShell_neg (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    {T : ℚ} (hT : T < 0) (y : OutWit m r → ℤ) : D.zQuadQ (toQ y) ≠ T := by
  intro heq
  have := D.sc_zQuadQ_nonneg hpos (toQ y)
  linarith

theorem definiteShell_zero (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (y : OutWit m r → ℤ) : D.zQuadQ (toQ y) = 0 ↔ y = 0 := by
  constructor
  · intro h0
    by_contra hne
    have hq : toQ y ≠ 0 := fun h => hne (funext fun k => by
      have := congrFun h k
      simpa [toQ] using this)
    have := hpos _ hq
    linarith
  · rintro rfl
    simp [zQuadQ, toQ]

theorem definiteShell_bound {h : ℚ} (h0 : 0 ≤ h)
    (hh : ∀ (y : OutWit m r → ℚ) (k : OutWit m r), (y k) ^ 2 ≤ h * D.zQuadQ y)
    (T : ℚ) {y : OutWit m r → ℤ} (hy : D.zQuadQ (toQ y) = T) (k : OutWit m r) :
    |y k| ≤ ((⌈h * max T 0⌉₊ + 1 : ℕ) : ℤ) := by
  have h1 : ((y k : ℤ) : ℚ) ^ 2 ≤ h * D.zQuadQ (toQ y) := hh (toQ y) k
  rw [hy] at h1
  have hT : h * T ≤ h * max T 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) h0
  have hc : h * max T 0 ≤ ((⌈h * max T 0⌉₊ : ℕ) : ℚ) := Nat.le_ceil _
  set Cn : ℕ := ⌈h * max T 0⌉₊
  have hsq : ((y k : ℤ) : ℚ) ^ 2 ≤ ((Cn : ℤ) : ℚ) := by push_cast; linarith
  have hsqZ : (y k) ^ 2 ≤ (Cn : ℤ) := by exact_mod_cast hsq
  have hC : (0 : ℤ) ≤ Cn := by positivity
  push_cast
  rw [abs_le]
  constructor
  · by_contra hlt
    push Not at hlt
    nlinarith [sq_nonneg (Cn : ℤ)]
  · by_contra hlt
    push Not at hlt
    nlinarith [sq_nonneg (Cn : ℤ)]

noncomputable def shellFinset (B : ℕ) (T : ℚ) : Finset (OutWit m r → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Icc (-(B : ℤ)) B).filter fun y => D.zQuadQ (toQ y) = T

theorem mem_shellFinset {h : ℚ} (h0 : 0 ≤ h)
    (hh : ∀ (y : OutWit m r → ℚ) (k : OutWit m r), (y k) ^ 2 ≤ h * D.zQuadQ y)
    (T : ℚ) (y : OutWit m r → ℤ) :
    y ∈ D.shellFinset (⌈h * max T 0⌉₊ + 1) T ↔ D.zQuadQ (toQ y) = T := by
  unfold shellFinset
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun hy => hy.2
  · intro hy
    refine ⟨fun k => ?_, hy⟩
    rw [Finset.mem_Icc]
    exact abs_le.mp (D.definiteShell_bound h0 hh T hy k)

end QuadraticGraphData

theorem sc_residue_mod {n : ℕ} {κ : Type*} [Fintype κ] (M : ℕ) (e0 : κ → ℤ)
    (E : Matrix κ (Fin n) ℤ) (a t : Fin n → ℤ) (y : κ → ℤ) :
    (∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ (a + (M : ℤ) • t)) k) ↔
      (∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ a) k) := by
  have hE : ∀ k, (E *ᵥ (a + (M : ℤ) • t)) k = (E *ᵥ a) k + (M : ℤ) * (E *ᵥ t) k := by
    intro k
    simp only [cr_mulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  refine forall_congr' fun k => ?_
  rw [hE k, show y k + e0 k + ((E *ᵥ a) k + (M : ℤ) * (E *ᵥ t) k)
      = (y k + e0 k + (E *ᵥ a) k) + (M : ℤ) * (E *ᵥ t) k by ring]
  exact dvd_add_left (dvd_mul_right _ _)

theorem shellResidue_mod {n s : ℕ} (M : ℕ) (e0 : Fin s → ℤ) (E : Matrix (Fin s) (Fin n) ℤ)
    (a t : Fin n → ℤ) (y : Fin s → ℤ) :
    (∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ (a + (M : ℤ) • t)) k) ↔
      (∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ a) k) :=
  sc_residue_mod M e0 E a t y

theorem sc_cong {n : ℕ} {κ : Type*} [Fintype κ] (M : ℕ) (e0 : κ → ℤ)
    (E : Matrix κ (Fin n) ℤ) (a : Fin n → ℤ) (y : κ → ℤ) :
    (∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ (fun i => a i % M)) k) ↔
      (∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ a) k) := by
  have hsplit : (fun i => a i % (M : ℤ)) + (M : ℤ) • (fun i => a i / (M : ℤ)) = a := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact Int.emod_add_mul_ediv (a i) M
  have := sc_residue_mod M e0 E (fun i => a i % (M : ℤ)) (fun i => a i / (M : ℤ)) y
  rw [hsplit] at this
  exact this.symm

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

theorem sc_solZ_iff {c0 : OutWit m r → ℚ} {C : Matrix (OutWit m r) (Fin n) ℚ} {R0 : ℚ}
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0) (a : Fin n → ℤ) (z : OutWit m r → ℤ) :
    D.SolZ a z ↔ D.zQuadQ (toQ z - centreAt c0 C a) = R0 := by
  constructor
  · intro hz
    have h0 : D.P.eval (Sum.elim a z) = 0 := hz
    have := D.cr_eval_cast (hcen a) z
    rw [h0, hR a] at this
    push_cast at this
    linarith
  · intro hq
    show D.P.eval _ = 0
    apply Int.cast_injective (α := ℚ)
    rw [D.cr_eval_cast (hcen a), hR a, hq]
    simp

theorem sc_toQ_shift {c0 : OutWit m r → ℚ} {C : Matrix (OutWit m r) (Fin n) ℚ}
    (M : ℕ) (e0 : OutWit m r → ℤ) (E : Matrix (OutWit m r) (Fin n) ℤ)
    (he0 : ∀ k, (e0 k : ℚ) = (M : ℚ) * c0 k) (hE : ∀ k i, (E k i : ℚ) = (M : ℚ) * C k i)
    (a : Fin n → ℤ) (z : OutWit m r → ℤ) :
    toQ ((M : ℤ) • z - (e0 + E *ᵥ a)) = (M : ℚ) • (toQ z - centreAt c0 C a) := by
  funext k
  simp only [toQ, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, cr_mulVec_apply,
    centreAt]
  push_cast
  simp only [he0, hE]
  have hs : ∑ i, (M : ℚ) * C k i * (a i : ℚ) = (M : ℚ) * ∑ i, C k i * (a i : ℚ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs]
  ring

theorem shellEquiv_of (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) (R0 : ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0)
    (M : ℕ) (hM : 1 ≤ M) (e0 : OutWit m r → ℤ) (E : Matrix (OutWit m r) (Fin n) ℤ)
    (he0 : ∀ k, (e0 k : ℚ) = (M : ℚ) * c0 k) (hE : ∀ k i, (E k i : ℚ) = (M : ℚ) * C k i)
    (a : Fin n → ℤ) :
    ∃ e : {z : OutWit m r → ℤ // D.SolZ a z} ≃
        {y : OutWit m r → ℤ // D.zQuadQ (toQ y) = (M : ℚ) ^ 2 * R0 ∧
          ∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ a) k},
      (∀ z, (e z : OutWit m r → ℤ) = (M : ℤ) • z.1 - (e0 + E *ᵥ a)) ∧
      (∀ y, (M : ℤ) • (e.symm y : OutWit m r → ℤ) = y.1 + (e0 + E *ᵥ a)) := by
  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have fwd : ∀ z, D.SolZ a z →
      D.zQuadQ (toQ ((M : ℤ) • z - (e0 + E *ᵥ a))) = (M : ℚ) ^ 2 * R0 ∧
        ∀ k, (M : ℤ) ∣ ((M : ℤ) • z - (e0 + E *ᵥ a)) k + e0 k + (E *ᵥ a) k := by
    intro z hz
    refine ⟨?_, fun k => ⟨z k, ?_⟩⟩
    · rw [sc_toQ_shift M e0 E he0 hE a z, D.zQuadQ_smul, (D.sc_solZ_iff hcen hR a z).mp hz]
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have bwd : ∀ y : OutWit m r → ℤ, (∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ a) k) →
      (M : ℤ) • (fun k => (y k + e0 k + (E *ᵥ a) k) / (M : ℤ)) = y + (e0 + E *ᵥ a) := by
    intro y hd
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    rw [Int.mul_ediv_cancel' (hd k)]
    ring
  have bwdSol : ∀ y : OutWit m r → ℤ, D.zQuadQ (toQ y) = (M : ℚ) ^ 2 * R0 →
      (∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ a) k) →
      D.SolZ a (fun k => (y k + e0 k + (E *ᵥ a) k) / (M : ℤ)) := by
    intro y hq hd
    rw [D.sc_solZ_iff hcen hR]
    have hsh := sc_toQ_shift M e0 E he0 hE a (fun k => (y k + e0 k + (E *ᵥ a) k) / (M : ℤ))
    rw [bwd y hd, add_sub_cancel_right] at hsh
    have := congrArg D.zQuadQ hsh
    rw [D.zQuadQ_smul, hq] at this
    exact (mul_left_cancel₀ (pow_ne_zero 2 hMq) this).symm
  refine ⟨{ toFun := fun z => ⟨_, fwd z.1 z.2⟩
            invFun := fun y => ⟨_, bwdSol y.1 y.2.1 y.2.2⟩
            left_inv := fun z => ?_
            right_inv := fun y => ?_ }, fun _ => rfl, fun y => bwd y.1 y.2.2⟩
  · apply Subtype.ext
    funext k
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (M : ℤ) * z.1 k - (e0 k + (E *ᵥ a) k) + e0 k + (E *ᵥ a) k = (M : ℤ) * z.1 k by ring]
    exact Int.mul_ediv_cancel_left _ hM0
  · apply Subtype.ext
    show (M : ℤ) • _ - _ = y.1
    rw [bwd y.1 y.2.2]
    exact add_sub_cancel_right _ _

theorem shellEquiv (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) (R0 : ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0) :
    ∃ (M : ℕ) (e0 : OutWit m r → ℤ) (E : Matrix (OutWit m r) (Fin n) ℤ), 1 ≤ M ∧
      (∀ k, (e0 k : ℚ) = (M : ℚ) * c0 k) ∧ (∀ k i, (E k i : ℚ) = (M : ℚ) * C k i) ∧
      ∀ a : Fin n → ℤ,
        ∃ e : {z : OutWit m r → ℤ // D.SolZ a z} ≃
            {y : OutWit m r → ℤ // D.zQuadQ (toQ y) = (M : ℚ) ^ 2 * R0 ∧
              ∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ a) k},
          (∀ z, (e z : OutWit m r → ℤ) = (M : ℤ) • z.1 - (e0 + E *ᵥ a)) ∧
          (∀ y, (M : ℤ) • (e.symm y : OutWit m r → ℤ) = y.1 + (e0 + E *ᵥ a)) := by
  obtain ⟨M, hM, hg⟩ :=
    cr_exists_common_den (Sum.elim c0 (fun p : OutWit m r × Fin n => C p.1 p.2))
  choose g hg using hg
  have he0 : ∀ k, (g (Sum.inl k) : ℚ) = (M : ℚ) * c0 k := fun k => by simpa using hg (Sum.inl k)
  have hE : ∀ k i, ((Matrix.of fun k i => g (Sum.inr (k, i))) k i : ℚ) = (M : ℚ) * C k i :=
    fun k i => by simpa using hg (Sum.inr (k, i))
  exact ⟨M, fun k => g (Sum.inl k), Matrix.of fun k i => g (Sum.inr (k, i)), hM, he0, hE,
    fun a => D.shellEquiv_of c0 C R0 hcen hR M hM _ _ he0 hE a⟩

noncomputable def residueShell (B : ℕ) (T : ℚ) (M : ℕ) (e0 : OutWit m r → ℤ)
    (E : Matrix (OutWit m r) (Fin n) ℤ) (ρ : Fin n → ℤ) : Finset (OutWit m r → ℤ) :=
  (D.shellFinset B T).filter fun y => ∀ k, (M : ℤ) ∣ y k + e0 k + (E *ᵥ ρ) k

theorem shellImage_eq_value
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) (R0 : ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0)
    (M : ℕ) (hM : 1 ≤ M) (e0 : OutWit m r → ℤ) (E : Matrix (OutWit m r) (Fin n) ℤ)
    (he0 : ∀ k, (e0 k : ℚ) = (M : ℚ) * c0 k) (hE : ∀ k i, (E k i : ℚ) = (M : ℚ) * C k i)
    (B : ℕ) (hB : ∀ y : OutWit m r → ℤ, D.zQuadQ (toQ y) = (M : ℚ) ^ 2 * R0 → ∀ k, |y k| ≤ B)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (a : Fin n → ℤ) :
    (D.residueShell B ((M : ℚ) ^ 2 * R0) M e0 E (fun i => a i % M)).image outProj
      = {fun j => (M : ℤ) * f a j - (e0 + E *ᵥ a) (Sum.inl j)} := by
  have _hpos := hpos
  obtain ⟨e, he, hes⟩ := D.shellEquiv_of c0 C R0 hcen hR M hM e0 E he0 hE a
  ext v
  simp only [Finset.mem_image, Finset.mem_singleton, residueShell, shellFinset, Finset.mem_filter,
    Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨y, ⟨⟨_, hq⟩, hd⟩, rfl⟩
    have hd' := (sc_cong M e0 E a y).mp hd
    have hzsol : D.SolZ a (e.symm ⟨y, hq, hd'⟩).1 := (e.symm ⟨y, hq, hd'⟩).2
    have hg := (hf a _).mp (D.graph_of_solZ hzsol)
    have hMz := hes ⟨y, hq, hd'⟩
    funext j
    have hj := congrFun hMz (Sum.inl j)
    have hfj := congrFun hg j
    simp only [outProj] at hfj ⊢
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at hj
    rw [← hfj]
    simp only [Pi.add_apply]
    linarith
  · rintro rfl
    obtain ⟨u, hu⟩ := (hf a (f a)).mpr rfl
    have hz : D.SolZ a (Sum.elim (f a) u) := (D.solZ_iff_sol a (f a) u).mpr hu
    refine ⟨(e ⟨_, hz⟩).1, ⟨⟨fun k => abs_le.mp (hB _ (e ⟨_, hz⟩).2.1 k), (e ⟨_, hz⟩).2.1⟩,
      (sc_cong M e0 E a _).mpr (e ⟨_, hz⟩).2.2⟩, ?_⟩
    rw [he]
    funext j
    simp [outProj]

theorem total_outputUnique_iff_shellImage
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) (R0 : ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0) :
    ∃ (M : ℕ) (e0 : OutWit m r → ℤ) (E : Matrix (OutWit m r) (Fin n) ℤ) (B : ℕ), 1 ≤ M ∧
      (∀ k, (e0 k : ℚ) = (M : ℚ) * c0 k) ∧ (∀ k i, (E k i : ℚ) = (M : ℚ) * C k i) ∧
      ((D.Total ∧ D.OutputUnique) ↔
        ∀ ρ : Fin n → Fin M,
          ((D.residueShell B ((M : ℚ) ^ 2 * R0) M e0 E (fun i => ((ρ i : ℕ) : ℤ))).image
            outProj).card = 1) := by
  classical
  obtain ⟨M, e0, E, hM, he0, hE, -⟩ := D.shellEquiv c0 C R0 hcen hR
  obtain ⟨h, h0, hh⟩ := D.definite_coord_sq_le hpos
  set B : ℕ := ⌈h * max ((M : ℚ) ^ 2 * R0) 0⌉₊ + 1 with hBdef
  have hB : ∀ y : OutWit m r → ℤ, D.zQuadQ (toQ y) = (M : ℚ) ^ 2 * R0 → ∀ k, |y k| ≤ B :=
    fun y hy k => D.definiteShell_bound h0 hh _ hy k
  refine ⟨M, e0, E, B, hM, he0, hE, ?_⟩
  have hMpos : (0 : ℤ) < M := by exact_mod_cast (show 0 < M by omega)
  have hrepr : ∀ ρ : Fin n → Fin M,
      (fun i => ((ρ i : ℕ) : ℤ)) = (fun i => ((fun i => ((ρ i : ℕ) : ℤ)) i) % M) := by
    intro ρ
    funext i
    exact (Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (ρ i).isLt)).symm
  have key : ∀ a : Fin n → ℤ, ∃ ρ : Fin n → Fin M,
      (fun i => ((ρ i : ℕ) : ℤ)) = fun i => a i % M := by
    intro a
    refine ⟨fun i => ⟨(a i % M).toNat, ?_⟩, ?_⟩
    · have h1 := Int.emod_lt_of_pos (a i) hMpos
      have h2 := Int.emod_nonneg (a i) (ne_of_gt hMpos)
      omega
    · funext i
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hMpos))
  constructor
  · rintro hTU ρ
    obtain ⟨f, hf⟩ := (D.exists_defines_iff).mpr hTU
    rw [hrepr ρ, D.shellImage_eq_value hpos c0 C R0 hcen hR M hM e0 E he0 hE B hB hf]
    exact Finset.card_singleton _
  · intro hcard
    have hsol : ∀ a : Fin n → ℤ, ∃ v, (D.residueShell B ((M : ℚ) ^ 2 * R0) M e0 E
        (fun i => a i % M)).image outProj = {v} := by
      intro a
      obtain ⟨ρ, hρ⟩ := key a
      have hc := hcard ρ
      rw [hρ] at hc
      exact Finset.card_eq_one.mp hc
    refine ⟨fun a => ?_, fun a b b' hb hb' => ?_⟩
    · obtain ⟨v, hv⟩ := hsol a
      have hvm : v ∈ (D.residueShell B ((M : ℚ) ^ 2 * R0) M e0 E
          (fun i => a i % M)).image outProj := by rw [hv]; exact Finset.mem_singleton_self _
      obtain ⟨y, hy, -⟩ := Finset.mem_image.mp hvm
      simp only [residueShell, shellFinset, Finset.mem_filter] at hy
      obtain ⟨⟨_, hq⟩, hd⟩ := hy
      obtain ⟨e, -, -⟩ := D.shellEquiv_of c0 C R0 hcen hR M hM e0 E he0 hE a
      have hz := (e.symm ⟨y, hq, (sc_cong M e0 E a y).mp hd⟩).2
      exact ⟨_, D.graph_of_solZ hz⟩
    · obtain ⟨v, hv⟩ := hsol a
      obtain ⟨e, he, -⟩ := D.shellEquiv_of c0 C R0 hcen hR M hM e0 E he0 hE a
      have img : ∀ (c : Fin m → ℤ), D.Graph a c →
          (fun j => (M : ℤ) * c j - (e0 + E *ᵥ a) (Sum.inl j)) = v := by
        intro c hc
        obtain ⟨u, hu⟩ := hc
        have hz : D.SolZ a (Sum.elim c u) := (D.solZ_iff_sol a c u).mpr hu
        have hmem : outProj (e ⟨_, hz⟩).1 ∈ (D.residueShell B ((M : ℚ) ^ 2 * R0) M e0 E
            (fun i => a i % M)).image outProj := by
          refine Finset.mem_image.mpr ⟨(e ⟨_, hz⟩).1, ?_, rfl⟩
          simp only [residueShell, shellFinset, Finset.mem_filter, Fintype.mem_piFinset,
            Finset.mem_Icc]
          exact ⟨⟨fun k => abs_le.mp (hB _ (e ⟨_, hz⟩).2.1 k), (e ⟨_, hz⟩).2.1⟩,
            (sc_cong M e0 E a _).mpr (e ⟨_, hz⟩).2.2⟩
        rw [hv, Finset.mem_singleton, he] at hmem
        rw [← hmem]
        funext j
        simp [outProj]
      have e1 := img b hb
      have e2 := img b' hb'
      funext j
      have := congrFun (e1.trans e2.symm) j
      have hM0 : (M : ℤ) ≠ 0 := ne_of_gt hMpos
      exact mul_left_cancel₀ hM0 (by linarith)

theorem not_total_of_negResidual
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) (R0 : ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0) (hR0 : R0 < 0) :
    ¬ D.Total := by
  intro hT
  obtain ⟨b, u, hu⟩ := hT 0
  have hz : D.SolZ 0 (Sum.elim b u) := (D.solZ_iff_sol 0 b u).mpr hu
  have h1 := (D.sc_solZ_iff hcen hR 0 _).mp hz
  have h2 := D.sc_zQuadQ_nonneg hpos (toQ (Sum.elim b u) - centreAt c0 C 0)
  linarith

end QuadraticGraphData

namespace DefiniteShellControl

def ctlC4 : QuadraticGraphData 1 1 2 where
  P :=
    { c := -1
      l := 0
      Q := fun p q => match p, q with
        | Sum.inl _, Sum.inl _ => 1
        | Sum.inl _, Sum.inr (Sum.inl _) => -6
        | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 10
        | Sum.inr (Sum.inl _), Sum.inr (Sum.inr i) => if (i : ℕ) = 0 then 2 else 0
        | Sum.inr (Sum.inr i), Sum.inr (Sum.inr i') => if i = i' then 1 else 0
        | _, _ => 0 }

def cC4 : Matrix (OutWit 1 2) (Fin 1) ℚ :=
  Matrix.of fun k _ => Sum.elim (fun _ => (1 : ℚ) / 3) (fun i => if (i : ℕ) = 0 then -1 / 3 else 0) k

def eC4 : Matrix (OutWit 1 2) (Fin 1) ℤ :=
  Matrix.of fun k _ => Sum.elim (fun _ => (1 : ℤ)) (fun i => if (i : ℕ) = 0 then -1 else 0) k

def fC4 : (Fin 1 → ℤ) → (Fin 1 → ℤ) := fun a _ => (a 0 + 1) / 3

theorem cC4_b (i : Fin 1) : cC4 (Sum.inl 0) i = 1 / 3 := rfl
theorem cC4_u (i : Fin 1) : cC4 (Sum.inr 0) i = -1 / 3 := rfl
theorem cC4_v (i : Fin 1) : cC4 (Sum.inr 1) i = 0 := rfl
theorem eC4_b (i : Fin 1) : eC4 (Sum.inl 0) i = 1 := rfl
theorem eC4_u (i : Fin 1) : eC4 (Sum.inr 0) i = -1 := rfl
theorem eC4_v (i : Fin 1) : eC4 (Sum.inr 1) i = 0 := rfl

theorem ctlC4_eval (a b : Fin 1 → ℤ) (u : Fin 2 → ℤ) :
    ctlC4.P.eval (pt a b u) = (3 * b 0 - a 0) ^ 2 + (u 0 + b 0) ^ 2 + u 1 ^ 2 - 1 := by
  simp [ctlC4, IntQuad.eval, pt, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem c4_zQuadQ (u : OutWit 1 2 → ℚ) :
    ctlC4.zQuadQ u = 9 * u (Sum.inl 0) ^ 2 + (u (Sum.inr 0) + u (Sum.inl 0)) ^ 2
      + u (Sum.inr 1) ^ 2 := by
  simp [QuadraticGraphData.zQuadQ, ctlC4, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem c4_elim_eq_iff (b b' : Fin 1 → ℤ) (u u' : Fin 2 → ℤ) :
    (Sum.elim b u : OutWit 1 2 → ℤ) = Sum.elim b' u' ↔
      b 0 = b' 0 ∧ u 0 = u' 0 ∧ u 1 = u' 1 := by
  constructor
  · intro h
    exact ⟨congrFun h (Sum.inl 0), congrFun h (Sum.inr 0), congrFun h (Sum.inr 1)⟩
  · rintro ⟨h1, h2, h3⟩
    funext k
    rcases k with k | k
    · fin_cases k
      exact h1
    · fin_cases k
      · exact h2
      · exact h3

theorem ctlC4_posDef : ∀ u : OutWit 1 2 → ℚ, u ≠ 0 → 0 < ctlC4.zQuadQ u := by
  intro u hu
  rw [c4_zQuadQ]
  by_contra hle
  push Not at hle
  have e1 : u (Sum.inl 0) ^ 2 = 0 := by
    nlinarith [sq_nonneg (u (Sum.inl 0)), sq_nonneg (u (Sum.inr 0) + u (Sum.inl 0)),
      sq_nonneg (u (Sum.inr 1))]
  have e2 : (u (Sum.inr 0) + u (Sum.inl 0)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (u (Sum.inl 0)), sq_nonneg (u (Sum.inr 0) + u (Sum.inl 0)),
      sq_nonneg (u (Sum.inr 1))]
  have e3 : u (Sum.inr 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (u (Sum.inl 0)), sq_nonneg (u (Sum.inr 0) + u (Sum.inl 0)),
      sq_nonneg (u (Sum.inr 1))]
  have f1 : u (Sum.inl 0) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e1
  have f3 : u (Sum.inr 1) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e3
  have f2 : u (Sum.inr 0) = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e2
    rw [f1] at this
    simpa using this
  apply hu
  funext k
  rcases k with k | k
  · fin_cases k
    exact f1
  · fin_cases k
    · exact f2
    · exact f3

theorem ctlC4_polarRank : ctlC4.polarRank = 3 := by
  have hinj : LinearMap.ker ctlC4.polarMapQ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hr : ctlC4.InRadicalQ v := ctlC4.mem_ker_polarMapQ.mp (LinearMap.mem_ker.mpr hv)
    by_contra hne
    have h1 := ctlC4_posDef v hne
    have h2 : ctlC4.zPolarQ v v = 0 := hr v
    rw [ctlC4.zPolarQ_self] at h2
    linarith
  unfold QuadraticGraphData.polarRank
  rw [LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hinj)]
  simp [Module.finrank_fintype_fun_eq_card]

theorem ctlC4_centre_residual :
    (∀ a, ctlC4.IsCentre a (QuadraticGraphData.centreAt 0 cC4 a)) ∧
    (∀ a, ctlC4.residual a (QuadraticGraphData.centreAt 0 cC4 a) = 1) := by
  refine ⟨fun a w => ?_, fun a => ?_⟩
  · simp only [QuadraticGraphData.zPolarQ, QuadraticGraphData.zLinQ, QuadraticGraphData.zLin,
      QuadraticGraphData.centreAt, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one,
      cC4_b, cC4_u, cC4_v]
    simp [ctlC4]
    ring
  · simp only [QuadraticGraphData.residual, QuadraticGraphData.zQuadQ, QuadraticGraphData.aPart,
      QuadraticGraphData.centreAt, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one,
      cC4_b, cC4_u, cC4_v]
    simp [ctlC4]
    ring

theorem ctlC4_defines : ctlC4.Defines fC4 := by
  intro a b
  have hb : b = fC4 a ↔ b 0 = (a 0 + 1) / 3 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h
      funext j
      fin_cases j
      exact h
  rw [hb]
  constructor
  · rintro ⟨u, hu⟩
    have h := hu
    unfold QuadraticGraphData.Sol at h
    rw [ctlC4_eval] at h
    have h1 : -1 ≤ 3 * b 0 - a 0 := by nlinarith [sq_nonneg (u 0 + b 0), sq_nonneg (u 1)]
    have h2 : 3 * b 0 - a 0 ≤ 1 := by nlinarith [sq_nonneg (u 0 + b 0), sq_nonneg (u 1)]
    omega
  · intro hb0
    have hd : 3 * b 0 - a 0 = -1 ∨ 3 * b 0 - a 0 = 0 ∨ 3 * b 0 - a 0 = 1 := by omega
    rcases hd with hd | hd | hd
    · refine ⟨![-b 0, 0], ?_⟩
      unfold QuadraticGraphData.Sol
      rw [ctlC4_eval, hd]
      simp
    · refine ⟨![1 - b 0, 0], ?_⟩
      unfold QuadraticGraphData.Sol
      rw [ctlC4_eval, hd]
      simp
    · refine ⟨![-b 0, 0], ?_⟩
      unfold QuadraticGraphData.Sol
      rw [ctlC4_eval, hd]
      simp

theorem ctlC4_solutions_zero (z : OutWit 1 2 → ℤ) :
    ctlC4.SolZ 0 z ↔
      z = Sum.elim (0 : Fin 1 → ℤ) (![1, 0] : Fin 2 → ℤ) ∨
      z = Sum.elim (0 : Fin 1 → ℤ) (![-1, 0] : Fin 2 → ℤ) ∨
      z = Sum.elim (0 : Fin 1 → ℤ) (![0, 1] : Fin 2 → ℤ) ∨
      z = Sum.elim (0 : Fin 1 → ℤ) (![0, -1] : Fin 2 → ℤ) := by
  obtain ⟨b, u, rfl⟩ : ∃ b u, z = Sum.elim b u :=
    ⟨fun i => z (Sum.inl i), fun i => z (Sum.inr i), by funext k; cases k <;> rfl⟩
  rw [QuadraticGraphData.solZ_iff_sol]
  unfold QuadraticGraphData.Sol
  rw [ctlC4_eval]
  simp only [c4_elim_eq_iff, Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro h
    have hb : b 0 = 0 := by
      by_contra hne
      have hp : 0 < (b 0) ^ 2 := by positivity
      have h1 : 0 + 1 ≤ (b 0) ^ 2 := Int.add_one_le_iff.mpr hp
      nlinarith [sq_nonneg (u 0 + b 0), sq_nonneg (u 1)]
    rw [hb] at h
    have p1 : -1 ≤ u 0 := by nlinarith [sq_nonneg (u 1)]
    have p2 : u 0 ≤ 1 := by nlinarith [sq_nonneg (u 1)]
    have q1 : -1 ≤ u 1 := by nlinarith [sq_nonneg (u 0)]
    have q2 : u 1 ≤ 1 := by nlinarith [sq_nonneg (u 0)]
    generalize u 0 = p at *
    generalize u 1 = q at *
    interval_cases p <;> interval_cases q <;> simp_all
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;>
      · rw [h1, h2, h3]; norm_num

theorem ctlC4_not_witnessUnique : ¬ ctlC4.WitnessUnique := by
  intro hW
  have hs : ∀ u : Fin 2 → ℤ, (u 0) ^ 2 + (u 1) ^ 2 = 1 → ctlC4.Sol 0 0 u := by
    intro u hu
    unfold QuadraticGraphData.Sol
    rw [ctlC4_eval]
    simp only [Pi.zero_apply]
    linarith
  have := hW 0 0 ![1, 0] ![-1, 0] (hs _ (by simp)) (hs _ (by simp))
  have := congrFun this 0
  simp at this

theorem ctlC4_translate (a t : Fin 1 → ℤ) :
    fC4 (a + (3 : ℤ) • t) = fun j => fC4 a j + t 0 := by
  funext j
  simp only [fC4, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  omega

theorem c4_box (y : OutWit 1 2 → ℤ) (hy : ctlC4.zQuadQ (toQ y) = ((3 : ℕ) : ℚ) ^ 2 * 1)
    (k : OutWit 1 2) : |y k| ≤ ((4 : ℕ) : ℤ) := by
  have hy9 : ctlC4.zQuadQ (toQ y) = 9 := by rw [hy]; norm_num
  rw [c4_zQuadQ] at hy9
  have hy' : 9 * (y (Sum.inl 0)) ^ 2 + (y (Sum.inr 0) + y (Sum.inl 0)) ^ 2
      + (y (Sum.inr 1)) ^ 2 = 9 := by
    have : ((9 * (y (Sum.inl 0)) ^ 2 + (y (Sum.inr 0) + y (Sum.inl 0)) ^ 2
      + (y (Sum.inr 1)) ^ 2 : ℤ) : ℚ) = ((9 : ℤ) : ℚ) := by
      push_cast
      simpa [toQ] using hy9
    exact_mod_cast this
  have b1 : y (Sum.inl 0) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (y (Sum.inr 0) + y (Sum.inl 0)), sq_nonneg (y (Sum.inr 1))]
  have b2 : (y (Sum.inr 0) + y (Sum.inl 0)) ^ 2 ≤ 9 := by
    nlinarith [sq_nonneg (y (Sum.inl 0)), sq_nonneg (y (Sum.inr 1))]
  have b3 : y (Sum.inr 1) ^ 2 ≤ 9 := by
    nlinarith [sq_nonneg (y (Sum.inl 0)), sq_nonneg (y (Sum.inr 0) + y (Sum.inl 0))]
  have c1 : -1 ≤ y (Sum.inl 0) ∧ y (Sum.inl 0) ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have c2 : -3 ≤ y (Sum.inr 0) + y (Sum.inl 0) ∧ y (Sum.inr 0) + y (Sum.inl 0) ≤ 3 :=
    ⟨by nlinarith, by nlinarith⟩
  have c3 : -3 ≤ y (Sum.inr 1) ∧ y (Sum.inr 1) ≤ 3 := ⟨by nlinarith, by nlinarith⟩
  push_cast
  rw [abs_le]
  rcases k with k | k
  · fin_cases k
    exact ⟨by simp only [Fin.zero_eta]; omega, by simp only [Fin.zero_eta]; omega⟩
  · fin_cases k
    · exact ⟨by simp only [Fin.zero_eta]; omega, by simp only [Fin.zero_eta]; omega⟩
    · exact ⟨by simp only [Fin.mk_one]; omega, by simp only [Fin.mk_one]; omega⟩

theorem c4_hE : ∀ k i, (eC4 k i : ℚ) = ((3 : ℕ) : ℚ) * cC4 k i := by
  intro k i
  rcases k with k | k
  · obtain rfl : k = 0 := Subsingleton.elim _ _
    rw [eC4_b, cC4_b]; norm_num
  · fin_cases k
    · show (eC4 (Sum.inr 0) i : ℚ) = ((3 : ℕ) : ℚ) * cC4 (Sum.inr 0) i
      rw [eC4_u, cC4_u]; norm_num
    · show (eC4 (Sum.inr 1) i : ℚ) = ((3 : ℕ) : ℚ) * cC4 (Sum.inr 1) i
      rw [eC4_v, cC4_v]; norm_num

theorem ctlC4_shellImage (ρ : Fin 1 → ℤ) (hρ : 0 ≤ ρ 0 ∧ ρ 0 < 3) :
    ((ctlC4.residueShell 4 9 3 0 eC4 ρ).image outProj).card = 1 := by
  have hdata := ctlC4_centre_residual
  have he0 : ∀ k, ((0 : OutWit 1 2 → ℤ) k : ℚ) = ((3 : ℕ) : ℚ) * (0 : OutWit 1 2 → ℚ) k := by
    intro k; simp
  have H := ctlC4.shellImage_eq_value ctlC4_posDef 0 cC4 1 hdata.1 hdata.2 3 (by norm_num) 0 eC4
    he0 c4_hE 4 c4_box ctlC4_defines ρ
  have hρ' : (fun i => ρ i % ((3 : ℕ) : ℤ)) = ρ := by
    funext i
    fin_cases i
    exact Int.emod_eq_of_lt hρ.1 (by exact_mod_cast hρ.2)
  have hT : ((3 : ℕ) : ℚ) ^ 2 * 1 = 9 := by norm_num
  rw [hρ', hT] at H
  rw [H]
  exact Finset.card_singleton _

theorem ctlC4_residueShell_zero_card : (ctlC4.residueShell 4 9 3 0 eC4 0).card = 4 := by
  have hS : ctlC4.residueShell 4 9 3 0 eC4 0 =
      ({Sum.elim (0 : Fin 1 → ℤ) (![3, 0] : Fin 2 → ℤ),
        Sum.elim (0 : Fin 1 → ℤ) (![-3, 0] : Fin 2 → ℤ),
        Sum.elim (0 : Fin 1 → ℤ) (![0, 3] : Fin 2 → ℤ),
        Sum.elim (0 : Fin 1 → ℤ) (![0, -3] : Fin 2 → ℤ)} : Finset (OutWit 1 2 → ℤ)) := by
    ext y
    obtain ⟨b, u, rfl⟩ : ∃ b u, y = Sum.elim b u :=
      ⟨fun i => y (Sum.inl i), fun i => y (Sum.inr i), by funext k; cases k <;> rfl⟩
    have hbox : ∀ z : OutWit 1 2 → ℤ, ctlC4.zQuadQ (toQ z) = 9 → ∀ k, |z k| ≤ ((4 : ℕ) : ℤ) :=
      fun z hz k => c4_box z (by rw [hz]; norm_num) k
    simp only [QuadraticGraphData.residueShell, QuadraticGraphData.shellFinset, Finset.mem_filter,
      Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      c4_elim_eq_iff, Matrix.mulVec_zero, Pi.zero_apply, add_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have hq : ctlC4.zQuadQ (toQ (Sum.elim b u)) = 9 ↔
        9 * (b 0) ^ 2 + (u 0 + b 0) ^ 2 + (u 1) ^ 2 = 9 := by
      rw [c4_zQuadQ]
      constructor
      · intro h
        have : ((9 * (b 0) ^ 2 + (u 0 + b 0) ^ 2 + (u 1) ^ 2 : ℤ) : ℚ) = ((9 : ℤ) : ℚ) := by
          push_cast; simpa [toQ] using h
        exact_mod_cast this
      · intro h
        have : ((9 * (b 0) ^ 2 + (u 0 + b 0) ^ 2 + (u 1) ^ 2 : ℤ) : ℚ) = ((9 : ℤ) : ℚ) := by
          exact_mod_cast h
        push_cast at this
        simpa [toQ] using this
    constructor
    · rintro ⟨⟨-, hq9⟩, hd⟩
      have hq9' := hq.mp hq9
      obtain ⟨β, hβ⟩ := hd (Sum.inl 0)
      obtain ⟨p, hp⟩ := hd (Sum.inr 0)
      obtain ⟨q, hq2⟩ := hd (Sum.inr 1)
      simp only [Sum.elim_inl, Sum.elim_inr] at hβ hp hq2
      push_cast at hβ hp hq2
      rw [hβ, hp, hq2] at hq9'
      have hβ0 : β = 0 := by
        by_contra hne
        have hpos : 0 < β ^ 2 := by positivity
        have h1 : 0 + 1 ≤ β ^ 2 := Int.add_one_le_iff.mpr hpos
        nlinarith [sq_nonneg (p + β), sq_nonneg q]
      subst hβ0
      have p1 : -1 ≤ p := by nlinarith [sq_nonneg q]
      have p2 : p ≤ 1 := by nlinarith [sq_nonneg q]
      have q1 : -1 ≤ q := by nlinarith [sq_nonneg p]
      have q2 : q ≤ 1 := by nlinarith [sq_nonneg p]
      rw [hβ, hp, hq2]
      interval_cases p <;> interval_cases q <;> simp_all
    · intro hmem
      have hvals : b 0 = 0 ∧ ((u 0 = 3 ∧ u 1 = 0) ∨ (u 0 = -3 ∧ u 1 = 0) ∨
          (u 0 = 0 ∧ u 1 = 3) ∨ (u 0 = 0 ∧ u 1 = -3)) := by
        rcases hmem with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
          simp_all
      obtain ⟨hb0, hu⟩ := hvals
      have hq9 : ctlC4.zQuadQ (toQ (Sum.elim b u)) = 9 := by
        rw [hq, hb0]
        rcases hu with ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> rw [h2, h3] <;> norm_num
      refine ⟨⟨fun k => abs_le.mp (hbox _ hq9 k), hq9⟩, fun k => ?_⟩
      rcases k with k | k
      · fin_cases k
        simp [hb0]
      · fin_cases k
        · rcases hu with ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> simp [h2]
        · rcases hu with ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> simp [h3]
  rw [hS]
  decide

end DefiniteShellControl

end DiophCompression.ResearchUpgrade
