/-
  SectionRigidity.lean — s56.  GPT R44 Packet A (GATE26 #86): affine-section rigidity and the
  unconditional rank-two branch of constant-residual rigidity (CCR).

  * `lineSection_centredSlope_zero` — positive definite, polar rank ≥ 2, at least one output,
    output-unique: an integer affine FULL solution section along an input line has zero centred
    slope.  Non-radial case: a reflection `x ↦ x − (P(x,w)/Q(w)) w` in a vector orthogonal to one
    point of the line, cleared to an integer step at a chosen progression point (`sr_nonradial_step`).
    Radial case: the rotation `w' = ((1 − abK²) w + 2aK v)/(1 + abK²)` with `v ⊥ w` and the
    congruence `H s + E ≡ 0 (mod 1 + abK²)`, `H ∣ K` (GPT R44 §1.3).
  * `affineSection_constResidual` — a full integer affine section on a full input coset forces a
    constant residual everywhere (`sr_const_of_coset`: the residual is a polynomial).
  * `discriminantZero_line_const` — discriminant zero along a line through a positive residual forces
    the line residual to be constant (radial rational section, cleared, then the rigidity).
  * `rankTwo_CCR` — CCR with two output/witness coordinates, from R44 `binary_baseSection`.
  * `rankTwoSemidefiniteFullNF_holds` — full-residue NF for every semidefinite datum of polar rank
    exactly two (either sign), via `definite_reduction`.  Rank one is not claimed here.
  * `ConstantResidualRigidity`, `LineCollision` and `ccr_of_lineCollision`,
    `residual_line_of_nonconstant` — the one-line form of CCR in the SAME datum (no compiler).

  Statements frozen before proof (`~/lean/s56_evidence/freeze/A_FREEZE_s56.lean`, ruling R3, Dr. Fukui
  2026-09-25); frozen = installed by `#check` output, planted control caught.
  Not claimed: CCR in polar rank ≥ 3 (open; the TCER route is conditional and separate).

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.ConstResidual
import ResearchUpgrade.OutputCoercivity
import ResearchUpgrade.AffineCentre
import ResearchUpgrade.PolarAnnihilator
import ResearchUpgrade.RankExcessCompiler
import ResearchUpgrade.DefiniteReduction
import ResearchUpgrade.AffineSection
import ResearchUpgrade.RadicalBridge
import ResearchUpgrade.BranchSplit
import ResearchUpgrade.DefiniteBinary

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadraticGraphData

variable {n m r : ℕ}

/-! ### Part 1 helpers -/

theorem sr_solZ_iff (D : QuadraticGraphData n m r) {a : Fin n → ℤ} {c : OutWit m r → ℚ}
    (hc : D.IsCentre a c) (z : OutWit m r → ℤ) :
    D.SolZ a z ↔ D.zQuadQ (toQ z - c) = D.residual a c := by
  constructor
  · intro hz
    have h0 : D.P.eval (Sum.elim a z) = 0 := hz
    have := D.cr_eval_cast hc z
    rw [h0] at this
    push_cast at this
    linarith
  · intro hq
    show D.P.eval _ = 0
    apply Int.cast_injective (α := ℚ)
    rw [D.cr_eval_cast hc, hq]
    simp

theorem sr_zQuadQ_nonneg (D : QuadraticGraphData n m r)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (u : OutWit m r → ℚ) :
    0 ≤ D.zQuadQ u := by
  by_cases hu : u = 0
  · subst hu; simp [zQuadQ]
  · exact le_of_lt (hpos u hu)

theorem sr_polarRank_eq (D : QuadraticGraphData n m r)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) : D.polarRank = m + r := by
  have hinj : LinearMap.ker D.polarMapQ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hr : D.InRadicalQ v := D.mem_ker_polarMapQ.mp (LinearMap.mem_ker.mpr hv)
    by_contra hne
    have h1 := hpos v hne
    have h2 : D.zPolarQ v v = 0 := hr v
    rw [D.zPolarQ_self] at h2
    linarith
  unfold QuadraticGraphData.polarRank
  rw [LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hinj)]
  simp [Module.finrank_fintype_fun_eq_card]

theorem sr_centreAt_line (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (a0 v : Fin n → ℤ) (t : ℤ) :
    centreAt c0 C (a0 + t • v)
      = centreAt c0 C a0 + (t : ℚ) • (fun k => ∑ i, C k i * (v i : ℚ)) := by
  funext k
  simp only [centreAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [add_assoc, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sr_aPart_line (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (t : ℤ) :
    D.aPart (a0 + t • v) = D.aPart a0
      + t * ((∑ i, D.P.l (Sum.inl i) * v i)
          + ∑ i, ∑ j, (a0 i * (D.P.Q (Sum.inl i) (Sum.inl j) * v j)
              + v i * (D.P.Q (Sum.inl i) (Sum.inl j) * a0 j)))
      + t ^ 2 * ∑ i, ∑ j, v i * (D.P.Q (Sum.inl i) (Sum.inl j) * v j) := by
  simp only [aPart, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : ∀ i, D.P.l (Sum.inl i) * (a0 i + t * v i)
      = D.P.l (Sum.inl i) * a0 i + t * (D.P.l (Sum.inl i) * v i) := fun i => by ring
  have h2 : ∀ i j, (a0 i + t * v i) * (D.P.Q (Sum.inl i) (Sum.inl j) * (a0 j + t * v j))
      = a0 i * (D.P.Q (Sum.inl i) (Sum.inl j) * a0 j)
        + t * (a0 i * (D.P.Q (Sum.inl i) (Sum.inl j) * v j)
            + v i * (D.P.Q (Sum.inl i) (Sum.inl j) * a0 j))
        + t ^ 2 * (v i * (D.P.Q (Sum.inl i) (Sum.inl j) * v j)) := fun i j => by ring
  simp only [h1, h2, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The residual along an input line is a quadratic polynomial in the line parameter. -/
theorem sr_residual_line (D : QuadraticGraphData n m r) (c0 : OutWit m r → ℚ)
    (C : Matrix (OutWit m r) (Fin n) ℚ) (a0 v : Fin n → ℤ) :
    ∃ A B : ℚ, ∀ t : ℤ, D.residual (a0 + t • v) (centreAt c0 C (a0 + t • v))
      = A * (t : ℚ) ^ 2 + B * t + D.residual a0 (centreAt c0 C a0) := by
  set σ : OutWit m r → ℚ := fun k => ∑ i, C k i * (v i : ℚ) with hσ
  set L1 : ℤ := (∑ i, D.P.l (Sum.inl i) * v i)
          + ∑ i, ∑ j, (a0 i * (D.P.Q (Sum.inl i) (Sum.inl j) * v j)
              + v i * (D.P.Q (Sum.inl i) (Sum.inl j) * a0 j)) with hL1
  set L2 : ℤ := ∑ i, ∑ j, v i * (D.P.Q (Sum.inl i) (Sum.inl j) * v j) with hL2
  refine ⟨D.zQuadQ σ - (L2 : ℚ), D.zPolarQ (centreAt c0 C a0) σ - (L1 : ℚ), fun t => ?_⟩
  simp only [residual]
  rw [sr_centreAt_line c0 C a0 v t, D.zQuadQ_add_smul, D.sr_aPart_line a0 v t]
  simp only [hL1, hL2, hσ]
  push_cast
  ring

/-- A rational quadratic that is non-negative at every integer has non-negative leading coefficient,
and if that coefficient vanishes so does the linear one. -/
theorem sr_quad_nonneg (A B C : ℚ) (h : ∀ t : ℤ, 0 ≤ A * (t : ℚ) ^ 2 + B * t + C) :
    0 ≤ A ∧ (A = 0 → B = 0) := by
  constructor
  · by_contra hA
    push_neg at hA
    set T : ℤ := ⌈(|B| + |C|) / (-A)⌉ + 1 with hT
    have hceil := Int.le_ceil ((|B| + |C|) / (-A))
    have hT1 : (1 : ℚ) ≤ T := by
      have : (0 : ℚ) ≤ (|B| + |C|) / (-A) := div_nonneg (by positivity) (by linarith)
      have h2 : (0 : ℚ) ≤ ((⌈(|B| + |C|) / (-A)⌉ : ℤ) : ℚ) := le_trans this hceil
      rw [hT]; push_cast; linarith
    have hT2 : (|B| + |C|) / (-A) < T := by rw [hT]; push_cast; linarith
    have hT3 : |B| + |C| < (-A) * T := by
      rw [div_lt_iff₀ (by linarith)] at hT2; linarith
    have hB : B * T ≤ |B| * T := mul_le_mul_of_nonneg_right (le_abs_self B) (by linarith)
    have hC : C ≤ |C| * T := by
      have := le_abs_self C
      nlinarith [abs_nonneg C]
    have := h T
    nlinarith
  · intro hA
    subst hA
    by_contra hB
    rcases lt_or_gt_of_ne hB with hBn | hBp
    · have hceil := Int.le_ceil ((|C| + 1) / (-B))
      rw [div_le_iff₀ (by linarith)] at hceil
      have := h ⌈(|C| + 1) / (-B)⌉
      nlinarith [le_abs_self C, neg_abs_le C]
    · have hceil := Int.le_ceil ((|C| + 1) / B)
      rw [div_le_iff₀ hBp] at hceil
      have := h (-⌈(|C| + 1) / B⌉)
      push_cast at this
      nlinarith [le_abs_self C, neg_abs_le C]

end QuadraticGraphData


/-! ### Part 2: definitions (as frozen) -/

def ConstantResidualRigidity : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ),
    0 < m → (∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) → 2 ≤ D.polarRank →
      (∀ a, D.IsCentre a (QuadraticGraphData.centreAt c0 C a)) → D.Total → D.OutputUnique →
        ∃ R0 : ℚ, ∀ a, D.residual a (QuadraticGraphData.centreAt c0 C a) = R0

def LineCollision : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (a0 v : Fin n → ℤ) (A B : ℚ),
    0 < m → (∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) → 2 ≤ D.polarRank →
      (∀ a, D.IsCentre a (QuadraticGraphData.centreAt c0 C a)) →
      (∀ t : ℤ, ∃ z, D.SolZ (a0 + t • v) z) →
      (∀ t : ℤ, D.residual (a0 + t • v) (QuadraticGraphData.centreAt c0 C (a0 + t • v))
          = A * (t : ℚ) ^ 2 + B * t + D.residual a0 (QuadraticGraphData.centreAt c0 C a0)) →
      0 < A → ¬ D.OutputUnique

def RankTwoSemidefiniteFullNF : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
    0 < m → (∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) →
    ((∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) ∨ (∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0)) →
    D.polarRank = 2 → D.Defines f → FullVectorCosetNF f

namespace QuadraticGraphData

variable {n m r : ℕ}

theorem sr_solZ_of_total (D : QuadraticGraphData n m r) (hT : D.Total) (a : Fin n → ℤ) :
    ∃ z, D.SolZ a z := by
  obtain ⟨b, u, hu⟩ := hT a
  exact ⟨Sum.elim b u, hu⟩

theorem sr_polar_comb_right (D : QuadraticGraphData n m r) (v y x : OutWit m r → ℚ) (α β : ℚ) :
    D.zPolarQ v (α • y - β • x) = α * D.zPolarQ v y - β * D.zPolarQ v x := by
  rw [sub_eq_add_neg, ← neg_smul, D.zPolarQ_add_right, D.zPolarQ_smul_right, D.zPolarQ_smul_right]
  ring

theorem sr_polar_comb_left (D : QuadraticGraphData n m r) (v y x : OutWit m r → ℚ) (α β : ℚ) :
    D.zPolarQ (α • y - β • x) v = α * D.zPolarQ y v - β * D.zPolarQ x v := by
  rw [D.zPolarQ_symm, sr_polar_comb_right, D.zPolarQ_symm v y, D.zPolarQ_symm v x]

theorem sr_ne_zero_of_quad (D : QuadraticGraphData n m r) {u : OutWit m r → ℚ}
    (h : 0 < D.zQuadQ u) : u ≠ 0 := by
  rintro rfl
  simp [zQuadQ] at h

/-- Two integer solutions at one input with different `j`-th output contradict output-uniqueness. -/
theorem sr_collide (D : QuadraticGraphData n m r) (hOU : D.OutputUnique) {a : Fin n → ℤ}
    {c : OutWit m r → ℚ} (hc : D.IsCentre a c) {z : OutWit m r → ℤ} (hz : D.SolZ a z)
    (κ : OutWit m r → ℤ) (j : Fin m) (hκ : κ (Sum.inl j) ≠ 0)
    (hnorm : D.zQuadQ (toQ z - c + toQ κ) = D.zQuadQ (toQ z - c)) : False := by
  have hz' : D.SolZ a (z + κ) := by
    have hq := (D.sr_solZ_iff hc z).mp hz
    rw [D.sr_solZ_iff hc]
    have e : toQ (z + κ) - c = toQ z - c + toQ κ := by
      funext k; simp only [toQ, Pi.add_apply, Pi.sub_apply]; push_cast; ring
    rw [e, hnorm, hq]
  have e := hOU a _ _ (D.graph_of_solZ hz) (D.graph_of_solZ hz')
  have h2 : outProj z j = outProj (z + κ) j := congrFun e j
  simp only [outProj, Pi.add_apply] at h2
  exact hκ (by linarith)

theorem sr_reflect_norm (D : QuadraticGraphData n m r) (x w : OutWit m r → ℚ)
    (hw : D.zQuadQ w ≠ 0) (t : ℚ) (ht : t = - D.zPolarQ x w / D.zQuadQ w) :
    D.zQuadQ (x + t • w) = D.zQuadQ x := by
  rw [D.zQuadQ_add_smul, ht]
  field_simp
  ring

/-- The non-radial reflection step (GPT R44 A2). -/
theorem sr_nonradial_step (D : QuadraticGraphData n m r)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (X h : OutWit m r → ℚ) (j0 : Fin m)
    (hV : (2 * D.zQuadQ X) • h - D.zPolarQ h X • X ≠ 0)
    (hf2 : ∃ y : OutWit m r → ℚ,
      2 * D.zQuadQ X * y (Sum.inl j0) - D.zPolarQ X y * X (Sum.inl j0) ≠ 0) :
    ∃ (M : ℕ) (κ : OutWit m r → ℤ), 1 ≤ M ∧ κ (Sum.inl j0) ≠ 0 ∧
      D.zQuadQ (X + (M : ℚ) • h + toQ κ) = D.zQuadQ (X + (M : ℚ) • h) := by
  classical
  set V := (2 * D.zQuadQ X) • h - D.zPolarQ h X • X with hVdef
  set L : (OutWit m r → ℚ) → (OutWit m r → ℚ) :=
    fun y => (2 * D.zQuadQ X) • y - D.zPolarQ X y • X with hLdef
  have f1_eq : ∀ y, D.zPolarQ h (L y) = D.zPolarQ V y := by
    intro y
    simp only [hLdef, hVdef]
    rw [sr_polar_comb_right, sr_polar_comb_left]
    ring
  set f2 : (OutWit m r → ℚ) → ℚ :=
    fun y => 2 * D.zQuadQ X * y (Sum.inl j0) - D.zPolarQ X y * X (Sum.inl j0) with hf2def
  have f2_add : ∀ y y', f2 (y + y') = f2 y + f2 y' := by
    intro y y'; simp only [hf2def, Pi.add_apply, D.zPolarQ_add_right]; ring
  have hPV : 0 < D.zPolarQ V V := by
    rw [D.zPolarQ_self]; have := hpos V hV; linarith
  obtain ⟨y2, hy2⟩ := hf2
  obtain ⟨y, hy1, hy2'⟩ : ∃ y, D.zPolarQ V y ≠ 0 ∧ f2 y ≠ 0 := by
    by_cases a1 : f2 V = 0
    · by_cases a2 : D.zPolarQ V y2 = 0
      · refine ⟨V + y2, ?_, ?_⟩
        · rw [D.zPolarQ_add_right, a2]; simpa using hPV.ne'
        · rw [f2_add, a1]; simpa using hy2
      · exact ⟨y2, a2, hy2⟩
    · exact ⟨V, hPV.ne', a1⟩
  set w := L y with hw
  have hwj : w (Sum.inl j0) = f2 y := by
    simp only [hw, hLdef, hf2def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hXw : D.zPolarQ X w = 0 := by
    simp only [hw, hLdef]
    rw [sr_polar_comb_right, D.zPolarQ_self]
    ring
  have hβ : D.zPolarQ h w ≠ 0 := by rw [hw, f1_eq]; exact hy1
  have hw0 : w ≠ 0 := by
    intro h0; apply hy2'; rw [← hwj, h0]; rfl
  have hQw : 0 < D.zQuadQ w := hpos w hw0
  set k1 : OutWit m r → ℚ := (- D.zPolarQ h w / D.zQuadQ w) • w with hk1
  obtain ⟨M, hM1, hden⟩ := cr_exists_common_den k1
  choose κ hκ using hden
  have hMq : (1 : ℚ) ≤ M := by exact_mod_cast hM1
  refine ⟨M, κ, hM1, ?_, ?_⟩
  · intro h0
    have := hκ (Sum.inl j0)
    rw [h0] at this
    simp only [hk1, Pi.smul_apply, smul_eq_mul, Int.cast_zero] at this
    have hne : (M : ℚ) * (-D.zPolarQ h w / D.zQuadQ w * w (Sum.inl j0)) ≠ 0 := by
      refine mul_ne_zero (by linarith) (mul_ne_zero ?_ ?_)
      · exact div_ne_zero (neg_ne_zero.mpr hβ) hQw.ne'
      · rw [hwj]; exact hy2'
    exact hne this.symm
  · have hκv : toQ κ = ((M : ℚ) * (- D.zPolarQ h w / D.zQuadQ w)) • w := by
      funext k; simp only [toQ, hκ k, hk1, Pi.smul_apply, smul_eq_mul]; ring
    rw [hκv]
    apply D.sr_reflect_norm _ _ hQw.ne'
    rw [D.zPolarQ_add_left, D.zPolarQ_smul_left, hXw]
    ring

/-- **A2 + A3 (collision), A4.1.** -/
theorem lineSection_centredSlope_zero (D : QuadraticGraphData n m r) (hm : 0 < m)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (hrank : 2 ≤ D.polarRank)
    (hOU : D.OutputUnique)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a))
    (a0 w : Fin n → ℤ) (z0 g : OutWit m r → ℤ)
    (hsec : ∀ s : ℤ, D.SolZ (a0 + s • w) (z0 + s • g)) :
    ∀ s : ℤ, toQ (z0 + s • g) - centreAt c0 C (a0 + s • w) = toQ z0 - centreAt c0 C a0 := by
  classical
  set j0 : Fin m := ⟨0, hm⟩
  have hmr : 2 ≤ m + r := by rw [← D.sr_polarRank_eq hpos]; exact hrank
  set x0 : OutWit m r → ℚ := toQ z0 - centreAt c0 C a0 with hx0
  set h : OutWit m r → ℚ := toQ g - (fun k => ∑ i, C k i * (w i : ℚ)) with hhdef
  have hx : ∀ s : ℤ, toQ (z0 + s • g) - centreAt c0 C (a0 + s • w) = x0 + (s : ℚ) • h := by
    intro s
    rw [sr_centreAt_line]
    funext k
    simp only [hx0, hhdef, toQ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  suffices hh : h = 0 by
    intro s; rw [hx s, hh]; simp
  by_contra hh0
  have tool : ∀ (s : ℤ) (κ : OutWit m r → ℤ), κ (Sum.inl j0) ≠ 0 →
      D.zQuadQ (x0 + (s : ℚ) • h + toQ κ) = D.zQuadQ (x0 + (s : ℚ) • h) → False := by
    intro s κ hκ hn
    exact D.sr_collide hOU (hc (a0 + s • w)) (hsec s) κ j0 hκ (by rw [hx s]; exact hn)
  by_cases hrad : ∃ μ : ℚ, x0 = μ • h
  · ---------------- radial branch (A3) ----------------
    obtain ⟨μ, hμ⟩ := hrad
    obtain ⟨N, hN1, hNden⟩ := cr_exists_common_den h
    choose W hW using hNden
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN1
    have hWq : toQ W = (N : ℚ) • h := by funext k; simp only [toQ, hW k, Pi.smul_apply, smul_eq_mul]
    have hWq0 : toQ W ≠ 0 := by
      rw [hWq]; intro h0; apply hh0
      funext k; have := congrFun h0 k
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 hNq.ne'
      · simpa using h1
    set a : ℤ := D.zQuad W with ha
    have haq : (a : ℚ) = D.zQuadQ (toQ W) := (D.zQuadQ_toQ W).symm
    have hapos : 0 < a := by
      have := hpos _ hWq0; rw [← haq] at this; exact_mod_cast this
    -- the orthogonal integer vector V
    set Vi : OutWit m r → (OutWit m r → ℤ) :=
      fun i => (2 * a) • Pi.single i (1 : ℤ) - D.zPolar W (Pi.single i 1) • W with hVi
    have hViq : ∀ i, toQ (Vi i) = (2 * (a : ℚ)) • toQ (Pi.single i (1 : ℤ))
        - D.zPolarQ (toQ W) (toQ (Pi.single i (1 : ℤ))) • toQ W := by
      intro i; funext k
      simp only [hVi, toQ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, D.zPolarQ_toQ]
      push_cast; ring
    have hperp : ∀ i, D.zPolarQ (toQ W) (toQ (Vi i)) = 0 := by
      intro i; rw [hViq, sr_polar_comb_right, D.zPolarQ_self, ← haq]; ring
    have hsingle : ∀ i k : OutWit m r, toQ (Pi.single i (1 : ℤ)) k = if k = i then (1 : ℚ) else 0 := by
      intro i k; simp only [toQ, Pi.single_apply]; split_ifs <;> simp
    obtain ⟨V, hV0, hVperp, hVj⟩ : ∃ V : OutWit m r → ℤ, toQ V ≠ 0 ∧ D.zPolarQ (toQ W) (toQ V) = 0 ∧
        (W (Sum.inl j0) ≠ 0 ∨ V (Sum.inl j0) ≠ 0) := by
      by_cases hWj : W (Sum.inl j0) = 0
      · have hc0 : (Vi (Sum.inl j0) (Sum.inl j0) : ℚ) = 2 * a := by
          have := congrFun (hViq (Sum.inl j0)) (Sum.inl j0)
          simp only [toQ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
          rw [this]; simp [hWj]
        have hne : Vi (Sum.inl j0) (Sum.inl j0) ≠ 0 := by
          intro h0; rw [h0] at hc0; push_cast at hc0
          have : (0 : ℚ) < a := by exact_mod_cast hapos
          linarith
        refine ⟨Vi (Sum.inl j0), ?_, hperp _, Or.inr hne⟩
        intro h0; apply hne
        have := congrFun h0 (Sum.inl j0); simpa [toQ] using this
      · obtain ⟨i, hi⟩ : ∃ i, toQ (Vi i) ≠ 0 := by
          by_contra H
          push_neg at H
          have hcard : 1 < Fintype.card (OutWit m r) := by simp; omega
          obtain ⟨i1, i2, hne⟩ := Fintype.exists_pair_of_one_lt_card hcard
          have e11 := congrFun (H i1) i1
          have e21 := congrFun (H i2) i1
          have e22 := congrFun (H i2) i2
          rw [hViq] at e11 e21 e22
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hsingle,
            if_neg hne, if_neg (Ne.symm hne)] at e11 e21 e22
          simp only [↓reduceIte, mul_one] at e11 e22
          have : (0 : ℚ) < a := by exact_mod_cast hapos
          simp only [toQ] at e11 e21 e22
          have hp2 : D.zPolarQ (toQ W) (toQ (Pi.single i2 (1 : ℤ))) ≠ 0 := by
            intro h0; rw [h0] at e22; linarith
          have hW1 : (W i1 : ℚ) = 0 := by
            rcases mul_eq_zero.mp (by linarith : D.zPolarQ (toQ W) (toQ (Pi.single i2 (1 : ℤ))) * (W i1 : ℚ) = 0)
              with h0 | h0
            · exact absurd h0 hp2
            · exact h0
          rw [hW1] at e11; linarith
        exact ⟨Vi i, hi, hperp i, Or.inl hWj⟩
    set b : ℤ := D.zQuad V with hb
    have hbq : (b : ℚ) = D.zQuadQ (toQ V) := (D.zQuadQ_toQ V).symm
    have hbpos : 0 < b := by have := hpos _ hV0; rw [← hbq] at this; exact_mod_cast this
    set H : ℤ := (μ.den : ℤ) with hH
    set E : ℤ := μ.num with hE
    have hHpos : 0 < H := by rw [hH]; exact_mod_cast μ.den_pos
    set NN : ℤ := H * N with hNN
    have hNNpos : 0 < NN := by rw [hNN]; positivity
    obtain ⟨m', hm'1, hK⟩ : ∃ m' : ℤ, 1 ≤ m' ∧ V (Sum.inl j0) - b * (NN * m') * W (Sum.inl j0) ≠ 0 := by
      rcases hVj with hWj | hVj
      · by_cases h1 : V (Sum.inl j0) - b * (NN * 1) * W (Sum.inl j0) = 0
        · refine ⟨2, by norm_num, ?_⟩
          intro h2
          have : b * NN * W (Sum.inl j0) = 0 := by linarith
          rcases mul_eq_zero.mp this with h3 | h3
          · rcases mul_eq_zero.mp h3 with h4 | h4 <;> omega
          · exact hWj h3
        · exact ⟨1, le_rfl, h1⟩
      · by_cases hWj : W (Sum.inl j0) = 0
        · exact ⟨1, le_rfl, by rw [hWj]; simpa using hVj⟩
        · by_cases h1 : V (Sum.inl j0) - b * (NN * 1) * W (Sum.inl j0) = 0
          · refine ⟨2, by norm_num, ?_⟩
            intro h2
            have : b * NN * W (Sum.inl j0) = 0 := by linarith
            rcases mul_eq_zero.mp this with h3 | h3
            · rcases mul_eq_zero.mp h3 with h4 | h4 <;> omega
            · exact hWj h3
          · exact ⟨1, le_rfl, h1⟩
    set K : ℤ := NN * m' with hKdef
    set d : ℤ := 1 + a * b * K ^ 2 with hd
    have hcop : IsCoprime H d := ⟨-(a * b * K * N * m'), 1, by rw [hd, hKdef, hNN]; ring⟩
    obtain ⟨u, v', huv⟩ := hcop
    obtain ⟨s, τ, hτ, hsτ⟩ : ∃ s τ : ℤ, τ ≠ 0 ∧ H * s + E = d * τ := by
      by_cases hEv : E * v' = 0
      · refine ⟨-E * u + d, E * v' + H, by rw [hEv]; omega, ?_⟩
        linear_combination (-E) * huv
      · exact ⟨-E * u, E * v', hEv, by linear_combination (-E) * huv⟩
    set κ : OutWit m r → ℤ := (τ * 2 * a * m') • (V - (b * K) • W) with hκdef
    apply tool s κ
    · simp only [hκdef, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hτ (by norm_num)) hapos.ne') ?_) ?_
      · omega
      · simpa [mul_assoc] using hK
    · have hNNq : (NN : ℚ) ≠ 0 := by exact_mod_cast hNNpos.ne'
      have hμq : μ = (E : ℚ) / H := by rw [hE, hH]; push_cast; exact (Rat.num_div_den μ).symm
      have hHq : (H : ℚ) ≠ 0 := by exact_mod_cast hHpos.ne'
      have hdτ : (d : ℚ) * τ = H * s + E := by exact_mod_cast hsτ.symm
      set lam : ℚ := (τ : ℚ) / NN with hlam
      have hxs : x0 + (s : ℚ) • h = lam • ((d : ℚ) • toQ W) := by
        funext k
        have hk := congrFun hμ k
        simp only [Pi.smul_apply, smul_eq_mul] at hk
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hk, hlam, toQ, hW k, hNN]
        push_cast
        rw [hμq]
        field_simp
        linear_combination (-(h k)) * hdτ
      have hxk : x0 + (s : ℚ) • h + toQ κ
          = lam • (((1 - a * b * K ^ 2 : ℤ) : ℚ) • toQ W + ((2 * a * K : ℤ) : ℚ) • toQ V) := by
        rw [hxs]
        funext k
        simp only [hκdef, hlam, toQ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hd, hKdef]
        push_cast
        field_simp
        ring
      rw [hxk, hxs, D.zQuadQ_smul, D.zQuadQ_smul]
      congr 1
      rw [D.zQuadQ_add, D.zQuadQ_smul, D.zQuadQ_smul, D.zPolarQ_smul_left, D.zPolarQ_smul_right, hVperp,
        D.zQuadQ_smul, ← haq, ← hbq, hd]
      push_cast
      ring
  · ---------------- non-radial branch (A2) ----------------
    have hXne : ∀ j : ℤ, x0 + (j : ℚ) • h ≠ 0 := by
      intro j hj; apply hrad; refine ⟨-(j : ℚ), ?_⟩
      funext k; have := congrFun hj k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
      linarith
    have hQX : ∀ j : ℤ, 0 < D.zQuadQ (x0 + (j : ℚ) • h) := fun j => hpos _ (hXne j)
    have hVne : ∀ j : ℤ, (2 * D.zQuadQ (x0 + (j : ℚ) • h)) • h
        - D.zPolarQ h (x0 + (j : ℚ) • h) • (x0 + (j : ℚ) • h) ≠ 0 := by
      intro j hj
      set X := x0 + (j : ℚ) • h with hX
      set q := D.zQuadQ X
      set p := D.zPolarQ h X
      have hq : 0 < q := hQX j
      have e1 : ∀ k, 2 * q * h k = p * X k := by
        intro k; have := congrFun hj k
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this; linarith
      by_cases hp : p = 0
      · apply hh0; funext k; have := e1 k; rw [hp] at this
        simp only [zero_mul, Pi.zero_apply] at this ⊢
        rcases mul_eq_zero.mp this with h1 | h1
        · linarith
        · exact h1
      · apply hrad
        refine ⟨2 * q / p - j, ?_⟩
        funext k
        have ek := e1 k
        simp only [hX, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ek ⊢
        apply mul_left_cancel₀ hp
        have hpc : p * (2 * q / p - j) = 2 * q - p * j := by field_simp
        calc p * x0 k = 2 * q * h k - p * j * h k := by linarith
          _ = p * ((2 * q / p - j) * h k) := by rw [← mul_assoc, hpc]; ring
    obtain ⟨j, hf2⟩ : ∃ j : ℤ, ∃ y : OutWit m r → ℚ,
        2 * D.zQuadQ (x0 + (j : ℚ) • h) * y (Sum.inl j0)
          - D.zPolarQ (x0 + (j : ℚ) • h) y * (x0 + (j : ℚ) • h) (Sum.inl j0) ≠ 0 := by
      by_contra H
      push_neg at H
      set e : OutWit m r → ℚ := Pi.single (Sum.inl j0) 1 with he
      have gam : ∀ j : ℤ, ∃ γ : ℚ, γ ≠ 0 ∧ ∀ y, D.zPolarQ (x0 + (j : ℚ) • h) y = γ * y (Sum.inl j0) := by
        intro j
        have hq := hQX j
        have he1 := H j e
        simp only [he, Pi.single_eq_same] at he1
        have hXj : (x0 + (j : ℚ) • h) (Sum.inl j0) ≠ 0 := by
          intro h0; rw [h0] at he1; linarith
        refine ⟨2 * D.zQuadQ (x0 + (j : ℚ) • h) / (x0 + (j : ℚ) • h) (Sum.inl j0),
          div_ne_zero (by linarith) hXj, fun y => ?_⟩
        have := H j y
        field_simp
        linarith
      obtain ⟨γ0, hγ0, hP0⟩ := gam 0
      obtain ⟨γ1, hγ1, hP1⟩ := gam 1
      set Z := γ1 • (x0 + ((0 : ℤ) : ℚ) • h) - γ0 • (x0 + ((1 : ℤ) : ℚ) • h) with hZ
      have hPZ : ∀ y, D.zPolarQ Z y = 0 := by
        intro y; rw [hZ, sr_polar_comb_left, hP0, hP1]; ring
      have hZ0 : Z = 0 := by
        by_contra hZne
        have := hpos Z hZne
        have h2 := hPZ Z
        rw [D.zPolarQ_self] at h2
        linarith
      by_cases hγ : γ1 = γ0
      · apply hh0; funext k
        have := congrFun hZ0 k
        simp only [hZ, hγ, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply] at this
        push_cast at this
        have : γ0 * h k = 0 := by linarith
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 hγ0
        · exact h1
      · apply hrad
        refine ⟨γ0 / (γ1 - γ0), ?_⟩
        funext k
        have := congrFun hZ0 k
        simp only [hZ, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
        push_cast at this
        have hne : γ1 - γ0 ≠ 0 := sub_ne_zero.mpr hγ
        field_simp
        linarith
    obtain ⟨M, κ, hM1, hκ, hn⟩ := D.sr_nonradial_step hpos (x0 + (j : ℚ) • h) h j0 (hVne j) hf2
    apply tool (j + M) κ hκ
    have e : x0 + (((j + M : ℤ)) : ℚ) • h = x0 + (j : ℚ) • h + (M : ℚ) • h := by
      push_cast; rw [add_smul, add_assoc]
    rw [e]
    exact hn

/-- The residual constant on one full input coset is constant everywhere (it is a polynomial). -/
theorem sr_const_of_coset (D : QuadraticGraphData n m r) (c0 : OutWit m r → ℚ)
    (C : Matrix (OutWit m r) (Fin n) ℚ) (a0 : Fin n → ℤ) (M : ℕ) (hM : 1 ≤ M) (R0 : ℚ)
    (h : ∀ t : Fin n → ℤ, D.residual (a0 + (M : ℤ) • t) (centreAt c0 C (a0 + (M : ℤ) • t)) = R0) :
    ∀ a, D.residual a (centreAt c0 C a) = R0 := by
  intro a
  obtain ⟨A, B, hl⟩ := D.sr_residual_line c0 C a0 (a - a0)
  have h0 : D.residual a0 (centreAt c0 C a0) = R0 := by simpa using h 0
  have hk : ∀ k : ℤ, A * ((M : ℚ) * k) ^ 2 + B * ((M : ℚ) * k) = 0 := by
    intro k
    have := hl ((M : ℤ) * k)
    have e : a0 + ((M : ℤ) * k) • (a - a0) = a0 + (M : ℤ) • (k • (a - a0)) := by rw [mul_smul]
    rw [e, h (k • (a - a0)), h0] at this
    push_cast at this
    linarith
  have hMq : (1 : ℚ) ≤ M := by exact_mod_cast hM
  have h1 := hk 1
  have h2 := hk 2
  push_cast at h1 h2
  have hA : A = 0 := by
    have : 2 * A * (M : ℚ) ^ 2 = 0 := by nlinarith
    have hM2 : (M : ℚ) ^ 2 ≠ 0 := by positivity
    rcases mul_eq_zero.mp this with h3 | h3
    · linarith
    · exact absurd h3 hM2
  have hB : B = 0 := by
    rw [hA] at h1
    have : B * (M : ℚ) = 0 := by linarith
    rcases mul_eq_zero.mp this with h3 | h3
    · exact h3
    · linarith
  have := hl 1
  have e1 : a0 + (1 : ℤ) • (a - a0) = a := by rw [one_smul]; abel
  rw [e1, hA, hB, h0] at this
  simpa using this

theorem affineSection_constResidual (D : QuadraticGraphData n m r) (hm : 0 < m)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (hrank : 2 ≤ D.polarRank)
    (hOU : D.OutputUnique)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a))
    (a0 : Fin n → ℤ) (M : ℕ) (hM : 1 ≤ M) (z0 : OutWit m r → ℤ) (G : Matrix (OutWit m r) (Fin n) ℤ)
    (hsec : ∀ t : Fin n → ℤ, D.SolZ (a0 + (M : ℤ) • t) (z0 + G *ᵥ t)) :
    ∃ R0 : ℚ, ∀ a, D.residual a (centreAt c0 C a) = R0 := by
  classical
  have hGC : ∀ k i, (G k i : ℚ) = (M : ℚ) * C k i := by
    intro k i
    have hs := D.lineSection_centredSlope_zero hm hpos hrank hOU c0 C hc a0 ((M : ℤ) • Pi.single i 1) z0
      (G *ᵥ Pi.single i 1) (fun s => by
        have := hsec (s • Pi.single i 1)
        rwa [Matrix.mulVec_smul, smul_comm] at this) 1
    rw [sr_centreAt_line] at hs
    have := congrFun hs k
    simp only [toQ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_smul] at this
    push_cast at this
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    push_cast at this
    have hsum : ∑ x, C k x * ((M : ℚ) * if x = i then 1 else 0) = (M : ℚ) * C k i := by
      rw [Finset.sum_eq_single i (fun x _ hx => by simp [hx]) (by simp)]
      simp; ring
    rw [hsum] at this
    linarith
  have hR0 := (D.sr_solZ_iff (hc a0) z0).mp (by simpa using hsec 0)
  refine ⟨D.residual a0 (centreAt c0 C a0), D.sr_const_of_coset c0 C a0 M hM _ fun t => ?_⟩
  have hq := (D.sr_solZ_iff (hc _) _).mp (hsec t)
  rw [← hq, ← hR0]
  congr 1
  funext k
  simp only [toQ, Pi.add_apply, Pi.sub_apply, cr_centreAt_add_smul, cr_mulVec_apply]
  push_cast
  simp only [hGC]
  have : ∑ i, (M : ℚ) * C k i * (t i : ℚ) = (M : ℚ) * ∑ i, C k i * (t i : ℚ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  linarith

theorem discriminantZero_line_const (D : QuadraticGraphData n m r) (hm : 0 < m)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (hrank : 2 ≤ D.polarRank)
    (hOU : D.OutputUnique)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a))
    (a0 v : Fin n → ℤ) (z0 : OutWit m r → ℤ) (hz0 : D.SolZ a0 z0)
    (hR0 : 0 < D.residual a0 (centreAt c0 C a0)) (A B : ℚ)
    (hline : ∀ t : ℤ, D.residual (a0 + t • v) (centreAt c0 C (a0 + t • v))
        = A * (t : ℚ) ^ 2 + B * t + D.residual a0 (centreAt c0 C a0))
    (hdisc : B ^ 2 = 4 * A * D.residual a0 (centreAt c0 C a0)) :
    A = 0 ∧ B = 0 := by
  classical
  set R0 := D.residual a0 (centreAt c0 C a0) with hR0def
  set x0 : OutWit m r → ℚ := toQ z0 - centreAt c0 C a0 with hx0
  have hQx0 : D.zQuadQ x0 = R0 := (D.sr_solZ_iff (hc a0) z0).mp hz0
  have hx0ne : x0 ≠ 0 := by intro h0; rw [h0] at hQx0; simp [zQuadQ] at hQx0; linarith
  set α : ℚ := B / (2 * R0) with hα
  set σ : OutWit m r → ℚ := (fun k => ∑ i, C k i * (v i : ℚ)) + α • x0 with hσ
  obtain ⟨M, hM1, hden⟩ := cr_exists_common_den σ
  choose G hG using hden
  have hMq : (1 : ℚ) ≤ M := by exact_mod_cast hM1
  have hA : A = B ^ 2 / (4 * R0) := by field_simp; linarith [hdisc]
  have e2 : ∀ s : ℤ, toQ (z0 + s • G) - centreAt c0 C (a0 + s • ((M : ℤ) • v))
      = (1 + α * ((s : ℚ) * M)) • x0 := by
    intro s
    have e1 : a0 + s • ((M : ℤ) • v) = a0 + (s * M) • v := by rw [smul_smul]
    rw [e1, sr_centreAt_line]
    funext k
    simp only [hx0, toQ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [hG k]
    simp only [hσ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx0, toQ, Pi.sub_apply]
    ring
  have hsec : ∀ s : ℤ, D.SolZ (a0 + s • ((M : ℤ) • v)) (z0 + s • G) := by
    intro s
    rw [D.sr_solZ_iff (hc _), e2 s, D.zQuadQ_smul, hQx0]
    have e1 : a0 + s • ((M : ℤ) • v) = a0 + (s * M) • v := by rw [smul_smul]
    rw [e1, hline (s * M), hA, hα]
    push_cast
    field_simp
    ring
  have hs := D.lineSection_centredSlope_zero hm hpos hrank hOU c0 C hc a0 ((M : ℤ) • v) z0 G hsec 1
  rw [e2 1] at hs
  have hαM : α * (M : ℚ) = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, x0 k ≠ 0 := by
      by_contra H; push_neg at H; exact hx0ne (funext H)
    have := congrFun hs k
    simp only [Pi.smul_apply, smul_eq_mul, hx0] at this
    push_cast at this
    have : α * M * x0 k = 0 := by rw [hx0] at hk; simp only [Pi.sub_apply] at hk ⊢; linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact h1
    · exact absurd h1 hk
  have hα0 : α = 0 := by
    rcases mul_eq_zero.mp hαM with h1 | h1
    · exact h1
    · linarith
  have hB : B = 0 := by
    rw [hα] at hα0
    rcases div_eq_zero_iff.mp hα0 with h1 | h1
    · exact h1
    · linarith
  refine ⟨by rw [hA, hB]; simp, hB⟩

theorem rankTwo_CCR (D : QuadraticGraphData n m r) (e : OutWit m r ≃ Fin 2) (hm : 0 < m)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a)) (hT : D.Total) (hOU : D.OutputUnique) :
    ∃ R0 : ℚ, ∀ a, D.residual a (centreAt c0 C a) = R0 := by
  by_cases hall : ∀ a, D.residual a (centreAt c0 C a) = 0
  · exact ⟨0, hall⟩
  push_neg at hall
  obtain ⟨a1, ha1⟩ := hall
  obtain ⟨z1, hz1⟩ := D.sr_solZ_of_total hT a1
  have hnn := D.sr_zQuadQ_nonneg hpos (toQ z1 - centreAt c0 C a1)
  rw [(D.sr_solZ_iff (hc a1) z1).mp hz1] at hnn
  have hR : 0 < D.residual a1 (centreAt c0 C a1) := lt_of_le_of_ne hnn (Ne.symm ha1)
  obtain ⟨M, G, hM, hs⟩ := D.binary_baseSection e hpos (D.sr_solZ_of_total hT) hz1 (hc a1) hR
  have hmr : m + r = 2 := by simpa using Fintype.card_congr e
  have hrank : 2 ≤ D.polarRank := by rw [D.sr_polarRank_eq hpos, hmr]
  exact D.affineSection_constResidual hm hpos hrank hOU c0 C hc a1 M hM z1 G hs

theorem residual_line_of_nonconstant (D : QuadraticGraphData n m r)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a)) (hT : D.Total)
    (hnc : ¬ ∃ R0 : ℚ, ∀ a, D.residual a (centreAt c0 C a) = R0) :
    ∃ (a0 v : Fin n → ℤ) (A B : ℚ), 0 < A ∧ ∀ t : ℤ,
      D.residual (a0 + t • v) (centreAt c0 C (a0 + t • v))
        = A * (t : ℚ) ^ 2 + B * t + D.residual a0 (centreAt c0 C a0) := by
  obtain ⟨a1, ha1⟩ : ∃ a1, D.residual a1 (centreAt c0 C a1) ≠ D.residual 0 (centreAt c0 C 0) := by
    by_contra H; push_neg at H; exact hnc ⟨_, H⟩
  obtain ⟨A, B, hl⟩ := D.sr_residual_line c0 C 0 a1
  have hnn : ∀ t : ℤ, 0 ≤ A * (t : ℚ) ^ 2 + B * t + D.residual 0 (centreAt c0 C 0) := by
    intro t
    rw [← hl t]
    obtain ⟨z, hz⟩ := D.sr_solZ_of_total hT (0 + t • a1)
    rw [← (D.sr_solZ_iff (hc _) z).mp hz]
    exact D.sr_zQuadQ_nonneg hpos _
  obtain ⟨hA0, hAB⟩ := sr_quad_nonneg A B _ hnn
  have h1 := hl 1
  have e1 : (0 : Fin n → ℤ) + (1 : ℤ) • a1 = a1 := by simp
  rw [e1] at h1
  refine ⟨0, a1, A, B, ?_, hl⟩
  rcases lt_or_eq_of_le hA0 with h | h
  · exact h
  · exfalso
    have hB := hAB h.symm
    rw [← h, hB] at h1
    apply ha1
    rw [h1]; push_cast; ring

theorem ccr_of_lineCollision (h : LineCollision) : ConstantResidualRigidity := by
  intro n m r D c0 C hm hpos hrank hc hT hOU
  by_contra hnc
  obtain ⟨a0, v, A, B, hA, hl⟩ := D.residual_line_of_nonconstant hpos c0 C hc hT hnc
  exact h n m r D c0 C a0 v A B hm hpos hrank hc (fun t => D.sr_solZ_of_total hT _) hl hA hOU

end QuadraticGraphData

theorem rankTwoSemidefiniteFullNF_holds : RankTwoSemidefiniteFullNF := by
  intro n m r D f hm hQ hsemi hrank hf
  have key : ∀ (D : QuadraticGraphData n m r), (∃ v, D.zQuad v ≠ 0) → (∀ u, 0 ≤ D.zQuadQ u) →
      D.polarRank = 2 → D.Defines f → FullVectorCosetNF f := by
    intro D hQ hnn hrank hf
    obtain ⟨U, hU, hdef, hpr, hpd⟩ := D.definite_reduction hm hf hQ hnn
    have hmle : m ≤ D.polarRank := D.m_le_polarRank hm hf hQ
    have hcard : Fintype.card (OutWit m (D.polarRank - m)) = 2 := by simp; omega
    let e : OutWit m (D.polarRank - m) ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
    have hnd : (D.compiledData U).NondegQ := fun v hv =>
      ⟨v, by rw [(D.compiledData U).zPolarQ_self]; have := hpd v hv; linarith⟩
    obtain ⟨c₀, cs, hcs⟩ := (D.compiledData U).exists_affine_centre_of_nondegQ hnd
    set C : Matrix (OutWit m (D.polarRank - m)) (Fin n) ℚ := fun k i => cs i k with hC
    have hcen : ∀ a, (D.compiledData U).IsCentre a (QuadraticGraphData.centreAt c₀ C a) := by
      intro a
      have : QuadraticGraphData.centreAt c₀ C a = c₀ + ∑ i, (a i : ℚ) • cs i := by
        funext k; simp [QuadraticGraphData.centreAt, hC, Finset.sum_apply, mul_comm]
      rw [this]; exact hcs a
    have hT : (D.compiledData U).Total := fun a => ⟨f a, (hdef a (f a)).mpr rfl⟩
    have hOU : (D.compiledData U).OutputUnique := (D.compiledData U).outputUnique_of_defines hdef
    obtain ⟨R0, hR0⟩ := (D.compiledData U).rankTwo_CCR e hm hpd c₀ C hcen hT hOU
    exact fullVectorCosetNF_of_commonSlope
      ((D.compiledData U).constResidual_commonSlopeIntNF c₀ C R0 hcen hR0 hdef)
  rcases hsemi with hnn | hnp
  · exact key D hQ hnn hrank hf
  · refine key D.negGraph ?_ ?_ ?_ (D.negGraph_defines hf)
    · obtain ⟨v, hv⟩ := hQ; exact ⟨v, by rw [D.negGraph_zQuad]; omega⟩
    · intro u; rw [D.negGraph_zQuadQ]; linarith [hnp u]
    · rw [D.negGraph_polarRank]; exact hrank

end DiophCompression.ResearchUpgrade
