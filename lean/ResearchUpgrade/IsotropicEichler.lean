/-
  IsotropicEichler.lean — s57.  GPT R45 Packet B (GATE27): the isotropic branch in polar rank ≥ 3, proved in the ORIGINAL
  coordinates with Eichler transformations (no radical compression and no hyperbolic basis, unlike the reviewer's route).

  * `zQuadQ_eichler` — for isotropic `e` and `v` polar-orthogonal to `e`,
    `x ↦ x + polar(x,e)·v − (polar(x,v) + Q(v)·polar(x,e))·e` preserves `Q`.
  * `exists_isotropic_partner`, `polarRank_le_two_of_null_complement`, `three_le_polarRank_of_complement` — the hyperbolic
    pair and the two rank tests (via `polarMapQ` and `finrank`).
  * `eichler_output_constraints` — the Eichler family through an integer solution returns to the integer lattice at
    `t = ±M` (one common denominator); output uniqueness at these two points kills both coefficients.
  * `outputs_vanish_on_perp`, `false_of_offRadical_of_three_le_polarRank` — in polar rank ≥ 3 no integer solution has an
    off-centre vector outside the radical; `isotropicBranchFullNF_of_three_le_polarRank` — hence a global affine form.

  Statements frozen before proof (`~/lean/s57_evidence/freeze/F3_FREEZE_s57.lean` `d842bd18`, ruling of Dr. Fukui
  2026-09-25 21:23).  Claim tags: [P] (std-3) for every theorem.
-/
import ResearchUpgrade.FullNFExtraction
import ResearchUpgrade.IsotropicDirection
import ResearchUpgrade.RankExcessCompiler
import ResearchUpgrade.ConstResidual

namespace DiophCompression.ResearchUpgrade

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

theorem zQuadQ_eichler {e v : OutWit m r → ℚ} (he : D.zQuadQ e = 0) (hev : D.zPolarQ e v = 0)
    (x : OutWit m r → ℚ) :
    D.zQuadQ (x + D.zPolarQ x e • v - (D.zPolarQ x v + D.zQuadQ v * D.zPolarQ x e) • e) = D.zQuadQ x := by
  have hve : D.zPolarQ v e = 0 := by rw [D.zPolarQ_symm]; exact hev
  set a := D.zPolarQ x e
  set s := D.zPolarQ x v + D.zQuadQ v * a
  have h1 : x + a • v - s • e = (x + a • v) + (-s) • e := by rw [neg_smul, ← sub_eq_add_neg]
  rw [h1, D.zQuadQ_add, D.zQuadQ_add, D.zQuadQ_smul, D.zQuadQ_smul, he, D.zPolarQ_smul_right,
    D.zPolarQ_smul_right, D.zPolarQ_add_left, D.zPolarQ_smul_left, hve]
  simp only [s, a]
  ring

theorem exists_isotropic_partner {e : OutWit m r → ℚ} (he : D.zQuadQ e = 0) (hne : ¬ D.InRadicalQ e) :
    ∃ e' : OutWit m r → ℚ, D.zQuadQ e' = 0 ∧ D.zPolarQ e e' = 1 := by
  obtain ⟨y, hy⟩ : ∃ y, D.zPolarQ e y ≠ 0 := by
    by_contra h; push_neg at h; exact hne h
  have h1 : y - (D.zQuadQ y / D.zPolarQ e y) • e = y + (-(D.zQuadQ y / D.zPolarQ e y)) • e := by
    rw [neg_smul, ← sub_eq_add_neg]
  refine ⟨(D.zPolarQ e y)⁻¹ • (y - (D.zQuadQ y / D.zPolarQ e y) • e), ?_, ?_⟩
  · rw [D.zQuadQ_smul, h1, D.zQuadQ_add, D.zQuadQ_smul, he, D.zPolarQ_smul_right, D.zPolarQ_symm y e]
    field_simp
    ring
  · rw [D.zPolarQ_smul_right, h1, D.zPolarQ_add_right, D.zPolarQ_smul_right, D.zPolarQ_self, he]
    field_simp
    ring

/-- Polar value of a vector against a two-term combination (helper for the rank lemmas). -/
theorem zPolarQ_sub_two_smul (u w : OutWit m r → ℚ) (α β : ℚ) (e₁ e₂ : OutWit m r → ℚ) :
    D.zPolarQ (u - α • e₁ - β • e₂) w = D.zPolarQ u w - α * D.zPolarQ e₁ w - β * D.zPolarQ e₂ w := by
  have := D.polarMapQ.map_sub (u - α • e₁) (β • e₂)
  have h2 := D.polarMapQ.map_sub u (α • e₁)
  have h3 := congrArg (fun φ => φ w) this
  have h4 := congrArg (fun φ => φ w) h2
  simp only [LinearMap.sub_apply, polarMapQ_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul] at h3 h4
  rw [h3, h4]

theorem polarRank_le_two_of_null_complement {e₁ e₂ : OutWit m r → ℚ} (h₁ : D.zQuadQ e₁ = 0)
    (h₂ : D.zQuadQ e₂ = 0) (h₁₂ : D.zPolarQ e₁ e₂ ≠ 0)
    (hnull : ∀ w, D.zPolarQ e₁ w = 0 → D.zPolarQ e₂ w = 0 → D.zQuadQ w = 0) : D.polarRank ≤ 2 := by
  classical
  set c := D.zPolarQ e₁ e₂
  have h21 : D.zPolarQ e₂ e₁ = c := D.zPolarQ_symm _ _
  have h11 : D.zPolarQ e₁ e₁ = 0 := by rw [D.zPolarQ_self, h₁, mul_zero]
  have h22 : D.zPolarQ e₂ e₂ = 0 := by rw [D.zPolarQ_self, h₂, mul_zero]
  -- projection onto the complement
  let pr : (OutWit m r → ℚ) → (OutWit m r → ℚ) := fun u =>
    u - (D.zPolarQ e₂ u / c) • e₁ - (D.zPolarQ e₁ u / c) • e₂
  have hpr1 : ∀ u, D.zPolarQ e₁ (pr u) = 0 := by
    intro u
    show D.zPolarQ e₁ (u - (D.zPolarQ e₂ u / c) • e₁ - (D.zPolarQ e₁ u / c) • e₂) = 0
    rw [D.zPolarQ_symm, zPolarQ_sub_two_smul, h11, h21, D.zPolarQ_symm u e₁, div_mul_cancel₀ _ h₁₂]
    ring
  have hpr2 : ∀ u, D.zPolarQ e₂ (pr u) = 0 := by
    intro u
    show D.zPolarQ e₂ (u - (D.zPolarQ e₂ u / c) • e₁ - (D.zPolarQ e₁ u / c) • e₂) = 0
    rw [D.zPolarQ_symm, zPolarQ_sub_two_smul, h22, D.zPolarQ_symm u e₂, div_mul_cancel₀ _ h₁₂]
    ring
  have hcomp : ∀ u w, D.zPolarQ (pr u) (pr w) = 0 := by
    intro u w
    have hs := D.zQuadQ_add (pr u) (pr w)
    have hsum : D.zQuadQ (pr u + pr w) = 0 := hnull _ (by rw [D.zPolarQ_add_right, hpr1, hpr1, add_zero])
      (by rw [D.zPolarQ_add_right, hpr2, hpr2, add_zero])
    rw [hsum, hnull _ (hpr1 u) (hpr2 u), hnull _ (hpr1 w) (hpr2 w)] at hs
    linarith
  -- every polar functional lies in the span of the two
  let g : (Fin 2 → ℚ) →ₗ[ℚ] Module.Dual ℚ (OutWit m r → ℚ) :=
    (LinearMap.proj 0).smulRight (D.polarMapQ e₁) + (LinearMap.proj 1).smulRight (D.polarMapQ e₂)
  have hle : LinearMap.range D.polarMapQ ≤ LinearMap.range g := by
    rintro φ ⟨u, rfl⟩
    refine ⟨![D.zPolarQ e₂ u / c, D.zPolarQ e₁ u / c], ?_⟩
    refine LinearMap.ext fun w => ?_
    simp only [g, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, polarMapQ_apply]
    have hu : D.zPolarQ (pr u) w = 0 := by
      have := hcomp u w
      have hw : pr w = w - (D.zPolarQ e₂ w / c) • e₁ - (D.zPolarQ e₁ w / c) • e₂ := rfl
      rw [D.zPolarQ_symm, hw, zPolarQ_sub_two_smul, D.zPolarQ_symm w, hpr1, hpr2] at this
      simpa using this
    have := zPolarQ_sub_two_smul D u w (D.zPolarQ e₂ u / c) (D.zPolarQ e₁ u / c) e₁ e₂
    change D.zPolarQ (pr u) w = _ at this
    rw [hu] at this
    linarith
  calc D.polarRank = Module.finrank ℚ (LinearMap.range D.polarMapQ) := rfl
    _ ≤ Module.finrank ℚ (LinearMap.range g) := Submodule.finrank_mono hle
    _ ≤ Module.finrank ℚ (Fin 2 → ℚ) := LinearMap.finrank_range_le g
    _ = 2 := by simp

theorem three_le_polarRank_of_complement {e₁ e₂ w : OutWit m r → ℚ} (h₁ : D.zQuadQ e₁ = 0)
    (h₂ : D.zQuadQ e₂ = 0) (h₁₂ : D.zPolarQ e₁ e₂ ≠ 0) (hw₁ : D.zPolarQ e₁ w = 0) (hw₂ : D.zPolarQ e₂ w = 0)
    (hw : D.zQuadQ w ≠ 0) : 3 ≤ D.polarRank := by
  classical
  let φ : Fin 3 → Module.Dual ℚ (OutWit m r → ℚ) := ![D.polarMapQ e₁, D.polarMapQ e₂, D.polarMapQ w]
  have h11 : D.zPolarQ e₁ e₁ = 0 := by rw [D.zPolarQ_self, h₁, mul_zero]
  have h22 : D.zPolarQ e₂ e₂ = 0 := by rw [D.zPolarQ_self, h₂, mul_zero]
  have hli : LinearIndependent ℚ φ := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have ev : ∀ y, g 0 * D.zPolarQ e₁ y + g 1 * D.zPolarQ e₂ y + g 2 * D.zPolarQ w y = 0 := by
      intro y
      have := congrArg (fun ψ => ψ y) hg
      simpa [φ, Fin.sum_univ_three] using this
    have a1 := ev e₂
    have a2 := ev e₁
    have a3 := ev w
    rw [h22, D.zPolarQ_symm w e₂, hw₂] at a1
    rw [h11, D.zPolarQ_symm e₂ e₁, D.zPolarQ_symm w e₁, hw₁] at a2
    rw [hw₁, hw₂, D.zPolarQ_self] at a3
    have g0 : g 0 = 0 := by
      have : g 0 * D.zPolarQ e₁ e₂ = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right h₁₂
    have g1 : g 1 = 0 := by
      have : g 1 * D.zPolarQ e₁ e₂ = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right h₁₂
    have g2 : g 2 = 0 := by
      have : g 2 * (2 * D.zQuadQ w) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd (by linarith : D.zQuadQ w = 0) hw
    intro i; fin_cases i <;> simp [g0, g1, g2]
  have hspan : Submodule.span ℚ (Set.range φ) ≤ LinearMap.range D.polarMapQ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> exact ⟨_, rfl⟩
  calc 3 = Fintype.card (Fin 3) := by simp
    _ = Module.finrank ℚ (Submodule.span ℚ (Set.range φ)) := (finrank_span_eq_card hli).symm
    _ ≤ Module.finrank ℚ (LinearMap.range D.polarMapQ) := Submodule.finrank_mono hspan
    _ = D.polarRank := rfl

theorem eichler_output_constraints (hOU : D.OutputUnique) {a : Fin n → ℤ} {c : OutWit m r → ℚ}
    (hc : D.IsCentre a c) {z : OutWit m r → ℤ} (hz : D.SolZ a z) {e v : OutWit m r → ℚ}
    (he : D.zQuadQ e = 0) (hev : D.zPolarQ e v = 0) (j : Fin m) :
    D.zPolarQ (toQ z - c) e * v (Sum.inl j) - D.zPolarQ (toQ z - c) v * e (Sum.inl j) = 0 ∧
      D.zQuadQ v * D.zPolarQ (toQ z - c) e * e (Sum.inl j) = 0 := by
  classical
  set x := toQ z - c with hxdef
  set A : OutWit m r → ℚ := D.zPolarQ x e • v - D.zPolarQ x v • e with hA
  set B : OutWit m r → ℚ := (-(D.zQuadQ v * D.zPolarQ x e)) • e with hB
  -- every integer point on the Eichler family `x + tA + t²B` is a solution
  have hsol : ∀ (Z : OutWit m r → ℤ) (t : ℚ), toQ Z = toQ z + t • A + t ^ 2 • B → D.SolZ a Z := by
    intro Z t hZ
    have hE : toQ Z - c
        = x + D.zPolarQ x e • (t • v) - (D.zPolarQ x (t • v) + D.zQuadQ (t • v) * D.zPolarQ x e) • e := by
      rw [hZ, D.zPolarQ_smul_right, D.zQuadQ_smul]
      funext k
      simp only [hxdef, hA, hB, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hq : D.zQuadQ (toQ Z - c) = D.zQuadQ x := by
      rw [hE]
      exact D.zQuadQ_eichler he (by rw [D.zPolarQ_smul_right, hev, mul_zero]) x
    have h0 := D.cr_eval_cast hc Z
    rw [hq, hxdef, D.offCentre_norm hc hz, sub_self] at h0
    unfold QuadraticGraphData.SolZ
    exact_mod_cast h0
  obtain ⟨wA, dA, hdA, hwA⟩ := exists_int_clear A
  obtain ⟨wB, dB, hdB, hwB⟩ := exists_int_clear B
  have hM : (0 : ℚ) < (dA : ℚ) * dB := by positivity
  let IA : OutWit m r → ℤ := fun k => (dB : ℤ) * wA k
  let IB : OutWit m r → ℤ := fun k => (dA : ℤ) * wB k
  have hIA : ∀ k, (IA k : ℚ) = ((dA : ℚ) * dB) * A k := by
    intro k; simp only [IA]; push_cast; rw [hwA k]; ring
  have hIB : ∀ k, (IB k : ℚ) = ((dA : ℚ) * dB) * B k := by
    intro k; simp only [IB]; push_cast; rw [hwB k]; ring
  let Zp : OutWit m r → ℤ := fun k => z k + IA k + ((dA : ℤ) * dB) * IB k
  let Zm : OutWit m r → ℤ := fun k => z k - IA k + ((dA : ℤ) * dB) * IB k
  have hZp : D.SolZ a Zp := hsol Zp ((dA : ℚ) * dB) (by
    funext k; simp only [toQ, Zp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; push_cast
    rw [hIA, hIB]; ring)
  have hZm : D.SolZ a Zm := hsol Zm (-((dA : ℚ) * dB)) (by
    funext k; simp only [toQ, Zm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; push_cast
    rw [hIA, hIB]; ring)
  have op := congrFun (hOU a _ _ (D.graph_of_solZ hZp) (D.graph_of_solZ hz)) j
  have om := congrFun (hOU a _ _ (D.graph_of_solZ hZm) (D.graph_of_solZ hz)) j
  simp only [outProj, Zp, Zm] at op om
  have hIA0 : IA (Sum.inl j) = 0 := by linarith
  have hIB0 : IB (Sum.inl j) = 0 := by
    have h2 : ((dA : ℤ) * dB) * IB (Sum.inl j) = 0 := by linarith
    have hne : ((dA : ℤ) * dB) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h2).resolve_left hne
  have hA0 : A (Sum.inl j) = 0 := by
    have := hIA (Sum.inl j); rw [hIA0, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hM.ne'
  have hB0 : B (Sum.inl j) = 0 := by
    have := hIB (Sum.inl j); rw [hIB0, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hM.ne'
  simp only [hA, hB, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hA0 hB0
  exact ⟨hA0, by linarith⟩

theorem outputs_vanish_on_perp (hOU : D.OutputUnique) {a : Fin n → ℤ} {c : OutWit m r → ℚ}
    (hc : D.IsCentre a c) {z : OutWit m r → ℤ} (hz : D.SolZ a z) {e : OutWit m r → ℚ}
    (he : D.zQuadQ e = 0) (hxe : D.zPolarQ (toQ z - c) e ≠ 0) (hrank : 3 ≤ D.polarRank)
    (v : OutWit m r → ℚ) (hv : D.zPolarQ e v = 0) (j : Fin m) : v (Sum.inl j) = 0 := by
  have hne : ¬ D.InRadicalQ e := fun h => hxe (by rw [D.zPolarQ_symm]; exact h _)
  obtain ⟨e', he'q, hee'⟩ := D.exists_isotropic_partner he hne
  obtain ⟨w, hw1, -, hwq⟩ : ∃ w, D.zPolarQ e w = 0 ∧ D.zPolarQ e' w = 0 ∧ D.zQuadQ w ≠ 0 := by
    by_contra H
    push_neg at H
    have := D.polarRank_le_two_of_null_complement he he'q (by rw [hee']; norm_num) H
    omega
  have hej : e (Sum.inl j) = 0 := by
    have h := (D.eichler_output_constraints hOU hc hz he hw1 j).2
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hwq
      · exact absurd h'' hxe
    · exact h'
  have h := (D.eichler_output_constraints hOU hc hz he hv j).1
  rw [hej, mul_zero, sub_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hxe

theorem false_of_offRadical_of_three_le_polarRank (hm : 0 < m) (hOU : D.OutputUnique) {a : Fin n → ℤ}
    {c : OutWit m r → ℚ} (hc : D.IsCentre a c) {z : OutWit m r → ℤ} (hz : D.SolZ a z)
    (hx : ¬ D.InRadicalQ (toQ z - c)) {e₀ : OutWit m r → ℚ} (he₀q : D.zQuadQ e₀ = 0) (he₀ : ¬ D.InRadicalQ e₀)
    (hrank : 3 ≤ D.polarRank) : False := by
  classical
  obtain ⟨e₁, he₁q, hxe₁⟩ := D.exists_isotropic_nonorthogonal_of_nonradical he₀q he₀ hx
  have hne₁ : ¬ D.InRadicalQ e₁ := fun h => hxe₁ (by rw [D.zPolarQ_symm]; exact h _)
  obtain ⟨e₂, he₂q, h12⟩ := D.exists_isotropic_partner he₁q hne₁
  obtain ⟨e₃, he₃q, hxe₃, h13⟩ : ∃ e₃, D.zQuadQ e₃ = 0 ∧ D.zPolarQ (toQ z - c) e₃ ≠ 0 ∧
      D.zPolarQ e₁ e₃ ≠ 0 := by
    by_cases hx2 : D.zPolarQ (toQ z - c) e₂ = 0
    · obtain ⟨w, hw1, hw2, hwq⟩ : ∃ w, D.zPolarQ e₁ w = 0 ∧ D.zPolarQ e₂ w = 0 ∧ D.zQuadQ w ≠ 0 := by
        by_contra H
        push_neg at H
        have := D.polarRank_le_two_of_null_complement he₁q he₂q (by rw [h12]; norm_num) H
        omega
      have key : ∀ s : ℚ, s ≠ 0 →
          D.zQuadQ (s • e₁ + (-(D.zQuadQ w) / s) • e₂ + w) = 0 ∧
          D.zPolarQ e₁ (s • e₁ + (-(D.zQuadQ w) / s) • e₂ + w) = -(D.zQuadQ w) / s ∧
          D.zPolarQ (toQ z - c) (s • e₁ + (-(D.zQuadQ w) / s) • e₂ + w)
            = s * D.zPolarQ (toQ z - c) e₁ + D.zPolarQ (toQ z - c) w := by
        intro s hs
        refine ⟨?_, ?_, ?_⟩
        · rw [D.zQuadQ_add, D.zQuadQ_add, D.zQuadQ_smul, D.zQuadQ_smul, D.zPolarQ_add_left,
            D.zPolarQ_smul_left, D.zPolarQ_smul_left, D.zPolarQ_smul_right, h12, he₁q, he₂q, hw1,
            D.zPolarQ_smul_left, hw2]
          field_simp
          ring
        · rw [D.zPolarQ_add_right, D.zPolarQ_add_right, D.zPolarQ_smul_right, D.zPolarQ_smul_right,
            D.zPolarQ_self, he₁q, h12, hw1]
          ring
        · rw [D.zPolarQ_add_right, D.zPolarQ_add_right, D.zPolarQ_smul_right, D.zPolarQ_smul_right, hx2]
          ring
      by_cases hs1 : D.zPolarQ (toQ z - c) e₁ + D.zPolarQ (toQ z - c) w = 0
      · obtain ⟨k1, k2, k3⟩ := key 2 two_ne_zero
        refine ⟨_, k1, ?_, ?_⟩
        · rw [k3]; intro h; apply hxe₁; linarith
        · rw [k2]; exact div_ne_zero (neg_ne_zero.mpr hwq) two_ne_zero
      · obtain ⟨k1, k2, k3⟩ := key 1 one_ne_zero
        refine ⟨_, k1, ?_, ?_⟩
        · rw [k3, one_mul]; exact hs1
        · rw [k2]; exact div_ne_zero (neg_ne_zero.mpr hwq) one_ne_zero
    · exact ⟨e₂, he₂q, hx2, by rw [h12]; norm_num⟩
  let j : Fin m := ⟨0, hm⟩
  let u : OutWit m r → ℚ := Pi.single (Sum.inl j) 1
  have he₃j : e₃ (Sum.inl j) = 0 :=
    D.outputs_vanish_on_perp hOU hc hz he₃q hxe₃ hrank e₃ (by rw [D.zPolarQ_self, he₃q, mul_zero]) j
  have hperp : D.zPolarQ e₁ (u - (D.zPolarQ e₁ u / D.zPolarQ e₁ e₃) • e₃) = 0 := by
    rw [sub_eq_add_neg, ← neg_smul, D.zPolarQ_add_right, D.zPolarQ_smul_right]
    field_simp
    ring
  have hu := D.outputs_vanish_on_perp hOU hc hz he₁q hxe₁ hrank _ hperp j
  simp [u, he₃j] at hu

end QuadraticGraphData

/-- **D1, polar rank ≥ 3.**  The isotropic branch in polar rank ≥ 3 has the full-residue NF (unconditional). -/
theorem isotropicBranchFullNF_of_three_le_polarRank :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ x : OutWit m r → ℚ, D.zQuadQ x = 0 ∧ ¬ D.InRadicalQ x) → 3 ≤ D.polarRank →
      D.Defines f → FullVectorCosetNF f := by
  classical
  intro n m r D f hm ⟨e₀, he₀q, he₀⟩ hrank hf
  have hQ : ∃ x : OutWit m r → ℤ, D.zQuad x ≠ 0 := by
    refine D.exists_int_zQuad_ne_zero (fun h => he₀ (fun w => ?_))
    have := D.zQuadQ_add e₀ w
    rw [h, h, h] at this
    linarith
  have hOU := D.outputUnique_of_defines hf
  have hall : ∀ (a : Fin n → ℤ) (e : OutWit m r → ℚ), D.InRadicalQ e → D.zLinQ a e = 0 := by
    intro a e he
    obtain ⟨z, hz⟩ := D.exists_solZ_of_defines hf a
    exact D.zLinQ_radicalQ_eq_zero hm hOU hz hQ he
  obtain ⟨c₀, cs, hcen⟩ := D.exists_affine_centre_of_all_inputs hall
  have hcen' : ∀ a : Fin n → ℤ, D.IsCentre a (centreFamily c₀ cs a) := hcen
  have hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
      D.InRadicalQ (toQ z - centreFamily c₀ cs a) := by
    intro a z hz
    by_contra hx
    exact D.false_of_offRadical_of_three_le_polarRank hm hOU (hcen' a) hz hx he₀q he₀ hrank
  exact D.fullVectorCosetNF_of_offCentre_radical hm hQ hf hrad

end DiophCompression.ResearchUpgrade
