/-
  SplitRankTwo.lean — s57.  GPT R45 Packet C (GATE27): the isotropic branch in polar rank ≤ 2 (split rank two), in the
  ORIGINAL coordinates.  The reviewer's prime-power roots and Hensel lifting are replaced by an elementary divisor
  construction (`exists_scaling_divisor`): with `k₀ = k₁ + K·F(k₁)·s`, `F(k₀) = F(k₁)·μ(s)` and `μ(s) ≡ 1 (mod K)`; the
  scaling factor `λ = μ(s)` may be negative (the scaling `(X, Y) ↦ (λX, Y/λ)` is an isometry for any `λ ≠ 0`).

  * `hyperbolic_form_of_polarRank_le_two` — `Q u = polar(u,e₂)·polar(u,e₁)` with a radical remainder.
  * `constResidual_of_isotropic_polarRank_le_two` — along an input line the quadratic section through one integer solution
    returns to the lattice on a progression; a factor scaling by `λ` gives a second integer solution at the same input with
    a different output, unless the residual is constant.
  * `isotropicBranchFullNF_of_polarRank_le_two` — then `constResidual_fullVectorCosetNF` (no definiteness needed).

  Statements frozen before proof (`~/lean/s57_evidence/freeze/F4_FREEZE_s57.lean` `3f4b493d`, ruling of Dr. Fukui
  2026-09-25 21:23).  Claim tags: [P] (std-3) for every theorem.
-/
import ResearchUpgrade.IsotropicEichler
import ResearchUpgrade.SectionRigidity

namespace DiophCompression.ResearchUpgrade

theorem exists_scaling_divisor (α β γ K : ℤ) (hF : α ≠ 0 ∨ β ≠ 0) (hK : 0 < K) :
    ∃ k₀ lam : ℤ, lam ≠ 0 ∧ lam ≠ 1 ∧ K ∣ lam - 1 ∧ lam ∣ α * k₀ ^ 2 + β * k₀ + γ := by
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℤ, α * k₁ ^ 2 + β * k₁ + γ ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    norm_num at h0 h1 h2
    rcases hF with hα | hβ
    · exact hα (by linarith)
    · exact hβ (by linarith)
  set F₁ := α * k₁ ^ 2 + β * k₁ + γ with hF₁
  set X := K * (2 * α * k₁ + β) with hX
  set Y := α * K ^ 2 * F₁ with hY
  have hXY : X ≠ 0 ∨ Y ≠ 0 := by
    by_cases hα : α = 0
    · left
      have hβ : β ≠ 0 := hF.resolve_left (not_not.mpr hα)
      rw [hX, hα]; simpa using ⟨hK.ne', hβ⟩
    · right
      exact mul_ne_zero (mul_ne_zero hα (pow_ne_zero 2 hK.ne')) hk₁
  have key : ∀ s : ℤ, α * (k₁ + K * F₁ * s) ^ 2 + β * (k₁ + K * F₁ * s) + γ = F₁ * (1 + s * X + s ^ 2 * Y) := by
    intro s; rw [hX, hY, hF₁]; ring
  obtain ⟨s, hs0, hs1⟩ : ∃ s : ℤ, 1 + s * X + s ^ 2 * Y ≠ 0 ∧ 1 + s * X + s ^ 2 * Y ≠ 1 := by
    by_contra h
    push_neg at h
    have c : ∀ s : ℤ, 1 + s * X + s ^ 2 * Y = 0 ∨ 1 + s * X + s ^ 2 * Y = 1 := by
      intro s; by_cases hz : 1 + s * X + s ^ 2 * Y = 0
      · exact Or.inl hz
      · exact Or.inr (h s hz)
    have c1 := c 1; have c2 := c 2; have c3 := c 3; have c4 := c 4; have c5 := c 5
    norm_num at c1 c2 c3 c4 c5
    omega
  refine ⟨k₁ + K * F₁ * s, 1 + s * X + s ^ 2 * Y, hs0, hs1, ⟨s * (2 * α * k₁ + β) + s ^ 2 * α * K * F₁, ?_⟩, ?_⟩
  · rw [hX, hY]; ring
  · rw [key]; exact Dvd.intro_left _ rfl

/-- Three equal values of an integer quadratic along an arithmetic progression force it to be constant. -/
theorem quad_const_of_three (α β γ k₀ lam : ℤ) (hlam : lam ≠ 0)
    (h1 : α * (k₀ + lam) ^ 2 + β * (k₀ + lam) + γ = α * k₀ ^ 2 + β * k₀ + γ)
    (h2 : α * (k₀ + 2 * lam) ^ 2 + β * (k₀ + 2 * lam) + γ = α * k₀ ^ 2 + β * k₀ + γ) :
    α = 0 ∧ β = 0 := by
  have e1 : lam * (2 * α * k₀ + β + α * lam) = 0 := by linear_combination h1
  have e2 : lam * (2 * (2 * α * k₀ + β + 2 * α * lam)) = 0 := by linear_combination h2
  have f1 := (mul_eq_zero.mp e1).resolve_left hlam
  have f2 := (mul_eq_zero.mp e2).resolve_left hlam
  have hαl : α * lam = 0 := by linarith
  have hα : α = 0 := (mul_eq_zero.mp hαl).resolve_right hlam
  refine ⟨hα, ?_⟩
  rw [hα] at f1; linarith

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

theorem hyperbolic_form_of_polarRank_le_two {e₁ e₂ : OutWit m r → ℚ} (h₁ : D.zQuadQ e₁ = 0)
    (h₂ : D.zQuadQ e₂ = 0) (h₁₂ : D.zPolarQ e₁ e₂ = 1) (hrank : D.polarRank ≤ 2) (u : OutWit m r → ℚ) :
    D.zQuadQ u = D.zPolarQ u e₂ * D.zPolarQ u e₁ ∧
      D.InRadicalQ (u - D.zPolarQ u e₂ • e₁ - D.zPolarQ u e₁ • e₂) := by
  have h21 : D.zPolarQ e₂ e₁ = 1 := by rw [D.zPolarQ_symm, h₁₂]
  have h11 : D.zPolarQ e₁ e₁ = 0 := by rw [D.zPolarQ_self, h₁, mul_zero]
  have h22 : D.zPolarQ e₂ e₂ = 0 := by rw [D.zPolarQ_self, h₂, mul_zero]
  have hnull : ∀ w, D.zPolarQ e₁ w = 0 → D.zPolarQ e₂ w = 0 → D.zQuadQ w = 0 := by
    intro w hw1 hw2
    by_contra hw
    have := D.three_le_polarRank_of_complement h₁ h₂ (by rw [h₁₂]; norm_num) hw1 hw2 hw
    omega
  have hcomp : ∀ v, D.zPolarQ e₁ (v - D.zPolarQ v e₂ • e₁ - D.zPolarQ v e₁ • e₂) = 0 ∧
      D.zPolarQ e₂ (v - D.zPolarQ v e₂ • e₁ - D.zPolarQ v e₁ • e₂) = 0 := by
    intro v
    constructor
    · rw [D.zPolarQ_symm, D.zPolarQ_sub_two_smul, h11, h21]; ring
    · rw [D.zPolarQ_symm, D.zPolarQ_sub_two_smul, h₁₂, h22]; ring
  set ρ := u - D.zPolarQ u e₂ • e₁ - D.zPolarQ u e₁ • e₂ with hρ
  have hρ1 : D.zPolarQ e₁ ρ = 0 := (hcomp u).1
  have hρ2 : D.zPolarQ e₂ ρ = 0 := (hcomp u).2
  have hρrad : D.InRadicalQ ρ := by
    intro w
    obtain ⟨hw1, hw2⟩ := hcomp w
    have hsum := D.zQuadQ_add ρ (w - D.zPolarQ w e₂ • e₁ - D.zPolarQ w e₁ • e₂)
    rw [hnull _ (by rw [D.zPolarQ_add_right, hρ1, hw1, add_zero]) (by rw [D.zPolarQ_add_right, hρ2, hw2, add_zero]),
      hnull _ hρ1 hρ2, hnull _ hw1 hw2] at hsum
    have hpw : D.zPolarQ ρ (w - D.zPolarQ w e₂ • e₁ - D.zPolarQ w e₁ • e₂) = 0 := by linarith
    rw [D.zPolarQ_symm, D.zPolarQ_sub_two_smul, hρ1, hρ2] at hpw
    rw [D.zPolarQ_symm]; linarith
  refine ⟨?_, hρrad⟩
  have hu : u = ρ + (D.zPolarQ u e₂ • e₁ + D.zPolarQ u e₁ • e₂) := by rw [hρ]; abel
  have hρq : D.zQuadQ ρ = 0 := hnull ρ hρ1 hρ2
  conv_lhs => rw [hu]
  rw [D.zQuadQ_add, D.zQuadQ_add, D.zQuadQ_smul, D.zQuadQ_smul, D.zPolarQ_add_right, D.zPolarQ_smul_right,
    D.zPolarQ_smul_right, D.zPolarQ_smul_left, D.zPolarQ_smul_right, D.zPolarQ_symm ρ e₁, D.zPolarQ_symm ρ e₂,
    hρ1, hρ2, hρq, h₁, h₂, h₁₂]
  ring

/-- The value of the form on `X e₁ + Y e₂ + ρ` with `ρ` radical. -/
theorem zQuadQ_hyperbolic_section {e₁ e₂ ρ : OutWit m r → ℚ} (h₁ : D.zQuadQ e₁ = 0) (h₂ : D.zQuadQ e₂ = 0)
    (h₁₂ : D.zPolarQ e₁ e₂ = 1) (hρ : D.InRadicalQ ρ) (X Y : ℚ) :
    D.zQuadQ (X • e₁ + Y • e₂ + ρ) = X * Y := by
  have hρq : D.zQuadQ ρ = 0 := D.zQuadQ_eq_zero_of_inRadicalQ hρ
  have hp : D.zPolarQ (X • e₁ + Y • e₂) ρ = 0 := by rw [D.zPolarQ_symm]; exact hρ _
  rw [D.zQuadQ_add, hp, hρq, D.zQuadQ_add, D.zQuadQ_smul, D.zQuadQ_smul, D.zPolarQ_smul_left,
    D.zPolarQ_smul_right, h₁, h₂, h₁₂]
  ring

theorem constResidual_of_isotropic_polarRank_le_two (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) {e₀ : OutWit m r → ℚ} (he₀q : D.zQuadQ e₀ = 0) (he₀ : ¬ D.InRadicalQ e₀)
    (hrank : D.polarRank ≤ 2) (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ)
    (hcen : ∀ a : Fin n → ℤ, D.IsCentre a (centreFamily c₀ cs a)) :
    ∃ R0 : ℚ, ∀ a : Fin n → ℤ, D.residual a (centreFamily c₀ cs a) = R0 := by
  classical
  have hOU := D.outputUnique_of_defines hf
  have hQ : ∃ x : OutWit m r → ℤ, D.zQuad x ≠ 0 := by
    refine D.exists_int_zQuad_ne_zero (fun h => he₀ (fun w => ?_))
    have := D.zQuadQ_add e₀ w
    rw [h, h, h] at this
    linarith
  let C : Matrix (OutWit m r) (Fin n) ℚ := fun k i => cs i k
  have hCF : ∀ a, centreFamily c₀ cs a = centreAt c₀ C a := by
    intro a; funext k
    simp [centreFamily, centreAt, C, Finset.sum_apply, mul_comm]
  have hc : ∀ a, D.IsCentre a (centreAt c₀ C a) := fun a => by rw [← hCF]; exact hcen a
  by_contra hnc
  obtain ⟨a1, ha1⟩ : ∃ a1, D.residual a1 (centreAt c₀ C a1) ≠ D.residual 0 (centreAt c₀ C 0) := by
    by_contra H
    push_neg at H
    exact hnc ⟨_, fun a => by rw [hCF]; exact H a⟩
  obtain ⟨A, B, hl⟩ := D.sr_residual_line c₀ C 0 a1
  set R0 := D.residual 0 (centreAt c₀ C 0) with hR0
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    by_contra h
    push_neg at h
    have h1 := hl 1
    have e1 : (0 : Fin n → ℤ) + (1 : ℤ) • a1 = a1 := by simp
    rw [e1, h.1, h.2] at h1
    apply ha1; rw [h1]; ring
  obtain ⟨t0, ht0⟩ : ∃ t0 : ℤ, A * (t0 : ℚ) ^ 2 + B * t0 + R0 ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    push_cast at h0 h1 h2
    rcases hAB with hA | hB
    · exact hA (by linarith)
    · exact hB (by linarith)
  -- the input line, its centre, and the residual along it
  let inp : ℤ → (Fin n → ℤ) := fun t => 0 + t • a1
  let ct : ℤ → (OutWit m r → ℚ) := fun t => centreAt c₀ C (inp t)
  let g : ℚ → ℚ := fun t => A * t ^ 2 + B * t + R0
  let σ : OutWit m r → ℚ := fun p => ∑ i, C p i * (a1 i : ℚ)
  have hct : ∀ t : ℤ, ∀ p, ct t p = c₀ p + (t : ℚ) * σ p := by
    intro t p
    simp only [ct, inp, centreAt, σ, Pi.smul_apply, smul_eq_mul, zero_add]
    push_cast
    rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hres : ∀ t : ℤ, D.residual (inp t) (ct t) = g t := fun t => hl t
  -- one integer solution at t0 and its hyperbolic coordinates
  obtain ⟨e₂, he₂q, h12⟩ := D.exists_isotropic_partner he₀q he₀
  obtain ⟨z0, hz0⟩ := D.exists_solZ_of_defines hf (inp t0)
  set x0 := toQ z0 - ct t0 with hx0
  set X0 := D.zPolarQ x0 e₂ with hX0
  set Y0 := D.zPolarQ x0 e₀ with hY0
  obtain ⟨hQx0', hr0'⟩ := D.hyperbolic_form_of_polarRank_le_two he₀q he₂q h12 hrank x0
  have hQx0 : D.zQuadQ x0 = X0 * Y0 := hQx0'
  set ρ0 := x0 - X0 • e₀ - Y0 • e₂ with hρ0
  have hr0 : D.InRadicalQ ρ0 := hr0'
  have hQg : D.zQuadQ x0 = g t0 := by rw [hx0, D.offCentre_norm (hc _) hz0]; exact hres t0
  have hX0ne : X0 ≠ 0 := by
    intro h; apply ht0
    have := hQg
    rw [hQx0, h, zero_mul] at this
    exact this.symm
  have hY0 : Y0 = g t0 / X0 := by rw [eq_div_iff hX0ne, mul_comm, ← hQx0, hQg]
  -- the quadratic section along the line, returned to the lattice
  let V1 : OutWit m r → ℚ := fun p => σ p + ((2 * A * t0 + B) / X0) * e₂ p
  let V2 : OutWit m r → ℚ := fun p => (A / X0) * e₂ p
  obtain ⟨w1, d1, hd1, hw1⟩ := exists_int_clear V1
  obtain ⟨w2, d2, hd2, hw2⟩ := exists_int_clear V2
  set M : ℤ := (d1 : ℤ) * d2 with hM
  have hMpos : 0 < M := by positivity
  let G : ℤ → ℚ := fun k => g ((t0 : ℚ) + M * k) / X0
  let Zk : ℤ → (OutWit m r → ℤ) := fun k p => z0 p + k * ((d2 : ℤ) * w1 p) + k ^ 2 * (M * ((d1 : ℤ) * w2 p))
  have hz0p : ∀ p, (z0 p : ℚ) = ct t0 p + X0 * e₀ p + Y0 * e₂ p + ρ0 p := by
    intro p
    have : x0 p = X0 * e₀ p + Y0 * e₂ p + ρ0 p := by
      simp only [hρ0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hx : x0 p = (z0 p : ℚ) - ct t0 p := by simp [hx0, toQ]
    linarith
  have hZk : ∀ k, toQ (Zk k) - ct (t0 + M * k) = X0 • e₀ + G k • e₂ + ρ0 := by
    intro k; funext p
    simp only [toQ, Zk, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, G, g]
    push_cast
    rw [hz0p p, hct t0 p, hct (t0 + M * k) p, hw1 p, hw2 p, hY0]
    simp only [V1, V2, g, hM]
    push_cast
    field_simp
    ring
  have hsolk : ∀ k, D.SolZ (inp (t0 + M * k)) (Zk k) := by
    intro k
    have h0 := D.cr_eval_cast (hc (inp (t0 + M * k))) (Zk k)
    change _ = D.zQuadQ (toQ (Zk k) - ct (t0 + M * k)) - D.residual (inp (t0 + M * k)) (ct (t0 + M * k)) at h0
    rw [hZk, D.zQuadQ_hyperbolic_section he₀q he₂q h12 hr0, hres] at h0
    have hG : X0 * G k = g ((t0 + M * k : ℤ) : ℚ) := by
      simp only [G]; push_cast; field_simp
    rw [hG, sub_self] at h0
    unfold QuadraticGraphData.SolZ
    exact_mod_cast h0
  -- the integer polynomial F(k) = D' · G(k)
  let p0 : ℚ := Y0
  let p1 : ℚ := (M : ℚ) * (2 * A * t0 + B) / X0
  let p2 : ℚ := (M : ℚ) ^ 2 * A / X0
  have hGk : ∀ k : ℤ, G k = p0 + p1 * k + p2 * k ^ 2 := by
    intro k; simp only [G, g, p0, p1, p2]; rw [hY0]; field_simp; ring
  obtain ⟨wv, Dp, hDp, hwv⟩ := exists_int_clear (![p0, p1, p2] : Fin 3 → ℚ)
  have hDp0 : (Dp : ℚ) ≠ 0 := by exact_mod_cast hDp.ne'
  let F : ℤ → ℤ := fun k => wv 2 * k ^ 2 + wv 1 * k + wv 0
  have hF : ∀ k, (F k : ℚ) = Dp * G k := by
    intro k; simp only [F]; push_cast; rw [hGk, hwv 0, hwv 1, hwv 2]; simp; ring
  have hnonconst : wv 2 ≠ 0 ∨ wv 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have a2 := hwv 2; have a1' := hwv 1
    rw [h.1] at a2; rw [h.2] at a1'
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_one, Int.cast_zero] at a2 a1'
    have hp2 : p2 = 0 := (mul_eq_zero.mp a2.symm).resolve_left hDp0
    have hp1 : p1 = 0 := (mul_eq_zero.mp a1'.symm).resolve_left hDp0
    have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hMpos.ne'
    have hA0 : A = 0 := by
      simp only [p2] at hp2
      rcases div_eq_zero_iff.mp hp2 with h' | h'
      · exact (mul_eq_zero.mp h').resolve_left (pow_ne_zero 2 hMq)
      · exact absurd h' hX0ne
    have hB0 : B = 0 := by
      simp only [p1, hA0] at hp1
      rcases div_eq_zero_iff.mp hp1 with h' | h'
      · have := (mul_eq_zero.mp h').resolve_left hMq; linarith
      · exact absurd h' hX0ne
    rcases hAB with h' | h'
    · exact h' hA0
    · exact h' hB0
  -- denominators of the two scaling directions
  obtain ⟨u1, k1, hk1, hu1⟩ := exists_int_clear (X0 • e₀)
  obtain ⟨u2, k2, hk2, hu2⟩ := exists_int_clear ((Dp : ℚ)⁻¹ • e₂)
  set K : ℤ := (k1 : ℤ) * k2 with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨k₀, lam, hl0, hl1, ⟨q, hq⟩, hdvd⟩ := exists_scaling_divisor (wv 2) (wv 1) (wv 0) K hnonconst hKpos
  have hdvdj : ∀ j : ℤ, lam ∣ F (k₀ + lam * j) := by
    intro j
    have : F (k₀ + lam * j) = (wv 2 * k₀ ^ 2 + wv 1 * k₀ + wv 0) + lam * (j * (2 * wv 2 * k₀ + wv 1) + wv 2 * lam * j ^ 2) := by
      simp only [F]; ring
    rw [this]; exact dvd_add hdvd (Dvd.intro _ rfl)
  -- the output coordinate that sees the hyperbolic plane
  let j0 : Fin m := ⟨0, hm⟩
  have hsee : e₀ (Sum.inl j0) ≠ 0 ∨ e₂ (Sum.inl j0) ≠ 0 := by
    let u0 : OutWit m r → ℚ := Pi.single (Sum.inl j0) 1
    obtain ⟨-, hrad0⟩ := D.hyperbolic_form_of_polarRank_le_two he₀q he₂q h12 hrank u0
    have h0 := D.outCoordQ_radicalQ_eq_zero hm hOU hz0 hQ hrad0 j0
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, u0, Pi.single_eq_same] at h0
    by_contra H
    push_neg at H
    rw [H.1, H.2] at h0
    simp at h0
  -- for every j, output uniqueness at k = k₀ + λ j forces F(k)·e₂ⱼ₀ = λ·D'·X0·e₀ⱼ₀
  have hE : ∀ j : ℤ, (F (k₀ + lam * j) : ℚ) * e₂ (Sum.inl j0) = lam * Dp * X0 * e₀ (Sum.inl j0) := by
    intro j
    set k := k₀ + lam * j with hk
    obtain ⟨fq, hfq⟩ := hdvdj j
    let Z' : OutWit m r → ℤ := fun p => Zk k p + q * ((k2 : ℤ) * u1 p) - q * fq * ((k1 : ℤ) * u2 p)
    have hlamq : (lam : ℚ) = 1 + q * K := by
      have : lam = 1 + K * q := by linarith
      rw [this]; push_cast; ring
    have hZ' : toQ Z' - ct (t0 + M * k) = (lam * X0) • e₀ + (fq / Dp : ℚ) • e₂ + ρ0 := by
      have hbase := congrFun (hZk k)
      funext p
      have hb := hbase p
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hb
      simp only [toQ, Z', Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      have hZq : ((Zk k p : ℤ) : ℚ) = ct (t0 + M * k) p + X0 * e₀ p + G k * e₂ p + ρ0 p := by
        have := hb; simp only [toQ] at this; linarith
      rw [hZq, hu1 p, hu2 p]
      simp only [Pi.smul_apply, smul_eq_mul]
      have hGF : G k = lam * fq / Dp := by
        have := hF k; rw [hfq] at this; push_cast at this
        field_simp; linarith
      rw [hGF, hlamq, hK]
      push_cast
      field_simp
      ring
    have hsol' : D.SolZ (inp (t0 + M * k)) Z' := by
      have h0 := D.cr_eval_cast (hc (inp (t0 + M * k))) Z'
      change _ = D.zQuadQ (toQ Z' - ct (t0 + M * k)) - D.residual (inp (t0 + M * k)) (ct (t0 + M * k)) at h0
      rw [hZ', D.zQuadQ_hyperbolic_section he₀q he₂q h12 hr0, hres] at h0
      have hval : lam * X0 * (fq / Dp) = g ((t0 + M * k : ℤ) : ℚ) := by
        have h1 : (F k : ℚ) = Dp * G k := hF k
        rw [hfq] at h1; push_cast at h1
        have h2 : G k = g ((t0 + M * k : ℤ) : ℚ) / X0 := by simp only [G]; push_cast; ring
        rw [h2] at h1
        field_simp at h1 ⊢
        linarith
      rw [hval, sub_self] at h0
      unfold QuadraticGraphData.SolZ
      exact_mod_cast h0
    have heq := congrFun (hOU _ _ _ (D.graph_of_solZ hsol') (D.graph_of_solZ (hsolk k))) j0
    simp only [outProj] at heq
    have hq1 := congrFun hZ' (Sum.inl j0)
    have hq2 := congrFun (hZk k) (Sum.inl j0)
    simp only [toQ, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hq1 hq2
    rw [heq] at hq1
    have hdiff : (lam * X0) * e₀ (Sum.inl j0) + fq / Dp * e₂ (Sum.inl j0) = X0 * e₀ (Sum.inl j0) + G k * e₂ (Sum.inl j0) := by
      linarith
    have hGF : G k = lam * fq / Dp := by
      have := hF k; rw [hfq] at this; push_cast at this
      field_simp; linarith
    rw [hGF] at hdiff
    have hlam1 : (lam : ℚ) - 1 ≠ 0 := by
      intro h; apply hl1; exact_mod_cast (by linarith : (lam : ℚ) = 1)
    have key : ((lam : ℚ) - 1) * (X0 * e₀ (Sum.inl j0) * Dp - fq * e₂ (Sum.inl j0)) = 0 := by
      field_simp at hdiff
      linear_combination hdiff
    have key2 := (mul_eq_zero.mp key).resolve_left hlam1
    rw [hfq]; push_cast
    linear_combination (-(lam : ℚ)) * key2
  -- three points of the progression
  have E0 := hE 0
  have E1 := hE 1
  have E2 := hE 2
  simp only [mul_zero, add_zero, mul_one] at E0 E1 E2
  by_cases he2 : e₂ (Sum.inl j0) = 0
  · have he0 : e₀ (Sum.inl j0) ≠ 0 := hsee.resolve_right (not_not.mpr he2)
    rw [he2, mul_zero] at E0
    have hl0q : (lam : ℚ) ≠ 0 := by exact_mod_cast hl0
    have : (lam : ℚ) * Dp * X0 * e₀ (Sum.inl j0) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hl0q hDp0) hX0ne) he0
    exact this E0.symm
  · have h1 : F (k₀ + lam) = F k₀ := by
      have : (F (k₀ + lam) : ℚ) = F k₀ := mul_right_cancel₀ he2 (E1.trans E0.symm)
      exact_mod_cast this
    have h2 : F (k₀ + lam * 2) = F k₀ := by
      have : (F (k₀ + lam * 2) : ℚ) = F k₀ := mul_right_cancel₀ he2 (E2.trans E0.symm)
      exact_mod_cast this
    simp only [F] at h1 h2
    have := quad_const_of_three (wv 2) (wv 1) (wv 0) k₀ lam hl0 h1 (by rw [← h2]; ring_nf)
    rcases hnonconst with h' | h'
    · exact h' this.1
    · exact h' this.2

end QuadraticGraphData

theorem isotropicBranchFullNF_of_polarRank_le_two :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ x : OutWit m r → ℚ, D.zQuadQ x = 0 ∧ ¬ D.InRadicalQ x) → D.polarRank ≤ 2 →
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
  obtain ⟨R0, hR⟩ := D.constResidual_of_isotropic_polarRank_le_two hm hf he₀q he₀ hrank c₀ cs hcen'
  let C : Matrix (OutWit m r) (Fin n) ℚ := fun k i => cs i k
  have hCF : ∀ a, centreFamily c₀ cs a = QuadraticGraphData.centreAt c₀ C a := by
    intro a; funext k
    simp [centreFamily, QuadraticGraphData.centreAt, C, Finset.sum_apply, mul_comm]
  exact D.constResidual_fullVectorCosetNF c₀ C R0 (fun a => by rw [← hCF]; exact hcen' a)
    (fun a => by rw [← hCF]; exact hR a) hf

end DiophCompression.ResearchUpgrade
