/-
  TCERSlice.lean — s56.  GPT R44 Packet B1 (GATE26): the fixed ternary coset slice of a positive definite datum.

  * `fixedCoset_slice` — from a positive definite datum of polar rank ≥ 3, an input line with positive leading
    residual coefficient and non-zero discriminant, and one integer solution with positive residual: an integral
    positive definite ternary Gram matrix `S`, a coset `e₁ + dℤ³`, a functional `p ≠ 0`, integers `A > 0, B` with
    non-zero discriminant, a modulus `M`, and the RETURN map — every representation of `A(Mk)² + B(Mk) + QS e₁` in
    the coset is an actual integer solution at input `a₀ + (Mk)v` whose output `j₀` is `α + β·(p-value) + γk`
    with `β ≠ 0`.  Totality of the slice is NOT claimed.
    Construction: `w = z₀ − c(a₀)`, three coordinates `k₁` (with `w_{k₁} ≠ 0`), `k₂`, `k₃` (one of them `j₀`
    whenever `w` misses it), the lattice map `ξ ↦ ξ₀ w + (ξ₁/d) e_{k₂} + (ξ₂/d) e_{k₃}`, the Gram matrix scaled by a
    common denominator `L` (which also clears `A`, `B`), and `M` clearing the centre drift `C v`.
  * `b1_common` — a common denominator for finitely many rationals.

  Statement frozen before installation (`~/lean/s56_evidence/freeze/B1_FREEZE_s56.lean`, ruled with R5 by
  Dr. Fukui 2026-09-25, frozen after the truth check); frozen = installed by `#check` output, planted control caught.
  Combined with `TCERBridge.ternaryCosetCollision_of_TCER` this gives two actual solutions at one input with
  different outputs, conditional on TCER; that capstone (C3/C4) is not stated here.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.TCERBridge
import ResearchUpgrade.SectionRigidity

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadraticGraphData

variable {n m r : ℕ}

/-- A common denominator for finitely many rationals. -/
theorem b1_common {ι : Type*} [Fintype ι] (f : ι → ℚ) :
    ∃ L : ℕ, 0 < L ∧ ∃ z : ι → ℤ, ∀ k, (z k : ℚ) = (L : ℚ) * f k := by
  classical
  refine ⟨∏ k, (f k).den, Finset.prod_pos (fun k _ => Nat.pos_of_ne_zero (f k).den_nz), ?_⟩
  have h : ∀ k, ∃ z : ℤ, (z : ℚ) = ((∏ k, (f k).den : ℕ) : ℚ) * f k := by
    intro k
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem (fun k => (f k).den) (Finset.mem_univ k)
    refine ⟨(t : ℤ) * (f k).num, ?_⟩
    rw [ht]
    push_cast
    rw [← Rat.mul_den_eq_num (f k)]
    ring
  choose z hz using h
  exact ⟨z, hz⟩

/-- **B1** (statement verbatim from `B_DRAFT_s56.lean` / `B1_FREEZE_s56.lean`). -/
theorem fixedCoset_slice (D : QuadraticGraphData n m r) (j0 : Fin m)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (hrank : 3 ≤ D.polarRank)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a))
    (a0 v : Fin n → ℤ) (z0 : OutWit m r → ℤ) (hz0 : D.SolZ a0 z0)
    (hR0 : 0 < D.residual a0 (centreAt c0 C a0)) (Aq Bq : ℚ)
    (hline : ∀ t : ℤ, D.residual (a0 + t • v) (centreAt c0 C (a0 + t • v))
        = Aq * (t : ℚ) ^ 2 + Bq * t + D.residual a0 (centreAt c0 C a0))
    (hA : 0 < Aq) (hdisc : Bq ^ 2 - 4 * Aq * D.residual a0 (centreAt c0 C a0) ≠ 0) :
    ∃ (S : Matrix (Fin 3) (Fin 3) ℤ) (d M : ℕ) (p : Fin 3 → ℤ) (A B : ℤ) (α β γ : ℚ),
      S.IsSymm ∧ (∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < TCERBridge.QS S y) ∧ 0 < d ∧ 0 < M ∧ p ≠ 0 ∧
      0 < A ∧ B ^ 2 - 4 * A * TCERBridge.QS S TCERBridge.e1 ≠ 0 ∧ β ≠ 0 ∧
      ∀ (k : ℤ) (x : Fin 3 → ℤ),
        TCERBridge.QS S (TCERBridge.e1 + (d : ℤ) • x) = A * (M * k) ^ 2 + B * (M * k) + TCERBridge.QS S TCERBridge.e1 →
        ∃ z : OutWit m r → ℤ, D.SolZ (a0 + ((M : ℤ) * k) • v) z ∧
          (z (Sum.inl j0) : ℚ) = α + β * (p ⬝ᵥ (TCERBridge.e1 + (d : ℤ) • x) : ℤ) + γ * k := by
  classical
  -- the off-centre vector of the given solution
  obtain ⟨R0, hR0def⟩ : ∃ R0, R0 = D.residual a0 (centreAt c0 C a0) := ⟨_, rfl⟩
  rw [← hR0def] at hR0 hdisc hline
  obtain ⟨w, hw⟩ : ∃ w : OutWit m r → ℚ, w = toQ z0 - centreAt c0 C a0 := ⟨_, rfl⟩
  have hQw : D.zQuadQ w = R0 := by
    rw [hw, hR0def]; exact (sr_solZ_iff D (hc a0) z0).mp hz0
  obtain ⟨k1, hk1⟩ : ∃ k1, w k1 ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : w = 0 := funext h
    rw [h0] at hQw
    simp [zQuadQ] at hQw
    linarith
  -- three distinct coordinates, one of them the output `j0` whenever `w` misses it
  have hcard : 3 ≤ Fintype.card (OutWit m r) := by
    have := D.polarRank_le
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨k2, hk21, hk2j⟩ : ∃ k2 : OutWit m r, k2 ≠ k1 ∧ (k2 = Sum.inl j0 ∨ Sum.inl j0 = k1) := by
    by_cases hj : (Sum.inl j0 : OutWit m r) = k1
    · obtain ⟨k2, hk2⟩ := Fintype.exists_ne_of_one_lt_card (by omega) k1
      exact ⟨k2, hk2, Or.inr hj⟩
    · exact ⟨Sum.inl j0, hj, Or.inl rfl⟩
  obtain ⟨k3, hk31, hk32⟩ : ∃ k3 : OutWit m r, k3 ≠ k1 ∧ k3 ≠ k2 := by
    have hc2 : ((Finset.univ.erase k1).erase k2).card = Fintype.card (OutWit m r) - 1 - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hk21, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    obtain ⟨k3, hk3⟩ : ((Finset.univ.erase k1).erase k2).Nonempty := by
      rw [← Finset.card_pos, hc2]; omega
    rw [Finset.mem_erase, Finset.mem_erase] at hk3
    exact ⟨k3, hk3.2.1, hk3.1⟩
  -- denominators
  obtain ⟨Cv, hCv⟩ : ∃ Cv : OutWit m r → ℚ, Cv = fun k => ∑ i, C k i * (v i : ℚ) := ⟨_, rfl⟩
  obtain ⟨d, hd, W, hW⟩ := b1_common w
  obtain ⟨M, hM, V, hV⟩ := b1_common Cv
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  obtain ⟨g1, hg1⟩ : ∃ g1 : OutWit m r → ℚ, g1 = fun k => if k = k2 then 1 / (d : ℚ) else 0 := ⟨_, rfl⟩
  obtain ⟨g2, hg2⟩ : ∃ g2 : OutWit m r → ℚ, g2 = fun k => if k = k3 then 1 / (d : ℚ) else 0 := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin 3 → ℤ) → OutWit m r → ℚ,
      φ = fun ξ => ((ξ 0 : ℤ) : ℚ) • w + ((ξ 1 : ℤ) : ℚ) • g1 + ((ξ 2 : ℤ) : ℚ) • g2 := ⟨_, rfl⟩
  have hQφ : ∀ ξ : Fin 3 → ℤ, D.zQuadQ (φ ξ)
      = (ξ 0 : ℚ) ^ 2 * D.zQuadQ w + (ξ 1 : ℚ) ^ 2 * D.zQuadQ g1 + (ξ 2 : ℚ) ^ 2 * D.zQuadQ g2
        + (ξ 0 : ℚ) * (ξ 1 : ℚ) * D.zPolarQ w g1 + (ξ 0 : ℚ) * (ξ 2 : ℚ) * D.zPolarQ w g2
        + (ξ 1 : ℚ) * (ξ 2 : ℚ) * D.zPolarQ g1 g2 := by
    intro ξ
    rw [hφ]
    simp only [D.zQuadQ_add, D.zPolarQ_add_left, D.zQuadQ_smul, D.zPolarQ_smul_left, D.zPolarQ_smul_right]
    ring
  -- the scaled Gram matrix
  obtain ⟨L, hL, s, hs⟩ := b1_common
    (![D.zQuadQ w, D.zQuadQ g1, D.zQuadQ g2, D.zPolarQ w g1 / 2, D.zPolarQ w g2 / 2, D.zPolarQ g1 g2 / 2,
      Aq, Bq] : Fin 8 → ℚ)
  have e0 : (s 0 : ℚ) = L * D.zQuadQ w := by simpa using hs 0
  have e1' : (s 1 : ℚ) = L * D.zQuadQ g1 := by simpa using hs 1
  have e2 : (s 2 : ℚ) = L * D.zQuadQ g2 := by simpa using hs 2
  have e3 : (s 3 : ℚ) = L * (D.zPolarQ w g1 / 2) := by simpa using hs 3
  have e4 : (s 4 : ℚ) = L * (D.zPolarQ w g2 / 2) := by simpa using hs 4
  have e5 : (s 5 : ℚ) = L * (D.zPolarQ g1 g2 / 2) := by simpa using hs 5
  have e6 : (s 6 : ℚ) = L * Aq := by simpa using hs 6
  have e7 : (s 7 : ℚ) = L * Bq := by simpa using hs 7
  have hL0 : (0 : ℚ) < L := by exact_mod_cast hL
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin 3) (Fin 3) ℤ,
      S = !![s 0, s 3, s 4; s 3, s 1, s 5; s 4, s 5, s 2] := ⟨_, rfl⟩
  have hSsym : S.IsSymm := by
    rw [hS]
    refine Matrix.IsSymm.ext (fun i j => ?_)
    fin_cases i <;> fin_cases j <;> rfl
  have hQS : ∀ ξ : Fin 3 → ℤ, (TCERBridge.QS S ξ : ℚ) = L * D.zQuadQ (φ ξ) := by
    intro ξ
    rw [hQφ ξ, hS]
    simp [TCERBridge.QS, dotProduct, mulVec, Fin.sum_univ_three]
    linear_combination ((ξ 0 : ℚ)) ^ 2 * e0 + ((ξ 1 : ℚ)) ^ 2 * e1' + ((ξ 2 : ℚ)) ^ 2 * e2
      + 2 * (ξ 0 : ℚ) * (ξ 1 : ℚ) * e3 + 2 * (ξ 0 : ℚ) * (ξ 2 : ℚ) * e4 + 2 * (ξ 1 : ℚ) * (ξ 2 : ℚ) * e5
  have hφk : ∀ (ξ : Fin 3 → ℤ) (k : OutWit m r),
      φ ξ k = (ξ 0 : ℚ) * w k + (ξ 1 : ℚ) * g1 k + (ξ 2 : ℚ) * g2 k := by
    intro ξ k; rw [hφ]; simp
  have g1k1 : g1 k1 = 0 := by rw [hg1]; simp [Ne.symm hk21]
  have g1k2 : g1 k2 = 1 / (d : ℚ) := by rw [hg1]; simp
  have g1k3 : g1 k3 = 0 := by rw [hg1]; simp [hk32]
  have g2k1 : g2 k1 = 0 := by rw [hg2]; simp [Ne.symm hk31]
  have g2k2 : g2 k2 = 0 := by rw [hg2]; simp [Ne.symm hk32]
  have g2k3 : g2 k3 = 1 / (d : ℚ) := by rw [hg2]; simp
  have hφe1 : φ TCERBridge.e1 = w := by
    rw [hφ]; funext k
    simp [TCERBridge.e1]
  have hQSe1 : (TCERBridge.QS S TCERBridge.e1 : ℚ) = L * R0 := by
    rw [hQS, hφe1, hQw]
  -- positive definiteness of `S`
  have hSpos : ∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < TCERBridge.QS S y := by
    intro y hy
    have hne : φ y ≠ 0 := by
      intro h0
      have h1 := congrFun h0 k1
      have h2 := congrFun h0 k2
      have h3 := congrFun h0 k3
      rw [hφk, g1k1, g2k1, Pi.zero_apply] at h1
      rw [hφk, g1k2, g2k2, Pi.zero_apply] at h2
      rw [hφk, g1k3, g2k3, Pi.zero_apply] at h3
      have hy0 : (y 0 : ℚ) = 0 := by
        have : (y 0 : ℚ) * w k1 = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h hk1
      have hy1 : (y 1 : ℚ) = 0 := by
        have : (y 1 : ℚ) * (1 / (d : ℚ)) = 0 := by rw [hy0] at h2; linarith
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h (one_div_ne_zero hd0)
      have hy2 : (y 2 : ℚ) = 0 := by
        have : (y 2 : ℚ) * (1 / (d : ℚ)) = 0 := by rw [hy0] at h3; linarith
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h (one_div_ne_zero hd0)
      apply hy
      funext i
      fin_cases i
      · exact_mod_cast hy0
      · exact_mod_cast hy1
      · exact_mod_cast hy2
    have := hQS y
    have hq : (0 : ℚ) < TCERBridge.QS S y := by rw [this]; exact mul_pos hL0 (hpos _ hne)
    exact_mod_cast hq
  -- the functional
  obtain ⟨p, hp⟩ : ∃ p : Fin 3 → ℤ, p = ![W (Sum.inl j0),
      if (Sum.inl j0 : OutWit m r) = k2 then 1 else 0, if (Sum.inl j0 : OutWit m r) = k3 then 1 else 0] :=
    ⟨_, rfl⟩
  have hpv0 : p 0 = W (Sum.inl j0) := by rw [hp]; rfl
  have hpv1 : p 1 = if (Sum.inl j0 : OutWit m r) = k2 then 1 else 0 := by rw [hp]; rfl
  have hpv2 : p 2 = if (Sum.inl j0 : OutWit m r) = k3 then 1 else 0 := by rw [hp]; rfl
  have hpdot : ∀ ξ : Fin 3 → ℤ, ((p ⬝ᵥ ξ : ℤ) : ℚ) = d * φ ξ (Sum.inl j0) := by
    intro ξ
    rw [hφk, hg1, hg2]
    simp only [dotProduct, Fin.sum_univ_three, hpv0, hpv1, hpv2]
    push_cast
    rw [hW]
    split_ifs <;> field_simp <;> ring
  have hp0 : p ≠ 0 := by
    intro h0
    rcases hk2j with h | h
    · have := congrFun h0 1
      rw [hpv1] at this
      simp [h] at this
    · have := congrFun h0 0
      rw [hpv0, Pi.zero_apply] at this
      have hWk : (W (Sum.inl j0) : ℚ) = d * w (Sum.inl j0) := hW _
      rw [this, h] at hWk
      push_cast at hWk
      exact hk1 ((mul_eq_zero.mp hWk.symm).resolve_left hd0)
  refine ⟨S, d, M, p, s 6, s 7, (z0 (Sum.inl j0) : ℚ) - w (Sum.inl j0), 1 / (d : ℚ), (V (Sum.inl j0) : ℚ),
    hSsym, hSpos, hd, hM, hp0, ?_, ?_, one_div_ne_zero hd0, ?_⟩
  · have : (0 : ℚ) < s 6 := by rw [e6]; exact mul_pos hL0 hA
    exact_mod_cast this
  · intro h
    have hq : ((s 7 : ℚ)) ^ 2 - 4 * (s 6 : ℚ) * (TCERBridge.QS S TCERBridge.e1 : ℚ) = 0 := by
      exact_mod_cast h
    rw [e6, e7, hQSe1] at hq
    have : (L : ℚ) ^ 2 * (Bq ^ 2 - 4 * Aq * R0) = 0 := by linear_combination hq
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' (pow_ne_zero 2 hL0.ne')
    · exact hdisc h'
  · intro k x hrep
    obtain ⟨Y, hY⟩ : ∃ Y : OutWit m r → ℤ,
        Y = fun k' => x 0 * W k' + x 1 * (if k' = k2 then 1 else 0) + x 2 * (if k' = k3 then 1 else 0) :=
      ⟨_, rfl⟩
    have hφξ : φ (TCERBridge.e1 + (d : ℤ) • x) = w + toQ Y := by
      rw [hφ, hg1, hg2, hY]
      funext k'
      simp only [TCERBridge.e1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, toQ]
      simp only [Pi.single_apply, Fin.one_eq_zero_iff, Fin.reduceEq, if_true, if_false]
      push_cast
      rw [hW k']
      split_ifs <;> field_simp <;> ring
    -- the target identity, divided by L
    have hQwY : D.zQuadQ (w + toQ Y) = Aq * (((M : ℤ) * k : ℤ) : ℚ) ^ 2 + Bq * (((M : ℤ) * k : ℤ) : ℚ) + R0 := by
      have h1 : (TCERBridge.QS S (TCERBridge.e1 + (d : ℤ) • x) : ℚ)
          = (s 6 : ℚ) * ((M : ℚ) * k) ^ 2 + (s 7 : ℚ) * ((M : ℚ) * k) + (TCERBridge.QS S TCERBridge.e1 : ℚ) := by
        exact_mod_cast hrep
      rw [hQS, hφξ, e6, e7, hQSe1] at h1
      push_cast
      have h2 : (L : ℚ) * (D.zQuadQ (w + toQ Y) - (Aq * ((M : ℚ) * k) ^ 2 + Bq * ((M : ℚ) * k) + R0)) = 0 := by
        linear_combination h1
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hL0.ne'
      · linarith
    have hcen : ∀ k', centreAt c0 C (a0 + ((M : ℤ) * k) • v) k'
        = centreAt c0 C a0 k' + ((M : ℚ) * k) * Cv k' := by
      intro k'
      simp only [centreAt, hCv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      rw [Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    refine ⟨z0 + k • V + Y, ?_, ?_⟩
    · apply (sr_solZ_iff D (hc _) _).mpr
      have hdiff : toQ (z0 + k • V + Y) - centreAt c0 C (a0 + ((M : ℤ) * k) • v) = w + toQ Y := by
        funext k'
        simp only [toQ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [hcen k', hw]
        simp only [toQ, Pi.sub_apply]
        push_cast
        rw [hV k']
        ring
      rw [hdiff, hQwY, hline]
    · have hpx := hpdot (TCERBridge.e1 + (d : ℤ) • x)
      rw [hφξ] at hpx
      simp only [Pi.add_apply, toQ] at hpx
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      rw [hpx]
      field_simp
      ring

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
