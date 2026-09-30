/-
  DiophCompression/SemanticQuadratic/PellOrbitOfXPos.lean — APAL Structural Theory Gate 5, 必須F step 2
  (the Pell hub in data form) (s28, 2026-09-02, claude.ai direct).

  `pell_infinite_of_X_pos` is the hub of the whole Pell side: branch D7 uses it, branch A1 uses it through
  the scaled line (FullRankGeneric), and the rank-two generic block uses it too. It returns bare
  infinitude. Here is its data twin: from one fibre point with a positive `X = 2Dc + β` it returns the
  EXPLICIT orbit of fibre points — the unit `(P, Q)`, the base `(X₀, Y₀)`, the family `pt k = (c k, u k)`,
  the affine relation `2D·c k + β = X k`, and strict growth of the output. The sign of `Q` is chosen ONCE
  at the base (`pellOrbit_neg_snd`), where the sealed proof chose it at every step. No sorry; std-3.
-/
import DiophCompression.SemanticQuadraticTwoWitness.PellStep
import DiophCompression.SemanticQuadratic.PellFiberOrbit

namespace DiophCompression.SemanticQuadratic

open MPUP

theorem pell_orbit_of_X_pos (A B C l m q : ℤ) (h : 0 < disc A B C) (hns : ¬ IsSquare (disc A B C))
    (c₀ : ℕ) (hc₀ : c₀ ∈ fiberSet A B C l m q)
    (hX₀ : 0 < 2 * disc A B C * (c₀ : ℤ) + (2 * B * m - 4 * C * l)) :
    ∃ (P Q Y₀ : ℤ) (pt : ℕ → ℤ × ℤ),
      P ^ 2 - disc A B C * Q ^ 2 = 1 ∧ 2 ≤ P ∧
      (pt 0).1 = (c₀ : ℤ) ∧
      (∀ k, fq A B C l m q (pt k).1 (pt k).2 = 0) ∧
      (∀ k, 2 * disc A B C * (pt k).1 + (2 * B * m - 4 * C * l)
          = (DiophCompression.pellOrbit (disc A B C) P Q
              (2 * disc A B C * (c₀ : ℤ) + (2 * B * m - 4 * C * l)) Y₀ k).1) ∧
      StrictMono (fun k => (pt k).1) := by
  classical
  obtain ⟨D, hDdef⟩ : ∃ D : ℤ, D = disc A B C := ⟨_, rfl⟩
  have hD : D = B ^ 2 - 4 * A * C := by rw [hDdef]; rfl
  have hDpos : 0 < D := by rw [hDdef]; exact h
  have hnsD : ¬ IsSquare D := by rw [hDdef]; exact hns
  have hC : C ≠ 0 := by
    intro h0; apply hns; refine ⟨B, ?_⟩; unfold disc; rw [h0]; ring
  have hDC : 16 * D * C ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · norm_num at h2
      · exact absurd h2 (by linarith : D ≠ 0)
    · exact hC h1
  -- a nontrivial unit, made nonnegative
  obtain ⟨p0, q0, hpq0, hq0⟩ := Pell.exists_of_not_isSquare hDpos hnsD
  obtain ⟨p, hp⟩ : ∃ p : ℤ, p = |p0| := ⟨_, rfl⟩
  obtain ⟨qU, hq⟩ : ∃ qU : ℤ, qU = |q0| := ⟨_, rfl⟩
  have hpq : p ^ 2 - D * qU ^ 2 = 1 := by rw [hp, hq, sq_abs, sq_abs]; exact hpq0
  have hq1 : 1 ≤ qU := by rw [hq]; exact Int.one_le_abs hq0
  have hp1 : 1 ≤ p := by
    have h0 : 0 ≤ p := by rw [hp]; exact abs_nonneg _
    by_contra hcon; push_neg at hcon
    have : p = 0 := by omega
    rw [this] at hpq; nlinarith
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤ, σ * C = |C| := by
    rcases lt_or_gt_of_ne hC with hneg | hpos
    · exact ⟨-1, by rw [abs_of_neg hneg]; ring⟩
    · exact ⟨1, by rw [abs_of_pos hpos]; ring⟩
  obtain ⟨Mn, hMn⟩ : ∃ Mn : ℕ, (Mn : ℤ) = 8 * D * |C| :=
    ⟨(8 * D * |C|).toNat, Int.toNat_of_nonneg (by positivity)⟩
  have hMpos : 0 < Mn := by
    have : (0 : ℤ) < Mn := by rw [hMn]; positivity
    exact_mod_cast this
  obtain ⟨T, hT, hT1, hT2⟩ := pellPow_periodic D p qU hpq Mn hMpos
  obtain ⟨P, hP⟩ : ∃ P : ℤ, P = (pellPow D p qU T).1 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = (pellPow D p qU T).2 := ⟨_, rfl⟩
  have hPQ : P ^ 2 - D * Q ^ 2 = 1 := by rw [hP, hQ]; exact pellPow_norm D p qU hpq T
  have hPQpos := pellPow_pos D p qU hDpos hp1 hq1 T
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact hPQpos.2.2 (by omega)
  have hP2 : 2 ≤ P := by
    have hP1 : 1 ≤ P := by rw [hP]; exact hPQpos.1
    by_contra hcon; push_neg at hcon
    have : P = 1 := by omega
    rw [this] at hPQ; nlinarith
  rw [← hP] at hT1; rw [← hQ] at hT2
  -- the base point
  obtain ⟨u₀, hu₀⟩ := hc₀
  obtain ⟨X₀, hX₀def⟩ : ∃ X₀ : ℤ, X₀ = 2 * D * (c₀ : ℤ) + (2 * B * m - 4 * C * l) := ⟨_, rfl⟩
  obtain ⟨Y₀, hY₀def⟩ : ∃ Y₀ : ℤ, Y₀ = 2 * (2 * C * u₀ + B * (c₀ : ℤ) + m) := ⟨_, rfl⟩
  have hX₀pos : 0 < X₀ := by rw [hX₀def, hDdef]; exact hX₀
  -- ONE sign choice at the base
  obtain ⟨Q', hQ'unit, hQ'dvd, hXmono⟩ :
      ∃ Q' : ℤ, P ^ 2 - D * Q' ^ 2 = 1 ∧ (Mn : ℤ) ∣ Q' ∧
        StrictMono (fun k => (DiophCompression.pellOrbit D P Q' X₀ Y₀ k).1) := by
    rcases le_or_gt 0 Y₀ with hY0 | hY0
    · exact ⟨Q, hPQ, hT2,
        DiophCompression.pellOrbit_strictMono_fst D P Q X₀ Y₀ hDpos hP2 (by linarith) hX₀pos hY0⟩
    · exact ⟨-Q, by rw [neg_sq]; exact hPQ, (dvd_neg).mpr hT2,
        DiophCompression.pellOrbit_strictMono_fst_neg D P (-Q) X₀ Y₀ hDpos hP2 (by linarith)
          hX₀pos (by linarith)⟩
  -- membership along the orbit
  have hmem := pell_fiber_orbit_mem A B C l m q D P Q' σ (Mn : ℤ) (c₀ : ℤ) u₀ hD hQ'unit hσ hMn
    hT1 hQ'dvd hDC hu₀
  choose c u hfq hcX hcY using hmem
  rw [← hY₀def] at hcX
  refine ⟨P, Q', Y₀, fun k => (c k, u k), ?_, hP2, ?_, hfq, ?_, ?_⟩
  · rw [← hDdef]; exact hQ'unit
  · have h0 := hcX 0
    simp only [DiophCompression.pellOrbit_zero] at h0
    have hc : 2 * D * c 0 = 2 * D * (c₀ : ℤ) := by linarith
    exact mul_left_cancel₀ (by positivity : (2 * D : ℤ) ≠ 0) hc
  · intro k
    simp only
    rw [← hDdef]
    exact hcX k
  · refine strictMono_nat_of_lt_succ (fun k => ?_)
    have hstep := hXmono (Nat.lt_succ_self k)
    simp only at hstep
    rw [hX₀def] at hstep
    rw [← hcX k, ← hcX (k + 1)] at hstep
    simp only
    nlinarith

end DiophCompression.SemanticQuadratic

#print axioms DiophCompression.SemanticQuadratic.pell_orbit_of_X_pos
