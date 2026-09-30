/-
  R43Completion.lean — s55.  The two items of the R43 task list that were open after the first pass
  (GATE25 #67, #70).

  * A4 Step 2, by the route of the task text: `weakIntAffine_of_small` — positive definite with at most
    two output/unknown coordinates; two coordinates go through A3's `weakIntAffineCosetNF_of_binary`,
    one coordinate through the full NF plus linear growth; `lowRankSemidefiniteIntAffineNF_holds_viaBinary`
    — sign flip, rank-excess compiler, `m = 0`.  (The first capstone,
    `lowRankSemidefiniteIntAffineNF_holds`, reaches the same statement through linear growth for every
    rank at once; both are kept.)
  * D1 Step 4: `d1_no_quadratic_section` — no section of degree at most two solves
    `b² + u² + v² = 1 + 8 Σ aᵢ²` along a full lattice coset (fourth differences along `s ↦ s·t` kill the
    quadratic part, then `d1_no_affine_section`).

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.AffineSection
import ResearchUpgrade.DefiniteReduction
import ResearchUpgrade.RankControls

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadraticGraphData

theorem weakIntAffine_of_small {n m r' : ℕ} (D : QuadraticGraphData n m r') (hmr : m + r' ≤ 2)
    (hm : 0 < m) (hpos : ∀ u : OutWit m r' → ℚ, u ≠ 0 → 0 < D.zQuadQ u)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : WeakIntAffineCosetNF f := by
  rcases Nat.lt_or_ge (m + r') 2 with h | h
  · obtain rfl : m = 1 := by omega
    obtain rfl : r' = 0 := by omega
    have hNF := weakVectorCosetNF_of_fullVectorCosetNF (D.fullVectorCosetNF_of_defines hf)
    have hQ : ∃ v, D.zQuad v ≠ 0 := by
      refine ⟨Pi.single (Sum.inl ⟨0, hm⟩) 1, fun h0 => ?_⟩
      have hne : toQ (Pi.single (Sum.inl ⟨0, hm⟩) (1 : ℤ) : OutWit 1 0 → ℤ) ≠ 0 := by
        intro h
        have := congrFun h (Sum.inl ⟨0, hm⟩)
        simp [toQ] at this
      have := hpos _ hne
      rw [D.zQuadQ_toQ, h0] at this
      simp at this
    have hsemi : ∀ u : OutWit 1 0 → ℚ, 0 ≤ D.zQuadQ u := by
      intro u
      by_cases hu : u = 0
      · subst hu; simp [zQuadQ]
      · exact le_of_lt (hpos u hu)
    exact weakIntAffine_of_weakNF_linearGrowth hNF (D.linearGrowth_of_semidefinite_defines hm hsemi hQ hf)
  · have h2 : m + r' = 2 := by omega
    exact D.weakIntAffineCosetNF_of_binary (finSumFinEquiv.trans (finCongr h2)) hpos hf

end QuadraticGraphData

theorem lowRankSemidefiniteIntAffineNF_holds_viaBinary : LowRankSemidefiniteIntAffineNF := by
  intro n m r D f hQ hsemi hrank hf
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨1, 0, 0, 0, le_rfl, fun t => funext fun j => j.elim0⟩
  · have key : ∀ D' : QuadraticGraphData n m r, D'.Defines f → (∃ v, D'.zQuad v ≠ 0) →
        (∀ u, 0 ≤ D'.zQuadQ u) → D'.polarRank ≤ 2 → WeakIntAffineCosetNF f := by
      intro D' hf' hQ' hpos' hrank'
      obtain ⟨U, -, hdef', -, hposdef⟩ := D'.definite_reduction hm hf' hQ' hpos'
      have hml := D'.m_le_polarRank hm hf' hQ'
      exact (D'.compiledData U).weakIntAffine_of_small (by omega) hm hposdef hdef'
    rcases hsemi with hpos | hneg
    · exact key D hf hQ hpos hrank
    · refine key D.negGraph (D.negGraph_defines hf) ?_ ?_ ?_
      · obtain ⟨v, hv⟩ := hQ
        exact ⟨v, by rw [D.negGraph_zQuad]; omega⟩
      · intro u; rw [D.negGraph_zQuadQ]; linarith [hneg u]
      · rw [D.negGraph_polarRank]; exact hrank

namespace RankControl

theorem d1_no_quadratic_section (M : ℕ) (hM : 1 ≤ M) (ρ : Fin 4 → ℤ) (p : Fin 3 → ℚ)
    (L : Matrix (Fin 3) (Fin 4) ℚ) (H : Fin 3 → Matrix (Fin 4) (Fin 4) ℚ) :
    ¬ ∀ t : Fin 4 → ℤ, ∑ k, (p k + (L *ᵥ castQ t) k + castQ t ⬝ᵥ (H k *ᵥ castQ t)) ^ 2
        = 1 + 8 * ∑ i, ((ρ i : ℚ) + (M : ℚ) * (t i : ℚ)) ^ 2 := by
  intro hall
  have hform : ∀ (t : Fin 4 → ℤ) (k : Fin 3), castQ t ⬝ᵥ (H k *ᵥ castQ t) = 0 := by
    intro t
    set ℓ : Fin 3 → ℚ := L *ᵥ castQ t with hℓ
    set h : Fin 3 → ℚ := fun k => castQ t ⬝ᵥ (H k *ᵥ castQ t) with hh
    have hc : ∀ s : ℤ, castQ (s • t) = (s : ℚ) • castQ t := by
      intro s; funext i; simp [castQ]
    have hL : ∀ (s : ℤ) (k : Fin 3), (L *ᵥ castQ (s • t)) k = (s : ℚ) * ℓ k := by
      intro s k; rw [hc, mulVec_smul]; simp [hℓ]
    have hH : ∀ (s : ℤ) (k : Fin 3),
        castQ (s • t) ⬝ᵥ (H k *ᵥ castQ (s • t)) = (s : ℚ) ^ 2 * h k := by
      intro s k
      rw [hc, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      simp only [hh]; ring
    have hR : ∀ (s : ℤ) (i : Fin 4), (((s • t) i : ℤ) : ℚ) = (s : ℚ) * (t i : ℚ) := by
      intro s i; simp
    have e : ∀ s : ℤ, ∑ k, (p k + (s : ℚ) * ℓ k + (s : ℚ) ^ 2 * h k) ^ 2
        = 1 + 8 * ∑ i, ((ρ i : ℚ) + (M : ℚ) * ((s : ℚ) * (t i : ℚ))) ^ 2 := by
      intro s
      have := hall (s • t)
      simp only [hL, hH, hR] at this
      exact this
    have e0 := e 0
    have e1 := e 1
    have e2 := e 2
    have e3 := e 3
    have e4 := e 4
    simp only [Fin.sum_univ_three, Fin.sum_univ_four] at e0 e1 e2 e3 e4
    push_cast at e0 e1 e2 e3 e4
    have hsum : h 0 ^ 2 + h 1 ^ 2 + h 2 ^ 2 = 0 := by
      linear_combination (e4 - 4 * e3 + 6 * e2 - 4 * e1 + e0) / 24
    clear e0 e1 e2 e3 e4 e hL hH hR hc
    have q0 := sq_nonneg (h 0)
    have q1 := sq_nonneg (h 1)
    have q2 := sq_nonneg (h 2)
    have a0 : h 0 ^ 2 = 0 := by linarith
    have a1 : h 1 ^ 2 = 0 := by linarith
    have a2 : h 2 ^ 2 = 0 := by linarith
    intro k
    fin_cases k
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp a0
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp a1
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp a2
  have hall' : ∀ t : Fin 4 → ℤ, ∑ k, (p k + (L *ᵥ castQ t) k) ^ 2
      = 1 + 8 * ∑ i, ((ρ i : ℚ) + (M : ℚ) * (t i : ℚ)) ^ 2 := by
    intro t
    have := hall t
    simp only [hform t, add_zero] at this
    exact this
  exact d1_no_affine_section M hM ρ p L hall'

end RankControl

end DiophCompression.ResearchUpgrade
