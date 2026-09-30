/-
  IsotropicDirection.lean — s48.  Gate22 task **G22-T10** — the isotropic direction lemma with
  `NondegQ` removed.

  `exists_isotropic_nonorthogonal` (G21-T10, RationalCentre.lean) assumes the form is nondegenerate
  on the WHOLE space.  That hypothesis is unavailable in the degenerate branches — which are the
  ones this packet exists for.  The reviewer's §5 weakens it to exactly what the construction uses:

      `e₀ ∉ rad(Q)` ,  `v₀ ∉ rad(Q)` ,  `Q(e₀) = 0`   ⇒   `∃ e, Q(e) = 0 ∧ polar(v₀, e) ≠ 0`.

  Nothing else changes: `polar(v₀,e₀) ≠ 0` still returns `e₀` itself, and otherwise one slides `e₀`
  along a direction seen by BOTH, which is where non-radicality is used and all it is used for.
  The `hpv : polar(v₀,e₀) = 0` side condition of the old statement is dropped: both cases are
  handled here.

  The two negative controls below show the two hypotheses are each load-bearing, and in different
  ways: a radical `v₀` makes the CONCLUSION unreachable, while a radical `e₀` makes the
  CONSTRUCTION degenerate.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.LinearBranchDimension
import ResearchUpgrade.OutputCoercivity
import ResearchUpgrade.PolarAnnihilator

namespace DiophCompression.ResearchUpgrade

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- A vector on which the form is non-zero is not radical — the usual source of non-radicality
downstream, since the off-centre vector has `Q(v) = R(a)`. -/
theorem not_inRadicalQ_of_zQuadQ_ne_zero {v : OutWit m r → ℚ} (hv : D.zQuadQ v ≠ 0) :
    ¬ D.InRadicalQ v := by
  intro h
  apply hv
  have := h v
  rw [D.zPolarQ_self] at this
  linarith

/-- Nondegeneracy is the special case: every non-zero vector is non-radical. -/
theorem not_inRadicalQ_of_nondegQ (hnd : D.NondegQ) {v : OutWit m r → ℚ} (hv : v ≠ 0) :
    ¬ D.InRadicalQ v := by
  intro h
  obtain ⟨w, hw⟩ := hnd v hv
  exact hw (h w)

/-! ### G22-T10 — a direction seen by both, without nondegeneracy -/

theorem exists_seen_by_both_of_nonradical {e₀ v₀ : OutWit m r → ℚ}
    (he₀ : ¬ D.InRadicalQ e₀) (hv₀ : ¬ D.InRadicalQ v₀) :
    ∃ y, D.zPolarQ e₀ y ≠ 0 ∧ D.zPolarQ v₀ y ≠ 0 := by
  obtain ⟨w, hw⟩ : ∃ w, D.zPolarQ v₀ w ≠ 0 := by
    by_contra hcon
    exact hv₀ (fun w => by
      by_contra hne
      exact hcon ⟨w, hne⟩)
  obtain ⟨u, hu⟩ : ∃ u, D.zPolarQ e₀ u ≠ 0 := by
    by_contra hcon
    exact he₀ (fun w => by
      by_contra hne
      exact hcon ⟨w, hne⟩)
  by_cases hew : D.zPolarQ e₀ w = 0
  · by_cases h1 : D.zPolarQ v₀ u + D.zPolarQ v₀ w = 0
    · refine ⟨u + (2 : ℚ) • w, ?_, ?_⟩
      · rw [D.zPolarQ_add_right, D.zPolarQ_smul_right, hew]
        simpa using hu
      · rw [D.zPolarQ_add_right, D.zPolarQ_smul_right]
        have hneg : D.zPolarQ v₀ u = - D.zPolarQ v₀ w := by linarith
        rw [hneg]
        intro hcon
        exact hw (by linarith)
    · refine ⟨u + w, ?_, ?_⟩
      · rw [D.zPolarQ_add_right, hew]
        simpa using hu
      · rw [D.zPolarQ_add_right]
        exact h1
  · by_cases h2 : D.zPolarQ v₀ w = 0
    · exact absurd h2 hw
    · exact ⟨w, hew, hw⟩

/-- **G22-T10.**  An isotropic direction the output can see, with NO global nondegeneracy and no
side condition on `polar(v₀, e₀)`.  Exactly the hypothesis `anchoredSection` (G21-T11) needs, now
available in the degenerate branches. -/
theorem exists_isotropic_nonorthogonal_of_nonradical
    {e₀ : OutWit m r → ℚ} (he₀q : D.zQuadQ e₀ = 0) (he₀ : ¬ D.InRadicalQ e₀)
    {v₀ : OutWit m r → ℚ} (hv₀ : ¬ D.InRadicalQ v₀) :
    ∃ e, D.zQuadQ e = 0 ∧ D.zPolarQ v₀ e ≠ 0 := by
  by_cases hb : D.zPolarQ v₀ e₀ = 0
  · obtain ⟨y, hy1, hy2⟩ := D.exists_seen_by_both_of_nonradical he₀ hv₀
    by_cases hQy : D.zQuadQ y = 0
    · exact ⟨y, hQy, hy2⟩
    · refine ⟨e₀ + (-(D.zPolarQ e₀ y) / D.zQuadQ y) • y, ?_, ?_⟩
      · rw [D.zQuadQ_add, D.zPolarQ_smul_right, D.zQuadQ_smul, he₀q]
        field_simp
        ring
      · rw [D.zPolarQ_add_right, D.zPolarQ_smul_right, hb]
        have ht : (-(D.zPolarQ e₀ y) / D.zQuadQ y) ≠ 0 :=
          div_ne_zero (by simpa using hy1) hQy
        simpa using mul_ne_zero ht hy2
  · exact ⟨e₀, he₀q, hb⟩

/-! ### Controls -/

/-- POSITIVE control: the weakened lemma RECOVERS G21-T10.  Under `NondegQ` a non-zero vector is
non-radical, so the old hypotheses imply the new ones and nothing was lost in the weakening. -/
theorem exists_isotropic_nonorthogonal_of_nondegQ (hnd : D.NondegQ)
    {e₀ : OutWit m r → ℚ} (he₀q : D.zQuadQ e₀ = 0) (he₀0 : e₀ ≠ 0)
    {v₀ : OutWit m r → ℚ} (hv₀0 : v₀ ≠ 0) :
    ∃ e, D.zQuadQ e = 0 ∧ D.zPolarQ v₀ e ≠ 0 :=
  D.exists_isotropic_nonorthogonal_of_nonradical he₀q
    (D.not_inRadicalQ_of_nondegQ hnd he₀0) (D.not_inRadicalQ_of_nondegQ hnd hv₀0)

/-- NEGATIVE control 1: `v₀ ∉ rad` is load-bearing because the CONCLUSION fails without it.  A
radical `v₀` is polar-orthogonal to everything, so no `e` whatsoever can work. -/
theorem not_exists_isotropic_nonorthogonal_of_radical {v₀ : OutWit m r → ℚ}
    (hv₀ : D.InRadicalQ v₀) : ¬ ∃ e, D.zQuadQ e = 0 ∧ D.zPolarQ v₀ e ≠ 0 := by
  rintro ⟨e, -, hne⟩
  exact hne (hv₀ e)

/-- NEGATIVE control 2: `e₀ ∉ rad` is load-bearing in a different way — the CONSTRUCTION goes
degenerate.  With `e₀` radical the reviewer's vector `Q(y)e₀ − polar(e₀,y)y` collapses to a
multiple of `e₀`, which is orthogonal to everything; the slide produces nothing, for every `y`. -/
theorem slide_degenerate_of_radical {e₀ : OutWit m r → ℚ} (he₀ : D.InRadicalQ e₀)
    (y v₀ : OutWit m r → ℚ) :
    D.zPolarQ v₀ (D.zQuadQ y • e₀ + (-(D.zPolarQ e₀ y)) • y) = 0 := by
  have h0 : D.zPolarQ e₀ y = 0 := he₀ y
  have h1 : D.zPolarQ v₀ e₀ = 0 := by rw [D.zPolarQ_symm v₀ e₀]; exact he₀ v₀
  rw [D.zPolarQ_add_right, D.zPolarQ_smul_right, D.zPolarQ_smul_right, h0, h1]
  ring

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
