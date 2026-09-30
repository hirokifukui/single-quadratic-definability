/-
  OutputCoercivity.lean — s48.  Gate22 tasks **G22-T06 (§3.2)** and **G22-T07**.

  ERRATUM E-21-2, repaired here.  `LatticeCoercive` / `CoercivityCertificate` (DefiniteBranch.lean)
  demand a bound on the WHOLE output/witness vector.  That is not merely awkward, it is
  unsatisfiable for legitimate SE₂ graphs: `P = (b − a)²` defines `f(a) = a`, has the centre
  `(a, 0)` and kills the radical with `π`, yet `c‖(b,u)‖∞² ≤ N Q(b,u)` fails at `(b,u) = (0,1)`.
  So the definite branch may not be closed by bounding `z`.  It must be closed by bounding the
  OUTPUT only, and that needs no coercivity at all — just the Cauchy inequality for a
  POSITIVE SEMIDEFINITE form, together with a polar representative for each output coordinate.

  What is proved:
  * `exists_polar_representative` — each output coordinate that kills the radical is `polar(wⱼ, ·)`
    for a fixed `wⱼ` (G22-T06 §3.2; the same linear algebra as the centre, via PolarAnnihilator).
  * `semidefinite_cauchy` — `polar(v,w)² ≤ 4 Q(v) Q(w)` from `0 ≤ Q` alone.  Neither positive
    definiteness nor nondegeneracy is used, and the `Q(w) = 0` case is proved, not skipped.
  * `outCoord_sq_le` — the output-only bound `|πⱼ(v)|² ≤ 4 Q(wⱼ) Q(v)`.

  Controls.  POSITIVE and sharpness: `cauchy_sharp_at_diagonal` — at `v = w` the inequality is an
  EQUALITY, so the constant 4 is the correct one under the convention `polar(v,v) = 2Q(v)`
  (regression control 5: the coefficient is 4, and the polar form is `2B`).  NEGATIVE:
  `not_semidefinite_of_isotropic_nonorthogonal` — a nonradical isotropic direction refutes
  semidefiniteness, so this packet and the isotropic packet cannot both apply, and the hypothesis
  `0 ≤ Q` is load-bearing rather than decorative.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.GraphVocabulary
import ResearchUpgrade.PolarAnnihilator
import ResearchUpgrade.RationalCentre

namespace DiophCompression.ResearchUpgrade

/-- The `j`-th output coordinate as a linear functional on the ℚ layer. -/
def outDualQ {m r : ℕ} (j : Fin m) : Module.Dual ℚ (OutWit m r → ℚ) where
  toFun z := z (Sum.inl j)
  map_add' := by intro _ _; rfl
  map_smul' := by intro _ _; rfl

@[simp] theorem outDualQ_apply {m r : ℕ} (j : Fin m) (z : OutWit m r → ℚ) :
    (outDualQ (r := r) j) z = z (Sum.inl j) := rfl

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

theorem zPolarQ_self (v : OutWit m r → ℚ) : D.zPolarQ v v = 2 * D.zQuadQ v := by
  simp only [zPolarQ, zQuadQ, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  ring

/-! ### G22-T06 §3.2 — an output coordinate is a polar form against a fixed vector -/

/-- If the `j`-th output coordinate vanishes on the radical — which is exactly what T05
(`outProj_radical_eq_zero`) supplies under output uniqueness — then it is represented by the polar
form against a single fixed vector `wⱼ`.  Same lemma as the centre, applied on the other side. -/
theorem exists_polar_representative {j : Fin m}
    (hann : ∀ e : OutWit m r → ℚ, D.InRadicalQ e → e (Sum.inl j) = 0) :
    ∃ w : OutWit m r → ℚ, ∀ v, D.zPolarQ w v = v (Sum.inl j) := by
  have hmem : (outDualQ (r := r) j) ∈ (LinearMap.ker D.polarMapQ).dualAnnihilator := by
    refine Submodule.mem_dualAnnihilator _ |>.mpr ?_
    intro e he
    simpa using hann e (D.mem_ker_polarMapQ.mp he)
  rw [← D.range_polarMapQ_eq_dualAnnihilator_ker] at hmem
  obtain ⟨w, hw⟩ := hmem
  refine ⟨w, fun v => ?_⟩
  have := congrArg (fun f : Module.Dual ℚ (OutWit m r → ℚ) => f v) hw
  simpa using this

/-! ### G22-T07 — the Cauchy inequality for a positive semidefinite form -/

/-- The one-variable expansion the inequality rests on. -/
theorem zQuadQ_add_smul (v w : OutWit m r → ℚ) (t : ℚ) :
    D.zQuadQ (v + t • w) = D.zQuadQ v + t * D.zPolarQ v w + t ^ 2 * D.zQuadQ w := by
  rw [D.zQuadQ_add, D.zPolarQ_smul_right, D.zQuadQ_smul]

/-- **G22-T07.**  `polar(v,w)² ≤ 4 Q(v) Q(w)` for a positive semidefinite `Q` over ℚ.
No definiteness, no nondegeneracy, and the degenerate case `Q(w) = 0` is proved rather than
assumed away. -/
theorem semidefinite_cauchy (hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u)
    (v w : OutWit m r → ℚ) :
    (D.zPolarQ v w) ^ 2 ≤ 4 * D.zQuadQ v * D.zQuadQ w := by
  have key : ∀ t : ℚ, 0 ≤ D.zQuadQ v + t * D.zPolarQ v w + t ^ 2 * D.zQuadQ w := by
    intro t
    have h := hpos (v + t • w)
    rwa [D.zQuadQ_add_smul] at h
  rcases eq_or_lt_of_le (hpos w) with hw | hw
  · -- `Q(w) = 0`: the linear function `t ↦ Q(v) + t·polar(v,w)` is nonnegative on all of ℚ,
    -- which forces the slope to vanish.  This is the case the route forbids skipping.
    have hQw : D.zQuadQ w = 0 := hw.symm
    have key0 : ∀ t : ℚ, 0 ≤ D.zQuadQ v + t * D.zPolarQ v w := by
      intro t
      have h := key t
      rw [hQw, mul_zero, add_zero] at h
      exact h
    have hb : D.zPolarQ v w = 0 := by
      by_contra hne
      have h := key0 (-(D.zQuadQ v + 1) / D.zPolarQ v w)
      have hval : D.zQuadQ v + (-(D.zQuadQ v + 1) / D.zPolarQ v w) * D.zPolarQ v w = -1 := by
        field_simp
        ring
      rw [hval] at h
      linarith
    rw [hb, hQw]
    simp
  · -- `Q(w) > 0`: complete the square at `t = −polar(v,w)/(2Q(w))`.
    have hA : (0 : ℚ) < 4 * D.zQuadQ w := by linarith
    have h := key (-(D.zPolarQ v w) / (2 * D.zQuadQ w))
    have hne : D.zQuadQ w ≠ 0 := ne_of_gt hw
    have hval : D.zQuadQ v + (-(D.zPolarQ v w) / (2 * D.zQuadQ w)) * D.zPolarQ v w
        + (-(D.zPolarQ v w) / (2 * D.zQuadQ w)) ^ 2 * D.zQuadQ w
        = D.zQuadQ v - (D.zPolarQ v w) ^ 2 / (4 * D.zQuadQ w) := by
      field_simp
      ring
    rw [hval] at h
    have hdiv : (D.zPolarQ v w) ^ 2 / (4 * D.zQuadQ w) ≤ D.zQuadQ v := by linarith
    have hmul := (div_le_iff₀ hA).mp hdiv
    calc (D.zPolarQ v w) ^ 2 ≤ D.zQuadQ v * (4 * D.zQuadQ w) := hmul
      _ = 4 * D.zQuadQ v * D.zQuadQ w := by ring

/-- The `Q(w) = 0` corollary, isolated because the route insists it be visible: on a positive
semidefinite form an isotropic vector is radical. -/
theorem polar_eq_zero_of_zQuadQ_eq_zero (hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u)
    {w : OutWit m r → ℚ} (hw : D.zQuadQ w = 0) : D.InRadicalQ w := by
  intro v
  have h := D.semidefinite_cauchy hpos w v
  rw [hw] at h
  have h0 : (D.zPolarQ w v) ^ 2 ≤ 0 := by linarith
  have := sq_nonneg (D.zPolarQ w v)
  have hsq : (D.zPolarQ w v) ^ 2 = 0 := le_antisymm h0 this
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq

/-- **The output-only bound.**  With a polar representative `wⱼ` for the `j`-th output coordinate,
the output is controlled by `Q(v)` alone — no bound on the witnesses is needed or available. -/
theorem outCoord_sq_le (hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u)
    {j : Fin m} {w : OutWit m r → ℚ} (hw : ∀ v, D.zPolarQ w v = v (Sum.inl j))
    (v : OutWit m r → ℚ) :
    (v (Sum.inl j)) ^ 2 ≤ 4 * D.zQuadQ w * D.zQuadQ v := by
  have h := D.semidefinite_cauchy hpos w v
  rwa [hw v] at h

/-! ### Controls -/

/-- POSITIVE control AND sharpness of the constant (regression control 5): at `v = w` the Cauchy
inequality is an equality, because `polar(v,v) = 2 Q(v)`.  So `4` is exactly right for this polar
convention, and the reviewer's `2B` factor must not be carried in on top of it. -/
theorem cauchy_sharp_at_diagonal (v : OutWit m r → ℚ) :
    (D.zPolarQ v v) ^ 2 = 4 * D.zQuadQ v * D.zQuadQ v := by
  rw [D.zPolarQ_self]
  ring

/-- NEGATIVE control: a nonradical isotropic direction refutes semidefiniteness.  So the
hypothesis `0 ≤ Q` is load-bearing, and this packet and the isotropic packet are disjoint rather
than overlapping. -/
theorem not_semidefinite_of_isotropic_nonorthogonal {e v : OutWit m r → ℚ}
    (he : D.zQuadQ e = 0) (hb : D.zPolarQ v e ≠ 0) :
    ¬ (∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) := by
  intro hpos
  exact hb (by rw [D.zPolarQ_symm v e]; exact D.polar_eq_zero_of_zQuadQ_eq_zero hpos he v)

/-- NEGATIVE control for the representative: if some radical vector is seen by the `j`-th output
coordinate, no representative exists — the hypothesis of `exists_polar_representative` is not
decorative. -/
theorem not_exists_polar_representative {j : Fin m} {e : OutWit m r → ℚ}
    (he : D.InRadicalQ e) (hne : e (Sum.inl j) ≠ 0) :
    ¬ ∃ w : OutWit m r → ℚ, ∀ v, D.zPolarQ w v = v (Sum.inl j) := by
  rintro ⟨w, hw⟩
  apply hne
  rw [← hw e, D.zPolarQ_symm w e]
  exact he w

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
