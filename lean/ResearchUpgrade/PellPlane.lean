/-
  PellPlane.lean — s48.  Gate22 task **G22-T13** — the visible opposite-sign orthogonal plane.

  The reviewer's §6.1, with his pass conditions: **the `πv = 0` branch is not omitted**, no global
  `NondegQ` is used, and the argument runs at ONE fixed input — it does not wait for the all-input
  section.

  From `v` with `Q(v) ≠ 0` and any `u` of opposite sign, orthogonalise:
  `w₀ = u − (polar(v,u)/(2Q(v)))·v`.  Then `polar(v,w₀) = 0` and, in ONE line with no case split
  on the sign of `Q(v)`,

      Q(v)·Q(w₀) = Q(v)·Q(u) − polar(v,u)²/4  <  0.

  If neither `v` nor `w₀` is seen by the output, orthogonalise a vector the output DOES see and
  add a large multiple of `w₀`: the `k²` term carries the sign while the output value is untouched.
  `k` is chosen explicitly — `(|B| + |C| + 1)/P + 1` — not by an existence argument.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.IsotropicBranch
import ResearchUpgrade.OutputCoercivity
import ResearchUpgrade.PolarAnnihilator
import ResearchUpgrade.RationalCentre

namespace DiophCompression.ResearchUpgrade

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-! ### Quotient-anisotropy and the opposite-sign partner -/

/-- Under quotient-anisotropy (`Q(x) = 0 ⇒ x ∈ rad`), a non-radical vector has `Q ≠ 0`. -/
theorem zQuadQ_ne_zero_of_nonradical
    (hqa : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0 → D.InRadicalQ x)
    {v : OutWit m r → ℚ} (hv : ¬ D.InRadicalQ v) : D.zQuadQ v ≠ 0 :=
  fun h => hv (hqa v h)

/-- Indefiniteness gives a partner of the opposite sign, whatever the sign of `Q(v)` is. -/
theorem exists_opposite_sign {p q : OutWit m r → ℚ}
    (hp : 0 < D.zQuadQ p) (hq : D.zQuadQ q < 0)
    {v : OutWit m r → ℚ} (hv : D.zQuadQ v ≠ 0) :
    ∃ u, D.zQuadQ v * D.zQuadQ u < 0 := by
  rcases lt_or_gt_of_ne hv with h | h
  · exact ⟨p, by nlinarith⟩
  · exact ⟨q, by nlinarith⟩

/-! ### Orthogonalisation against `v` -/

/-- The orthogonal projection away from `v`. -/
noncomputable def orthoAgainst (v u : OutWit m r → ℚ) : OutWit m r → ℚ :=
  u + (-(D.zPolarQ v u) / (2 * D.zQuadQ v)) • v

theorem zPolarQ_orthoAgainst {v u : OutWit m r → ℚ} (hv : D.zQuadQ v ≠ 0) :
    D.zPolarQ v (D.orthoAgainst v u) = 0 := by
  simp only [orthoAgainst]
  rw [D.zPolarQ_add_right, D.zPolarQ_smul_right, D.zPolarQ_self]
  field_simp
  ring

/-- **The sign identity, with no case split.**  `Q(v)·Q(w₀) = Q(v)·Q(u) − polar(v,u)²/4`. -/
theorem zQuadQ_orthoAgainst {v u : OutWit m r → ℚ} (hv : D.zQuadQ v ≠ 0) :
    D.zQuadQ v * D.zQuadQ (D.orthoAgainst v u)
      = D.zQuadQ v * D.zQuadQ u - (D.zPolarQ v u) ^ 2 / 4 := by
  simp only [orthoAgainst]
  rw [D.zQuadQ_add_smul, D.zPolarQ_symm u v]
  field_simp
  ring

theorem orthoAgainst_apply (v u : OutWit m r → ℚ) (k : OutWit m r) :
    D.orthoAgainst v u k = u k + (-(D.zPolarQ v u) / (2 * D.zQuadQ v)) * v k := rfl

/-! ### G22-T13 — a visible orthogonal partner of the opposite sign -/

/-- **G22-T13.**  Given `v` and any `u` of opposite sign, there is a `w` polar-orthogonal to `v`,
of sign opposite to `v`, such that `v` and `w` are NOT both invisible to the output.  The
`πv = 0` case is handled, not skipped; no global nondegeneracy is used; one fixed input. -/
theorem exists_visible_orthogonal (hm : 0 < m)
    {v u : OutWit m r → ℚ} (hvu : D.zQuadQ v * D.zQuadQ u < 0) :
    ∃ w, D.zPolarQ v w = 0 ∧ D.zQuadQ v * D.zQuadQ w < 0 ∧
      ((∃ j, v (Sum.inl j) ≠ 0) ∨ ∃ j, w (Sum.inl j) ≠ 0) := by
  classical
  have hv : D.zQuadQ v ≠ 0 := by
    intro h; rw [h] at hvu; simp at hvu
  set w₀ := D.orthoAgainst v u with hw₀
  have hb0 : D.zPolarQ v w₀ = 0 := D.zPolarQ_orthoAgainst hv
  have hs0 : D.zQuadQ v * D.zQuadQ w₀ < 0 := by
    rw [hw₀, D.zQuadQ_orthoAgainst hv]
    nlinarith [sq_nonneg (D.zPolarQ v u)]
  by_cases hpv : ∃ j, v (Sum.inl j) ≠ 0
  · exact ⟨w₀, hb0, hs0, Or.inl hpv⟩
  by_cases hpw : ∃ j, w₀ (Sum.inl j) ≠ 0
  · exact ⟨w₀, hb0, hs0, Or.inr hpw⟩
  -- both invisible: orthogonalise a visible vector and add a large multiple of `w₀`
  have hpv' : ∀ j, v (Sum.inl j) = 0 := by
    intro j; by_contra hc; exact hpv ⟨j, hc⟩
  have hpw' : ∀ j, w₀ (Sum.inl j) = 0 := by
    intro j; by_contra hc; exact hpw ⟨j, hc⟩
  set j₀ : Fin m := ⟨0, hm⟩ with hj₀
  set x : OutWit m r → ℚ := Pi.single (Sum.inl j₀) (1 : ℚ) with hx
  set t := D.orthoAgainst v x with ht
  have hbt : D.zPolarQ v t = 0 := D.zPolarQ_orthoAgainst hv
  have htj : t (Sum.inl j₀) = 1 := by
    rw [ht, D.orthoAgainst_apply, hpv' j₀, hx]
    simp
  set P : ℚ := -(D.zQuadQ v * D.zQuadQ w₀) with hP
  have hPpos : 0 < P := by rw [hP]; linarith
  set Bc : ℚ := D.zQuadQ v * D.zPolarQ w₀ t with hBc
  set Cc : ℚ := D.zQuadQ v * D.zQuadQ t with hCc
  set k : ℚ := (|Bc| + |Cc| + 1) / P + 1 with hk
  have hk1 : (1 : ℚ) ≤ k := by
    rw [hk]
    have : (0 : ℚ) ≤ (|Bc| + |Cc| + 1) / P := by positivity
    linarith
  have hPk : |Bc| + |Cc| + 1 ≤ P * k := by
    rw [hk, mul_add, mul_div_cancel₀ _ (ne_of_gt hPpos), mul_one]
    linarith
  refine ⟨k • w₀ + t, ?_, ?_, Or.inr ⟨j₀, ?_⟩⟩
  · rw [D.zPolarQ_add_right, D.zPolarQ_smul_right, hb0, hbt]
    ring
  · have hexp : D.zQuadQ v * D.zQuadQ (k • w₀ + t) = -(P * k ^ 2) + k * Bc + Cc := by
      rw [D.zQuadQ_add, D.zQuadQ_smul, D.zPolarQ_smul_left, hP, hBc, hCc]
      ring
    rw [hexp]
    have hkpos : (0 : ℚ) < k := by linarith
    have h1 : Bc * k ≤ |Bc| * k := by nlinarith [le_abs_self Bc]
    have h2 : Cc ≤ |Cc| * k := by nlinarith [le_abs_self Cc, abs_nonneg Cc]
    have h3 : (|Bc| + |Cc| + 1) * k ≤ P * k * k := by nlinarith
    nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hpw' j₀, htj]
    norm_num

/-! ### Controls -/

/-- POSITIVE control: the orthogonalisation does what it says — the partner is polar-orthogonal to
`v` and its sign is opposite, with no hypothesis beyond `Q(v) ≠ 0` and the opposite sign of `u`. -/
theorem orthoAgainst_spec {v u : OutWit m r → ℚ} (hv : D.zQuadQ v ≠ 0)
    (hvu : D.zQuadQ v * D.zQuadQ u < 0) :
    D.zPolarQ v (D.orthoAgainst v u) = 0
      ∧ D.zQuadQ v * D.zQuadQ (D.orthoAgainst v u) < 0 := by
  refine ⟨D.zPolarQ_orthoAgainst hv, ?_⟩
  rw [D.zQuadQ_orthoAgainst hv]
  nlinarith [sq_nonneg (D.zPolarQ v u)]

/-- NEGATIVE control: non-radicality of `v` is load-bearing.  A radical `v` has `Q(v) = 0`, so no
`u` whatsoever satisfies `Q(v)·Q(u) < 0` and the whole construction is unavailable. -/
theorem not_exists_opposite_sign_of_radical {v : OutWit m r → ℚ} (hv : D.InRadicalQ v) :
    ¬ ∃ u, D.zQuadQ v * D.zQuadQ u < 0 := by
  rintro ⟨u, hu⟩
  have h0 : D.zQuadQ v = 0 := by
    have h := hv v
    rw [D.zPolarQ_self] at h
    linarith
  rw [h0] at hu
  simp at hu

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
