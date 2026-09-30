/-
  RationalCentre.lean — Gate-20 Packet 1/2, task T07 (and a redesign of T06).

  The reviewer's §2 picks a rational COMPLEMENT `W` to the radical, moves the problem there, and
  then has to carry the return-to-the-lattice data (his controls #8 and #12).  That step is not
  needed.  What every downstream branch actually uses is the CENTRE:

      c : OutWit → ℚ   with   polar(c, w) + ℓ_a(w) = 0  for every w,

  and then, in the SAME coordinates, with no change of basis and no complement,

      Q(z) + ℓ_a(z) + q(a) = Q(z − c) − (Q(c) − q(a)).

  So `‖z − c‖` is what the definite branch bounds and `Q(z − c) = R₀(a)` is the prescribed norm
  the isotropic (§4) and Pell (§5) branches deform.  Because no basis is changed and no lattice is
  re-identified, controls #8 and #12 have nothing to bite on here: the only rational object is `c`
  itself, and it is carried explicitly as data.

  **Existence of `c` is NOT proved here** (named leaf `exists_centre_of_lin_annihilates_radical`).
  The reduction is worth recording: over ℚ the image of the polar map is the annihilator of the
  radical, so a centre exists exactly when `ℓ_a` kills the radical — and that is precisely what
  T05 (`zLinEval_radical_eq_zero`) proves.  The degenerate case therefore does NOT need a
  complement; it needs T05 plus one linear-algebra fact.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.GraphVocabulary
import ResearchUpgrade.RadicalDrift

namespace DiophCompression.ResearchUpgrade

open Matrix

/-- An integer vector read over ℚ. -/
def toQ {m r : ℕ} (z : OutWit m r → ℤ) : OutWit m r → ℚ := fun k => (z k : ℚ)

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- The output/witness quadratic form, over ℚ. -/
def zQuadQ (z : OutWit m r → ℚ) : ℚ :=
  ∑ k, ∑ k', z k * ((D.P.Q (Sum.inr k) (Sum.inr k') : ℚ) * z k')

/-- Its polar form, over ℚ. -/
def zPolarQ (v w : OutWit m r → ℚ) : ℚ :=
  ∑ k, ∑ k', (v k * ((D.P.Q (Sum.inr k) (Sum.inr k') : ℚ) * w k')
              + w k * ((D.P.Q (Sum.inr k) (Sum.inr k') : ℚ) * v k'))

/-- The linear part, over ℚ. -/
def zLinQ (a : Fin n → ℤ) (z : OutWit m r → ℚ) : ℚ := ∑ k, (D.zLin a k : ℚ) * z k

/-! ### Faithfulness: the ℚ layer computes the same numbers on integer points -/

theorem zQuadQ_toQ (z : OutWit m r → ℤ) : D.zQuadQ (toQ z) = (D.zQuad z : ℚ) := by
  simp only [zQuadQ, zQuad, toQ]
  push_cast
  rfl

theorem zLinQ_toQ (a : Fin n → ℤ) (z : OutWit m r → ℤ) :
    D.zLinQ a (toQ z) = (D.zLinEval a z : ℚ) := by
  simp only [zLinQ, zLinEval, toQ]
  push_cast
  rfl

/-! ### Algebra of the ℚ layer -/

theorem zPolarQ_symm (v w : OutWit m r → ℚ) : D.zPolarQ v w = D.zPolarQ w v := by
  simp only [zPolarQ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  ring

theorem zQuadQ_sub (z c : OutWit m r → ℚ) :
    D.zQuadQ (z - c) = D.zQuadQ z - D.zPolarQ z c + D.zQuadQ c := by
  simp only [zQuadQ, zPolarQ, Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  ring

/-! ### T07 — the centre and the completed square -/

/-- `c` is a centre for the input `a`: the polar form against `c` cancels the linear part. -/
def IsCentre (a : Fin n → ℤ) (c : OutWit m r → ℚ) : Prop :=
  ∀ w, D.zPolarQ c w + D.zLinQ a w = 0

/-- The residual `R₀(a) = Q(c) − q(a)`. -/
def residual (a : Fin n → ℤ) (c : OutWit m r → ℚ) : ℚ := D.zQuadQ c - (D.aPart a : ℚ)

/-- **T07.**  With a centre, the polynomial is a completed square in the SAME coordinates:
`Q(z) + ℓ_a(z) + q(a) = Q(z − c) − R₀(a)`, identically in `z` over ℚ. -/
theorem completeSquare {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    (z : OutWit m r → ℚ) :
    D.zQuadQ z + D.zLinQ a z + (D.aPart a : ℚ) = D.zQuadQ (z - c) - D.residual a c := by
  have hz := hc z
  have hsym : D.zPolarQ z c = D.zPolarQ c z := D.zPolarQ_symm z c
  rw [D.zQuadQ_sub, residual, hsym]
  linarith [hz]

/-- **The prescribed norm of the off-centre vector.**  Every integer solution sits at squared
distance exactly `R₀(a)` from the centre.  This is what §4.2 anchors and §5 deforms. -/
theorem offCentre_norm {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    {z : OutWit m r → ℤ} (hz : D.SolZ a z) :
    D.zQuadQ (toQ z - c) = D.residual a c := by
  have h0 : D.zQuad z + D.zLinEval a z + D.aPart a = 0 := by
    have := hz; unfold QuadraticGraphData.SolZ at this; rwa [D.evalZ] at this
  have hQ : D.zQuadQ (toQ z) + D.zLinQ a (toQ z) + (D.aPart a : ℚ) = 0 := by
    rw [D.zQuadQ_toQ, D.zLinQ_toQ]
    exact_mod_cast congrArg (fun t : ℤ => (t : ℚ)) h0
  have hcs := D.completeSquare hc (toQ z)
  linarith [hQ, hcs]

/-! ### ℚ-layer bilinearity (needed by the isotropic section) -/

theorem zQuadQ_add (v w : OutWit m r → ℚ) :
    D.zQuadQ (v + w) = D.zQuadQ v + D.zPolarQ v w + D.zQuadQ w := by
  simp only [zQuadQ, zPolarQ, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem zQuadQ_smul (lam : ℚ) (v : OutWit m r → ℚ) :
    D.zQuadQ (lam • v) = lam ^ 2 * D.zQuadQ v := by
  simp only [zQuadQ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  ring

theorem zPolarQ_smul_right (lam : ℚ) (v w : OutWit m r → ℚ) :
    D.zPolarQ v (lam • w) = lam * D.zPolarQ v w := by
  simp only [zPolarQ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  ring

/-! ### T11 — the anchored section along an isotropic direction -/

/-- **T11.**  Along an isotropic direction `e` that is not polar-orthogonal to `v₀`, the value of
the form can be moved to ANY prescribed `R` by an explicit affine shift.  Note the constant: the
reviewer writes `2B(v₀,e)` because his `B` is the bilinear form with `polar = 2B`; here `zPolarQ`
IS the polar form, so the factor 2 must NOT appear.  (Carrying it would be an error of exactly the
kind control #7 is aimed at.) -/
theorem anchoredSection {e v₀ : OutWit m r → ℚ} (he : D.zQuadQ e = 0)
    (hb : D.zPolarQ v₀ e ≠ 0) (R : ℚ) :
    D.zQuadQ (v₀ + ((R - D.zQuadQ v₀) / D.zPolarQ v₀ e) • e) = R := by
  rw [D.zQuadQ_add, D.zPolarQ_smul_right, D.zQuadQ_smul, he]
  field_simp
  ring

/-- **The all-inputs rational section.**  One centre and one isotropic direction produce a rational
solution at EVERY input `a` — the content of the reviewer's §4.2, at the rational level, with no
`LineToCoset` and no line-by-line construction. -/
theorem exists_rational_solution_of_isotropic {a : Fin n → ℤ} {c : OutWit m r → ℚ}
    (hc : D.IsCentre a c) {e v₀ : OutWit m r → ℚ} (he : D.zQuadQ e = 0)
    (hb : D.zPolarQ v₀ e ≠ 0) :
    ∃ w : OutWit m r → ℚ, D.zQuadQ w + D.zLinQ a w + (D.aPart a : ℚ) = 0 := by
  refine ⟨c + (v₀ + ((D.residual a c - D.zQuadQ v₀) / D.zPolarQ v₀ e) • e), ?_⟩
  have hsec := D.anchoredSection he hb (D.residual a c)
  have hcs := D.completeSquare hc (c + (v₀ + ((D.residual a c - D.zQuadQ v₀) / D.zPolarQ v₀ e) • e))
  have hsub : (c + (v₀ + ((D.residual a c - D.zQuadQ v₀) / D.zPolarQ v₀ e) • e)) - c
      = v₀ + ((D.residual a c - D.zQuadQ v₀) / D.zPolarQ v₀ e) • e := by
    abel
  rw [hsub] at hcs
  rw [hcs, hsec]
  ring

/-- NEGATIVE control for T11: if `e` is isotropic AND polar-orthogonal to `v₀`, the shift moves
nothing — the value stays `Q(v₀)`, so the hypothesis `zPolarQ v₀ e ≠ 0` is load-bearing. -/
theorem anchoredSection_degenerate {e v₀ : OutWit m r → ℚ} (he : D.zQuadQ e = 0)
    (hb : D.zPolarQ v₀ e = 0) (lam : ℚ) :
    D.zQuadQ (v₀ + lam • e) = D.zQuadQ v₀ := by
  rw [D.zQuadQ_add, D.zPolarQ_smul_right, D.zQuadQ_smul, he, hb]
  ring


/-! ### T10 — an isotropic direction that the output can see -/

theorem zPolarQ_add_right (v w1 w2 : OutWit m r → ℚ) :
    D.zPolarQ v (w1 + w2) = D.zPolarQ v w1 + D.zPolarQ v w2 := by
  simp only [zPolarQ, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

/-- Nondegeneracy of the polar form, stated WITHOUT matrices or duals: every nonzero vector is
seen by the form. -/
def NondegQ : Prop := ∀ v : OutWit m r → ℚ, v ≠ 0 → ∃ w, D.zPolarQ v w ≠ 0

/-- Auxiliary: one direction seen by BOTH `e₀` and `v₀`. -/
theorem exists_seen_by_both (hnd : D.NondegQ) {e₀ v₀ : OutWit m r → ℚ}
    (he₀0 : e₀ ≠ 0) (hv₀ : v₀ ≠ 0) :
    ∃ y, D.zPolarQ e₀ y ≠ 0 ∧ D.zPolarQ v₀ y ≠ 0 := by
  obtain ⟨w, hw⟩ := hnd v₀ hv₀
  obtain ⟨u, hu⟩ := hnd e₀ he₀0
  by_cases hew : D.zPolarQ e₀ w = 0
  · by_cases h1 : D.zPolarQ v₀ u + D.zPolarQ v₀ w = 0
    · refine ⟨u + (2 : ℚ) • w, ?_, ?_⟩
      · rw [D.zPolarQ_add_right, D.zPolarQ_smul_right, hew]
        simpa using hu
      · rw [D.zPolarQ_add_right, D.zPolarQ_smul_right]
        have : D.zPolarQ v₀ u = - D.zPolarQ v₀ w := by linarith
        rw [this]
        intro hcon
        apply hw
        linarith [hcon]
    · refine ⟨u + w, ?_, ?_⟩
      · rw [D.zPolarQ_add_right, hew]
        simpa using hu
      · rw [D.zPolarQ_add_right]
        exact h1
  · by_cases h2 : D.zPolarQ v₀ w = 0
    · exact absurd h2 hw
    · exact ⟨w, hew, hw⟩

/-- **T10.**  If the form is nondegenerate and has ONE nonzero isotropic vector, then for every
nonzero `v₀` there is an isotropic direction not polar-orthogonal to `v₀` — exactly the hypothesis
`anchoredSection` (T11) needs.  The reviewer's §4.1 proves this by building a hyperbolic pair and
showing the isotropic vectors span; the argument here is shorter and needs no basis: slide `e₀`
along a direction seen by both `e₀` and `v₀`. -/
theorem exists_isotropic_nonorthogonal (hnd : D.NondegQ)
    {e₀ : OutWit m r → ℚ} (he₀ : D.zQuadQ e₀ = 0) (he₀0 : e₀ ≠ 0)
    {v₀ : OutWit m r → ℚ} (hv₀ : v₀ ≠ 0) (hpv : D.zPolarQ v₀ e₀ = 0) :
    ∃ e, D.zQuadQ e = 0 ∧ D.zPolarQ v₀ e ≠ 0 := by
  obtain ⟨y, hy1, hy2⟩ := D.exists_seen_by_both hnd he₀0 hv₀
  by_cases hQy : D.zQuadQ y = 0
  · exact ⟨y, hQy, hy2⟩
  · refine ⟨e₀ + (-(D.zPolarQ e₀ y) / D.zQuadQ y) • y, ?_, ?_⟩
    · rw [D.zQuadQ_add, D.zPolarQ_smul_right, D.zQuadQ_smul, he₀]
      field_simp
      ring
    · rw [D.zPolarQ_add_right, D.zPolarQ_smul_right, hpv]
      have ht : (-(D.zPolarQ e₀ y) / D.zQuadQ y) ≠ 0 := by
        apply div_ne_zero
        · simpa using hy1
        · exact hQy
      simpa using mul_ne_zero ht hy2


/-! ### Controls -/

/-- POSITIVE control: when the linear part vanishes the origin is a centre, so `IsCentre` is
satisfiable and `completeSquare` is not vacuous. -/
theorem isCentre_zero_of_lin_zero {a : Fin n → ℤ} (h : ∀ k, D.zLin a k = 0) :
    D.IsCentre a 0 := by
  intro w
  simp [zPolarQ, zLinQ, h]

/-- NEGATIVE control: if the form is identically zero but the linear part is not, NO centre
exists.  So the hypothesis of `completeSquare` is a real restriction — it is exactly the point
where degeneracy must be handled, and it is what the named leaf below has to supply. -/
theorem not_isCentre_of_polar_zero {a : Fin n → ℤ}
    (hpol : ∀ v w : OutWit m r → ℚ, D.zPolarQ v w = 0)
    {w : OutWit m r → ℚ} (hw : D.zLinQ a w ≠ 0) (c : OutWit m r → ℚ) :
    ¬ D.IsCentre a c := by
  intro hc
  have := hc w
  rw [hpol c w] at this
  exact hw (by linarith)

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
