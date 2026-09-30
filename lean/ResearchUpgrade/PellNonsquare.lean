/-
  PellNonsquare.lean — s48.  Gate22 task **G22-T14** — the non-square certificate for the Pell
  discriminant.

  In the quotient-anisotropic branch one puts `A = Q(V)`, `C = Q(W)` on the visible orthogonal
  plane of G22-T13 and forms `d = −A·C > 0`.  `exists_pell_unit_congr` (T15, held) needs `d` to be
  a NON-SQUARE, and that is not a side condition to be assumed: it is exactly what
  quotient-anisotropy buys.  If `d = s²` then

      e = s·V + A·W  satisfies  Q(e) = A·(s² + A·C) = A·(d − d) = 0,

  while `polar(e, V) = 2sA ≠ 0`, so `e` is ISOTROPIC and NOT radical — which quotient-anisotropy
  forbids.  The witness is explicit, so the implication is sharp in both directions: `d` square
  and the plane orthogonal is precisely what produces the forbidden vector.

  The cross term `s·A·polar(V,W)` is what the orthogonality of the plane kills; the general
  identity is recorded so that this is visible rather than buried.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.OutputCoercivity
import ResearchUpgrade.PellPlane
import ResearchUpgrade.PolarAnnihilator

namespace DiophCompression.ResearchUpgrade

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- The general value of the combination, with the cross term visible. -/
theorem zQuadQ_combo (V W : OutWit m r → ℚ) (s : ℚ) :
    D.zQuadQ (s • V + (D.zQuadQ V) • W)
      = D.zQuadQ V * (s ^ 2 + D.zQuadQ V * D.zQuadQ W)
        + s * D.zQuadQ V * D.zPolarQ V W := by
  rw [D.zQuadQ_add, D.zQuadQ_smul, D.zQuadQ_smul, D.zPolarQ_smul_left, D.zPolarQ_smul_right]
  ring

/-- **The forbidden vector.**  On an orthogonal plane with `d = −A·C` a square, `s·V + A·W` is
isotropic. -/
theorem zQuadQ_combo_eq_zero {V W : OutWit m r → ℚ} (hperp : D.zPolarQ V W = 0)
    {s : ℚ} (hs : s ^ 2 = -(D.zQuadQ V * D.zQuadQ W)) :
    D.zQuadQ (s • V + (D.zQuadQ V) • W) = 0 := by
  rw [D.zQuadQ_combo, hperp, hs]
  ring

/-- …and it is NOT radical, because the polar form already separates it from `V`. -/
theorem not_inRadicalQ_combo {V W : OutWit m r → ℚ} (hperp : D.zPolarQ V W = 0)
    (hA : D.zQuadQ V ≠ 0) {s : ℚ} (hs : s ≠ 0) :
    ¬ D.InRadicalQ (s • V + (D.zQuadQ V) • W) := by
  intro hcon
  have h := hcon V
  rw [D.zPolarQ_add_left, D.zPolarQ_smul_left, D.zPolarQ_smul_left, D.zPolarQ_self,
    D.zPolarQ_symm W V, hperp] at h
  have h2 : s * (2 * D.zQuadQ V) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hs h3
  · exact hA (by linarith)

/-- **G22-T14 (over ℚ).**  Quotient-anisotropy forbids `d = −A·C` from being a square. -/
theorem not_isSquare_of_quotientAnisotropic
    (hqa : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0 → D.InRadicalQ x)
    {V W : OutWit m r → ℚ} (hperp : D.zPolarQ V W = 0) (hA : D.zQuadQ V ≠ 0)
    (hd : 0 < -(D.zQuadQ V * D.zQuadQ W)) :
    ¬ ∃ s : ℚ, s ^ 2 = -(D.zQuadQ V * D.zQuadQ W) := by
  rintro ⟨s, hs⟩
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    have h0 : -(D.zQuadQ V * D.zQuadQ W) = 0 := by rw [← hs]; ring
    linarith
  exact D.not_inRadicalQ_combo hperp hA hs0
    (hqa _ (D.zQuadQ_combo_eq_zero hperp hs))

/-- **G22-T14.**  The integral form, which is what `exists_pell_unit_congr` consumes: on the
visible orthogonal plane of G22-T13, scaled to integer vectors, the Pell discriminant
`d = −Q(V)·Q(W)` is a positive NON-SQUARE integer. -/
theorem not_isSquare_pellDiscr
    (hqa : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0 → D.InRadicalQ x)
    {V W : OutWit m r → ℤ} (hperp : D.zPolarQ (toQ V) (toQ W) = 0)
    (hA : D.zQuad V ≠ 0) (hd : 0 < -(D.zQuad V * D.zQuad W)) :
    ¬ IsSquare (-(D.zQuad V * D.zQuad W)) := by
  rintro ⟨k, hk⟩
  have hAQ : D.zQuadQ (toQ V) = ((D.zQuad V : ℤ) : ℚ) := D.zQuadQ_toQ V
  have hCQ : D.zQuadQ (toQ W) = ((D.zQuad W : ℤ) : ℚ) := D.zQuadQ_toQ W
  refine D.not_isSquare_of_quotientAnisotropic hqa hperp ?_ ?_ ⟨(k : ℚ), ?_⟩
  · rw [hAQ]; exact_mod_cast hA
  · rw [hAQ, hCQ]; exact_mod_cast hd
  · rw [hAQ, hCQ, sq]
    have h3 : ((-(D.zQuad V * D.zQuad W) : ℤ) : ℚ) = ((k * k : ℤ) : ℚ) := by exact_mod_cast hk
    push_cast at h3
    linarith

/-! ### Controls -/

/-- POSITIVE control: the implication is SHARP — if `d` is a square the forbidden vector exists
explicitly, is isotropic and is not radical.  So quotient-anisotropy really does decide the
non-squareness; it is not merely sufficient in an abstract sense. -/
theorem square_gives_forbidden_vector {V W : OutWit m r → ℚ} (hperp : D.zPolarQ V W = 0)
    (hA : D.zQuadQ V ≠ 0) {s : ℚ} (hs0 : s ≠ 0)
    (hs : s ^ 2 = -(D.zQuadQ V * D.zQuadQ W)) :
    ∃ e, D.zQuadQ e = 0 ∧ ¬ D.InRadicalQ e :=
  ⟨s • V + (D.zQuadQ V) • W, D.zQuadQ_combo_eq_zero hperp hs,
    D.not_inRadicalQ_combo hperp hA hs0⟩

/-- NEGATIVE control: the orthogonality of the plane is load-bearing.  Without `polar(V,W) = 0`
the combination carries the cross term `s·A·polar(V,W)`, so squareness of `d` no longer makes it
isotropic — which is why G22-T13 has to produce an ORTHOGONAL partner, not merely one of the
opposite sign. -/
theorem combo_cross_term {V W : OutWit m r → ℚ} {s : ℚ}
    (hs : s ^ 2 = -(D.zQuadQ V * D.zQuadQ W)) :
    D.zQuadQ (s • V + (D.zQuadQ V) • W) = s * D.zQuadQ V * D.zPolarQ V W := by
  rw [D.zQuadQ_combo, hs]
  ring

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
