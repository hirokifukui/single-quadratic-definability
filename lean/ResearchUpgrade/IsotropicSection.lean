/-
  IsotropicSection.lean — s48.  Gate22 task **G22-T11**, the section itself.

  The pieces are all in place: an AFFINE centre family (G22-T06 §3.1), an isotropic direction the
  output can see WITHOUT global nondegeneracy (G22-T10), the anchored-section identity (G21-T11),
  and the degree algebra (QuadCoef.lean).  This file writes the section down and proves the three
  things the reviewer's pass condition asks for:

      z(a) = h(a) + v₀ + ((R(a) − Q(v₀)) / polar(v₀,e)) · e

   * it SOLVES the equation at every input (not just: a solution exists at every input);
   * it is of total degree ≤ 2 in the input, coordinate by coordinate;
   * it is ANCHORED — `z(a₀) = z₀`, the integer solution one started from.

  Note the convention trap recorded at s47: the reviewer writes `2B(v₀,e)` because his `B` has
  `polar = 2B`; our `zPolarQ` IS the polar form, so the factor 2 must NOT appear.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.GraphVocabulary
import ResearchUpgrade.QuadCoef
import ResearchUpgrade.RationalCentre

namespace DiophCompression.ResearchUpgrade

/-- The affine centre family, as a function of the input. -/
def centreFamily {n m r : ℕ} (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ)
    (a : Fin n → ℤ) : OutWit m r → ℚ := c₀ + ∑ i, (a i : ℚ) • cs i

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- **The all-input isotropic section.** -/
noncomputable def isoSection (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ)
    (e v₀ : OutWit m r → ℚ) (a : Fin n → ℤ) : OutWit m r → ℚ :=
  centreFamily c₀ cs a
    + (v₀ + ((D.residual a (centreFamily c₀ cs a) - D.zQuadQ v₀) / D.zPolarQ v₀ e) • e)

theorem isoSection_sub_centre (c₀ cs e v₀) (a : Fin n → ℤ) :
    D.isoSection c₀ cs e v₀ a - centreFamily c₀ cs a
      = v₀ + ((D.residual a (centreFamily c₀ cs a) - D.zQuadQ v₀) / D.zPolarQ v₀ e) • e := by
  simp only [isoSection]
  abel

/-- **T11(a): the section solves the equation at EVERY input.** -/
theorem isoSection_solves {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    {e v₀ : OutWit m r → ℚ} (he : D.zQuadQ e = 0) (hb : D.zPolarQ v₀ e ≠ 0)
    (hcen : ∀ a : Fin n → ℤ, D.IsCentre a (centreFamily c₀ cs a)) (a : Fin n → ℤ) :
    D.zQuadQ (D.isoSection c₀ cs e v₀ a) + D.zLinQ a (D.isoSection c₀ cs e v₀ a)
      + (D.aPart a : ℚ) = 0 := by
  have hcs := D.completeSquare (hcen a) (D.isoSection c₀ cs e v₀ a)
  rw [D.isoSection_sub_centre] at hcs
  rw [hcs, D.anchoredSection he hb (D.residual a (centreFamily c₀ cs a))]
  ring

/-- **T11(b): the section is anchored** at the integer solution one started from. -/
theorem isoSection_anchor {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    {e : OutWit m r → ℚ} {a₀ : Fin n → ℤ} {z₀ : OutWit m r → ℤ}
    (hcen : ∀ a : Fin n → ℤ, D.IsCentre a (centreFamily c₀ cs a)) (hz₀ : D.SolZ a₀ z₀) :
    D.isoSection c₀ cs e (toQ z₀ - centreFamily c₀ cs a₀) a₀ = toQ z₀ := by
  have hnorm : D.zQuadQ (toQ z₀ - centreFamily c₀ cs a₀)
      = D.residual a₀ (centreFamily c₀ cs a₀) := D.offCentre_norm (hcen a₀) hz₀
  simp only [isoSection, hnorm, sub_self, zero_div, zero_smul, add_zero]
  abel

/-- **T11(c): every coordinate of the section is of total degree ≤ 2 in the input.**  This is the
part that a per-input choice of centre could not give. -/
theorem isQuadCoef_isoSection (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ)
    (e v₀ : OutWit m r → ℚ) (k : OutWit m r) :
    IsQuadCoef (fun a : Fin n → ℤ => D.isoSection c₀ cs e v₀ a k) := by
  have hcoord : ∀ a : Fin n → ℤ, D.isoSection c₀ cs e v₀ a k
      = (centreFamily c₀ cs a) k + (v₀ k
          + (e k / D.zPolarQ v₀ e) * (D.residual a (centreFamily c₀ cs a) - D.zQuadQ v₀)) := by
    intro a
    simp only [isoSection, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h1 : IsQuadCoef (fun a : Fin n → ℤ => (centreFamily c₀ cs a) k) :=
    (isAffineCoef_centreFamily c₀ cs k).isQuadCoef
  have h2 : IsQuadCoef (fun _ : Fin n → ℤ => v₀ k) := (isAffineCoef_const _).isQuadCoef
  have h3 : IsQuadCoef (fun a : Fin n → ℤ =>
      (e k / D.zPolarQ v₀ e) * (D.residual a (centreFamily c₀ cs a) - D.zQuadQ v₀)) :=
    IsQuadCoef.smul _ ((D.isQuadCoef_residual c₀ cs).sub (isAffineCoef_const _).isQuadCoef)
  obtain ⟨q, hq⟩ := h1.add (h2.add h3)
  refine ⟨q, fun a => ?_⟩
  show D.isoSection c₀ cs e v₀ a k = _
  rw [hcoord a]
  exact hq a

/-! ### Controls -/

/-- POSITIVE control: the section is not a trivial object — at the anchor it reproduces the given
integer solution, so the hypotheses of T11 are satisfiable whenever a solution and a visible
isotropic direction exist. -/
theorem isoSection_anchor_value {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    {e : OutWit m r → ℚ} {a₀ : Fin n → ℤ} {z₀ : OutWit m r → ℤ}
    (hcen : ∀ a : Fin n → ℤ, D.IsCentre a (centreFamily c₀ cs a)) (hz₀ : D.SolZ a₀ z₀)
    (k : OutWit m r) :
    D.isoSection c₀ cs e (toQ z₀ - centreFamily c₀ cs a₀) a₀ k = ((z₀ k : ℤ) : ℚ) :=
  congrFun (D.isoSection_anchor hcen hz₀) k

/-- NEGATIVE control: `polar(v₀,e) ≠ 0` is load-bearing.  If the isotropic direction is
polar-orthogonal to `v₀` the shift moves nothing — the "section" is the constant `h(a) + v₀`, whose
form value stays `Q(v₀)` at every input and therefore fails to track `R(a)`.  (This is
`anchoredSection_degenerate`, G21-T11, read at the level of the section.) -/
theorem isoSection_degenerate {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    {e v₀ : OutWit m r → ℚ} (he : D.zQuadQ e = 0) (hb : D.zPolarQ v₀ e = 0) (a : Fin n → ℤ) :
    D.zQuadQ (D.isoSection c₀ cs e v₀ a - centreFamily c₀ cs a) = D.zQuadQ v₀ := by
  rw [D.isoSection_sub_centre]
  exact D.anchoredSection_degenerate he hb _

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
