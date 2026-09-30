/-
  A3(e) / T03 — the REVERSE compiler `IntQuad → MvPolynomial`, with its degree bound.

  The r40 package carries the forward direction only: `isQuadRep_of_totalDegree_le_two`
  (`QuadRep.lean`) turns any `MvPolynomial` of total degree ≤ 2 into an `IntQuad` with the same
  evaluation.  The reviewer asked where the reverse compiler is.  A search of
  `ResearchUpgrade/` and `DiophCompression/` for
      `toMvPolynomial | IntQuad.*→ *MvPolynomial | mvPolynomialOf | ofIntQuad`
  returned nothing, so rather than record it as missing it is built here: it is four lines of
  data and a degree bound.

  With both directions the two carriers are interchangeable at degree ≤ 2, which is what T03
  asked for.  Note the asymmetry that remains: the forward direction needs the hypothesis
  `totalDegree ≤ 2`, the reverse direction proves it.

  s51.
-/
import ResearchUpgrade.QuadRep

namespace DiophCompression.ResearchUpgrade

open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The reverse compiler: an `IntQuad` as an honest multivariate polynomial. -/
noncomputable def IntQuad.toMv (q : IntQuad ι) : MvPolynomial ι ℤ :=
  (C q.c + ∑ i, C (q.l i) * X i) + ∑ i, ∑ j, C (q.Q i j) * (X i * X j)

/-- The reverse compiler is faithful: same values at every integer point. -/
theorem IntQuad.eval_toMv (q : IntQuad ι) (x : ι → ℤ) :
    MvPolynomial.eval x q.toMv = q.eval x := by
  have hq : ∀ i, ∑ j, q.Q i j * (x i * x j) = x i * ∑ j, q.Q i j * x j := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [IntQuad.toMv, IntQuad.eval, map_add, map_sum, map_mul, eval_C, eval_X,
    dotProduct, Matrix.mulVec]
  rw [Finset.sum_congr rfl fun i _ => hq i]

/-- The degree bound the reviewer asked for, PROVED rather than assumed. -/
theorem IntQuad.totalDegree_toMv (q : IntQuad ι) : q.toMv.totalDegree ≤ 2 := by
  refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
  · refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
    · show (C q.c : MvPolynomial ι ℤ).totalDegree ≤ 2
      rw [totalDegree_C]
      omega
    · refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun i _ => ?_)
      refine le_trans (totalDegree_mul _ _) ?_
      have h1 : (C (q.l i) : MvPolynomial ι ℤ).totalDegree = 0 := totalDegree_C _
      have h2 : (X i : MvPolynomial ι ℤ).totalDegree ≤ 1 := by
        rw [totalDegree_X]
      omega
  · refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun i _ => ?_)
    refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun j _ => ?_)
    refine le_trans (totalDegree_mul _ _) ?_
    have h1 : (C (q.Q i j) : MvPolynomial ι ℤ).totalDegree = 0 := totalDegree_C _
    have h2 : ((X i : MvPolynomial ι ℤ) * X j).totalDegree ≤ 2 := by
      refine le_trans (totalDegree_mul _ _) ?_
      have hx : (X i : MvPolynomial ι ℤ).totalDegree ≤ 1 := by rw [totalDegree_X]
      have hy : (X j : MvPolynomial ι ℤ).totalDegree ≤ 1 := by rw [totalDegree_X]
      omega
    omega

/-- **T03, both directions.**  A function `ι → ℤ` is the evaluation of a degree-≤2 multivariate
integer polynomial if and only if it is the evaluation of an `IntQuad`.  Forward is the existing
`isQuadRep_of_totalDegree_le_two`; backward is the compiler above. -/
theorem intQuad_iff_totalDegree_le_two (g : (ι → ℤ) → ℤ) :
    (∃ q : IntQuad ι, ∀ x, q.eval x = g x) ↔
      (∃ P : MvPolynomial ι ℤ, P.totalDegree ≤ 2 ∧ ∀ x, MvPolynomial.eval x P = g x) := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q.toMv, q.totalDegree_toMv, fun x => by rw [q.eval_toMv x, hq x]⟩
  · rintro ⟨P, hdeg, hP⟩
    obtain ⟨q, hq⟩ := IntQuad.isQuadRep_of_totalDegree_le_two P hdeg
    exact ⟨q, fun x => by rw [hq x, hP x]⟩

end DiophCompression.ResearchUpgrade
