/-
  BranchSplit.lean — s48.  Gate22 **G22-T19**: the split, stated ON THE FORM and proved
  EXHAUSTIVE, plus the negation reduction that the negative-semidefinite case needs.

  HAZARD (recorded s48): `QuadForm.Q` / `IntQuad.Q` is a bare `Matrix`, and `eval` sees only its
  symmetric part.  A case split written as `Q = 0` at the MATRIX level is therefore wrong on our
  own type.  Everything here is stated on `zQuadQ` / `zPolarQ` — the form and its polar — never on
  the matrix.

  The split is not the reviewer's four-way list read literally: `semidefinite` has two signs, and
  `dim_le_of_semidefinite_defines` only knows the positive one.  The fix is not a second proof but
  a reduction: `P` and `−P` have the SAME zero set, hence define the same function, and negating
  flips the form.  `negGraph` makes that a theorem.

  The second thing this file fixes is the line between the isotropic and quotient-anisotropic
  cases.  It must be drawn on RADICALITY, not on `Q(x) = 0` — `isotropic_not_radical_possible`
  exhibits a graph where the two differ.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.GraphVocabulary
import ResearchUpgrade.IsotropicBranch
import ResearchUpgrade.PellBranch
import ResearchUpgrade.PolarAnnihilator
import ResearchUpgrade.RadicalBridge
import ResearchUpgrade.RationalCentre

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-! ### The negation reduction -/

/-- The graph of the negated polynomial.  Same zero set, opposite form. -/
def negGraph : QuadraticGraphData n m r := ⟨⟨-D.P.c, -D.P.l, -D.P.Q⟩⟩

theorem negGraph_eval (x : Vars n m r → ℤ) : D.negGraph.P.eval x = - D.P.eval x := by
  simp only [negGraph, IntQuad.eval]
  have h1 : (-D.P.l) ⬝ᵥ x = -(D.P.l ⬝ᵥ x) := neg_dotProduct _ _
  have h2 : x ⬝ᵥ ((-D.P.Q) *ᵥ x) = -(x ⬝ᵥ (D.P.Q *ᵥ x)) := by
    rw [Matrix.neg_mulVec, dotProduct_neg]
  rw [h1, h2]
  ring

theorem negGraph_sol (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin r → ℤ) :
    D.negGraph.Sol a b u ↔ D.Sol a b u := by
  unfold QuadraticGraphData.Sol
  rw [D.negGraph_eval]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

theorem negGraph_graph (a : Fin n → ℤ) (b : Fin m → ℤ) :
    D.negGraph.Graph a b ↔ D.Graph a b := by
  constructor
  · rintro ⟨u, hu⟩; exact ⟨u, (D.negGraph_sol a b u).mp hu⟩
  · rintro ⟨u, hu⟩; exact ⟨u, (D.negGraph_sol a b u).mpr hu⟩

theorem negGraph_defines {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    D.negGraph.Defines f := fun a b => (D.negGraph_graph a b).trans (hf a b)

theorem negGraph_zQuadQ (u : OutWit m r → ℚ) : D.negGraph.zQuadQ u = - D.zQuadQ u := by
  simp only [zQuadQ, negGraph, Matrix.neg_apply, Int.cast_neg]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k' _ => by ring

theorem negGraph_zQuad (u : OutWit m r → ℤ) : D.negGraph.zQuad u = - D.zQuad u := by
  simp only [zQuad, negGraph, Matrix.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k' _ => by ring

/-- **The negative-semidefinite case**, obtained from the positive one by negating the graph
rather than by a second proof. -/
theorem dim_le_of_negSemidefinite_defines (hm : 0 < m)
    (hneg : ∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (hinj : Function.Injective f) :
    n ≤ m := by
  refine D.negGraph.dim_le_of_semidefinite_defines hm ?_ ?_ (D.negGraph_defines hf) hinj
  · intro u; rw [D.negGraph_zQuadQ]; linarith [hneg u]
  · obtain ⟨v, hv⟩ := hQ
    exact ⟨v, by rw [D.negGraph_zQuad]; omega⟩

/-! ### G22-T19 — the split is exhaustive -/

/-- **G22-T19.**  Over `ℚ`, and stated ON THE FORM, the four branch conditions are exhaustive:
either the form vanishes identically, or some isotropic vector is non-radical, or the form is
quotient-anisotropic and then it is positive semidefinite, negative semidefinite, or indefinite. -/
theorem branch_exhaustive :
    (∀ x : OutWit m r → ℚ, D.zQuadQ x = 0)
    ∨ (∃ x : OutWit m r → ℚ, D.zQuadQ x = 0 ∧ ¬ D.InRadicalQ x)
    ∨ ((∀ x : OutWit m r → ℚ, D.zQuadQ x = 0 → D.InRadicalQ x)
        ∧ ((∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u)
           ∨ (∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0)
           ∨ ((∃ p, 0 < D.zQuadQ p) ∧ ∃ q, D.zQuadQ q < 0))) := by
  classical
  by_cases hiso : ∃ x : OutWit m r → ℚ, D.zQuadQ x = 0 ∧ ¬ D.InRadicalQ x
  · exact Or.inr (Or.inl hiso)
  have hqa : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0 → D.InRadicalQ x := by
    intro x hx
    by_contra hc
    exact hiso ⟨x, hx, hc⟩
  by_cases hp : ∃ p : OutWit m r → ℚ, 0 < D.zQuadQ p
  · by_cases hq : ∃ q : OutWit m r → ℚ, D.zQuadQ q < 0
    · exact Or.inr (Or.inr ⟨hqa, Or.inr (Or.inr ⟨hp, hq⟩)⟩)
    · refine Or.inr (Or.inr ⟨hqa, Or.inl ?_⟩)
      intro u
      by_contra hc
      exact hq ⟨u, by linarith⟩
  · by_cases hq : ∃ q : OutWit m r → ℚ, D.zQuadQ q < 0
    · refine Or.inr (Or.inr ⟨hqa, Or.inr (Or.inl ?_)⟩)
      intro u
      by_contra hc
      exact hp ⟨u, by linarith⟩
    · refine Or.inl (fun x => ?_)
      have h1 : ¬ (0 < D.zQuadQ x) := fun h => hp ⟨x, h⟩
      have h2 : ¬ (D.zQuadQ x < 0) := fun h => hq ⟨x, h⟩
      linarith [lt_trichotomy (D.zQuadQ x) 0]

/-- The `Q ≡ 0` branch, translated to the INTEGER polar form that
`dim_le_one_of_linearBranch` consumes. -/
theorem zPolar_eq_zero_of_zQuadQ_zero (h : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0)
    (v w : OutWit m r → ℤ) : D.zPolar v w = 0 := by
  have hQ : D.zPolarQ (toQ v) (toQ w) = 0 := by
    have hsum := D.zQuadQ_add (toQ v) (toQ w)
    rw [h (toQ v + toQ w), h (toQ v), h (toQ w)] at hsum
    linarith
  rw [D.zPolarQ_toQ v w] at hQ
  exact_mod_cast hQ

/-! ### Controls -/

/-- POSITIVE control: the negation reduction is faithful — negating twice is the identity on the
form, so nothing is lost or double-counted by routing the negative-semidefinite case through it. -/
theorem negGraph_zQuadQ_involutive (u : OutWit m r → ℚ) :
    D.negGraph.negGraph.zQuadQ u = D.zQuadQ u := by
  rw [D.negGraph.negGraph_zQuadQ, D.negGraph_zQuadQ, neg_neg]

/-- NEGATIVE control: the isotropic / quotient-anisotropic line CANNOT be drawn on `Q(x) = 0`.
The explicit `(1,1,1)` hyperbolic graph has an isotropic vector outside the radical, so the two
conditions are genuinely different and the split above is stated on the right predicate. -/
theorem split_needs_radicality :
    ∃ (D' : QuadraticGraphData 1 1 1) (x : OutWit 1 1 → ℚ),
      D'.zQuadQ x = 0 ∧ ¬ D'.InRadicalQ x :=
  isotropic_not_radical_possible

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
