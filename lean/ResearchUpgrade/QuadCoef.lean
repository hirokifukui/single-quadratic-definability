/-
  QuadCoef.lean — s48.  Infrastructure for Gate22 **G22-T11** (the all-input quadratic section).

  The reviewer's pass condition for T11 is that the section be of degree ≤ 2 **in the input
  variables**, not merely that a rational solution exist for each fixed input.  Proving that by
  assembling `QuadForm` structures by hand, coordinate by coordinate, is where such arguments go
  wrong.  Instead this file gives the two closure predicates and their algebra:

      `IsAffineCoef g`  :  `g a = c + Σᵢ aᵢ lᵢ`
      `IsQuadCoef g`    :  `g a = q.eval a` for some `QuadForm n`

  with: constants and coordinates are affine; affine is closed under `+`, scalar `•` and finite
  sums; **a product of two affines is quadratic**; and quadratic is closed under `+`, `-`, `•` and
  finite sums.  Every coefficient function of the isotropic section is built from these five moves,
  so no `QuadForm` is ever written out by hand.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.Rat
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.GraphVocabulary
import ResearchUpgrade.IsotropicDirection
import ResearchUpgrade.RationalCentre

namespace DiophCompression.ResearchUpgrade

open Matrix

variable {n : ℕ}

/-- `g` is an affine function of the input, with rational coefficients. -/
def IsAffineCoef (g : (Fin n → ℤ) → ℚ) : Prop :=
  ∃ (c : ℚ) (l : Fin n → ℚ), ∀ a, g a = c + ∑ i, (a i : ℚ) * l i

/-- `g` is a rational polynomial of total degree ≤ 2 in the input. -/
def IsQuadCoef (g : (Fin n → ℤ) → ℚ) : Prop :=
  ∃ q : QuadForm n, ∀ a, g a = q.eval (castQ a)

/-! ### Affine algebra -/

theorem isAffineCoef_const (c : ℚ) : IsAffineCoef (fun _ : Fin n → ℤ => c) :=
  ⟨c, 0, fun a => by simp⟩

theorem isAffineCoef_zero : IsAffineCoef (0 : (Fin n → ℤ) → ℚ) :=
  ⟨0, 0, fun a => by simp⟩

theorem isAffineCoef_coord (i : Fin n) : IsAffineCoef (fun a : Fin n → ℤ => (a i : ℚ)) := by
  refine ⟨0, Pi.single i 1, fun a => ?_⟩
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem IsAffineCoef.add {g h : (Fin n → ℤ) → ℚ} (hg : IsAffineCoef g) (hh : IsAffineCoef h) :
    IsAffineCoef (fun a => g a + h a) := by
  obtain ⟨c₁, l₁, h₁⟩ := hg
  obtain ⟨c₂, l₂, h₂⟩ := hh
  refine ⟨c₁ + c₂, l₁ + l₂, fun a => ?_⟩
  show g a + h a = _
  rw [h₁, h₂]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem IsAffineCoef.add' {g h : (Fin n → ℤ) → ℚ} (hg : IsAffineCoef g) (hh : IsAffineCoef h) :
    IsAffineCoef (g + h) := hg.add hh

theorem IsAffineCoef.smul {g : (Fin n → ℤ) → ℚ} (c : ℚ) (hg : IsAffineCoef g) :
    IsAffineCoef (fun a => c * g a) := by
  obtain ⟨c₁, l₁, h₁⟩ := hg
  refine ⟨c * c₁, c • l₁, fun a => ?_⟩
  show c * g a = _
  rw [h₁, mul_add]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem isAffineCoef_sum {ι : Type*} [Fintype ι] (g : ι → (Fin n → ℤ) → ℚ)
    (h : ∀ i, IsAffineCoef (g i)) : IsAffineCoef (fun a => ∑ i, g i a) := by
  classical
  obtain ⟨c, l, hc⟩ : IsAffineCoef (∑ i, g i) :=
    Finset.sum_induction g IsAffineCoef (fun _ _ => IsAffineCoef.add') isAffineCoef_zero
      (fun i _ => h i)
  refine ⟨c, l, fun a => ?_⟩
  show (∑ i, g i a) = _
  rw [← Finset.sum_apply]
  exact hc a

/-! ### Quadratic algebra -/

theorem IsAffineCoef.isQuadCoef {g : (Fin n → ℤ) → ℚ} (hg : IsAffineCoef g) : IsQuadCoef g := by
  obtain ⟨c, l, hc⟩ := hg
  refine ⟨⟨c, l, 0⟩, fun a => ?_⟩
  have hdot : l ⬝ᵥ castQ a = ∑ i, (a i : ℚ) * l i := by
    simp only [dotProduct, castQ]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [QuadForm.eval, Matrix.zero_mulVec, dotProduct_zero, add_zero, hdot]
  exact hc a

theorem isQuadCoef_zero : IsQuadCoef (0 : (Fin n → ℤ) → ℚ) :=
  isAffineCoef_zero.isQuadCoef

theorem IsQuadCoef.add {g h : (Fin n → ℤ) → ℚ} (hg : IsQuadCoef g) (hh : IsQuadCoef h) :
    IsQuadCoef (fun a => g a + h a) := by
  obtain ⟨q₁, h₁⟩ := hg
  obtain ⟨q₂, h₂⟩ := hh
  refine ⟨⟨q₁.c + q₂.c, q₁.l + q₂.l, q₁.Q + q₂.Q⟩, fun a => ?_⟩
  show g a + h a = _
  rw [h₁, h₂]
  simp only [QuadForm.eval, add_dotProduct, Matrix.add_mulVec, dotProduct_add]
  ring

theorem IsQuadCoef.add' {g h : (Fin n → ℤ) → ℚ} (hg : IsQuadCoef g) (hh : IsQuadCoef h) :
    IsQuadCoef (g + h) := hg.add hh

theorem IsQuadCoef.smul {g : (Fin n → ℤ) → ℚ} (c : ℚ) (hg : IsQuadCoef g) :
    IsQuadCoef (fun a => c * g a) := by
  obtain ⟨q, hq⟩ := hg
  refine ⟨⟨c * q.c, c • q.l, c • q.Q⟩, fun a => ?_⟩
  have hl : (c • q.l) ⬝ᵥ castQ a = c * (q.l ⬝ᵥ castQ a) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hs : castQ a ⬝ᵥ ((c • q.Q) *ᵥ castQ a) = c * (castQ a ⬝ᵥ (q.Q *ᵥ castQ a)) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  show c * g a = _
  rw [hq]
  simp only [QuadForm.eval, hl, hs]
  ring

theorem IsQuadCoef.sub {g h : (Fin n → ℤ) → ℚ} (hg : IsQuadCoef g) (hh : IsQuadCoef h) :
    IsQuadCoef (fun a => g a - h a) := by
  have h2 := hg.add (hh.smul (-1))
  have heq : (fun a => g a + (-1) * h a) = (fun a => g a - h a) := by funext a; ring
  rwa [heq] at h2

theorem isQuadCoef_sum {ι : Type*} [Fintype ι] (g : ι → (Fin n → ℤ) → ℚ)
    (h : ∀ i, IsQuadCoef (g i)) : IsQuadCoef (fun a => ∑ i, g i a) := by
  classical
  obtain ⟨q, hq⟩ : IsQuadCoef (∑ i, g i) :=
    Finset.sum_induction g IsQuadCoef (fun _ _ => IsQuadCoef.add') isQuadCoef_zero (fun i _ => h i)
  refine ⟨q, fun a => ?_⟩
  show (∑ i, g i a) = _
  rw [← Finset.sum_apply]
  exact hq a

/-- **The one non-formal closure step.**  A product of two affine functions of the input has
total degree ≤ 2, with the rank-one matrix `l₁ l₂ᵀ` as its quadratic part. -/
theorem IsAffineCoef.mul {g h : (Fin n → ℤ) → ℚ} (hg : IsAffineCoef g) (hh : IsAffineCoef h) :
    IsQuadCoef (fun a => g a * h a) := by
  obtain ⟨c₁, l₁, h₁⟩ := hg
  obtain ⟨c₂, l₂, h₂⟩ := hh
  refine ⟨⟨c₁ * c₂, c₁ • l₂ + c₂ • l₁, vecMulVec l₁ l₂⟩, fun a => ?_⟩
  have hquad : castQ a ⬝ᵥ (vecMulVec l₁ l₂ *ᵥ castQ a)
      = (∑ i, (a i : ℚ) * l₁ i) * (∑ i, (a i : ℚ) * l₂ i) := by
    simp only [dotProduct, Matrix.mulVec, vecMulVec_apply, castQ]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlin : (c₁ • l₂ + c₂ • l₁) ⬝ᵥ castQ a
      = c₁ * (∑ i, (a i : ℚ) * l₂ i) + c₂ * (∑ i, (a i : ℚ) * l₁ i) := by
    simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, castQ,
      Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  show g a * h a = _
  rw [h₁, h₂]
  simp only [QuadForm.eval]
  rw [hlin, hquad]
  ring

/-! ### The applications: the residual `R(a)` has total degree ≤ 2 in the input

This is the substantive content of G22-T11's pass condition.  `R(a) = Q(h(a)) − q(a)` must be a
degree-≤2 polynomial IN THE INPUT, not merely a number attached to each input; that is what makes
the isotropic section a polynomial section rather than a pointwise existence statement.  With the
affine centre family (G22-T06 §3.1) it follows from the closure algebra above and nothing else. -/

/-- Each coordinate of the affine centre family is an affine function of the input. -/
theorem isAffineCoef_centreFamily {m r : ℕ} (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ)
    (k : OutWit m r) :
    IsAffineCoef (fun a : Fin n → ℤ => (c₀ + ∑ i, (a i : ℚ) • cs i) k) := by
  refine ⟨c₀ k, fun i => cs i k, fun a => ?_⟩
  simp [Finset.sum_apply]

namespace QuadraticGraphData

variable {m r : ℕ} (D : QuadraticGraphData n m r)

/-- The input-only part `q(a)` has total degree ≤ 2 — by construction, but stated so the closure
algebra can consume it. -/
theorem isQuadCoef_aPart : IsQuadCoef (fun a : Fin n → ℤ => ((D.aPart a : ℤ) : ℚ)) := by
  have hsplit : ∀ a : Fin n → ℤ, ((D.aPart a : ℤ) : ℚ)
      = ((D.P.c : ℤ) : ℚ) + (∑ i, (a i : ℚ) * ((D.P.l (Sum.inl i) : ℤ) : ℚ))
        + ∑ i, ∑ j, (a i : ℚ) * (((D.P.Q (Sum.inl i) (Sum.inl j) : ℤ) : ℚ) * (a j : ℚ)) := by
    intro a
    simp only [aPart]
    push_cast
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl
      (Finset.sum_congr rfl fun i _ => by ring)) rfl
  have h1 : IsQuadCoef (fun _ : Fin n → ℤ => ((D.P.c : ℤ) : ℚ)) :=
    (isAffineCoef_const _).isQuadCoef
  have h2aff : IsAffineCoef (fun a : Fin n → ℤ =>
      ∑ i, (a i : ℚ) * ((D.P.l (Sum.inl i) : ℤ) : ℚ)) :=
    ⟨0, fun i => ((D.P.l (Sum.inl i) : ℤ) : ℚ), fun a => by simp⟩
  have h2 := h2aff.isQuadCoef
  have h3 : IsQuadCoef (fun a : Fin n → ℤ =>
      ∑ i, ∑ j, (a i : ℚ) * (((D.P.Q (Sum.inl i) (Sum.inl j) : ℤ) : ℚ) * (a j : ℚ))) := by
    refine isQuadCoef_sum _ fun i => isQuadCoef_sum _ fun j => ?_
    exact (isAffineCoef_coord i).mul ((isAffineCoef_coord j).smul _)
  have := (h1.add h2).add h3
  obtain ⟨q, hq⟩ := this
  refine ⟨q, fun a => ?_⟩
  show ((D.aPart a : ℤ) : ℚ) = _
  rw [hsplit a]
  exact hq a

/-- `Q(h(a))` has total degree ≤ 2 when `h` is the affine centre family: a finite sum of products
of two affine functions. -/
theorem isQuadCoef_zQuadQ_centre (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ) :
    IsQuadCoef (fun a : Fin n → ℤ => D.zQuadQ (c₀ + ∑ i, (a i : ℚ) • cs i)) := by
  have hform : ∀ a : Fin n → ℤ, D.zQuadQ (c₀ + ∑ i, (a i : ℚ) • cs i)
      = ∑ k, ∑ k', (c₀ + ∑ i, (a i : ℚ) • cs i) k
          * (((D.P.Q (Sum.inr k) (Sum.inr k') : ℤ) : ℚ) * (c₀ + ∑ i, (a i : ℚ) • cs i) k') :=
    fun a => rfl
  have hq : IsQuadCoef (fun a : Fin n → ℤ =>
      ∑ k, ∑ k', (c₀ + ∑ i, (a i : ℚ) • cs i) k
        * (((D.P.Q (Sum.inr k) (Sum.inr k') : ℤ) : ℚ) * (c₀ + ∑ i, (a i : ℚ) • cs i) k')) := by
    refine isQuadCoef_sum _ fun k => isQuadCoef_sum _ fun k' => ?_
    exact (isAffineCoef_centreFamily c₀ cs k).mul
      ((isAffineCoef_centreFamily c₀ cs k').smul _)
  obtain ⟨q, hqq⟩ := hq
  refine ⟨q, fun a => ?_⟩
  show D.zQuadQ (c₀ + ∑ i, (a i : ℚ) • cs i) = _
  rw [hform a]
  exact hqq a

/-- **G22-T11, the degree statement.**  With an AFFINE centre family the residual
`R(a) = Q(h(a)) − q(a)` is a rational polynomial of total degree ≤ 2 in the input.  This is the
pass condition the reviewer sets for T11: not "a rational solution exists at each `a`", but a
section that is polynomial in `a`. -/
theorem isQuadCoef_residual (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ) :
    IsQuadCoef (fun a : Fin n → ℤ => D.residual a (c₀ + ∑ i, (a i : ℚ) • cs i)) :=
  (D.isQuadCoef_zQuadQ_centre c₀ cs).sub D.isQuadCoef_aPart

/-! ### Controls -/

/-- POSITIVE control: the predicates are inhabited and the degree bound is attained — `a ↦ a₀·a₀`
is quadratic and not affine-by-inspection, so `IsQuadCoef` is not secretly `IsAffineCoef`. -/
theorem isQuadCoef_sq (i : Fin n) :
    IsQuadCoef (fun a : Fin n → ℤ => (a i : ℚ) * (a i : ℚ)) :=
  (isAffineCoef_coord i).mul (isAffineCoef_coord i)

/-- NEGATIVE control: the affine predicate is a genuine restriction — `a ↦ a₀²` is NOT affine.
Evaluating a putative affine representation at `0`, `e₀` and `2e₀` forces `4c = 4(c + l)` and
`c = c + 2l` simultaneously, which is impossible.  So the distinction the closure algebra draws
between `IsAffineCoef` and `IsQuadCoef` is real, and `IsAffineCoef.mul` is not vacuous. -/
theorem not_isAffineCoef_sq (i : Fin n) :
    ¬ IsAffineCoef (fun a : Fin n → ℤ => (a i : ℚ) * (a i : ℚ)) := by
  rintro ⟨c, l, hc⟩
  have h0 := hc (fun _ => (0 : ℤ))
  have h1 := hc (fun _ => (1 : ℤ))
  have h2 := hc (fun _ => (2 : ℤ))
  have e0 : ∑ j, (((0 : ℤ) : ℚ)) * l j = 0 := by simp
  have e2 : ∑ j, (((2 : ℤ) : ℚ)) * l j = 2 * ∑ j, l j := by
    push_cast
    rw [Finset.mul_sum]
  simp only [e0] at h0
  simp only [e2] at h2
  push_cast at h0 h1 h2
  simp only [one_mul] at h1
  linarith

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
