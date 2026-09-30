/-
  C3Reflection.lean — Gate-18 research program, Packet c3_reflection.
  The reflection sub-case of the C2-3 / C3 definite case (kernel-able part).

  Setting: one input `x`, one witness `u`, a general `(y,u)`-quadratic
    P(x,y,u) = a y² + b y u + c u² + d x y + e x u + f x² + g y + h u + i x + j.
  NO definiteness assumption is needed for this part.

  Reflection lemma. Suppose there are integer-valued affine centres
    y₀(x) = p x + q,   u₀(x) = r x + s
  such that P is invariant under `(y,u) ↦ (2 y₀(x) − y, 2 u₀(x) − u)` for all `x, y, u`
  (the "integral centre" identity `CentreId`).  We prove:
  * `centre_iff`   — the identity holds iff the gradient of the `(y,u)`-part vanishes at the
                     centre as a polynomial in `x`:
                        2a p + b r + d = 0 ∧ 2a q + b s + g = 0 ∧
                        b p + 2c r + e = 0 ∧ b q + 2c s + h = 0.
  * `rgen_reflect` — the reflection of a solution is a solution.
  * `rgen_unique_forces_centre` — uniqueness of the output forces `y = p x + q`.
  * `rgen_centre_global` / `rgen_centre_full` — total + unique ⇒ the output function is
    `GlobalQuadratic` (an affine `QuadForm`), hence `FullCosetNF`.
  * The coset version `rgen_centre_coset_weak` — when the centre is integral only on a coset
    `x = ρ + M t` (with `y₀ = p' t + q'`, `u₀ = r' t + s'` integral there), the restricted
    output lands in `WeakScalarCosetNF`.

  Controls (n = 1):
  (i)   y² + (u − x)² = 0                — centre (0, x), total-unique, output ≡ 0 (Global).
  (ii)  (y − x)² + u² − 1 = 0            — centre (x, 0): the centre identity holds and the
        reflection lemma applies, but the relation is NOT unique in `y`
        (y ∈ {x−1, x, x+1}); a control showing that uniqueness is a genuinely separate
        hypothesis from reflection symmetry.
  (iii) (2y − x)² + (2u − 1)² − 2 = 0    — half-integral centre (x/2, 1/2): NO integer
        `p q r s` satisfy the centre identity, so the integral-centre hypothesis fails.

  Baseline (mpup-lean r39) is read-only; nothing here is imported by the baseline.
  std-3 only (see certificates/AxiomReport_c3r.log); no `sorry`, no new axioms.
-/
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.NInputNoWitness

namespace DiophCompression.ResearchUpgrade

open Matrix

/-- The general one-input / one-witness `(y,u)`-quadratic polynomial. -/
def Pgen (a b c d e f g h i j x y u : ℤ) : ℤ :=
  a * y ^ 2 + b * y * u + c * u ^ 2 + d * x * y + e * x * u + f * x ^ 2
    + g * y + h * u + i * x + j

/-- The relation `∃ u, P(x,y,u) = 0`: input `x`, output `y`, witness `u`. -/
def Rgen (a b c d e f g h i j : ℤ) (x y : ℤ) : Prop :=
  ∃ u : ℤ, Pgen a b c d e f g h i j x y u = 0

/-- The integral-centre identity: `P` is invariant under the reflection
`(y,u) ↦ (2(p x + q) − y, 2(r x + s) − u)` for all `x, y, u`. -/
def CentreId (a b c d e f g h i j p q r s : ℤ) : Prop :=
  ∀ x y u : ℤ,
    Pgen a b c d e f g h i j x y u
      = Pgen a b c d e f g h i j x (2 * (p * x + q) - y) (2 * (r * x + s) - u)

/-! ### The centre identity ⇔ the vanishing-gradient coefficient conditions. -/

/-- The reflection identity holds iff the gradient of the `(y,u)`-part vanishes at the
centre, as a polynomial identity in `x`. -/
theorem centre_iff (a b c d e f g h i j p q r s : ℤ) :
    CentreId a b c d e f g h i j p q r s ↔
      (2 * a * p + b * r + d = 0 ∧ 2 * a * q + b * s + g = 0 ∧
        b * p + 2 * c * r + e = 0 ∧ b * q + 2 * c * s + h = 0) := by
  constructor
  · intro hh
    have e1 := hh 1 1 0
    have e2 := hh 1 0 0
    have e3 := hh 0 1 0
    have e4 := hh 0 0 0
    have e5 := hh 0 0 1
    have e6 := hh 1 0 1
    simp only [Pgen] at e1 e2 e3 e4 e5 e6
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h1 : (2 : ℤ) * (2 * a * p + b * r + d) = 0 := by linear_combination e1 - e2 - e3 + e4
      linarith
    · have h2 : (2 : ℤ) * (2 * a * q + b * s + g) = 0 := by linear_combination e3 - e4
      linarith
    · have h3 : (2 : ℤ) * (b * p + 2 * c * r + e) = 0 := by linear_combination e6 - e2 - e5 + e4
      linarith
    · have h4 : (2 : ℤ) * (b * q + 2 * c * s + h) = 0 := by linear_combination e5 - e4
      linarith
  · rintro ⟨hc1, hc2, hc3, hc4⟩ x y u
    simp only [Pgen]
    linear_combination (2 * x * (y - p * x - q)) * hc1 + (2 * (y - p * x - q)) * hc2
      + (2 * x * (u - r * x - s)) * hc3 + (2 * (u - r * x - s)) * hc4

/-! ### Theorem 1 — reflection of a solution is a solution. -/

theorem rgen_reflect (a b c d e f g h i j p q r s : ℤ)
    (hc : CentreId a b c d e f g h i j p q r s) (x y : ℤ)
    (hR : Rgen a b c d e f g h i j x y) :
    Rgen a b c d e f g h i j x (2 * (p * x + q) - y) := by
  obtain ⟨u, hu⟩ := hR
  exact ⟨2 * (r * x + s) - u, by rw [← hc x y u]; exact hu⟩

/-! ### Theorem 2 — uniqueness forces the output onto the centre. -/

theorem rgen_unique_forces_centre (a b c d e f g h i j p q r s : ℤ)
    (hc : CentreId a b c d e f g h i j p q r s)
    (hU : RelUnique (Rgen a b c d e f g h i j)) :
    ∀ x y, Rgen a b c d e f g h i j x y → y = p * x + q := by
  intro x y hxy
  have hrefl := rgen_reflect a b c d e f g h i j p q r s hc x y hxy
  have hEq := hU x y (2 * (p * x + q) - y) hxy hrefl
  linarith

/-! ### Theorem 3 — total + unique ⇒ the output function is (affine) Global / Full. -/

/-- The choice-extracted output of the total relation, as a function `(Fin 1 → ℤ) → ℤ`. -/
noncomputable def rgenOut (a b c d e f g h i j : ℤ)
    (hT : RelTotal (Rgen a b c d e f g h i j)) : (Fin 1 → ℤ) → ℤ :=
  fun v => Classical.choose (hT (v 0))

theorem rgen_centre_global (a b c d e f g h i j p q r s : ℤ)
    (hc : CentreId a b c d e f g h i j p q r s)
    (hT : RelTotal (Rgen a b c d e f g h i j))
    (hU : RelUnique (Rgen a b c d e f g h i j)) :
    GlobalQuadratic (rgenOut a b c d e f g h i j hT) := by
  refine ⟨⟨(q : ℚ), fun _ => (p : ℚ), 0⟩, fun v => ?_⟩
  have hval : Rgen a b c d e f g h i j (v 0) (Classical.choose (hT (v 0))) :=
    Classical.choose_spec (hT (v 0))
  have hy : Classical.choose (hT (v 0)) = p * (v 0) + q :=
    rgen_unique_forces_centre a b c d e f g h i j p q r s hc hU (v 0) _ hval
  simp only [rgenOut]
  rw [hy]
  simp only [QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one, Matrix.zero_apply,
    mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
  push_cast
  ring

theorem rgen_centre_full (a b c d e f g h i j p q r s : ℤ)
    (hc : CentreId a b c d e f g h i j p q r s)
    (hT : RelTotal (Rgen a b c d e f g h i j))
    (hU : RelUnique (Rgen a b c d e f g h i j)) :
    FullCosetNF (rgenOut a b c d e f g h i j hT) :=
  globalQuadratic_imp_fullCoset (rgen_centre_global a b c d e f g h i j p q r s hc hT hU)

/-! ### Theorem 4 — the coset version (integral centre only on `x ≡ ρ (mod M)`). -/

/-- The integral-centre identity restricted to the coset `x = ρ + M t`, with the centre
written in the coset coordinate `t` as `y₀ = p' t + q'`, `u₀ = r' t + s'` (all integers). -/
def CosetCentreId (a b c d e f g h i j : ℤ) (M : ℕ) (ρ p' q' r' s' : ℤ) : Prop :=
  ∀ t y u : ℤ,
    Pgen a b c d e f g h i j (ρ + (M : ℤ) * t) y u
      = Pgen a b c d e f g h i j (ρ + (M : ℤ) * t)
          (2 * (p' * t + q') - y) (2 * (r' * t + s') - u)

theorem rgen_reflect_coset (a b c d e f g h i j : ℤ) (M : ℕ) (ρ p' q' r' s' : ℤ)
    (hc : CosetCentreId a b c d e f g h i j M ρ p' q' r' s') (t y : ℤ)
    (hR : Rgen a b c d e f g h i j (ρ + (M : ℤ) * t) y) :
    Rgen a b c d e f g h i j (ρ + (M : ℤ) * t) (2 * (p' * t + q') - y) := by
  obtain ⟨u, hu⟩ := hR
  exact ⟨2 * (r' * t + s') - u, by rw [← hc t y u]; exact hu⟩

theorem rgen_unique_forces_centre_coset (a b c d e f g h i j : ℤ) (M : ℕ) (ρ p' q' r' s' : ℤ)
    (hc : CosetCentreId a b c d e f g h i j M ρ p' q' r' s')
    (hU : RelUnique (Rgen a b c d e f g h i j)) :
    ∀ t y, Rgen a b c d e f g h i j (ρ + (M : ℤ) * t) y → y = p' * t + q' := by
  intro t y hxy
  have hrefl := rgen_reflect_coset a b c d e f g h i j M ρ p' q' r' s' hc t y hxy
  have hEq := hU (ρ + (M : ℤ) * t) y (2 * (p' * t + q') - y) hxy hrefl
  linarith

theorem rgen_centre_coset_weak (a b c d e f g h i j : ℤ) (M : ℕ) (ρ p' q' r' s' : ℤ)
    (hM : 1 ≤ M)
    (hc : CosetCentreId a b c d e f g h i j M ρ p' q' r' s')
    (hT : RelTotal (Rgen a b c d e f g h i j))
    (hU : RelUnique (Rgen a b c d e f g h i j)) :
    WeakScalarCosetNF (rgenOut a b c d e f g h i j hT) := by
  refine ⟨M, fun _ => ρ, ⟨(q' : ℚ), fun _ => (p' : ℚ), 0⟩, hM, fun t => ?_⟩
  have hx0 : ((fun _ => ρ : Fin 1 → ℤ) + (M : ℤ) • t) 0 = ρ + (M : ℤ) * (t 0) := by
    simp [Pi.add_apply]
  have hval : Rgen a b c d e f g h i j (ρ + (M : ℤ) * (t 0))
      (Classical.choose (hT (((fun _ => ρ : Fin 1 → ℤ) + (M : ℤ) • t) 0))) := by
    have hsp := Classical.choose_spec (hT (((fun _ => ρ : Fin 1 → ℤ) + (M : ℤ) • t) 0))
    rwa [hx0] at hsp
  have hy := rgen_unique_forces_centre_coset a b c d e f g h i j M ρ p' q' r' s' hc hU (t 0) _ hval
  simp only [rgenOut]
  rw [hy]
  simp only [QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one, Matrix.zero_apply,
    mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
  push_cast
  ring

/-! ### Control (i): `y² + (u − x)² = 0` — centre (0, x), total-unique, output ≡ 0. -/

/-- `P = y² + u² − 2 x u + x² = y² + (u − x)²`. -/
theorem control_i_total : RelTotal (Rgen 1 0 1 0 (-2) 1 0 0 0 0) := by
  intro x
  exact ⟨0, x, by simp only [Pgen]; ring⟩

theorem control_i_unique : RelUnique (Rgen 1 0 1 0 (-2) 1 0 0 0 0) := by
  rintro x y y' ⟨u, hu⟩ ⟨u', hu'⟩
  simp only [Pgen] at hu hu'
  have hy2 : y ^ 2 = 0 := by nlinarith [sq_nonneg y, sq_nonneg (u - x)]
  have hy'2 : y' ^ 2 = 0 := by nlinarith [sq_nonneg y', sq_nonneg (u' - x)]
  have hy : y = 0 := sq_eq_zero_iff.mp hy2
  have hy' : y' = 0 := sq_eq_zero_iff.mp hy'2
  rw [hy, hy']

theorem control_i_centre : CentreId 1 0 1 0 (-2) 1 0 0 0 0 0 0 1 0 :=
  (centre_iff 1 0 1 0 (-2) 1 0 0 0 0 0 0 1 0).mpr (by norm_num)

/-- The output of control (i) is `GlobalQuadratic` (the constant `0`). -/
theorem control_i_global :
    GlobalQuadratic (rgenOut 1 0 1 0 (-2) 1 0 0 0 0 control_i_total) :=
  rgen_centre_global 1 0 1 0 (-2) 1 0 0 0 0 0 0 1 0 control_i_centre control_i_total
    control_i_unique

/-! ### Control (ii): `(y − x)² + u² − 1 = 0` — centre (x, 0).
The centre identity holds and the reflection lemma applies, but the relation is NOT unique in
`y` (for `x = 0` the outputs `y ∈ {−1, 0, 1}` all occur): uniqueness is a strictly stronger
hypothesis than reflection symmetry. -/

/-- `P = y² + u² − 2 x y + x² − 1 = (y − x)² + u² − 1`. -/
theorem control_ii_centre : CentreId 1 0 1 (-2) 0 1 0 0 0 (-1) 1 0 0 0 :=
  (centre_iff 1 0 1 (-2) 0 1 0 0 0 (-1) 1 0 0 0).mpr (by norm_num)

/-- Reflection lemma in action: at `x = 0` the solution `y = 1` reflects to `y = −1`. -/
theorem control_ii_reflect : Rgen 1 0 1 (-2) 0 1 0 0 0 (-1) 0 (-1) := by
  have h : Rgen 1 0 1 (-2) 0 1 0 0 0 (-1) 0 1 := ⟨0, by simp only [Pgen]; ring⟩
  have hr := rgen_reflect 1 0 1 (-2) 0 1 0 0 0 (-1) 1 0 0 0 control_ii_centre 0 1 h
  simpa using hr

/-- Control (ii) is NOT unique: at `x = 0` both `y = 1` (via `u = 0`) and `y = 0` (via `u = 1`)
solve, so reflection symmetry alone does not pin the output. -/
theorem control_ii_not_unique : ¬ RelUnique (Rgen 1 0 1 (-2) 0 1 0 0 0 (-1)) := by
  intro hU
  have h1 : Rgen 1 0 1 (-2) 0 1 0 0 0 (-1) 0 1 := ⟨0, by simp only [Pgen]; ring⟩
  have h2 : Rgen 1 0 1 (-2) 0 1 0 0 0 (-1) 0 0 := ⟨1, by simp only [Pgen]; ring⟩
  exact one_ne_zero (hU 0 1 0 h1 h2)

/-! ### Control (iii): `(2y − x)² + (2u − 1)² − 2 = 0` — half-integral centre (x/2, 1/2).
No integer `p q r s` satisfy the centre identity (the first condition is `8 p = 4`), so the
integral-centre hypothesis fails; the reflection argument does not apply. -/

/-- `P = 4 y² + 4 u² − 4 x y + x² − 4 u − 1 = (2y − x)² + (2u − 1)² − 2`. -/
theorem control_iii_no_integral_centre :
    ¬ ∃ p q r s : ℤ, CentreId 4 0 4 (-4) 0 1 0 (-4) 0 (-1) p q r s := by
  rintro ⟨p, q, r, s, hc⟩
  rw [centre_iff] at hc
  obtain ⟨h1, -, -, -⟩ := hc
  omega

end DiophCompression.ResearchUpgrade
