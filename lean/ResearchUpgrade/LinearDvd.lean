/-
  LinearDvd.lean — s48.  The arithmetic core of case A3 in the `(2,1,0)` split
  (`reports/CASE210_REPORT.md` §1).

  A3 says: when the coefficient of `b` is a NON-CONSTANT affine form `L(a)`, the equation
  `L(a)·b + Q(a) = 0` forces `L ∣ Q` as polynomials, so the defined function is affine.
  The whole content of that step is the fact below — a non-constant linear form takes values of
  unbounded size along a line, and an integer divisible by all of them is zero.  Everything else
  in A3 is polynomial division, which is bookkeeping and is NOT formalized here.

  Claim tags: [P] (std-3).  Baseline read-only.
-/
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF

namespace DiophCompression.ResearchUpgrade

/-- **A non-constant integer linear form divides only zero.**  If `c * a + d` divides `R` for
every integer `a`, and `c ≠ 0`, then `R = 0`. -/
theorem eq_zero_of_forall_linear_dvd {c d R : ℤ} (hc : c ≠ 0)
    (h : ∀ a : ℤ, (c * a + d) ∣ R) : R = 0 := by
  by_contra hR
  set a : ℤ := |R| + |d| + 1 with ha
  have habs : |R| + 1 ≤ |c * a + d| := by
    have h1 : (1 : ℤ) ≤ |c| := Int.one_le_abs hc
    have hA : (0 : ℤ) ≤ a := by rw [ha]; positivity
    have h5 : |a| = a := abs_of_nonneg hA
    have h6 : a ≤ |c| * a := le_mul_of_one_le_left hA h1
    have h3 : |c * a| = |c| * a := by rw [abs_mul, h5]
    have e : (c * a + d) + (-d) = c * a := by ring
    have h4 : |c * a| ≤ |c * a + d| + |d| := by
      calc |c * a| = |(c * a + d) + (-d)| := by rw [e]
        _ ≤ |c * a + d| + |(-d)| := abs_add_le _ _
        _ = |c * a + d| + |d| := by rw [abs_neg]
    have h7 : |R| + |d| + 1 ≤ |c * a| := by rw [h3, ha] at *; linarith
    linarith
  have hdvd : |c * a + d| ∣ |R| := (abs_dvd _ _).mpr ((dvd_abs _ _).mpr (h a))
  have hpos : 0 < |R| := abs_pos.mpr hR
  have := Int.le_of_dvd hpos hdvd
  linarith

/-- POSITIVE control: the hypothesis is satisfiable — it holds for `R = 0`. -/
theorem forall_linear_dvd_zero (c d : ℤ) : ∀ a : ℤ, (c * a + d) ∣ (0 : ℤ) :=
  fun _ => dvd_zero _

/-- NEGATIVE control: `c ≠ 0` is load-bearing.  With `c = 0` the form is the constant `5`, which
divides `5` at every `a`, yet `5 ≠ 0`. -/
theorem not_eq_zero_of_forall_linear_dvd_of_const :
    (∀ a : ℤ, ((0 : ℤ) * a + 5) ∣ (5 : ℤ)) ∧ (5 : ℤ) ≠ 0 := by
  refine ⟨fun a => ?_, by norm_num⟩
  simp

/-- The form used in A3: a non-constant affine form in TWO variables, restricted to a line in the
first variable, divides only zero.  (`c₁ ≠ 0`; the case `c₂ ≠ 0` is the same statement with the
variables exchanged.) -/
theorem eq_zero_of_forall_affine_dvd {c₀ c₁ c₂ R : ℤ} (hc : c₁ ≠ 0) (a₂ : ℤ)
    (h : ∀ a₁ : ℤ, (c₀ + c₁ * a₁ + c₂ * a₂) ∣ R) : R = 0 := by
  refine eq_zero_of_forall_linear_dvd (c := c₁) (d := c₀ + c₂ * a₂) hc ?_
  intro a
  have := h a
  have he : c₁ * a + (c₀ + c₂ * a₂) = c₀ + c₁ * a + c₂ * a₂ := by ring
  rwa [he]

end DiophCompression.ResearchUpgrade
