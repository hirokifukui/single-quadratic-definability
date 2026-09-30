/-
  UniformFiniteOrLog.lean — Gate-20 Packet S1, task S1.1.

  The first-stage statement in its exact final form: ONE constant `C` for the whole polynomial,
  and for every parameter point either a uniform height bound on the scalar fibre or the
  logarithmic lower bound.

  The two halves already exist and are joined here without weakening either:
  * baseline (mpup-lean r39, untouched): `singleQuadratic_finiteFiber_height_scalar_sup` —
    `∃ C, ∀ a, (fiberZZ P a).Finite → ∀ c ∈ fiberZZ P a, |c| ≤ C · (1 + ‖a‖_∞)²`.
  * research (s45): `logBarrier_of_quadratic_unconditional` — for every `a`, the fibre is bounded
    or `LogLowerBound`, with NO `FixedAPPrimeLowerBound` and no other analytic input.

  The bridge is that a bounded set of integers is finite, so the bounded branch of the log barrier
  feeds the uniform height theorem.

  QUANTIFIER DISCIPLINE (reviewer's acceptance criterion, and regression controls #2 and #6).
  `C` is bound BEFORE `a`: it depends only on `P`.  The constants `κ, X₀` inside `LogLowerBound`
  are bound after `a`, i.e. they may depend on the parameter point — and the statement does not
  claim otherwise.  The two quantifications are not mixed: no `κ` is uniform, no `C` is local.

  Claim tags: [P] (std-3).  Baseline read-only; nothing here is imported by the baseline.
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import ResearchUpgrade.Shadow.SummitClosureR

namespace DiophCompression.ResearchUpgrade

open MvPolynomial MPUP

variable {n r : ℕ}

/-- A bounded set of integers is finite. -/
theorem finite_of_bounded_int {S : Set ℤ} {B : ℕ} (hB : ∀ c ∈ S, |c| ≤ (B : ℤ)) : S.Finite :=
  Set.Finite.subset (Set.finite_Icc (-(B : ℤ)) (B : ℤ))
    (fun _ hc => Set.mem_Icc.mpr (abs_le.mp (hB _ hc)))

/-- **S1.1 — uniform finite-or-log.**  One constant `C` depending only on `P`: for every parameter
point `a`, either every element of the scalar fibre satisfies `|c| ≤ C · (1 + ‖a‖_∞)²`, or the
fibre satisfies the logarithmic lower bound. -/
theorem uniform_finite_or_log (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2) :
    ∃ C : ℕ, ∀ a : Fin n → ℤ,
      (∀ c ∈ fiberZZ P a,
          |c| ≤ (C : ℤ) * ((1 + Finset.univ.sup fun i => (a i).natAbs : ℕ) : ℤ) ^ 2)
        ∨ LogLowerBound (fiberZZ P a) := by
  obtain ⟨C, hC⟩ := singleQuadratic_finiteFiber_height_scalar_sup P hP
  refine ⟨C, fun a => ?_⟩
  rcases logBarrier_of_quadratic_unconditional P hP a with ⟨B, hB⟩ | hlog
  · exact Or.inl (hC a (finite_of_bounded_int hB))
  · exact Or.inr hlog

/-- The infinite-fibre corollary: an infinite scalar fibre of a quadratic always satisfies the
logarithmic lower bound.  (The bounded branch cannot occur, since bounded ⇒ finite.) -/
theorem logLowerBound_of_infinite_fiber (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2)
    (a : Fin n → ℤ) (hinf : (fiberZZ P a).Infinite) : LogLowerBound (fiberZZ P a) := by
  rcases logBarrier_of_quadratic_unconditional P hP a with ⟨B, hB⟩ | hlog
  · exact absurd (finite_of_bounded_int hB) hinf
  · exact hlog

/-- The same dichotomy stated so that BOTH constants are visible at once: the height constant is
uniform in `a`, the log constants are not.  Kept as a separate root so that a later edit cannot
silently promote `κ` to a uniform constant (regression control #2). -/
theorem uniform_finite_or_log_explicit (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2) :
    ∃ C : ℕ, ∀ a : Fin n → ℤ,
      (∀ c ∈ fiberZZ P a,
          |c| ≤ (C : ℤ) * ((1 + Finset.univ.sup fun i => (a i).natAbs : ℕ) : ℤ) ^ 2)
        ∨ ∃ (κ : ℝ) (X₀ : ℕ), 0 < κ ∧ 2 ≤ X₀ ∧
            ∀ X : ℕ, X₀ ≤ X → κ * Real.log X ≤ (fiberCountZZ (fiberZZ P a) X : ℝ) := by
  obtain ⟨C, hC⟩ := uniform_finite_or_log P hP
  exact ⟨C, fun a => (hC a).imp id id⟩

end DiophCompression.ResearchUpgrade
