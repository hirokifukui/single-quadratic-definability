/-
  ParityWitness.lean — s48.  The `(2,1,0)` witness of `reports/CASE210_REPORT.md` §7c, as
  theorems rather than as a script.

  `P(a, b) = 4b² − (4a+2)b + (a² + a) = (2b − a)(2b − a − 1)`

  is total and output-unique over ℤ — exactly one of `2b = a`, `2b = a + 1` is solvable, by parity
  — and the function it defines is NOT a polynomial of degree ≤ 2.  That matters for attribution:
  **Lew–Rosenberg 1978 Thm 5.3(2) assumes the function is a polynomial, so it does not reach this
  graph.**  The non-polynomial branch at `(2,1,0)` is not theirs.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import Mathlib.Tactic.Ring.RingNF

namespace DiophCompression.ResearchUpgrade

/-- The defining polynomial factors. -/
theorem parity_factor (a b : ℤ) :
    4 * b ^ 2 - (4 * a + 2) * b + (a ^ 2 + a) = (2 * b - a) * (2 * b - a - 1) := by
  ring

/-- A solution is a `b` with `2b = a` or `2b = a + 1`. -/
theorem parity_sol_iff (a b : ℤ) :
    4 * b ^ 2 - (4 * a + 2) * b + (a ^ 2 + a) = 0 ↔ (2 * b = a ∨ 2 * b = a + 1) := by
  rw [parity_factor]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rintro (h | h)
    · have : 2 * b - a = 0 := by omega
      rw [this]; ring
    · have : 2 * b - a - 1 = 0 := by omega
      rw [this]; ring

/-- **TOTAL.**  Every integer `a` has a solution — by parity. -/
theorem parity_total (a : ℤ) : ∃ b : ℤ, 4 * b ^ 2 - (4 * a + 2) * b + (a ^ 2 + a) = 0 := by
  rcases Int.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k, (parity_sol_iff a k).mpr (Or.inl (by omega))⟩
  · exact ⟨k + 1, (parity_sol_iff a (k + 1)).mpr (Or.inr (by omega))⟩

/-- **OUTPUT-UNIQUE.**  At most one solution — the two branches cannot both be solvable, since
`a` and `a + 1` have opposite parities. -/
theorem parity_unique (a b b' : ℤ)
    (h : 4 * b ^ 2 - (4 * a + 2) * b + (a ^ 2 + a) = 0)
    (h' : 4 * b' ^ 2 - (4 * a + 2) * b' + (a ^ 2 + a) = 0) : b = b' := by
  rcases (parity_sol_iff a b).mp h with hb | hb <;>
    rcases (parity_sol_iff a b').mp h' with hb' | hb' <;> omega

/-- **NOT A POLYNOMIAL OF DEGREE ≤ 2.**  Any `f` solving the equation at every integer takes the
values `0, 1, 1, 2` at `a = 0, 1, 2, 3`, and no rational quadratic does that. -/
theorem parity_not_quadratic {f : ℤ → ℤ}
    (hf : ∀ a : ℤ, 4 * (f a) ^ 2 - (4 * a + 2) * (f a) + (a ^ 2 + a) = 0) :
    ¬ ∃ c₀ c₁ c₂ : ℚ, ∀ a : ℤ, ((f a : ℚ)) = c₀ + c₁ * (a : ℚ) + c₂ * (a : ℚ) ^ 2 := by
  have val : ∀ a : ℤ, 2 * f a = a ∨ 2 * f a = a + 1 := fun a => (parity_sol_iff a (f a)).mp (hf a)
  have h0 : f 0 = 0 := by have := val 0; omega
  have h1 : f 1 = 1 := by have := val 1; omega
  have h2 : f 2 = 1 := by have := val 2; omega
  have h3 : f 3 = 2 := by have := val 3; omega
  rintro ⟨c₀, c₁, c₂, hc⟩
  have e0 := hc 0
  have e1 := hc 1
  have e2 := hc 2
  have e3 := hc 3
  rw [h0] at e0; rw [h1] at e1; rw [h2] at e2; rw [h3] at e3
  push_cast at e0 e1 e2 e3
  linarith

/-- POSITIVE control: the witness function exists — `parity_total` plus `parity_unique` give a
genuine total, output-unique graph, so `parity_not_quadratic` is not vacuous. -/
theorem parity_exists_unique (a : ℤ) :
    ∃! b : ℤ, 4 * b ^ 2 - (4 * a + 2) * b + (a ^ 2 + a) = 0 := by
  obtain ⟨b, hb⟩ := parity_total a
  exact ⟨b, hb, fun b' hb' => parity_unique a b' b hb' hb⟩

/-- NEGATIVE control: the equation is genuinely quadratic in `b` — the `b²` coefficient is `4`,
not `0`, so this is case B of the split and not case A.  (With `α = 0` the analysis is different;
see the report.) -/
theorem parity_discriminant (a : ℤ) : (4 * a + 2) ^ 2 - 4 * 4 * (a ^ 2 + a) = 4 := by ring

end DiophCompression.ResearchUpgrade
