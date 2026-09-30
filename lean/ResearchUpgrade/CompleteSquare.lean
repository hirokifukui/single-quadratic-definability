/-
  CompleteSquare.lean — Gate-20 Packet N3, task N3.1.

  The constant-matrix complete-square compiler (reviewer §5).  For

      P(t, y, u) = a y² + b y u + c u² + d t y + e t u + f t² + g y + h u + i t + j

  — the general one-input / one-witness quadratic, `Pgen` in ℚ coordinates — the homogeneous
  `(y,u)`-part `a, b, c` carries NO `t`-dependence (reviewer P0 #3: that is forced by
  totalDegree ≤ 2, and it is what makes the matrix constant).  Completing the square in `(y,u)`
  around the affine centre gives

      P(t, z) = F(z − c(t)) − N(t),    F(Y,U) = a Y² + b Y U + c U²,  c affine,  deg N ≤ 2

  with `F` FIXED — no input-dependent quadratic matrix anywhere (reviewer's prohibition, and
  regression control #11: this file contains no `t` inside `F`, which is visible in the type).

  * `PQ` — the ℚ-coordinates form; `PQ_cast` ties it to the integer `Pgen` of `C3Reflection.lean`.
  * `complete_square_compiler` — the centre and `N`, explicitly, over `Δ = 4ac − b² ≠ 0`.
  * `definite_diagonalization` — the rational diagonalisation `F(Y,U) = a·(v₁² + D v₂²)` with
    `D = Δ/(4a²)`, i.e. `λ·q_D` with `λ = a`; `diag_D_pos` gives `D > 0` in the definite case.
  * `rational_norm_of_total` — the bridge that hands the next packet its input: if `P(t,·,·) = 0`
    is solvable over ℚ at every `t`, then the degree-≤2 polynomial `N(t)/a` is represented by
    `x² + D y²` at every `t` — exactly the hypothesis shape of N2.2 / N2.3.

  Every coefficient below was derived and checked symbolically (sympy) before the Lean was written.

  Claim tags: [P] (std-3).  Baseline read-only.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import Mathlib.Tactic.LinearCombination
import ResearchUpgrade.C3Reflection

namespace DiophCompression.ResearchUpgrade

/-- The one-input / one-witness quadratic in ℚ coordinates (the image of `Pgen`). -/
def PQ (a b c d e f g h i j t y u : ℚ) : ℚ :=
  a * y ^ 2 + b * y * u + c * u ^ 2 + d * t * y + e * t * u + f * t ^ 2
    + g * y + h * u + i * t + j

/-- `PQ` is the rational image of the integer `Pgen`. -/
theorem PQ_cast (a b c d e f g h i j x y u : ℤ) :
    ((Pgen a b c d e f g h i j x y u : ℤ) : ℚ)
      = PQ (a : ℚ) b c d e f g h i j x y u := by
  simp only [Pgen, PQ]; push_cast; ring

/-- **N3.1 — constant-matrix complete-square compiler.**  The quadratic part `(a,b,c)` is fixed and
carries no `t`; the centre is affine and `N` has degree ≤ 2. -/
theorem complete_square_compiler (a b c d e f g h i j : ℚ) (hΔ : 4 * a * c - b ^ 2 ≠ 0) :
    ∃ p q r s n₂ n₁ n₀ : ℚ, ∀ t y u : ℚ,
      PQ a b c d e f g h i j t y u
        = (a * (y - (p * t + q)) ^ 2 + b * (y - (p * t + q)) * (u - (r * t + s))
            + c * (u - (r * t + s)) ^ 2) - (n₂ * t ^ 2 + n₁ * t + n₀) := by
  set Δ : ℚ := 4 * a * c - b ^ 2 with hΔdef
  refine ⟨(-2 * c * d + b * e) / Δ, (-2 * c * g + b * h) / Δ,
    (-2 * a * e + b * d) / Δ, (-2 * a * h + b * g) / Δ,
    a * ((-2 * c * d + b * e) / Δ) ^ 2
      + b * ((-2 * c * d + b * e) / Δ) * ((-2 * a * e + b * d) / Δ)
      + c * ((-2 * a * e + b * d) / Δ) ^ 2 - f,
    2 * a * ((-2 * c * d + b * e) / Δ) * ((-2 * c * g + b * h) / Δ)
      + b * (((-2 * c * d + b * e) / Δ) * ((-2 * a * h + b * g) / Δ)
        + ((-2 * c * g + b * h) / Δ) * ((-2 * a * e + b * d) / Δ))
      + 2 * c * ((-2 * a * e + b * d) / Δ) * ((-2 * a * h + b * g) / Δ) - i,
    a * ((-2 * c * g + b * h) / Δ) ^ 2
      + b * ((-2 * c * g + b * h) / Δ) * ((-2 * a * h + b * g) / Δ)
      + c * ((-2 * a * h + b * g) / Δ) ^ 2 - j, ?_⟩
  intro t y u
  simp only [PQ]
  field_simp
  ring

/-- The rational diagonalisation `F(Y,U) = a · (v₁² + D v₂²)`, `D = (4ac − b²)/(4a²)`. -/
theorem definite_diagonalization (a b c : ℚ) (ha : a ≠ 0) (Y U : ℚ) :
    a * Y ^ 2 + b * Y * U + c * U ^ 2
      = a * ((Y + (b / (2 * a)) * U) ^ 2 + ((4 * a * c - b ^ 2) / (4 * a ^ 2)) * U ^ 2) := by
  field_simp
  ring

/-- In the positive-definite case the diagonal parameter is positive. -/
theorem diag_D_pos (a b c : ℚ) (ha : 0 < a) (hΔ : 0 < 4 * a * c - b ^ 2) :
    0 < (4 * a * c - b ^ 2) / (4 * a ^ 2) :=
  div_pos hΔ (by positivity)

/-- **The bridge to N2.2 / N2.3.**  If `P(t,·,·) = 0` is solvable over ℚ at every `t`, then the
degree-≤2 polynomial `N(t)/a` is represented by `x² + D y²` at every `t`. -/
theorem rational_norm_of_total (a b c d e f g h i j : ℚ) (ha : a ≠ 0)
    (hΔ : 4 * a * c - b ^ 2 ≠ 0)
    (htot : ∀ t : ℚ, ∃ y u : ℚ, PQ a b c d e f g h i j t y u = 0) :
    ∃ A' B' C' : ℚ, ∀ t : ℚ, ∃ x z : ℚ,
      A' * t ^ 2 + B' * t + C' = x ^ 2 + ((4 * a * c - b ^ 2) / (4 * a ^ 2)) * z ^ 2 := by
  obtain ⟨p, q, r, s, n₂, n₁, n₀, hid⟩ := complete_square_compiler a b c d e f g h i j hΔ
  refine ⟨n₂ / a, n₁ / a, n₀ / a, fun t => ?_⟩
  obtain ⟨y, u, hyu⟩ := htot t
  have hF : a * (y - (p * t + q)) ^ 2 + b * (y - (p * t + q)) * (u - (r * t + s))
      + c * (u - (r * t + s)) ^ 2 = n₂ * t ^ 2 + n₁ * t + n₀ := by
    linear_combination hyu - hid t y u
  have hdiag := definite_diagonalization a b c ha (y - (p * t + q)) (u - (r * t + s))
  exact ⟨(y - (p * t + q)) + (b / (2 * a)) * (u - (r * t + s)), u - (r * t + s), by
    linear_combination (norm := (field_simp; ring)) (-(1 : ℚ) / a) * hF + ((1 : ℚ) / a) * hdiag⟩

end DiophCompression.ResearchUpgrade
