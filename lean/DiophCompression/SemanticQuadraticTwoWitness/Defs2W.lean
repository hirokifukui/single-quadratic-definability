/-
  DiophCompression/SemanticQuadraticTwoWitness/Defs2W.lean — definitions for the two-witness cell (n, 2, 2)
  (GPT r06 §7 必須D; session 7, 2026-08-27). Definitions only, no theorems.
  Explicit coefficients: H(c,u,v) = A c² + B₁ c u + B₂ c v + C₁₁ u² + C₁₂ u v + C₂₂ v² (witness block W = C₁₁u²+C₁₂uv+C₂₂v²).
  Mathematics: SemanticQuadraticGeneral/CLASSIFICATION_2W.md.
-/
import DiophCompression.SemanticQuadraticGeneral.Defs

namespace DiophCompression.SemanticQuadraticTwoWitness

/-- The fiber polynomial with two witnesses, explicit coefficients. -/
def fq2 (A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q : ℤ) (c u v : ℤ) : ℤ :=
  A * c ^ 2 + B₁ * c * u + B₂ * c * v + C₁₁ * u ^ 2 + C₁₂ * u * v + C₂₂ * v ^ 2
    + l * c + m₁ * u + m₂ * v + q

/-- Naturals c that have integer witnesses (u, v). -/
def fiberSet2 (A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q : ℤ) : Set ℕ :=
  {c | ∃ u v : ℤ, fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q (c : ℤ) u v = 0}

/-- The bound shape K·((1 + |l| + |m₁| + |m₂|)² + |q|). -/
def fbound2 (K : ℕ) (l m₁ m₂ q : ℤ) : ℤ := (K : ℤ) * ((1 + |l| + |m₁| + |m₂|) ^ 2 + |q|)

/-- Projection dichotomy for a fixed ternary quadratic part. -/
def Dichotomy2 (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) : Prop :=
  ∃ K : ℕ, ∀ l m₁ m₂ q : ℤ, (fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q).Infinite ∨
    ∀ c ∈ fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q, (c : ℤ) ≤ fbound2 K l m₁ m₂ q

/-- Discriminant of the witness block W. -/
def discW (C₁₁ C₁₂ C₂₂ : ℤ) : ℤ := C₁₂ ^ 2 - 4 * C₁₁ * C₂₂

/-- Schur complement of the witness block in H, scaled by 2N with N = −discW:
    α = 2N A − (2C₂₂B₁² − 2C₁₂B₁B₂ + 2C₁₁B₂²). -/
def schur (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) : ℤ :=
  2 * (4 * C₁₁ * C₂₂ - C₁₂ ^ 2) * A - (2 * C₂₂ * B₁ ^ 2 - 2 * C₁₂ * B₁ * B₂ + 2 * C₁₁ * B₂ ^ 2)

end DiophCompression.SemanticQuadraticTwoWitness
