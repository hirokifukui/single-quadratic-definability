/-
  DiophCompression/SemanticQuadraticSingular/DefsSingular.lean — r10 (GPT r09 必須B/H/I): definitions for the
  singular witness block at r = 3 (definitions only, no theorems). Radical variable last: F = fq2-block(u,v)
  + (b c + μ) w. Statements frozen first in `Singular_STATEMENTS.lean` (md5 281708fb); definitions here are
  identical to the freeze. Session 10, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticTwoWitness.Assembly2W
import DiophCompression.SemanticQuadraticMatrix.FullRankGeneric
import DiophCompression.SemanticQuadraticMatrix.AffineGcd
import DiophCompression.SemanticQuadraticThreeWitness.Bridge3W

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticTwoWitness
  DiophCompression.SemanticQuadraticGeneral

/-- Fiber polynomial with a two-witness block (u, v) and one radical variable w with affine coefficient b c + μ. -/
def fq3S (A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q : ℤ) (c u v w : ℤ) : ℤ :=
  fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v + (b * c + μ) * w

/-- Naturals c with integer witnesses (u, v, w). -/
def fiberSet3S (A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q : ℤ) : Set ℕ :=
  {c | ∃ u v w : ℤ, fq3S A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q (c : ℤ) u v w = 0}

/-- The bound shape K·((1 + |l| + |m₁| + |m₂| + |μ|)² + |q|) (= `fboundM` on `Fin 3`). -/
def fbound3S (K : ℕ) (l m₁ m₂ μ q : ℤ) : ℤ := (K : ℤ) * ((1 + |l| + |m₁| + |m₂| + |μ|) ^ 2 + |q|)

/-- Projection dichotomy for a fixed quadratic part (A, B₁, B₂, C₁₁, C₁₂, C₂₂, b) in singular coordinates. -/
def DichotomyS (A B₁ B₂ C₁₁ C₁₂ C₂₂ b : ℤ) : Prop :=
  ∃ K : ℕ, ∀ l m₁ m₂ μ q : ℤ, (fiberSet3S A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q).Infinite ∨
    ∀ c ∈ fiberSet3S A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q, (c : ℤ) ≤ fbound3S K l m₁ m₂ μ q

/-- g = gcd(b, μ). -/
def modulusContent (b μ : ℤ) : ℤ := Int.gcd b μ

/-- b₀ = |b| / g > 0. -/
def normalizedSlope (b μ : ℤ) : ℤ := |b| / modulusContent b μ

/-- μ₀ = sign(b)·μ / g. -/
def normalizedOffset (b μ : ℤ) : ℤ := (Int.sign b * μ) / modulusContent b μ

/-- d₀(c) = b₀ c + μ₀. -/
def normalizedLinearModulus (b μ c : ℤ) : ℤ := normalizedSlope b μ * c + normalizedOffset b μ

/-- R(x, y) = W(x,y) + (b m − μ B)·(x,y) + A μ² − b l μ + b² q (c-free). -/
def movingRemainderPoly (A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q : ℤ) (x y : ℤ) : ℤ :=
  C₁₁ * x ^ 2 + C₁₂ * x * y + C₂₂ * y ^ 2 + (b * m₁ - μ * B₁) * x + (b * m₂ - μ * B₂) * y
    + (A * μ ^ 2 - b * l * μ + b ^ 2 * q)

/-- A vector of ℤ³ is primitive when the gcd of its entries is 1. -/
def IsPrimitiveVector (v : Fin 3 → ℤ) : Prop := Finset.univ.gcd v = 1

/-- The integral radical (kernel) of an integer 3×3 matrix. -/
def IntegralRadical (G : Matrix (Fin 3) (Fin 3) ℤ) : Set (Fin 3 → ℤ) := {v | G *ᵥ v = 0}

/-- Singular block form: the Gram matrix vanishes on the last row and column (radical variable last). -/
def SingularBlockForm3 (C : Matrix (Fin 3) (Fin 3) ℤ) : Prop :=
  ∀ i, witnessGram C i 2 = 0 ∧ witnessGram C 2 i = 0

end DiophCompression.SemanticQuadraticSingular
