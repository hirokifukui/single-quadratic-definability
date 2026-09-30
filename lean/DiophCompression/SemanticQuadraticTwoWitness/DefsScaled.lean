/-
  DiophCompression/SemanticQuadraticTwoWitness/DefsScaled.lean — definitions for the s8 re-freeze
  (GPT r07 必須2/3: orientation, adjugate form, scaled line). Definitions only, no theorems.
  Mathematics: SemanticQuadraticGeneral/CLASSIFICATION_2W.md §3 (revised s8).
-/
import DiophCompression.SemanticQuadraticTwoWitness.Defs2W

namespace DiophCompression.SemanticQuadraticTwoWitness

/-- N = det G = 4C₁₁C₂₂ − C₁₂² = −discW. -/
def nW (C₁₁ C₁₂ C₂₂ : ℤ) : ℤ := 4 * C₁₁ * C₂₂ - C₁₂ ^ 2

/-- Oriented Schur complement: sign(C₁₁) · schur (positive-definite orientation of the witness block). -/
def orientedSchur (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) : ℤ := Int.sign C₁₁ * schur A B₁ B₂ C₁₁ C₁₂ C₂₂

/-- The adjugate form W̃(Y) = Yᵀ(adj G)Y = 2C₂₂Y₁² − 2C₁₂Y₁Y₂ + 2C₁₁Y₂². -/
def wt (C₁₁ C₁₂ C₂₂ Y₁ Y₂ : ℤ) : ℤ := 2 * C₂₂ * Y₁ ^ 2 - 2 * C₁₂ * Y₁ * Y₂ + 2 * C₁₁ * Y₂ ^ 2

/-- Its bilinear form: wt (Y + w) = wt Y + 2·wtBil Y w + wt w. -/
def wtBil (C₁₁ C₁₂ C₂₂ Y₁ Y₂ w₁ w₂ : ℤ) : ℤ :=
  2 * C₂₂ * Y₁ * w₁ - C₁₂ * (Y₁ * w₂ + Y₂ * w₁) + 2 * C₁₁ * Y₂ * w₂

/-- Y₁ = 2C₁₁u + C₁₂v + B₁c + m₁. -/
def y1 (B₁ C₁₁ C₁₂ m₁ c u v : ℤ) : ℤ := 2 * C₁₁ * u + C₁₂ * v + B₁ * c + m₁

/-- Y₂ = C₁₂u + 2C₂₂v + B₂c + m₂. -/
def y2 (B₂ C₁₂ C₂₂ m₂ c u v : ℤ) : ℤ := C₁₂ * u + 2 * C₂₂ * v + B₂ * c + m₂

/-- β = 2Nl − 2Bᵀ(adj G)m. -/
def betaR (B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ : ℤ) : ℤ :=
  2 * nW C₁₁ C₁₂ C₂₂ * l - 2 * (2 * C₂₂ * B₁ * m₁ - C₁₂ * (B₁ * m₂ + B₂ * m₁) + 2 * C₁₁ * B₂ * m₂)

/-- γ = 2Nq − mᵀ(adj G)m. -/
def gammaR (C₁₁ C₁₂ C₂₂ m₁ m₂ q : ℤ) : ℤ :=
  2 * nW C₁₁ C₁₂ C₂₂ * q - (2 * C₂₂ * m₁ ^ 2 - 2 * C₁₂ * m₁ * m₂ + 2 * C₁₁ * m₂ ^ 2)

/-- The rank-one coupled fiber polynomial Q(c,u) = Ac² + B₁cu + ku² + lc + m₁u + q. -/
def qOne (A B₁ k l m₁ q c u : ℤ) : ℤ := A * c ^ 2 + B₁ * c * u + k * u ^ 2 + l * c + m₁ * u + q

end DiophCompression.SemanticQuadraticTwoWitness
