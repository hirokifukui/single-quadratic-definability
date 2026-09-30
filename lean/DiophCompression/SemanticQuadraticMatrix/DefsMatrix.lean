/-
  DiophCompression/SemanticQuadraticMatrix/DefsMatrix.lean — r09 必須D (GPT r08 §6): definitions for the
  arbitrary-r matrix form of the fiber polynomial (definitions only, no theorems). Witness block = integer matrix
  C with W(u) = uᵀCu; Gram matrix G = C + Cᵀ (symmetric, even diagonal); N = det G (signed); only adj G is used.
  Statements frozen first in the frozen statement file `MatrixForm_STATEMENTS.lean` (md5 74995c63).
  Session 9, 2026-08-27, claude.ai direct.
-/
import Mathlib
import DiophCompression.StructuredFamilyCore

namespace DiophCompression.SemanticQuadraticMatrix

open Matrix

variable {r : ℕ}

/-- The witness quadratic form of an integer coefficient matrix C: W(u) = uᵀ C u. -/
def witnessQuad (C : Matrix (Fin r) (Fin r) ℤ) (u : Fin r → ℤ) : ℤ := u ⬝ᵥ (C *ᵥ u)

/-- The Gram matrix G = C + Cᵀ (symmetric, even diagonal; uᵀ G u = 2 W(u)). -/
def witnessGram (C : Matrix (Fin r) (Fin r) ℤ) : Matrix (Fin r) (Fin r) ℤ := C + Cᵀ

/-- The fiber polynomial with r witnesses: F(c,u) = A c² + c (B·u) + W(u) + ℓ c + m·u + q. -/
def fqM (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ) (m : Fin r → ℤ) (q : ℤ)
    (c : ℤ) (u : Fin r → ℤ) : ℤ :=
  A * c ^ 2 + c * (B ⬝ᵥ u) + witnessQuad C u + l * c + m ⬝ᵥ u + q

/-- Naturals c that have integer witnesses u. -/
def fiberSetM (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ) (m : Fin r → ℤ) (q : ℤ) :
    Set ℕ :=
  {c | ∃ u : Fin r → ℤ, fqM A B C l m q (c : ℤ) u = 0}

/-- The completed vector Y = G u + c B + m. -/
def completedVector (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (m : Fin r → ℤ) (c : ℤ)
    (u : Fin r → ℤ) : Fin r → ℤ :=
  witnessGram C *ᵥ u + c • B + m

/-- The adjugate form W̃(Y) = Yᵀ (adj G) Y. -/
def adjugateQuad (G : Matrix (Fin r) (Fin r) ℤ) (Y : Fin r → ℤ) : ℤ := Y ⬝ᵥ (adjugate G *ᵥ Y)

/-- α = 2 N A − Bᵀ (adj G) B (the Schur complement of the witness block in H, scaled by 2N). -/
def alphaMatrix (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) : ℤ :=
  2 * (witnessGram C).det * A - B ⬝ᵥ (adjugate (witnessGram C) *ᵥ B)

/-- β = 2 N ℓ − 2 Bᵀ (adj G) m. -/
def betaMatrix (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ) (m : Fin r → ℤ) : ℤ :=
  2 * (witnessGram C).det * l - 2 * (B ⬝ᵥ (adjugate (witnessGram C) *ᵥ m))

/-- γ = 2 N q − mᵀ (adj G) m. -/
def gammaMatrix (C : Matrix (Fin r) (Fin r) ℤ) (m : Fin r → ℤ) (q : ℤ) : ℤ :=
  2 * (witnessGram C).det * q - m ⬝ᵥ (adjugate (witnessGram C) *ᵥ m)

/-- The scaled line through (c₀, u₀) in direction w: u(t, s) = u₀ + s·(adj G)w − t·(adj G)B. -/
def scaledLineU (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (u₀ w : Fin r → ℤ) (t s : ℤ) :
    Fin r → ℤ :=
  u₀ + s • (adjugate (witnessGram C) *ᵥ w) - t • (adjugate (witnessGram C) *ᵥ B)


/-- s28 必須F step 3: the matrix-level dichotomy in data-carrying form. Placed here, beside the sealed
    `fiberSetM`, because the singular assembly imports downward. -/
def DichotomyMData (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) : Prop :=
  ∃ K : ℕ, ∀ (l : ℤ) (m : Fin r → ℤ) (q : ℤ),
    Nonempty (DiophCompression.StructuredFamily (fiberSetM A B C l m q)) ∨
      ∀ c ∈ fiberSetM A B C l m q, (c : ℤ) ≤ (K : ℤ) * ((1 + |l| + ∑ i, |m i|) ^ 2 + |q|)

end DiophCompression.SemanticQuadraticMatrix
