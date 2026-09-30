/-
  DiophCompression/SemanticQuadraticGeneral/Defs.lean — definitions for the general-witness quadratic cell
  (GPT r06 §7 必須C / 必須F; session 7, 2026-08-27). Definitions only, no theorems.
  Fiber coordinates x : Fin (r+1) → ℤ with x 0 = c (the output) and x (succ j) = u j (the r integer witnesses).
  For a fixed constant-coefficient quadratic part H the fiber polynomial is H(x) + Σ ℓ_i x_i + q.
-/
import DiophCompression.CapacityFunctions

namespace DiophCompression.SemanticQuadraticGeneral

open MvPolynomial

/-- The fiber polynomial value at x: H(x) + ℓ·x + q. -/
noncomputable def fiberVal {r : ℕ} (H : MvPolynomial (Fin (r + 1)) ℤ) (ℓ : Fin (r + 1) → ℤ) (q : ℤ)
    (x : Fin (r + 1) → ℤ) : ℤ :=
  eval x H + ∑ i, ℓ i * x i + q

/-- Naturals c that have integer witnesses u with H(c,u) + ℓ·(c,u) + q = 0. -/
def fiberSetG {r : ℕ} (H : MvPolynomial (Fin (r + 1)) ℤ) (ℓ : Fin (r + 1) → ℤ) (q : ℤ) : Set ℕ :=
  {c | ∃ u : Fin r → ℤ, fiberVal H ℓ q (Fin.cons (c : ℤ) u) = 0}

/-- The bound shape K·((1 + Σ|ℓ_i|)² + |q|). -/
def fboundG {r : ℕ} (K : ℕ) (ℓ : Fin (r + 1) → ℤ) (q : ℤ) : ℤ :=
  (K : ℤ) * ((1 + ∑ i, |ℓ i|) ^ 2 + |q|)

/-- Projection dichotomy for a fixed quadratic part H: for every linear part the fiber set is infinite
    or bounded by `fboundG K`. -/
def DichotomyG {r : ℕ} (H : MvPolynomial (Fin (r + 1)) ℤ) : Prop :=
  ∃ K : ℕ, ∀ (ℓ : Fin (r + 1) → ℤ) (q : ℤ), (fiberSetG H ℓ q).Infinite ∨
    ∀ c ∈ fiberSetG H ℓ q, (c : ℤ) ≤ fboundG K ℓ q

/-- GPT r06 必須C: the projection dichotomy holds for every homogeneous quadratic part in r+1 variables. -/
def QuadraticProjectionDichotomyZ (r : ℕ) : Prop :=
  ∀ H : MvPolynomial (Fin (r + 1)) ℤ, H.IsHomogeneous 2 → DichotomyG H

/-- GPT r06 必須F: the Quadratic Witness Inertia Conjecture (definition only; never a bare axiom). -/
def QuadraticWitnessInertiaZ : Prop := ∀ r, graphCapacityZ r 2 = 2

end DiophCompression.SemanticQuadraticGeneral
