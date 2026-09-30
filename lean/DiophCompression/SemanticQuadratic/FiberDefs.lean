/-
  DiophCompression/SemanticQuadratic/FiberDefs.lean — definitions for the cell (n,1,2) destroyer (session 6, 2026-08-27).
  Definitions only (no theorems): the fiber quadratic `fq`, the fiber set of naturals c that have an integer
  root u, the fiber discriminant, the bound shape and the `Dichotomy` predicate. The frozen theorem statements
  live in frozen statement file `FiberDichotomy_STATEMENTS.lean` (md5 04977cc1); proofs are filled in separate files.
-/
import DiophCompression.CapacityFunctions
import DiophCompression.SemanticQuadratic.NormalForm

namespace DiophCompression.SemanticQuadratic

open MPUP

/-- The fiber quadratic: value at (c, u). -/
def fq (A B C l m q : ℤ) (c u : ℤ) : ℤ := A * c ^ 2 + B * c * u + C * u ^ 2 + l * c + m * u + q
/-- Naturals c that have an integer root u. -/
def fiberSet (A B C l m q : ℤ) : Set ℕ := {c | ∃ u : ℤ, fq A B C l m q (c : ℤ) u = 0}
/-- Fiber discriminant. -/
def disc (A B C : ℤ) : ℤ := B ^ 2 - 4 * A * C
/-- The bound shape: K·((1+|l|+|m|)² + |q|). -/
def fbound (K : ℕ) (l m q : ℤ) : ℤ := (K : ℤ) * ((1 + |l| + |m|) ^ 2 + |q|)
/-- Dichotomy for a fixed fiber form (A, B, C): the fiber set is infinite or bounded by `fbound K`. -/
def Dichotomy (A B C : ℤ) : Prop :=
  ∃ K : ℕ, ∀ l m q : ℤ, (fiberSet A B C l m q).Infinite ∨
    ∀ c ∈ fiberSet A B C l m q, (c : ℤ) ≤ fbound K l m q

end DiophCompression.SemanticQuadratic
