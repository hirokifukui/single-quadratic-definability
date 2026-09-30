/-
  frozen_statements/FiniteFiberGrowth_STATEMENTS.lean — Gate 6 statement freeze (session 23, 2026-08-31).
  GPT r20 必須A (finite-fiber growth, scalar + vector) and 必須B (definable functions: quadratic growth,
  injective dimension bound n ≤ 2m). Bodies are `sorry`; this file is the frozen contract for
  DiophCompression/FiniteFiberGrowth.lean. Height is the box form: for every N ≥ 1 and every input with
  |a_i| ≤ N, every element of a FINITE fiber has |c| ≤ C·N²; the (1+|a|_∞)² form is a corollary.
-/
import DiophCompression.OneSorted

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Definitions -/

/-- The fiber of `P` over the input `a` (output = last coordinate): outputs `c` with an integer witness. -/
def fiberZZ {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) : Set ℤ :=
  {c | ∃ u : Fin r → ℤ, evalAtZZ P (Fin.snoc a c) u = 0}

/-- The fiber of `P` over the first `n` coordinates: output vectors `b ∈ ℤᵐ` with an integer witness. -/
def fiberVecZZ {n m r : ℕ} (P : Poly (n + m) r) (a : Fin n → ℤ) : Set (Fin m → ℤ) :=
  {b | ∃ u : Fin r → ℤ, evalAtZZ P (Fin.append a b) u = 0}

/-- `P` has finite fibers over every input (GPT: FiniteFiberRelationZZ). -/
def FiniteFiberRelationZZ {n m r : ℕ} (P : Poly (n + m) r) : Prop :=
  ∀ a : Fin n → ℤ, (fiberVecZZ P a).Finite

/-- Scalar height bound: on every box `|a_i| ≤ N` (N ≥ 1), every element of a finite fiber has |c| ≤ C·N². -/
def FiberHeightBoundZZ {n r : ℕ} (P : Poly (n + 1) r) (C : ℕ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
    (fiberZZ P a).Finite → ∀ c ∈ fiberZZ P a, |c| ≤ (C : ℤ) * (N : ℤ) ^ 2

/-- Vector height bound: same, coordinatewise on `ℤᵐ`. -/
def FiberHeightBoundVecZZ {n m r : ℕ} (P : Poly (n + m) r) (C : ℕ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
    (fiberVecZZ P a).Finite → ∀ b ∈ fiberVecZZ P a, ∀ j, |b j| ≤ (C : ℤ) * (N : ℤ) ^ 2

/-- Graph of a total function `ℤⁿ → ℤᵐ` as a relation on `ℤⁿ⁺ᵐ` (inputs first). -/
def graphVecZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Set (Fin (n + m) → ℤ) :=
  {v | (fun j => v (Fin.natAdd n j)) = f (fun i => v (Fin.castAdd m i))}

/-- `f : ℤⁿ → ℤᵐ` is defined by a single equation of total degree ≤ 2 with integer witnesses. -/
def SingleQuadraticDefinableFunctionZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop :=
  ∃ r, ∃ P : Poly (n + m) r, P.totalDegree ≤ 2 ∧ RepresentsZZ P (graphVecZZ f)

/-! ### 必須A — finite-fiber growth -/

/-- Scalar finite-fiber growth theorem (Theorem D applied to `c` and `−c`; finiteness only refutes the
    infinite branch of the dichotomy). -/
theorem singleQuadratic_finiteFiber_height_scalar {n r : ℕ} (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) : ∃ C : ℕ, FiberHeightBoundZZ P C := by
  sorry

/-- The same in GPT's shape: |c| ≤ C·(1 + |a|_∞)², with |a|_∞ = sup_i |a_i| (= 0 for n = 0). -/
theorem singleQuadratic_finiteFiber_height_scalar_sup {n r : ℕ} (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) :
    ∃ C : ℕ, ∀ a : Fin n → ℤ, (fiberZZ P a).Finite → ∀ c ∈ fiberZZ P a,
      |c| ≤ (C : ℤ) * ((1 + Finset.univ.sup (fun i => (a i).natAbs) : ℕ) : ℤ) ^ 2 := by
  sorry

/-- Vector finite-fiber growth theorem: each output coordinate is a scalar fiber of a renamed `P`. -/
theorem singleQuadratic_finiteFiber_height_vector {n m r : ℕ} (P : Poly (n + m) r)
    (hP : P.totalDegree ≤ 2) : ∃ C : ℕ, FiberHeightBoundVecZZ P C := by
  sorry

/-! ### 必須B — definable functions -/

/-- Every single-quadratic-definable total function `ℤⁿ → ℤᵐ` has quadratic growth on boxes. -/
theorem singleQuadratic_function_quadratic_growth {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ))
    (hf : SingleQuadraticDefinableFunctionZZ f) :
    ∃ C : ℕ, ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
      ∀ j, |f a j| ≤ (C : ℤ) * (N : ℤ) ^ 2 := by
  sorry

/-- Injective dimension inequality: a single-quadratic-definable injection `ℤⁿ ↪ ℤᵐ` forces `n ≤ 2m`. -/
theorem singleQuadratic_injective_dimension_bound {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ))
    (hf : SingleQuadraticDefinableFunctionZZ f) (hinj : Function.Injective f) : n ≤ 2 * m := by
  sorry

/-- The one-sorted theorem of Gate 3 (`AtomGraphZZ 2 n → n ≤ 2`) is the case `m = 1` of the dimension bound. -/
theorem atomGraphZZ_le_two_from_dimension_bound : ∀ n, AtomGraphZZ 2 n → n ≤ 2 := by
  sorry

end DiophCompression
