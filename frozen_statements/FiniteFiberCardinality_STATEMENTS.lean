/-
  frozen_statements/FiniteFiberCardinality_STATEMENTS.lean — Gate 9 statement freeze (session 24, 2026-08-31).
  GPT r21 必須B: cardinality bounds for finite fibers of single-quadratic relations (scalar and vector),
  the bundled definition `SingleQuadraticFiniteValuedRelationZZ`, and the graph/function special cases.
  Bodies are `sorry`; this file is the frozen contract for DiophCompression/FiniteFiberCardinality.lean.
  Box form: for N ≥ 1 and |a_i| ≤ N, a FINITE fiber has at most 2·C·N²+1 elements (scalar), (2·C·N²+1)^m (vector),
  with the SAME constant C as the height bound. The (1+|a|_∞)² forms are corollaries.
-/
import DiophCompression.FiniteFiberGrowth

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Definitions -/

/-- Scalar cardinality bound on boxes: a finite fiber over |a_i| ≤ N has at most 2·C·N²+1 elements. -/
def FiberCardBoundZZ {n r : ℕ} (P : Poly (n + 1) r) (C : ℕ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
    (fiberZZ P a).Finite → (fiberZZ P a).ncard ≤ 2 * C * N ^ 2 + 1

/-- Vector cardinality bound on boxes: a finite fiber over |a_i| ≤ N has at most (2·C·N²+1)^m elements. -/
def FiberCardBoundVecZZ {n m r : ℕ} (P : Poly (n + m) r) (C : ℕ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
    (fiberVecZZ P a).Finite → (fiberVecZZ P a).ncard ≤ (2 * C * N ^ 2 + 1) ^ m

/-- A single-quadratic finite-valued relation: `P` has total degree ≤ 2 and every input fiber is finite. -/
def SingleQuadraticFiniteValuedRelationZZ {n m r : ℕ} (P : Poly (n + m) r) : Prop :=
  P.totalDegree ≤ 2 ∧ FiniteFiberRelationZZ P

/-! ### Theorems -/

/-- Any set of integers bounded by `B` in absolute value has at most `2B+1` elements. -/
theorem ncard_le_of_abs_le (S : Set ℤ) (B : ℕ) (hS : ∀ c ∈ S, |c| ≤ (B : ℤ)) :
    S.ncard ≤ 2 * B + 1 := by
  sorry

/-- Any set of integer vectors bounded coordinatewise by `B` has at most `(2B+1)^m` elements. -/
theorem ncard_le_of_abs_le_vec {m : ℕ} (S : Set (Fin m → ℤ)) (B : ℕ)
    (hS : ∀ b ∈ S, ∀ j, |b j| ≤ (B : ℤ)) : S.ncard ≤ (2 * B + 1) ^ m := by
  sorry

/-- Height bound ⇒ cardinality bound (scalar), same constant. -/
theorem fiberCardBound_of_fiberHeightBound {n r : ℕ} (P : Poly (n + 1) r) (C : ℕ)
    (h : FiberHeightBoundZZ P C) : FiberCardBoundZZ P C := by
  sorry

/-- Height bound ⇒ cardinality bound (vector), same constant. -/
theorem fiberCardBoundVec_of_fiberHeightBoundVec {n m r : ℕ} (P : Poly (n + m) r) (C : ℕ)
    (h : FiberHeightBoundVecZZ P C) : FiberCardBoundVecZZ P C := by
  sorry

/-- 必須B (scalar): a single quadratic has finite fibers of size ≤ 2·C·N²+1 on the box |a_i| ≤ N. -/
theorem singleQuadratic_finiteFiber_cardinality_scalar {n r : ℕ} (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) : ∃ C : ℕ, FiberHeightBoundZZ P C ∧ FiberCardBoundZZ P C := by
  sorry

/-- 必須B (vector): finite fibers of size ≤ (2·C·N²+1)^m on the box, same C as the height bound. -/
theorem singleQuadratic_finiteFiber_cardinality_vector {n m r : ℕ} (P : Poly (n + m) r)
    (hP : P.totalDegree ≤ 2) : ∃ C : ℕ, FiberHeightBoundVecZZ P C ∧ FiberCardBoundVecZZ P C := by
  sorry

/-- Sup-norm form (scalar): |R_P(a)| ≤ 2·C·(1+|a|_∞)²+1 for every finite fiber. -/
theorem singleQuadratic_finiteFiber_cardinality_scalar_sup {n r : ℕ} (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) :
    ∃ C : ℕ, ∀ a : Fin n → ℤ, (fiberZZ P a).Finite →
      (fiberZZ P a).ncard ≤ 2 * C * (1 + Finset.univ.sup (fun i => (a i).natAbs)) ^ 2 + 1 := by
  sorry

/-- Sup-norm form (vector): |R_P(a)| ≤ (2·C·(1+|a|_∞)²+1)^m for every finite fiber. -/
theorem singleQuadratic_finiteFiber_cardinality_vector_sup {n m r : ℕ} (P : Poly (n + m) r)
    (hP : P.totalDegree ≤ 2) :
    ∃ C : ℕ, ∀ a : Fin n → ℤ, (fiberVecZZ P a).Finite →
      (fiberVecZZ P a).ncard ≤ (2 * C * (1 + Finset.univ.sup (fun i => (a i).natAbs)) ^ 2 + 1) ^ m := by
  sorry

/-- Bundle: a single-quadratic finite-valued relation has, for one constant C, the height bound and the
    cardinality bound at every input (the finiteness hypothesis of the box forms is discharged globally). -/
theorem singleQuadraticFiniteValuedRelation_bounds {n m r : ℕ} (P : Poly (n + m) r)
    (hR : SingleQuadraticFiniteValuedRelationZZ P) :
    ∃ C : ℕ, ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
      (∀ b ∈ fiberVecZZ P a, ∀ j, |b j| ≤ (C : ℤ) * (N : ℤ) ^ 2) ∧
      (fiberVecZZ P a).ncard ≤ (2 * C * N ^ 2 + 1) ^ m := by
  sorry

/-- Graph special case: the fiber of a representing polynomial of a definable function is the singleton {f a}. -/
theorem fiberVecZZ_eq_singleton_of_represents {n m r : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ))
    (P : Poly (n + m) r) (hrep : RepresentsZZ P (graphVecZZ f)) (a : Fin n → ℤ) :
    fiberVecZZ P a = {f a} := by
  sorry

/-- Function special case: the graph relation of a single-quadratic-definable function is a
    single-quadratic finite-valued relation (fibers are singletons). -/
theorem singleQuadraticDefinableFunction_finiteValued {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ))
    (hf : SingleQuadraticDefinableFunctionZZ f) :
    ∃ r, ∃ P : Poly (n + m) r, RepresentsZZ P (graphVecZZ f) ∧ SingleQuadraticFiniteValuedRelationZZ P := by
  sorry

end DiophCompression
