/-
  frozen_statements/FunctionPhaseByArity_STATEMENTS.lean — APAL Structural Theory Gate 3, 必須E
  (frozen s26, 2026-09-01). The function phase diagram Fun_{n,m}(SE_2) ⊊ TotComp_{n,m} made exact at every
  arity: strict for n, m ≥ 1 (witness (a₀³, 0, …, 0), UNCONDITIONAL), collapsed at n = 0 (every function
  ℤ^0 → ℤ^m is a computable constant vector, SE_2-definable by Σ_j (b_j − c_j)² = 0) and at m = 0 (unique
  empty output, graph = univ = {0 = 0}).
-/
import DiophCompression.ComputableFunctions

namespace DiophCompression

open MvPolynomial MPUP

/-- The strictness witness ℤ^{n+1} → ℤ^{m+1}: `a ↦ (a₀³, 0, …, 0)`. -/
def cubeFirstZZ (n m : ℕ) (a : Fin (n + 1) → ℤ) (j : Fin (m + 1)) : ℤ := if j = 0 then (a 0) ^ 3 else 0

/-- `cubeFirstZZ` is total computable. -/
theorem cubeFirstZZ_computable (n m : ℕ) : TotalComputableFunctionZZ (cubeFirstZZ n m) := by
  sorry

/-- `cubeFirstZZ` is not SE_2-definable (quadratic growth barrier on the first output). -/
theorem cubeFirstZZ_not_singleQuadratic (n m : ℕ) : ¬ SingleQuadraticDefinableFunctionZZ (cubeFirstZZ n m) := by
  sorry

/-- Unconditional, every n, m ≥ 1: Fun_{n,m}(SE_2) ⊊ TotComp_{n,m}. -/
theorem singleQuadratic_functions_strict_of_pos_arity {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (∀ f : (Fin n → ℤ) → (Fin m → ℤ), SingleQuadraticDefinableFunctionZZ f → TotalComputableFunctionZZ f) ∧
    ∃ f : (Fin n → ℤ) → (Fin m → ℤ), TotalComputableFunctionZZ f ∧ ¬ SingleQuadraticDefinableFunctionZZ f := by
  sorry

/-- Zero inputs: every function ℤ^0 → ℤ^m is both SE_2-definable and total computable, so
    Fun_{0,m}(SE_2) = TotComp_{0,m} (= all constant vectors). -/
theorem singleQuadratic_functions_eq_at_zero_input {m : ℕ} (f : (Fin 0 → ℤ) → (Fin m → ℤ)) :
    SingleQuadraticDefinableFunctionZZ f ∧ TotalComputableFunctionZZ f := by
  sorry

/-- Zero outputs: every function ℤ^n → ℤ^0 is both SE_2-definable and total computable, so
    Fun_{n,0}(SE_2) = TotComp_{n,0} (= the unique function). -/
theorem singleQuadratic_functions_eq_at_zero_output {n : ℕ} (f : (Fin n → ℤ) → (Fin 0 → ℤ)) :
    SingleQuadraticDefinableFunctionZZ f ∧ TotalComputableFunctionZZ f := by
  sorry

/-- The function phase diagram, exact at every arity (DPRM only for TotComp = Fun(PP_2)):
    strict for n, m ≥ 1; collapsed at n = 0 and at m = 0; TotComp = Fun(PP_2) = Fun(SE_4) at every arity. -/
theorem function_phase_diagram_by_arity (hD : DPRM_ZZ) :
    (∀ {n m : ℕ}, 0 < n → 0 < m →
      ∃ f : (Fin n → ℤ) → (Fin m → ℤ), TotalComputableFunctionZZ f ∧ ¬ SingleQuadraticDefinableFunctionZZ f) ∧
    (∀ {m : ℕ} (f : (Fin 0 → ℤ) → (Fin m → ℤ)), SingleQuadraticDefinableFunctionZZ f ∧ TotalComputableFunctionZZ f) ∧
    (∀ {n : ℕ} (f : (Fin n → ℤ) → (Fin 0 → ℤ)), SingleQuadraticDefinableFunctionZZ f ∧ TotalComputableFunctionZZ f) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
      (SingleQuadraticDefinableFunctionZZ f → TotalComputableFunctionZZ f) ∧
      (TotalComputableFunctionZZ f ↔ PPQuadraticDefinableFunctionZZ f) ∧
      (PPQuadraticDefinableFunctionZZ f ↔ SingleQuarticDefinableFunctionZZ f)) := by
  sorry

end DiophCompression
