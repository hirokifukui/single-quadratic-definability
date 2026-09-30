/-
  frozen_statements/FunctionPhaseByArityNN_STATEMENTS.lean — Theorem 7.1 under DPRM_NN directly (frozen s40, 2026-09-11; Gate-14 P09). Wrapper of function_phase_diagram_by_arity through DPRM_ZZ_of_DPRM_NN; no new mathematics.
-/
import DiophCompression.FunctionPhaseByArity
import DiophCompression.DPRMTransport

namespace DiophCompression

open MvPolynomial MPUP

/-- The function phase diagram, exact at every arity, under DPRM over ℕ (Theorem 7.1 as stated in the paper):
    strict for n, m ≥ 1; collapsed at n = 0 and at m = 0; TotComp = Fun(PP_2) = Fun(SE_4) at every arity.
    Direct wrapper of `function_phase_diagram_by_arity` through `DPRM_ZZ_of_DPRM_NN`. -/
theorem function_phase_diagram_by_arity_of_DPRM_NN (hN : DPRM_NN) :
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
