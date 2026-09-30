/-
  frozen_statements/ComputableFunctions_STATEMENTS.lean — APAL Structural Theory Gate 2, 必須C (frozen s25, 2026-09-01).
  Total-function hierarchy Fun(SE_2) ⊊ TotComp = Fun(PP_2) = Fun(SE_4) (the equalities conditional on DPRM_ZZ,
  every inclusion Fun(PP_2) ⊆ TotComp unconditional), composition closure of Fun(PP_2), in mathlib vocabulary.
  Names follow the GPT Gate-1 review §9 必須C. Supersedes drafts/ComputableFunctions_STATEMENTS_draft.lean.
-/
import DiophCompression.ComputabilityFragments

namespace DiophCompression

open MvPolynomial MPUP

/-- TotComp: `f : ℤⁿ → ℤᵐ` is (total) computable. -/
def TotalComputableFunctionZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop := Computable f

/-- Fun(PP_2): the graph of `f` is defined by a quadratic pp-system with integer witnesses. -/
def PPQuadraticDefinableFunctionZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop :=
  WithinPPZZ 2 (graphVecZZ f)

/-- Fun(SE_4): the graph of `f` is defined by a single equation of total degree ≤ 4. -/
def SingleQuarticDefinableFunctionZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop :=
  WithinSingleEquationZZ 4 (graphVecZZ f)

/-! ### 必須C — total-function hierarchy -/

/-- Unconditional: a PP_2-definable total function is computable (search on the graph system). -/
theorem ppQuadratic_total_function_computable {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ))
    (h : PPQuadraticDefinableFunctionZZ f) : TotalComputableFunctionZZ f := by
  sorry

/-- Unconditional: an SE_2-definable total function is computable. -/
theorem singleQuadratic_total_function_computable {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ))
    (h : SingleQuadraticDefinableFunctionZZ f) : TotalComputableFunctionZZ f := by
  sorry

/-- Conditional on DPRM: every total computable function is PP_2-definable. -/
theorem computable_total_function_ppQuadratic_of_DPRM (hD : DPRM_ZZ) {n m : ℕ}
    (f : (Fin n → ℤ) → (Fin m → ℤ)) (h : TotalComputableFunctionZZ f) :
    PPQuadraticDefinableFunctionZZ f := by
  sorry

/-- Conditional on DPRM: Fun(PP_2) = TotComp. -/
theorem ppQuadratic_functions_eq_totalComputable_of_DPRM (hD : DPRM_ZZ) {n m : ℕ}
    (f : (Fin n → ℤ) → (Fin m → ℤ)) :
    PPQuadraticDefinableFunctionZZ f ↔ TotalComputableFunctionZZ f := by
  sorry

/-- Unconditional: Fun(PP_2) = Fun(SE_4) (Skolem degree reduction). -/
theorem ppQuadratic_functions_eq_singleQuartic {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) :
    PPQuadraticDefinableFunctionZZ f ↔ SingleQuarticDefinableFunctionZZ f := by
  sorry

/-- Unconditional: PP_2-definable functions are closed under composition (intermediate vector as
    fresh witnesses). -/
theorem ppQuadratic_functions_closed_under_composition {n m l : ℕ}
    (f : (Fin n → ℤ) → (Fin m → ℤ)) (g : (Fin m → ℤ) → (Fin l → ℤ))
    (hf : PPQuadraticDefinableFunctionZZ f) (hg : PPQuadraticDefinableFunctionZZ g) :
    PPQuadraticDefinableFunctionZZ (g ∘ f) := by
  sorry

/-- Unconditional: Fun(SE_2) ⊊ TotComp — `x ↦ x³` is computable and not SE_2-definable. -/
theorem singleQuadratic_functions_proper_subset_totalComputable :
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)), SingleQuadraticDefinableFunctionZZ f →
      TotalComputableFunctionZZ f) ∧
    ∃ f : (Fin 1 → ℤ) → (Fin 1 → ℤ), TotalComputableFunctionZZ f ∧ ¬ SingleQuadraticDefinableFunctionZZ f := by
  sorry

/-- The function phase diagram (DPRM): TotComp = Fun(PP_2) = Fun(SE_4), Fun(SE_2) ⊊ TotComp,
    and Fun(PP_2) is composition-closed. -/
theorem function_phase_diagram (hD : DPRM_ZZ) :
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
      TotalComputableFunctionZZ f ↔ PPQuadraticDefinableFunctionZZ f) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
      PPQuadraticDefinableFunctionZZ f ↔ SingleQuarticDefinableFunctionZZ f) ∧
    (∃ f : (Fin 1 → ℤ) → (Fin 1 → ℤ), TotalComputableFunctionZZ f ∧ ¬ SingleQuadraticDefinableFunctionZZ f) ∧
    (∀ {n m l : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) (g : (Fin m → ℤ) → (Fin l → ℤ)),
      PPQuadraticDefinableFunctionZZ f → PPQuadraticDefinableFunctionZZ g →
        PPQuadraticDefinableFunctionZZ (g ∘ f)) := by
  sorry

end DiophCompression
