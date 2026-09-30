/-
  frozen_statements/APALStructuralTheoryCore_STATEMENTS.lean — APAL Structural Theory Gate 2, 必須D
  (frozen s25, 2026-09-01). The bundled APAL main root; individual roots are frozen in their own files.
-/
import DiophCompression.UnaryDiagonal
import DiophCompression.ArityZeroFragments
import DiophCompression.FunctionPhaseByArity
import DiophCompression.QuadraticCodes
import DiophCompression.DPRMTransport
import DiophCompression.GlobalQuadraticCode
import DiophCompression.ComputableFunctions
import DiophCompression.FiniteFiberCardinality
import DiophCompression.MultivariatePolynomialGraphs
import DiophCompression.PolynomialGraphs

namespace DiophCompression

open MvPolynomial MPUP

theorem apal_structural_theory_core (hU : UniformQuadraticSolvabilityDecidableZZ) (hD : DPRM_ZZ) :
    (∀ {n m r : ℕ} (P : Poly (n + m) r), P.totalDegree ≤ 2 →
      ∃ C : ℕ, FiberHeightBoundVecZZ P C ∧ FiberCardBoundVecZZ P C) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)), SingleQuadraticDefinableFunctionZZ f →
      ∃ C : ℕ, ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
        ∀ j, |f a j| ≤ (C : ℤ) * (N : ℤ) ^ 2) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)), SingleQuadraticDefinableFunctionZZ f →
      Function.Injective f → n ≤ 2 * m) ∧
    (∀ {n : ℕ} (p : MvPolynomial (Fin n) ℤ),
      WithinSingleEquationZZ 2 (polyGraphZZ p) ↔ p.totalDegree ≤ 2) ∧
    (∀ {k : ℕ}, 0 < k →
      SingleEqFragmentZZ 2 k ⊂ RecFragmentZZ k ∧ RecFragmentZZ k ⊂ REFragmentZZ k ∧
        REFragmentZZ k = PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k) ∧
    ((∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
        TotalComputableFunctionZZ f ↔ PPQuadraticDefinableFunctionZZ f) ∧
      (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
        PPQuadraticDefinableFunctionZZ f ↔ SingleQuarticDefinableFunctionZZ f) ∧
      (∃ f : (Fin 1 → ℤ) → (Fin 1 → ℤ), TotalComputableFunctionZZ f ∧ ¬ SingleQuadraticDefinableFunctionZZ f) ∧
      (∀ {n m l : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) (g : (Fin m → ℤ) → (Fin l → ℤ)),
        PPQuadraticDefinableFunctionZZ f → PPQuadraticDefinableFunctionZZ g →
          PPQuadraticDefinableFunctionZZ (g ∘ f))) ∧
    ¬ ∀ f g : ℤ → ℤ, UnarySE2ZZ f → UnarySE2ZZ g → UnarySE2ZZ (g ∘ f) := by
  sorry


/-! ### Gate 3 必須C — the core split by dependency layer (the bundled theorem above is kept as the
    artifact INDEX theorem only; these four are the paper roots). -/

/-- UNCONDITIONAL layer (no external hypothesis): finite-fibre height + cardinality; quadratic growth of
    SE_2 functions; n ≤ 2m for SE_2 injections; graph(p) ∈ SE_2 ↔ deg p ≤ 2; REC ⊊ RE (positive arity);
    PP_2 = SE_4 (every arity); the arity-0 collapse; Fun(PP_2) ⊆ TotComp; Fun(PP_2) = Fun(SE_4); Fun(PP_2)
    composition-closed; Fun_{n,m}(SE_2) ⊊ TotComp_{n,m} for n, m ≥ 1; Fun(SE_2) not composition-closed. -/
theorem apal_structural_core_unconditional :
    (∀ {n m r : ℕ} (P : Poly (n + m) r), P.totalDegree ≤ 2 →
      ∃ C : ℕ, FiberHeightBoundVecZZ P C ∧ FiberCardBoundVecZZ P C) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)), SingleQuadraticDefinableFunctionZZ f →
      ∃ C : ℕ, ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
        ∀ j, |f a j| ≤ (C : ℤ) * (N : ℤ) ^ 2) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)), SingleQuadraticDefinableFunctionZZ f →
      Function.Injective f → n ≤ 2 * m) ∧
    (∀ {n : ℕ} (p : MvPolynomial (Fin n) ℤ),
      WithinSingleEquationZZ 2 (polyGraphZZ p) ↔ p.totalDegree ≤ 2) ∧
    (∀ k : ℕ, RecFragmentZZ (k + 1) ⊂ REFragmentZZ (k + 1)) ∧
    (∀ k : ℕ, PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k) ∧
    (SingleEqFragmentZZ 2 0 = RecFragmentZZ 0 ∧ RecFragmentZZ 0 = REFragmentZZ 0 ∧
      REFragmentZZ 0 = PPFragmentZZ 2 0 ∧ PPFragmentZZ 2 0 = SingleEqFragmentZZ 4 0) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
      PPQuadraticDefinableFunctionZZ f → TotalComputableFunctionZZ f) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
      PPQuadraticDefinableFunctionZZ f ↔ SingleQuarticDefinableFunctionZZ f) ∧
    (∀ {n m l : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) (g : (Fin m → ℤ) → (Fin l → ℤ)),
      PPQuadraticDefinableFunctionZZ f → PPQuadraticDefinableFunctionZZ g →
        PPQuadraticDefinableFunctionZZ (g ∘ f)) ∧
    (∀ {n m : ℕ}, 0 < n → 0 < m →
      ∃ f : (Fin n → ℤ) → (Fin m → ℤ), TotalComputableFunctionZZ f ∧ ¬ SingleQuadraticDefinableFunctionZZ f) ∧
    ¬ ∀ f g : ℤ → ℤ, UnarySE2ZZ f → UnarySE2ZZ g → UnarySE2ZZ (g ∘ f) := by
  sorry

/-- CODE-UNIFORM Grunewald–Segal layer: SE_2(k) ⊊ REC(k) at every positive arity. -/
theorem apal_structural_core_of_uniformGS (hU : UniformQuadraticSolvabilityDecidableZZ) :
    ∀ {k : ℕ}, 0 < k → SingleEqFragmentZZ 2 k ⊂ RecFragmentZZ k := by
  sorry

/-- PER-EQUATION Grunewald–Segal layer: SE_2(k) ⊊ REC(k) at every arity k ≥ 2 (x³ witness; no
    diagonalization, no DPRM). -/
theorem apal_structural_core_of_perEquationGS (hGS : QuadraticSolvabilityDecidableZZ) :
    ∀ {k : ℕ}, 2 ≤ k → SingleEqFragmentZZ 2 k ⊂ RecFragmentZZ k := by
  sorry

/-- DPRM layer: RE = PP_2 = SE_4 at every arity, and TotComp = Fun(PP_2) = Fun(SE_4) at every arity. -/
theorem apal_structural_core_of_DPRM (hD : DPRM_ZZ) :
    (∀ k : ℕ, REFragmentZZ k = PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
      (TotalComputableFunctionZZ f ↔ PPQuadraticDefinableFunctionZZ f) ∧
      (TotalComputableFunctionZZ f ↔ SingleQuarticDefinableFunctionZZ f)) := by
  sorry

/-- The full phase diagram (bundled corollary of the three layers): relations at every positive arity,
    SE_2 ⊊ REC ⊊ RE = PP_2 = SE_4; functions exact at every arity. -/
theorem apal_full_phase_diagram (hU : UniformQuadraticSolvabilityDecidableZZ) (hD : DPRM_ZZ) :
    (∀ {k : ℕ}, 0 < k →
      SingleEqFragmentZZ 2 k ⊂ RecFragmentZZ k ∧ RecFragmentZZ k ⊂ REFragmentZZ k ∧
        REFragmentZZ k = PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k) ∧
    (∀ {n m : ℕ}, 0 < n → 0 < m →
      ∃ f : (Fin n → ℤ) → (Fin m → ℤ), TotalComputableFunctionZZ f ∧ ¬ SingleQuadraticDefinableFunctionZZ f) ∧
    (∀ {m : ℕ} (f : (Fin 0 → ℤ) → (Fin m → ℤ)), SingleQuadraticDefinableFunctionZZ f ∧ TotalComputableFunctionZZ f) ∧
    (∀ {n : ℕ} (f : (Fin n → ℤ) → (Fin 0 → ℤ)), SingleQuadraticDefinableFunctionZZ f ∧ TotalComputableFunctionZZ f) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
      (SingleQuadraticDefinableFunctionZZ f → TotalComputableFunctionZZ f) ∧
      (TotalComputableFunctionZZ f ↔ PPQuadraticDefinableFunctionZZ f) ∧
      (PPQuadraticDefinableFunctionZZ f ↔ SingleQuarticDefinableFunctionZZ f)) := by
  sorry


/-! ### Gate 3 必須B — the DPRM layer rebased on the CLASSICAL hypothesis over ℕ -/

/-- DPRM layer from the classical DPRM theorem over ℕ (via DPRM_ZZ_of_DPRM_NN). -/
theorem apal_structural_core_of_DPRM_NN (hN : DPRM_NN) :
    (∀ k : ℕ, REFragmentZZ k = PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
      (TotalComputableFunctionZZ f ↔ PPQuadraticDefinableFunctionZZ f) ∧
      (TotalComputableFunctionZZ f ↔ SingleQuarticDefinableFunctionZZ f)) := by
  sorry

/-- The full phase diagram from the code-uniform Grunewald–Segal hypothesis on STANDARD codes and the
    classical DPRM theorem over ℕ — the two external inputs in their literature forms. -/
theorem apal_full_phase_diagram_classical (hC : UniformQuadraticSolvabilityOnCodes) (hN : DPRM_NN) :
    (∀ {k : ℕ}, 0 < k →
      SingleEqFragmentZZ 2 k ⊂ RecFragmentZZ k ∧ RecFragmentZZ k ⊂ REFragmentZZ k ∧
        REFragmentZZ k = PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k) ∧
    (∀ {n m : ℕ}, 0 < n → 0 < m →
      ∃ f : (Fin n → ℤ) → (Fin m → ℤ), TotalComputableFunctionZZ f ∧ ¬ SingleQuadraticDefinableFunctionZZ f) ∧
    (∀ {m : ℕ} (f : (Fin 0 → ℤ) → (Fin m → ℤ)), SingleQuadraticDefinableFunctionZZ f ∧ TotalComputableFunctionZZ f) ∧
    (∀ {n : ℕ} (f : (Fin n → ℤ) → (Fin 0 → ℤ)), SingleQuadraticDefinableFunctionZZ f ∧ TotalComputableFunctionZZ f) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
      (SingleQuadraticDefinableFunctionZZ f → TotalComputableFunctionZZ f) ∧
      (TotalComputableFunctionZZ f ↔ PPQuadraticDefinableFunctionZZ f) ∧
      (PPQuadraticDefinableFunctionZZ f ↔ SingleQuarticDefinableFunctionZZ f)) := by
  sorry

theorem apal_full_phase_diagram_literature (hG : GlobalQuadraticSolvabilityDecidable) (hN : DPRM_NN) :
    (∀ {k : ℕ}, 0 < k →
      SingleEqFragmentZZ 2 k ⊂ RecFragmentZZ k ∧ RecFragmentZZ k ⊂ REFragmentZZ k ∧
        REFragmentZZ k = PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k) ∧
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
