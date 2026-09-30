/-
  DiophCompression/APALStructuralTheoryCore.lean — APAL Structural Theory Gate 2, 必須D
  (session 25, 2026-09-01, claude.ai direct). The new APAL main root: the structural theory of the
  single-quadratic existential fragment SE_2 over ℤ. One bundled statement plus the individual roots.
  No new mathematics; no sorry; std-3 expected. Supersedes APALLogicCore.lean as the artifact centre
  (that file is kept unchanged as the r20 capacity/tuple-coding core).
  NOT exported (does not exist yet): quadraticFiber_bounded_or_certifiedInfinite (必須E, statement design).
  Gate 3 必須C (s26, 2026-09-01): the bundled apal_structural_theory_core is DEMOTED to the artifact index
  theorem; the paper roots are the four layered theorems below (unconditional / of_uniformGS /
  of_perEquationGS / of_DPRM) and the bundled corollary apal_full_phase_diagram.
-/
import DiophCompression.FiniteFiberCardinality
import DiophCompression.MultivariatePolynomialGraphs
import DiophCompression.PolynomialGraphs
import DiophCompression.ComputableFunctions
import DiophCompression.UnaryDiagonal
import DiophCompression.ArityZeroFragments
import DiophCompression.FunctionPhaseByArity
import DiophCompression.QuadraticCodes
import DiophCompression.DPRMTransport
import DiophCompression.GlobalQuadraticCode

namespace DiophCompression

open MvPolynomial MPUP

/-- The APAL structural theory of SE_2 over ℤ, bundled (uniform Grunewald–Segal + DPRM as hypotheses;
    only (5) and the first conjunct of (6) use them):
    (1) finite fibres of an SE_2 relation ℤⁿ → ℤᵐ lie in a quadratic-height box and have polynomial
        cardinality, with one constant C_P for both;
    (2) SE_2-definable total functions have quadratic growth on boxes;
    (3) SE_2-definable injections ℤⁿ → ℤᵐ satisfy n ≤ 2m;
    (4) the graph of an integer polynomial is SE_2 iff its total degree is ≤ 2 (every arity);
    (5) relation phase diagram at every positive arity: SE_2 ⊊ REC ⊊ RE = PP_2 = SE_4;
    (6) function phase diagram: TotComp = Fun(PP_2) = Fun(SE_4), Fun(SE_2) ⊊ TotComp, Fun(PP_2)
        composition-closed;
    (7) Fun(SE_2) is not composition-closed. -/
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
    ¬ ∀ f g : ℤ → ℤ, UnarySE2ZZ f → UnarySE2ZZ g → UnarySE2ZZ (g ∘ f) :=
  ⟨fun P hP => singleQuadratic_finiteFiber_cardinality_vector P hP,
   fun f hf => singleQuadratic_function_quadratic_growth f hf,
   fun f hf hinj => singleQuadratic_injective_dimension_bound f hf hinj,
   fun p => polynomial_graph_singleQuadratic_iff p,
   fun hk => relation_phase_diagram_all_positive_arity hU hD hk,
   function_phase_diagram hD,
   singleQuadratic_functions_not_closed_under_composition⟩


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
  refine ⟨fun P hP => singleQuadratic_finiteFiber_cardinality_vector P hP,
    fun f hf => singleQuadratic_function_quadratic_growth f hf,
    fun f hf hinj => singleQuadratic_injective_dimension_bound f hf hinj,
    fun p => polynomial_graph_singleQuadratic_iff p,
    fun k => recursive_strictly_contained_re k,
    fun k => (singleEqFragmentZZ_four_eq_ppFragmentZZ_two k).symm,
    relation_phase_diagram_arity_zero,
    fun f hf => ppQuadratic_total_function_computable f hf,
    fun f => ppQuadratic_functions_eq_singleQuartic f,
    fun f g hf hg => ppQuadratic_functions_closed_under_composition f g hf hg,
    fun hn hm => (singleQuadratic_functions_strict_of_pos_arity hn hm).2,
    singleQuadratic_functions_not_closed_under_composition⟩

/-- CODE-UNIFORM Grunewald–Segal layer: SE_2(k) ⊊ REC(k) at every positive arity. -/
theorem apal_structural_core_of_uniformGS (hU : UniformQuadraticSolvabilityDecidableZZ) :
    ∀ {k : ℕ}, 0 < k → SingleEqFragmentZZ 2 k ⊂ RecFragmentZZ k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact singleQuadratic_strict_recursive_all_positive_arity hU j

/-- PER-EQUATION Grunewald–Segal layer: SE_2(k) ⊊ REC(k) at every arity k ≥ 2 (x³ witness; no
    diagonalization, no DPRM). -/
theorem apal_structural_core_of_perEquationGS (hGS : QuadraticSolvabilityDecidableZZ) :
    ∀ {k : ℕ}, 2 ≤ k → SingleEqFragmentZZ 2 k ⊂ RecFragmentZZ k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [Set.ssubset_def]
  refine ⟨singleEqFragmentZZ_two_subset_recFragmentZZ hGS _, fun hsub => ?_⟩
  have hmem : powerGraphZZ j 3 ∈ RecFragmentZZ (j + 2) := powerGraphZZ_computablePred j 3
  exact cubic_graph_not_withinSingleEquationZZ j (hsub hmem)

/-- DPRM layer: RE = PP_2 = SE_4 at every arity, and TotComp = Fun(PP_2) = Fun(SE_4) at every arity. -/
theorem apal_structural_core_of_DPRM (hD : DPRM_ZZ) :
    (∀ k : ℕ, REFragmentZZ k = PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
      (TotalComputableFunctionZZ f ↔ PPQuadraticDefinableFunctionZZ f) ∧
      (TotalComputableFunctionZZ f ↔ SingleQuarticDefinableFunctionZZ f)) := by
  refine ⟨fun k => ⟨(ppQuadratic_eq_re_of_DPRM hD k).symm, (singleEqFragmentZZ_four_eq_ppFragmentZZ_two k).symm⟩,
    fun f => ⟨(ppQuadratic_functions_eq_totalComputable_of_DPRM hD f).symm, ?_⟩⟩
  exact (ppQuadratic_functions_eq_totalComputable_of_DPRM hD f).symm.trans (ppQuadratic_functions_eq_singleQuartic f)

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
  obtain ⟨h1, h2, h3, h4⟩ := function_phase_diagram_by_arity hD
  exact ⟨fun hk => relation_phase_diagram_all_positive_arity hU hD hk, h1, h2, h3, h4⟩


/-! ### Gate 3 必須B — the DPRM layer rebased on the CLASSICAL hypothesis over ℕ -/

/-- DPRM layer from the classical DPRM theorem over ℕ (via DPRM_ZZ_of_DPRM_NN). -/
theorem apal_structural_core_of_DPRM_NN (hN : DPRM_NN) :
    (∀ k : ℕ, REFragmentZZ k = PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k) ∧
    (∀ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)),
      (TotalComputableFunctionZZ f ↔ PPQuadraticDefinableFunctionZZ f) ∧
      (TotalComputableFunctionZZ f ↔ SingleQuarticDefinableFunctionZZ f)) := by
  exact apal_structural_core_of_DPRM (DPRM_ZZ_of_DPRM_NN hN)

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
  exact apal_full_phase_diagram (uniformGS_of_uniformOnCodes hC) (DPRM_ZZ_of_DPRM_NN hN)

/-- Gate 4 必須B: the full phase diagram from the GLOBAL (literature-form) Grunewald–Segal decider and the
    classical DPRM theorem over ℕ — one algorithm on the whole instance, one theorem on ℕ. -/
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
  exact apal_full_phase_diagram_classical (globalGS_implies_fixedArityGS hG) hN

end DiophCompression

#print axioms DiophCompression.apal_structural_theory_core
#print axioms DiophCompression.singleQuadratic_finiteFiber_height_vector
#print axioms DiophCompression.singleQuadratic_finiteFiber_cardinality_vector
#print axioms DiophCompression.singleQuadratic_function_quadratic_growth
#print axioms DiophCompression.singleQuadratic_injective_dimension_bound
#print axioms DiophCompression.polynomial_graph_singleQuadratic_iff
#print axioms DiophCompression.relation_phase_diagram_all_positive_arity
#print axioms DiophCompression.function_phase_diagram
#print axioms DiophCompression.singleQuadratic_functions_not_closed_under_composition
#print axioms DiophCompression.apal_structural_core_unconditional
#print axioms DiophCompression.apal_structural_core_of_uniformGS
#print axioms DiophCompression.apal_structural_core_of_perEquationGS
#print axioms DiophCompression.apal_structural_core_of_DPRM
#print axioms DiophCompression.apal_full_phase_diagram
#print axioms DiophCompression.apal_structural_core_of_DPRM_NN
#print axioms DiophCompression.apal_full_phase_diagram_classical
#print axioms DiophCompression.apal_full_phase_diagram_literature
