/-
  DiophCompression/FunctionPhaseByArity.lean — APAL Structural Theory Gate 3, 必須E
  (session 26, 2026-09-01, claude.ai direct). Statements frozen in
  frozen_statements/FunctionPhaseByArity_STATEMENTS.lean. The strictness witness is the vector function
  (a₀³, 0, …, 0), excluded from SE_2 by the vector quadratic-growth theorem
  (singleQuadratic_function_quadratic_growth) — no substitution lemma needed. No sorry; std-3 expected.
-/
import DiophCompression.ComputableFunctions

namespace DiophCompression

open MvPolynomial MPUP

/-- The strictness witness ℤ^{n+1} → ℤ^{m+1}: `a ↦ (a₀³, 0, …, 0)`. -/
def cubeFirstZZ (n m : ℕ) (a : Fin (n + 1) → ℤ) (j : Fin (m + 1)) : ℤ := if j = 0 then (a 0) ^ 3 else 0

/-- `cubeFirstZZ` is total computable. -/
theorem cubeFirstZZ_computable (n m : ℕ) : TotalComputableFunctionZZ (cubeFirstZZ n m) := by
  refine (Primrec.fin_curry.2 ?_).to_comp
  show Primrec fun p : (Fin (n + 1) → ℤ) × Fin (m + 1) => if p.2 = 0 then (p.1 0) ^ 3 else 0
  refine Primrec.ite ?_ ?_ (Primrec.const 0)
  · exact Primrec.eq.comp Primrec.snd (Primrec.const 0)
  · exact (primrec_int_pow 3).comp (Primrec.fin_app.comp Primrec.fst (Primrec.const 0))

/-- `cubeFirstZZ` is not SE_2-definable (quadratic growth barrier on the first output). -/
theorem cubeFirstZZ_not_singleQuadratic (n m : ℕ) : ¬ SingleQuadraticDefinableFunctionZZ (cubeFirstZZ n m) := by
  intro h
  obtain ⟨C, hC⟩ := singleQuadratic_function_quadratic_growth _ h
  set N : ℕ := C + 1 with hN
  have h1 : 1 ≤ N := by omega
  have hb : (N : ℤ) ^ 3 ≤ (C : ℤ) * (N : ℤ) ^ 2 := by
    have := hC N h1 (fun i => if i = 0 then (N : ℤ) else 0) (fun i => by split_ifs <;> simp) 0
    simpa [cubeFirstZZ] using this
  have hN2 : (0 : ℤ) < (N : ℤ) ^ 2 := by positivity
  have hcube : (N : ℤ) ^ 3 = (N : ℤ) * (N : ℤ) ^ 2 := by ring
  have hle : (N : ℤ) * (N : ℤ) ^ 2 ≤ (C : ℤ) * (N : ℤ) ^ 2 := by rw [← hcube]; exact hb
  have h4 : (N : ℤ) ≤ C := le_of_mul_le_mul_right hle hN2
  have hNc : (N : ℤ) = (C : ℤ) + 1 := by rw [hN]; push_cast; ring
  linarith

/-- Unconditional, every n, m ≥ 1: Fun_{n,m}(SE_2) ⊊ TotComp_{n,m}. -/
theorem singleQuadratic_functions_strict_of_pos_arity {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (∀ f : (Fin n → ℤ) → (Fin m → ℤ), SingleQuadraticDefinableFunctionZZ f → TotalComputableFunctionZZ f) ∧
    ∃ f : (Fin n → ℤ) → (Fin m → ℤ), TotalComputableFunctionZZ f ∧ ¬ SingleQuadraticDefinableFunctionZZ f := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact ⟨fun f h => singleQuadratic_total_function_computable f h,
    cubeFirstZZ n' m', cubeFirstZZ_computable n' m', cubeFirstZZ_not_singleQuadratic n' m'⟩

/-- Zero inputs: every function ℤ^0 → ℤ^m is both SE_2-definable and total computable, so
    Fun_{0,m}(SE_2) = TotComp_{0,m} (= all constant vectors). -/
theorem singleQuadratic_functions_eq_at_zero_input {m : ℕ} (f : (Fin 0 → ℤ) → (Fin m → ℤ)) :
    SingleQuadraticDefinableFunctionZZ f ∧ TotalComputableFunctionZZ f := by
  refine ⟨⟨0, ∑ j : Fin m, (X (Sum.inl (Fin.natAdd 0 j)) - C (f default j)) ^ 2, ?_, ?_⟩, ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_pow _ _).trans ?_
    have h1 : (X (Sum.inl (Fin.natAdd 0 j)) - C (f default j) : Poly (0 + m) 0).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (max_le (totalDegree_X _).le (by rw [totalDegree_C]; exact zero_le_one))
    omega
  · intro v
    have hf : f (fun i => v (Fin.castAdd m i)) = f default := by
      rw [Subsingleton.elim (fun i => v (Fin.castAdd m i)) default]
    have hsum : ∀ y : Fin 0 → ℤ, evalAtZZ (∑ j : Fin m, (X (Sum.inl (Fin.natAdd 0 j)) - C (f default j)) ^ 2) v y
        = ∑ j : Fin m, (v (Fin.natAdd 0 j) - f default j) ^ 2 := by
      intro y; simp [evalAtZZ]
    constructor
    · intro hv
      refine ⟨default, ?_⟩
      rw [hsum]
      apply Finset.sum_eq_zero
      intro j _
      simp only [graphVecZZ, Set.mem_setOf_eq, hf] at hv
      rw [congrFun hv j]; ring
    · rintro ⟨y, hy⟩
      rw [hsum] at hy
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)] at hy
      simp only [graphVecZZ, Set.mem_setOf_eq, hf]
      funext j
      have := hy j (Finset.mem_univ j)
      exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 this)
  · exact (Computable.const (f default)).of_eq (fun a => by rw [Subsingleton.elim a default])

/-- Zero outputs: every function ℤ^n → ℤ^0 is both SE_2-definable and total computable, so
    Fun_{n,0}(SE_2) = TotComp_{n,0} (= the unique function). -/
theorem singleQuadratic_functions_eq_at_zero_output {n : ℕ} (f : (Fin n → ℤ) → (Fin 0 → ℤ)) :
    SingleQuadraticDefinableFunctionZZ f ∧ TotalComputableFunctionZZ f := by
  refine ⟨⟨0, 0, by simp, fun v => ?_⟩, ?_⟩
  · simp only [graphVecZZ, Set.mem_setOf_eq, evalAtZZ, map_zero]
    constructor
    · intro _
      exact ⟨default, by simp⟩
    · intro _
      exact Subsingleton.elim _ _
  · exact (Computable.const (default : Fin 0 → ℤ)).of_eq (fun a => Subsingleton.elim _ _)

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
  refine ⟨fun hn hm => (singleQuadratic_functions_strict_of_pos_arity hn hm).2,
    fun f => singleQuadratic_functions_eq_at_zero_input f,
    fun f => singleQuadratic_functions_eq_at_zero_output f,
    fun f => ⟨singleQuadratic_total_function_computable f,
      (ppQuadratic_functions_eq_totalComputable_of_DPRM hD f).symm, ppQuadratic_functions_eq_singleQuartic f⟩⟩

end DiophCompression

#print axioms DiophCompression.singleQuadratic_functions_strict_of_pos_arity
#print axioms DiophCompression.singleQuadratic_functions_eq_at_zero_input
#print axioms DiophCompression.singleQuadratic_functions_eq_at_zero_output
#print axioms DiophCompression.function_phase_diagram_by_arity
