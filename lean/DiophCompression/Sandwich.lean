/-
  DiophCompression/Sandwich.lean — r04 Task 5 (session 4, 2026-08-26, claude.ai direct).
  universal_implies_graph : UniversalAchievable (n+1) r d → GraphAchievable n r d   (ℕ and ℤ unknowns)
  graph_implies_specialization : GraphAchievable n r d → SpecializationAchievable n (r+1) d
  universality_graph_specialization_sandwich : the composite.
  Reuses the frozen MPUP machinery (code / diophN_graph_code / Phi / aux_Phi_injective) read-only.
-/
import MPUP.Obstruction
import DiophCompression.Definitions
import DiophCompression.SpecializationCapacity

namespace DiophCompression

open MvPolynomial MPUP

variable {n r d : ℕ}

/-- U − 1 ≤ G (ℕ-unknowns): universality at n+1 parameters yields a graph coder at n parameters. -/
theorem universal_implies_graph (h : UniversalAchievableN (n + 1) r d) : GraphAchievableN n r d :=
  ⟨code, code_injective n, h _ (diophN_graph_code n)⟩

/-- U − 1 ≤ G (ℤ-unknowns). -/
theorem universal_implies_graph_Z (h : UniversalAchievableZ (n + 1) r d) : GraphAchievableZ n r d :=
  ⟨code, code_injective n, h _ (diophN_graph_code n)⟩

/-! ### Variable renaming `Fin (n+1) ⊕ Fin r' → Fin n ⊕ Fin (r+1)` (parameter block first,
    then the output variable `c`, then the witnesses). -/

/-- Rename the frozen coder variables into the specialization layout. -/
def rho {n r r' : ℕ} (hr : r' ≤ r) : Fin (n + 1) ⊕ Fin r' → Fin n ⊕ Fin (r + 1)
  | Sum.inl i => if h : (i : ℕ) < n then Sum.inl ⟨i, h⟩ else Sum.inr 0
  | Sum.inr j => Sum.inr ⟨(j : ℕ) + 1, by omega⟩

/-- The induced renaming of the unknown variables `Fin 1 ⊕ Fin r' → Fin (r+1)`. -/
def tau {r r' : ℕ} (hr : r' ≤ r) : Fin 1 ⊕ Fin r' → Fin (r + 1)
  | Sum.inl _ => 0
  | Sum.inr j => ⟨(j : ℕ) + 1, by omega⟩

theorem tau_injective {r r' : ℕ} (hr : r' ≤ r) : Function.Injective (tau hr) := by
  intro v w hvw
  cases v with
  | inl i =>
    cases w with
    | inl i' => exact congrArg Sum.inl (Subsingleton.elim i i')
    | inr j' =>
      exfalso
      have := Fin.val_eq_of_eq hvw
      simp [tau] at this
  | inr j =>
    cases w with
    | inl i' =>
      exfalso
      have := Fin.val_eq_of_eq hvw
      simp [tau] at this
    | inr j' =>
      have := Fin.val_eq_of_eq hvw
      simp only [tau] at this
      exact congrArg Sum.inr (Fin.ext (by omega))

/-- Specializing the renamed polynomial is the renaming of the frozen specialization `Phi`. -/
theorem specialize_rename_eq {r' : ℕ} (hr : r' ≤ r) (C0 : Poly (n + 1) r') (a : Fin n → ℕ) :
    specialize (rename (rho (n := n) hr) C0) a = rename (tau hr) (Phi C0 a) := by
  unfold specialize Phi
  rw [aeval_rename]
  have hcomp : rename (tau hr) (aeval (fsub a) C0)
      = aeval (fun v => rename (tau hr) (fsub a v)) C0 := by
    have := congrArg (fun φ => φ C0) (comp_aeval (fsub a) (rename (tau hr)))
    simpa using this
  rw [hcomp]
  have hfun : (Sum.elim (fun i => C ((a i : ℕ) : ℤ)) X ∘ rho (n := n) hr)
      = fun v => rename (tau hr) (fsub a v) := by
    funext v
    cases v with
    | inl i =>
      by_cases h : (i : ℕ) < n
      · simp [rho, fsub, h, Function.comp]
      · simp [rho, fsub, h, Function.comp, tau]
    | inr j =>
      simp [rho, fsub, Function.comp, tau]
  rw [hfun]

/-- G ≤ S (ℕ-unknowns): a graph coder within (r, d) specializes injectively in r+1 variables. -/
theorem graph_implies_specialization (h : GraphAchievableN n r d) :
    SpecializationAchievable n (r + 1) d := by
  obtain ⟨e, he, r', hr', C0, hC0d, hrep⟩ := h
  have hPhi : Function.Injective (Phi C0) :=
    aux_Phi_injective C0 he ((representsN_iff_representsIn C0 _).1 hrep)
  refine ⟨rename (rho hr') C0, le_trans (totalDegree_rename_le _ _) hC0d, ?_⟩
  intro a a' haa
  rw [specialize_rename_eq hr', specialize_rename_eq hr'] at haa
  exact hPhi (rename_injective _ (tau_injective hr') haa)

/-- G ≤ S (ℤ-unknowns). -/
theorem graph_implies_specialization_Z (h : GraphAchievableZ n r d) :
    SpecializationAchievable n (r + 1) d := by
  obtain ⟨e, he, r', hr', C0, hC0d, hrep⟩ := h
  have hPhi : Function.Injective (Phi C0) :=
    aux_Phi_injective C0 he ((representsZ_iff_representsIn C0 _).1 hrep)
  refine ⟨rename (rho hr') C0, le_trans (totalDegree_rename_le _ _) hC0d, ?_⟩
  intro a a' haa
  rw [specialize_rename_eq hr', specialize_rename_eq hr'] at haa
  exact hPhi (rename_injective _ (tau_injective hr') haa)

/-- THE SANDWICH (ℕ-unknowns): U(n+1) ⟹ G(n) ⟹ S(n, r+1). -/
theorem universality_graph_specialization_sandwich (h : UniversalAchievableN (n + 1) r d) :
    GraphAchievableN n r d ∧ SpecializationAchievable n (r + 1) d :=
  ⟨universal_implies_graph h, graph_implies_specialization (universal_implies_graph h)⟩

theorem universality_graph_specialization_sandwich_Z (h : UniversalAchievableZ (n + 1) r d) :
    GraphAchievableZ n r d ∧ SpecializationAchievable n (r + 1) d :=
  ⟨universal_implies_graph_Z h, graph_implies_specialization_Z (universal_implies_graph_Z h)⟩

end DiophCompression

#print axioms DiophCompression.universal_implies_graph
#print axioms DiophCompression.graph_implies_specialization
#print axioms DiophCompression.graph_implies_specialization_Z
#print axioms DiophCompression.universality_graph_specialization_sandwich
#print axioms DiophCompression.universality_graph_specialization_sandwich_Z
