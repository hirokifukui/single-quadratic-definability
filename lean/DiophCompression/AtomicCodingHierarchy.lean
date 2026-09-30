/-
  DiophCompression/AtomicCodingHierarchy.lean — APAL Logic Pivot, Gate 1 (session 19, 2026-08-30, claude.ai direct).
  Theorem A (coding-arity hierarchy of the single-equation fragments Atom_d on injective graphs):
    ca(Atom_0) = −∞ (empty),  ca(Atom_1) = 1,  ca(Atom_2) = 2,  ca(Atom_3) ≥ 3,  ca(Atom_4) = ∞.
  Every theorem is a wrapper of a sealed r18 declaration (ERRATA_r18 E2–E5):
    degree 0: graph_degree_zero_impossible_Z; degree 1: graph_degree_one_le_one_Z / graph_degree_one_achievable_Z;
    degree 2: SemanticQuadraticSingular.graphAchievableZ_degree_two_iff (Quadratic Witness Inertia);
    degree 3: graph_no_witness_achievable_Z 3; degree 4: chain_graph_achievable_Z with β = 1 (arity r+2).
  Statements frozen in frozen_statements/LogicPivot_STATEMENTS.lean (md5 4b647f55).
-/
import DiophCompression.LogicFragments
import DiophCompression.WeightedMPUP
import DiophCompression.BoundaryCasesZ
import DiophCompression.ArityMonotonicity
import DiophCompression.TreeCoding
import DiophCompression.CapacityFunctions
import DiophCompression.DegreeZero
import DiophCompression.SemanticQuadraticSingular.SingularAssembly

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Monotonicity of Atom_d in the degree and in the arity -/

theorem atomGraph_mono_degree {d d' n : ℕ} (hd : d ≤ d') (h : AtomGraphZ d n) : AtomGraphZ d' n := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, graphAchievableZ_mono le_rfl hd hr⟩

theorem atomGraph_mono_arity {d m n : ℕ} (h : m ≤ n) (hn : AtomGraphZ d n) : AtomGraphZ d m := by
  obtain ⟨r, hr⟩ := hn
  exact ⟨r, graph_arity_downward_Z h hr⟩

/-! ### The hierarchy -/

/-- Degree 0: no injective graph at all (a constant equation cannot depend on `c`). -/
theorem atomGraph_degree_zero_iff {n : ℕ} : ¬ AtomGraphZ 0 n := by
  rintro ⟨r, hr⟩
  exact graph_degree_zero_impossible_Z n r hr

/-- ca(Atom_1) = 1. -/
theorem atomGraph_degree_one_iff {n : ℕ} : AtomGraphZ 1 n ↔ n ≤ 1 := by
  constructor
  · rintro ⟨r, hr⟩; exact graph_degree_one_le_one_Z hr
  · intro hn
    exact atomGraph_mono_arity hn ⟨0, graph_degree_one_achievable_Z 0⟩

/-- ca(Atom_2) = 2 — the Quadratic Witness Inertia theorem in fragment language: no number of
    ℤ-witnesses lets one quadratic equation define the graph of an injection `ℕ^3 → ℕ`. -/
theorem atomGraph_degree_two_iff {n : ℕ} : AtomGraphZ 2 n ↔ n ≤ 2 := by
  constructor
  · rintro ⟨r, hr⟩
    exact (SemanticQuadraticSingular.graphAchievableZ_degree_two_iff r n).mp hr
  · intro hn
    exact ⟨0, (SemanticQuadraticSingular.graphAchievableZ_degree_two_iff 0 n).mpr hn⟩

/-- ca(Atom_3) ≥ 3: the integer cubic `6·skolem` on `ℕ^3`, with no witness. -/
theorem atomGraph_degree_three_ternary : AtomGraphZ 3 3 :=
  ⟨0, graph_no_witness_achievable_Z 3 (by norm_num)⟩

/-- ca(Atom_4) = ∞: the chain of quadratic Skolem gates (β = 1) codes arity `r + 2` with `r`
    witnesses in total degree 4; arities 0 and 1 by monotonicity. -/
theorem atomGraph_degree_four_all : ∀ n, AtomGraphZ 4 n := by
  intro n
  rcases Nat.lt_or_ge n 2 with hn | hn
  · exact atomGraph_mono_arity (by omega : n ≤ 1)
      (atomGraph_mono_degree (by norm_num) ⟨0, graph_degree_one_achievable_Z 0⟩)
  · have h := chain_graph_achievable_Z (r := n - 2) (β := 1)
    have hl : leafCount (n - 2) 1 = n := by unfold leafCount; omega
    rw [hl] at h
    exact ⟨n - 2, h⟩

/-! ### Coding spectra as sets -/

theorem atomicCodingSpectrumZ_one : AtomicCodingSpectrumZ 1 = Set.Iic 1 := by
  ext n; exact atomGraph_degree_one_iff

theorem atomicCodingSpectrumZ_two : AtomicCodingSpectrumZ 2 = Set.Iic 2 := by
  ext n; exact atomGraph_degree_two_iff

theorem atomicCodingSpectrumZ_four : AtomicCodingSpectrumZ 4 = Set.univ := by
  ext n; exact ⟨fun _ => trivial, fun _ => atomGraph_degree_four_all n⟩

end DiophCompression

#print axioms DiophCompression.atomGraph_degree_zero_iff
#print axioms DiophCompression.atomGraph_degree_one_iff
#print axioms DiophCompression.atomGraph_degree_two_iff
#print axioms DiophCompression.atomGraph_degree_three_ternary
#print axioms DiophCompression.atomGraph_degree_four_all
#print axioms DiophCompression.atomicCodingSpectrumZ_one
#print axioms DiophCompression.atomicCodingSpectrumZ_two
#print axioms DiophCompression.atomicCodingSpectrumZ_four
