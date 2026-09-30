/-
  DiophCompression/CodingDegree.lean — APAL Logic Pivot, Gate 1 (session 19, 2026-08-30, claude.ai direct).
  Minimal single-equation coding degree δ_code(n) = min{d : AtomGraphZ d n}, stated as predicates
  (exact values for n = 1, 2, 3; the window 3 ≤ δ_code(n) ≤ 4 for n ≥ 4 — whether 3 or 4 is OPEN).
  Statements frozen in frozen_statements/LogicPivot_STATEMENTS.lean (md5 4b647f55).
-/
import DiophCompression.AtomicCodingHierarchy

namespace DiophCompression

/-- δ_code(1) = 1. -/
theorem codingDegree_one_exact : AtomGraphZ 1 1 ∧ ¬ AtomGraphZ 0 1 :=
  ⟨atomGraph_degree_one_iff.mpr le_rfl, atomGraph_degree_zero_iff⟩

/-- δ_code(2) = 2. -/
theorem codingDegree_two_exact : AtomGraphZ 2 2 ∧ ¬ AtomGraphZ 1 2 :=
  ⟨atomGraph_degree_two_iff.mpr le_rfl, fun h => by have := atomGraph_degree_one_iff.mp h; omega⟩

/-- δ_code(3) = 3. -/
theorem codingDegree_three_exact : AtomGraphZ 3 3 ∧ ¬ AtomGraphZ 2 3 :=
  ⟨atomGraph_degree_three_ternary, fun h => by have := atomGraph_degree_two_iff.mp h; omega⟩

/-- 3 ≤ δ_code(n) ≤ 4 for n ≥ 4 (degree 2 fails by Quadratic Witness Inertia, degree 4 succeeds
    by the chain). Which of 3, 4 holds is left open. -/
theorem codingDegree_ge_three_le_four {n : ℕ} (hn : 4 ≤ n) : ¬ AtomGraphZ 2 n ∧ AtomGraphZ 4 n :=
  ⟨fun h => by have := atomGraph_degree_two_iff.mp h; omega, atomGraph_degree_four_all n⟩

/-- The open question, stated as a proposition (never an axiom): does degree 3 code every arity? -/
def CubicCodesAllArities : Prop := ∀ n, AtomGraphZ 3 n

end DiophCompression

#print axioms DiophCompression.codingDegree_one_exact
#print axioms DiophCompression.codingDegree_two_exact
#print axioms DiophCompression.codingDegree_three_exact
#print axioms DiophCompression.codingDegree_ge_three_le_four
