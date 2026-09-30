/-
  DiophCompression/SemanticQuadratic/Corollaries.lean — r07 必須A (GPT r06 §7): the r06 result in its
  official corollary forms. Statements frozen first in the frozen statement file `Corollaries_STATEMENTS.lean` (md5 6d81ee20).
  G_ℤ(1, 2) = 2 is a single number; the quantifier over n lives in the achievability iff (E-r07-1).
  Session 7, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadratic.FiberDichotomy
import DiophCompression.CapacityBireduction
import DiophCompression.CapacitySharpness

namespace DiophCompression.SemanticQuadratic

/-- GraphAchievableZ(n, 1, 2) ⟺ n ≤ 2 (the achievability form; E-r07-1). -/
theorem graphAchievableZ_one_two_iff {n : ℕ} : GraphAchievableZ n 1 2 ↔ n ≤ 2 := by
  rw [graphCapacityZ_spec 1 2 (by norm_num) n, graphCapacityZ_one_two]

/-- Quadratic witness inertia at r = 1: one integer witness adds nothing to the degree-2 graph capacity. -/
theorem one_witness_quadratic_inertia_Z : graphCapacityZ 1 2 = graphCapacityZ 0 2 := by
  rw [graphCapacityZ_one_two, graphCapacityZ_noWitness 2 (by norm_num)]

/-- U_ℤ(1, 2) ≤ G_ℤ(1, 2) + 1 = 3. -/
theorem universalCapacityZ_one_two_le_three : universalCapacityZ 1 2 ≤ 3 := by
  have h := universalCapacityZ_le_graphCapacityZ_succ 1 2 (by norm_num)
  rw [graphCapacityZ_one_two] at h
  exact h

theorem not_universalAchievableZ_four_one_two : ¬ UniversalAchievableZ 4 1 2 := fun h => by
  have h4 := (universalCapacityZ_spec 1 2 4).mp h
  have h3 := universalCapacityZ_one_two_le_three
  omega

/-- Syntactic vs semantic at (r, d) = (1, 2): S(2, 2) = C(4, 3) = 4 (both directions) while G_ℤ(1, 2) = 2. -/
theorem syntactic_semantic_gap_one_two :
    capBound 1 2 = 4 ∧
    (∀ n, SpecializationAchievable n 2 2 → n ≤ 4) ∧ SpecializationAchievable 4 2 2 ∧
    graphCapacityZ 1 2 = 2 ∧ graphCapacityZ 1 2 < capBound 1 2 := by
  have hS := specialization_capacity_exact 2 2
  have hc : capBound 1 2 = 4 := by unfold capBound; norm_num [Nat.choose]
  refine ⟨hc, ?_, ?_, graphCapacityZ_one_two, ?_⟩
  · intro n hn; have := hS.1 n hn; simpa using this
  · simpa using hS.2
  · rw [graphCapacityZ_one_two, hc]; norm_num

end DiophCompression.SemanticQuadratic

#print axioms DiophCompression.SemanticQuadratic.graphAchievableZ_one_two_iff
#print axioms DiophCompression.SemanticQuadratic.one_witness_quadratic_inertia_Z
#print axioms DiophCompression.SemanticQuadratic.universalCapacityZ_one_two_le_three
#print axioms DiophCompression.SemanticQuadratic.not_universalAchievableZ_four_one_two
#print axioms DiophCompression.SemanticQuadratic.syntactic_semantic_gap_one_two
