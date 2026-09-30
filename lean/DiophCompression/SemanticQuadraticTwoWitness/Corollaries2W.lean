/-
  DiophCompression/SemanticQuadraticTwoWitness/Corollaries2W.lean — r09 必須A (GPT r08 §6): the r08 result
  G_ℤ(2,2) = 2 in its official corollary forms. Statements frozen first in the frozen statement file
  `Corollaries2W_STATEMENTS.lean` (md5 5cf837b9); six names are GPT's verbatim.
  `bounded_branch_sharp` exports the inequality behind CLASSIFICATION_2W §3.5 (c₀ ≤ |β|/(2|α|), GPT r08 §3.4).
  Session 9, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticTwoWitness.Assembly2W
import DiophCompression.SemanticQuadratic.Corollaries

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadratic

/-- GraphAchievableZ(n, 2, 2) ⟺ n ≤ 2. -/
theorem graphAchievableZ_two_two_iff {n : ℕ} : GraphAchievableZ n 2 2 ↔ n ≤ 2 := by
  rw [graphCapacityZ_spec 2 2 (by norm_num) n, graphCapacityZ_two_two]

/-- Quadratic witness inertia at r = 2: two integer witnesses add nothing to the degree-2 graph capacity. -/
theorem two_witness_quadratic_inertia_Z : graphCapacityZ 2 2 = graphCapacityZ 0 2 := by
  rw [graphCapacityZ_two_two, graphCapacityZ_noWitness 2 (by norm_num)]

/-- G_ℤ(r, 2) = 2 for r = 0, 1, 2. -/
theorem quadratic_inertia_up_to_two_Z : ∀ r ≤ 2, graphCapacityZ r 2 = 2 := by
  intro r hr
  interval_cases r
  · exact graphCapacityZ_noWitness 2 (by norm_num)
  · exact graphCapacityZ_one_two
  · exact graphCapacityZ_two_two

/-- Semantic 2 versus syntactic 5 at (r, d) = (2, 2). -/
theorem two_witness_semantic_gap_Z : graphCapacityZ 2 2 = 2 ∧ capBound 2 2 = 5 :=
  ⟨graphCapacityZ_two_two, by unfold capBound; norm_num [Nat.choose]⟩

/-- U_ℤ(2, 2) ≤ G_ℤ(2, 2) + 1 = 3. -/
theorem universalCapacityZ_two_two_le_three : universalCapacityZ 2 2 ≤ 3 := by
  have h := universalCapacityZ_le_graphCapacityZ_succ 2 2 (by norm_num)
  rw [graphCapacityZ_two_two] at h
  exact h

theorem not_universalAchievableZ_four_two_two : ¬ UniversalAchievableZ 4 2 2 := fun h => by
  have h4 := (universalCapacityZ_spec 2 2 4).mp h
  have h3 := universalCapacityZ_two_two_le_three
  omega

/-- Syntactic vs semantic at (r, d) = (2, 2): S(2, 3) = C(5, 4) = 5 (both directions) while G_ℤ(2, 2) = 2. -/
theorem syntactic_semantic_gap_two_two :
    capBound 2 2 = 5 ∧
    (∀ n, SpecializationAchievable n 3 2 → n ≤ 5) ∧ SpecializationAchievable 5 3 2 ∧
    graphCapacityZ 2 2 = 2 ∧ graphCapacityZ 2 2 < capBound 2 2 := by
  have hS := specialization_capacity_exact 2 3
  have hc : capBound 2 2 = 5 := by unfold capBound; norm_num [Nat.choose]
  refine ⟨hc, ?_, ?_, graphCapacityZ_two_two, ?_⟩
  · intro n hn; have := hS.1 n hn; simpa [Nat.choose] using this
  · simpa [Nat.choose] using hS.2
  · rw [graphCapacityZ_two_two, hc]; norm_num

/-- The sharp bounded-branch inequality of the generic rank-2 theorem: on the branch α(2αc + β) ≤ 0
    (α ≠ 0, c ≥ 0) one has 2|α|c ≤ |β|, i.e. c ≤ |β|/(2|α|); the exported coarse bound c ≤ |β| follows. -/
theorem bounded_branch_sharp (α β c : ℤ) (hα : α ≠ 0) (hc : 0 ≤ c) (hle : α * (2 * α * c + β) ≤ 0) :
    2 * |α| * c ≤ |β| := by
  have hαpos : 0 < |α| := abs_pos.mpr hα
  have h1 : 2 * α ^ 2 * c ≤ |α| * |β| := by
    have := neg_abs_le (α * β)
    rw [abs_mul] at this
    nlinarith
  have h2 : α ^ 2 = |α| * |α| := by rw [abs_mul_abs_self α]; ring
  rw [h2] at h1
  have h3 : |α| * (2 * |α| * c) ≤ |α| * |β| := by nlinarith
  exact le_of_mul_le_mul_left h3 hαpos

theorem bounded_branch_coarse (α β c : ℤ) (hα : α ≠ 0) (hc : 0 ≤ c) (hle : α * (2 * α * c + β) ≤ 0) :
    c ≤ |β| := by
  have h := bounded_branch_sharp α β c hα hc hle
  have hα1 : 1 ≤ |α| := Int.one_le_abs hα
  nlinarith

end DiophCompression.SemanticQuadraticTwoWitness

#print axioms DiophCompression.SemanticQuadraticTwoWitness.graphAchievableZ_two_two_iff
#print axioms DiophCompression.SemanticQuadraticTwoWitness.two_witness_quadratic_inertia_Z
#print axioms DiophCompression.SemanticQuadraticTwoWitness.quadratic_inertia_up_to_two_Z
#print axioms DiophCompression.SemanticQuadraticTwoWitness.two_witness_semantic_gap_Z
#print axioms DiophCompression.SemanticQuadraticTwoWitness.universalCapacityZ_two_two_le_three
#print axioms DiophCompression.SemanticQuadraticTwoWitness.not_universalAchievableZ_four_two_two
#print axioms DiophCompression.SemanticQuadraticTwoWitness.syntactic_semantic_gap_two_two
#print axioms DiophCompression.SemanticQuadraticTwoWitness.bounded_branch_sharp
#print axioms DiophCompression.SemanticQuadraticTwoWitness.bounded_branch_coarse
