/-
  DiophCompression/SemanticQuadratic/FiberDichotomy.lean — assembly for the cell (n, 1, 2), ℤ-unknown (session 6, 2026-08-27).
  Leaves (all std-3): Class_D1 (definite), Class_D2 (degenerate, C ≠ 0; swarm worker, re-run by claude.ai),
  Class_D3 (degenerate, C = 0), Class_D4 (square, C ≠ 0), Class_D6 (square, C = 0), Class_D7 (Pell: PellPow + step identity),
  Class_D9 (box-counting assembly from the dichotomy; swarm worker, re-run by claude.ai).
  Frozen statements: `FiberDichotomy_STATEMENTS.lean` (md5 04977cc1). Result: G_ℤ(1, 2) = 2 for every n.
-/
import DiophCompression.SemanticQuadratic.Class_D1
import DiophCompression.SemanticQuadratic.Class_D2
import DiophCompression.SemanticQuadratic.Class_D3
import DiophCompression.SemanticQuadratic.Class_D4
import DiophCompression.SemanticQuadratic.Class_D6
import DiophCompression.SemanticQuadratic.Class_D7
import DiophCompression.SemanticQuadratic.Class_D9

namespace DiophCompression.SemanticQuadratic

open MPUP

-- D8: case split on the discriminant, then on C and on IsSquare.
theorem fiber_dichotomy (A B C : ℤ) : Dichotomy A B C := by
  rcases lt_trichotomy (disc A B C) 0 with hlt | heq | hgt
  · exact dichotomy_definite A B C hlt
  · by_cases hC : C = 0
    · exact dichotomy_degenerate_C_zero A B C heq hC
    · exact dichotomy_degenerate_C_ne A B C heq hC
  · by_cases hC : C = 0
    · exact dichotomy_square_C_zero A B C hgt hC
    · by_cases hs : IsSquare (disc A B C)
      · exact dichotomy_square_C_ne A B C hgt hs hC
      · exact dichotomy_pell A B C hgt hs

/-- One integer witness of degree 2 encodes at most two ℕ-parameters. -/
theorem graph_one_witness_degree_two_le_two {n : ℕ} (h : GraphAchievableZ n 1 2) : n ≤ 2 :=
  graph_one_witness_degree_two_le_two_of_dichotomy fiber_dichotomy h

/-- G_ℤ(1, 2) = 2. -/
theorem graphCapacityZ_one_two : graphCapacityZ 1 2 = 2 :=
  le_antisymm
    (graph_one_witness_degree_two_le_two ((graphCapacityZ_spec 1 2 (by norm_num) _).mpr le_rfl))
    ((graphCapacityZ_spec 1 2 (by norm_num) 2).mp
      (graphAchievableZ_mono (by norm_num) le_rfl (graph_no_witness_achievable_Z 2 (by norm_num))))

/-- GPT's first semantic cell, as stated: no graph coding of three ℕ-parameters with one ℤ-witness at degree 2. -/
theorem not_graphAchievableZ_three_one_two : ¬ GraphAchievableZ 3 1 2 := fun h => by
  have := graph_one_witness_degree_two_le_two h; omega

end DiophCompression.SemanticQuadratic

#print axioms DiophCompression.SemanticQuadratic.fiber_dichotomy
#print axioms DiophCompression.SemanticQuadratic.graph_one_witness_degree_two_le_two
#print axioms DiophCompression.SemanticQuadratic.graphCapacityZ_one_two
#print axioms DiophCompression.SemanticQuadratic.not_graphAchievableZ_three_one_two
