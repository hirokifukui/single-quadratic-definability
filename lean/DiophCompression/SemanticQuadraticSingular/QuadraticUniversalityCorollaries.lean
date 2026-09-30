/-
  DiophCompression/SemanticQuadraticSingular/QuadraticUniversalityCorollaries.lean
  — r13 mandatory F (session 13, 2026-08-28): universality corollaries excised
  from SingularAssembly.lean so the graph-theorem dependency closure no longer
  pulls Sandwich / CapacityBireduction (and transitively GraphToUniversality /
  NatGuard). Theorem names, namespace, statements and proofs are VERBATIM from
  SingularAssembly.lean (vault md5 698c3566); only the file changed. Import
  architecture only — no proof re-implementation (GPT r12 §3.3 / mandatory F).
-/
import DiophCompression.SemanticQuadraticSingular.SingularAssembly
import DiophCompression.CapacityBireduction
import DiophCompression.Sandwich

namespace DiophCompression.SemanticQuadraticSingular

theorem universalCapacityZ_degree_two_le_three : ∀ r, universalCapacityZ r 2 ≤ 3 := by
  intro r
  have h := universalCapacityZ_le_graphCapacityZ_succ r 2 (by norm_num)
  rw [quadraticWitnessInertiaZ r] at h
  omega

theorem no_four_parameter_quadratic_universality : ∀ r, ¬ UniversalAchievableZ 4 r 2 := by
  intro r h
  have h1 := universal_implies_graph_Z h
  have h2 := (graphAchievableZ_degree_two_iff r 3).mp h1
  omega

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.universalCapacityZ_degree_two_le_three
#print axioms DiophCompression.SemanticQuadraticSingular.no_four_parameter_quadratic_universality
