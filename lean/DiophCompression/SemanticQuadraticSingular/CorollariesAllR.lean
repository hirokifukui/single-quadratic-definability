import DiophCompression.SemanticQuadraticSingular.SingularAssembly
import DiophCompression.DegreeZero
import DiophCompression.BoundaryCasesZ

/-! # All-r corollaries of Quadratic Witness Inertia (GPT r11 mandatory D)

The exact syntactic/semantic gap `capBound r 2 - graphCapacityZ r 2 = r + 1`,
the degree lower bound for arity ≥ 3, and the arity-spectrum inertia
`GraphAchievableZ n r 2 ↔ GraphAchievableZ n 0 2`. -/

namespace DiophCompression
open SemanticQuadraticSingular

theorem capBound_degree_two (r : ℕ) : capBound r 2 = r + 3 := by
  unfold capBound
  rw [show 2 + r + 1 = r + 3 by omega, show r + 2 = (r + 3) - 1 by omega,
    Nat.choose_symm (by omega), Nat.choose_one_right]

theorem quadratic_syntactic_semantic_gap (r : ℕ) :
    graphCapacityZ r 2 = 2 ∧ capBound r 2 = r + 3 :=
  ⟨quadraticWitnessInertiaZ r, capBound_degree_two r⟩

theorem quadratic_gap_exact (r : ℕ) :
    capBound r 2 - graphCapacityZ r 2 = r + 1 := by
  rw [quadraticWitnessInertiaZ r, capBound_degree_two r]
  omega

theorem quadratic_graph_degree_lower_bound {n r d : ℕ}
    (hn : 3 ≤ n) (h : GraphAchievableZ n r d) : 3 ≤ d := by
  by_contra hd
  push Not at hd
  interval_cases d
  · exact graph_degree_zero_impossible_Z n r h
  · have h1 := (graphCapacityZ_spec r 1 (by norm_num) n).mp h
    rw [graphCapacityZ_degree_one r] at h1
    omega
  · have h2 := (graphAchievableZ_degree_two_iff r n).mp h
    omega

/-- The achievable graph-arity spectrum at total degree 2 is identical for every
witness count `r`. This is an equality of achievable arities (`n ≤ 2` on both
sides), NOT a theorem transforming a given injective graph representation into a
witness-free one. -/
theorem quadratic_graph_arity_inertia {n r : ℕ} :
    GraphAchievableZ n r 2 ↔ GraphAchievableZ n 0 2 :=
  (graphAchievableZ_degree_two_iff r n).trans (graphAchievableZ_degree_two_iff 0 n).symm

end DiophCompression
