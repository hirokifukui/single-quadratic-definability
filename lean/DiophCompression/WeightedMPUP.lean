/-
  DiophCompression/WeightedMPUP.lean — r04 Task 4 (session 4, 2026-08-26, claude.ai direct).
  Weighted obstruction: G_R(r,d) ≤ C(d+r+1, r+2); p−1 ≤ C(δ(p)+ν(p)+1, ν(p)+2) for any
  multiparameter universal pair; hence ¬MPUP (second, sharper proof — the frozen
  Obstruction.lean / Quantitative.lean remain the backup certificate and are not modified).
  Boundary: d = 1 ⇒ n ≤ 1 (so p ≤ 2), the sharp form GPT r02 asked for.
-/
import DiophCompression.Sandwich

namespace DiophCompression

open MPUP

variable {n r d : ℕ}

/-- graph_dimension_le_totalDegreeCapacity_N : G_ℕ(r, d) ≤ C(d+r+1, r+2). -/
theorem graph_dimension_le_totalDegreeCapacity_N (h : GraphAchievableN n r d) :
    n ≤ (d + r + 1).choose (r + 2) := by
  have := specialization_bound (graph_implies_specialization h)
  simpa [add_assoc] using this

/-- graph_dimension_le_totalDegreeCapacity_Z : G_ℤ(r, d) ≤ C(d+r+1, r+2). -/
theorem graph_dimension_le_totalDegreeCapacity_Z (h : GraphAchievableZ n r d) :
    n ≤ (d + r + 1).choose (r + 2) := by
  have := specialization_bound (graph_implies_specialization_Z h)
  simpa [add_assoc] using this

/-- Weighted quantitative obstruction (ℕ-unknowns), in the `n+1` indexing of Quantitative.lean:
    n ≤ C(δ(n+1) + ν(n+1) + 1, ν(n+1) + 2) for ARBITRARY maps ν δ. -/
theorem quantitative_MPUP_N_weighted {ν δ : ℕ → ℕ} (h : MultiUniversalN ν δ) (n : ℕ) :
    n ≤ (δ (n + 1) + ν (n + 1) + 1).choose (ν (n + 1) + 2) :=
  graph_dimension_le_totalDegreeCapacity_N (universal_implies_graph (h (n + 1)))

/-- Weighted quantitative obstruction (ℤ-unknowns). -/
theorem quantitative_MPUP_Z_weighted {ν δ : ℕ → ℕ} (h : MultiUniversalZ ν δ) (n : ℕ) :
    n ≤ (δ (n + 1) + ν (n + 1) + 1).choose (ν (n + 1) + 2) :=
  graph_dimension_le_totalDegreeCapacity_Z (universal_implies_graph_Z (h (n + 1)))

/-- GPT r03 Task 4 form: for p ≥ 1 parameters, p − 1 ≤ C(δ(p) + ν(p) + 1, ν(p) + 2). -/
theorem quantitative_MPUP_N_weighted' {ν δ : ℕ → ℕ} (h : MultiUniversalN ν δ) (p : ℕ) (hp : 1 ≤ p) :
    p - 1 ≤ (δ p + ν p + 1).choose (ν p + 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  simpa using quantitative_MPUP_N_weighted h n

theorem quantitative_MPUP_Z_weighted' {ν δ : ℕ → ℕ} (h : MultiUniversalZ ν δ) (p : ℕ) (hp : 1 ≤ p) :
    p - 1 ≤ (δ p + ν p + 1).choose (ν p + 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  simpa using quantitative_MPUP_Z_weighted h n

/-- ¬MPUP_N, weighted route (independent of the frozen not_MPUP_N). -/
theorem not_MPUP_N_weighted : ¬ MPUP_N := by
  rintro ⟨ν, δ, h⟩
  have := quantitative_MPUP_N_weighted h ((δ + ν + 1).choose (ν + 2) + 1)
  omega

/-- ¬MPUP_Z, weighted route. -/
theorem not_MPUP_Z_weighted : ¬ MPUP_Z := by
  rintro ⟨ν, δ, h⟩
  have := quantitative_MPUP_Z_weighted h ((δ + ν + 1).choose (ν + 2) + 1)
  omega

/-! ### Boundary d = 1 (GPT r03 Task 8 first target, upper half): G_R(r, 1) ≤ 1. -/

theorem graph_degree_one_le_one_N (h : GraphAchievableN n r 1) : n ≤ 1 := by
  have := graph_dimension_le_totalDegreeCapacity_N h
  rwa [show 1 + r + 1 = r + 2 by ring, Nat.choose_self] at this

theorem graph_degree_one_le_one_Z (h : GraphAchievableZ n r 1) : n ≤ 1 := by
  have := graph_dimension_le_totalDegreeCapacity_Z h
  rwa [show 1 + r + 1 = r + 2 by ring, Nat.choose_self] at this

/-- Lower half: G_R(r, 1) ≥ 1 via the identity coder c = a (no witness, degree 1). -/
theorem graph_degree_one_achievable_N (r : ℕ) : GraphAchievableN 1 r 1 := by
  refine ⟨fun a => a 0, fun a a' h => funext fun i => by fin_cases i; exact h, 0, Nat.zero_le _,
    MvPolynomial.X (Sum.inl (Fin.last 1)) - MvPolynomial.X (Sum.inl 0), ?_, ?_⟩
  · exact le_trans (MvPolynomial.totalDegree_sub _ _)
      (max_le (MvPolynomial.totalDegree_X _).le (MvPolynomial.totalDegree_X _).le)
  · intro v
    constructor
    · intro hv
      refine ⟨fun i => 0, ?_⟩
      have hv' : v 1 = v 0 := hv
      simp [evalAt, hv']
    · rintro ⟨y, hy⟩
      simp [evalAt] at hy
      show v (Fin.last 1) = v 0
      have h1 : v (Fin.last 1) = v 1 := rfl
      omega

/-- A multiparameter universal pair with δ ≡ 1 has at most 2 parameters: n ≤ 1 for all n,
    i.e. MultiUniversalN ν (fun _ => 1) is impossible (sharpening Quantitative.lean's
    `multiUniversalN_degree_one`, which gives n ≤ ν(n+1)+2). -/
theorem multiUniversalN_degree_one_sharp {ν : ℕ → ℕ} (h : MultiUniversalN ν (fun _ => 1)) (n : ℕ) :
    n ≤ 1 :=
  graph_degree_one_le_one_N (universal_implies_graph (h (n + 1)))

theorem not_multiUniversalN_degree_one (ν : ℕ → ℕ) : ¬ MultiUniversalN ν (fun _ => 1) :=
  fun h => by have := multiUniversalN_degree_one_sharp h 2; omega

end DiophCompression

#print axioms DiophCompression.graph_dimension_le_totalDegreeCapacity_N
#print axioms DiophCompression.graph_dimension_le_totalDegreeCapacity_Z
#print axioms DiophCompression.quantitative_MPUP_N_weighted
#print axioms DiophCompression.quantitative_MPUP_Z_weighted
#print axioms DiophCompression.not_MPUP_N_weighted
#print axioms DiophCompression.not_MPUP_Z_weighted
#print axioms DiophCompression.graph_degree_one_le_one_N
#print axioms DiophCompression.graph_degree_one_achievable_N
#print axioms DiophCompression.not_multiUniversalN_degree_one
