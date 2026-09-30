/-
  MPUP/Gate.lean — statement-fidelity gate (METHODOLOGY §3) for the FROZEN spec (MPUP/Spec.lean).
  Positive / negative / near-miss instances proved in Lean against the frozen predicates;
  the same instances are checked numerically by verifier/fidelity_gate.sage (independent reimplementation).
  Mirrors: pos even / neg even-poly-vs-odd / pos a≥1 over N / near-miss a≥1 over Z /
           pos a1≤a0 (n=2) / neg swapped index / degree = total degree.
-/
import MPUP.Spec

namespace MPUP
open MvPolynomial

theorem gate_pos_even :
    RepresentsN (X (Sum.inl 0) - 2 * X (Sum.inr 0) : Poly 1 1) {a | Even (a 0)} := by
  intro a
  simp only [Set.mem_setOf_eq, evalAt, map_sub, map_mul, map_ofNat, eval_X, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨fun _ => k, by rw [hk]; push_cast; ring⟩
  · rintro ⟨y, hy⟩
    exact ⟨y 0, by omega⟩

theorem gate_neg_even_vs_odd :
    ¬ RepresentsN (X (Sum.inl 0) - 2 * X (Sum.inr 0) : Poly 1 1) {a | Odd (a 0)} := by
  intro h
  have h0 := (h (fun _ => 0)).2 ⟨fun _ => 0, by simp [evalAt]⟩
  simp at h0

theorem gate_pos_ge1_N :
    RepresentsN (X (Sum.inl 0) - X (Sum.inr 0) - 1 : Poly 1 1) {a | 1 ≤ a 0} := by
  intro a
  simp only [Set.mem_setOf_eq, evalAt, map_sub, map_one, eval_X, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h1
    exact ⟨fun _ => a 0 - 1, by dsimp only; omega⟩
  · rintro ⟨y, hy⟩
    omega

/-- Near-miss: the same polynomial over ℤ-unknowns represents EVERYTHING, not {a ≥ 1}. -/
theorem gate_nearmiss_ge1_Z :
    ¬ RepresentsZ (X (Sum.inl 0) - X (Sum.inr 0) - 1 : Poly 1 1) {a | 1 ≤ a 0} := by
  intro h
  have h0 := (h (fun _ => 0)).2 ⟨fun _ => -1, by simp [evalAt]⟩
  simp at h0

theorem gate_pos_le_n2 :
    RepresentsN (X (Sum.inl 0) - X (Sum.inl 1) - X (Sum.inr 0) : Poly 2 1) {a | a 1 ≤ a 0} := by
  intro a
  simp only [Set.mem_setOf_eq, evalAt, map_sub, eval_X, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h1
    exact ⟨fun _ => a 0 - a 1, by dsimp only; omega⟩
  · rintro ⟨y, hy⟩
    omega

/-- Negative control for the parameter index order: swapping the set breaks representation. -/
theorem gate_neg_le_swapped :
    ¬ RepresentsN (X (Sum.inl 0) - X (Sum.inl 1) - X (Sum.inr 0) : Poly 2 1) {a | a 0 ≤ a 1} := by
  intro h
  obtain ⟨y, hy⟩ := (h ![0, 1]).1 (by simp)
  simp [evalAt] at hy
  omega

/-- Degree convention: `totalDegree`, so a parameter times an unknown has degree 2, not 1. -/
theorem gate_degree_total :
    (X (Sum.inl 0) * X (Sum.inr 0) : Poly 1 1).totalDegree = 2 := by
  rw [X, X, monomial_mul, one_mul, totalDegree_monomial _ one_ne_zero]
  simp [Finsupp.sum_add_index']

end MPUP

#print axioms MPUP.gate_pos_even
#print axioms MPUP.gate_neg_even_vs_odd
#print axioms MPUP.gate_pos_ge1_N
#print axioms MPUP.gate_nearmiss_ge1_Z
#print axioms MPUP.gate_pos_le_n2
#print axioms MPUP.gate_neg_le_swapped
#print axioms MPUP.gate_degree_total
