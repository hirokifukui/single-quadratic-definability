/-
  DiophCompression/DegreeZero.lean — r06 必須B (session 6, 2026-08-27, claude.ai direct, no CC).
  Statements frozen first: frozen statement file `DegreeZero_STATEMENTS.lean` (md5 dcc3e9f0).
  GPT r05 §2.2: a polynomial of total degree 0 is a constant (`totalDegree_eq_zero_iff_eq_C`), so it
  represents either everything or nothing, and never the graph of a function — the graph contains
  (a, e a) and omits (a, e a + 1). This holds for every arity n, including n = 0, and every witness
  count r. Consequently the d = 0 value of `graphCapacity{N,Z}` (= 0, the `Nat.findGreatest` default)
  is NOT an attained maximum (`*_not_attained`), which is why the capacity theorems are stated for
  d ≥ 1 and the paper defines G_R(r, d) only for d ≥ 1. For universality, arity 0 is always achievable
  (constants 0/1) and arity ≥ 1 is not at degree 0 (U(n+1) ⇒ G(n)), so `universalCapacity r 0 = 0` is
  a true maximum.
-/
import DiophCompression.CapacityFunctions

namespace DiophCompression

open MvPolynomial MPUP

/-- A constant polynomial evaluates to its constant coefficient. -/
theorem evalAt_of_totalDegree_zero {n r : ℕ} (P : Poly n r) (hP : P.totalDegree ≤ 0)
    (a : Fin n → ℕ) (y : Fin r → ℤ) : evalAt P a y = coeff 0 P := by
  have hc : P = C (coeff 0 P) := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hP)
  calc evalAt P a y = evalAt (C (coeff 0 P)) a y := by rw [← hc]
    _ = coeff 0 P := by simp [evalAt]

/-- (a, e a) is in the graph. -/
theorem snoc_mem_graph {n : ℕ} (e : (Fin n → ℕ) → ℕ) (a : Fin n → ℕ) :
    (Fin.snoc a (e a) : Fin (n + 1) → ℕ) ∈ graph e := by
  simp [graph, Fin.snoc_last, Fin.init_snoc]

/-- (a, e a + 1) is not in the graph. -/
theorem snoc_succ_not_mem_graph {n : ℕ} (e : (Fin n → ℕ) → ℕ) (a : Fin n → ℕ) :
    (Fin.snoc a (e a + 1) : Fin (n + 1) → ℕ) ∉ graph e := by
  simp [graph, Fin.snoc_last, Fin.init_snoc]

theorem graph_degree_zero_impossible_N (n r : ℕ) : ¬ GraphAchievableN n r 0 := by
  rintro ⟨e, -, r', -, P, hP, hrep⟩
  set a : Fin n → ℕ := fun _ => 0
  obtain ⟨y, hy⟩ := (hrep _).mp (snoc_mem_graph e a)
  rw [evalAt_of_totalDegree_zero P hP] at hy
  exact snoc_succ_not_mem_graph e a ((hrep _).mpr ⟨y, by rw [evalAt_of_totalDegree_zero P hP]; exact hy⟩)

theorem graph_degree_zero_impossible_Z (n r : ℕ) : ¬ GraphAchievableZ n r 0 := by
  rintro ⟨e, -, r', -, P, hP, hrep⟩
  set a : Fin n → ℕ := fun _ => 0
  obtain ⟨y, hy⟩ := (hrep _).mp (snoc_mem_graph e a)
  rw [evalAt_of_totalDegree_zero P hP] at hy
  exact snoc_succ_not_mem_graph e a ((hrep _).mpr ⟨y, by rw [evalAt_of_totalDegree_zero P hP]; exact hy⟩)

/-- The d = 0 value of `graphCapacityN` is a `Nat.findGreatest` default, not an attained maximum. -/
theorem graphCapacityN_degree_zero_not_attained (r : ℕ) : ¬ GraphAchievableN (graphCapacityN r 0) r 0 :=
  graph_degree_zero_impossible_N _ r

theorem graphCapacityZ_degree_zero_not_attained (r : ℕ) : ¬ GraphAchievableZ (graphCapacityZ r 0) r 0 :=
  graph_degree_zero_impossible_Z _ r

theorem universalAchievableN_degree_zero_iff (n r : ℕ) : UniversalAchievableN n r 0 ↔ n = 0 := by
  constructor
  · intro h
    cases n with
    | zero => rfl
    | succ m => exact absurd (universal_implies_graph h) (graph_degree_zero_impossible_N m r)
  · rintro rfl
    exact universalAchievableN_zero r 0

theorem universalAchievableZ_degree_zero_iff (n r : ℕ) : UniversalAchievableZ n r 0 ↔ n = 0 := by
  constructor
  · intro h
    cases n with
    | zero => rfl
    | succ m => exact absurd (universal_implies_graph_Z h) (graph_degree_zero_impossible_Z m r)
  · rintro rfl
    exact universalAchievableZ_zero r 0

theorem universalCapacityN_degree_zero (r : ℕ) : universalCapacityN r 0 = 0 :=
  (universalAchievableN_degree_zero_iff _ r).mp
    ((universalCapacityN_spec r 0 _).mpr (le_refl (universalCapacityN r 0)))

theorem universalCapacityZ_degree_zero (r : ℕ) : universalCapacityZ r 0 = 0 :=
  (universalAchievableZ_degree_zero_iff _ r).mp
    ((universalCapacityZ_spec r 0 _).mpr (le_refl (universalCapacityZ r 0)))

end DiophCompression

#print axioms DiophCompression.graph_degree_zero_impossible_N
#print axioms DiophCompression.graph_degree_zero_impossible_Z
#print axioms DiophCompression.graphCapacityN_degree_zero_not_attained
#print axioms DiophCompression.graphCapacityZ_degree_zero_not_attained
#print axioms DiophCompression.universalAchievableN_degree_zero_iff
#print axioms DiophCompression.universalAchievableZ_degree_zero_iff
#print axioms DiophCompression.universalCapacityN_degree_zero
#print axioms DiophCompression.universalCapacityZ_degree_zero
