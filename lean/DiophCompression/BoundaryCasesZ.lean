/-
  DiophCompression/BoundaryCasesZ.lean — r05 必須A (session 5, 2026-08-26, claude.ai direct, no CC).
  Integer-unknown boundary values: G_ℤ(r,1) = 1 and G_ℤ(0,d) = d (d ≥ 1).
  Mechanism: with zero unknowns the ℕ- and ℤ-unknown representations coincide
  (Fin 0 → ℕ and Fin 0 → ℤ are singletons), so every witness-free ℕ-construction transfers
  verbatim; the upper halves G_ℤ(r,1) ≤ 1 (WeightedMPUP) and G(0,d) ≤ d (BoundaryCases, via the
  same transfer at r = 0) are already available. Names as prescribed in GPT r04 §6 必須A.
  Statements frozen 2026-08-26 (draft md5 9380a14c, `frozen statement file `BoundaryCasesZ_STATEMENTS.lean``); proofs filled after.
-/
import DiophCompression.WeightedMPUP
import DiophCompression.BoundaryCases

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Zero unknowns: ℕ-representation and ℤ-representation coincide. -/

theorem representsN_iff_representsZ_zero {n : ℕ} (P : Poly n 0) (A : Set (Fin n → ℕ)) :
    RepresentsN P A ↔ RepresentsZ P A := by
  unfold RepresentsN RepresentsZ
  have key : ∀ a : Fin n → ℕ,
      (∃ y : Fin 0 → ℕ, evalAt P a (fun i => (y i : ℤ)) = 0) ↔ ∃ y : Fin 0 → ℤ, evalAt P a y = 0 := by
    intro a
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨_, hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨Fin.elim0, ?_⟩
      have hy' : y = fun i => ((Fin.elim0 i : ℕ) : ℤ) := funext fun i => i.elim0
      rw [hy'] at hy
      exact hy
  exact forall_congr' fun a => by rw [key a]

theorem withinN_zero_iff_withinZ {n d : ℕ} (A : Set (Fin n → ℕ)) :
    WithinN 0 d A ↔ WithinZ 0 d A := by
  constructor
  · rintro ⟨r, hr, P, hP, hrep⟩
    obtain rfl : r = 0 := Nat.le_zero.mp hr
    exact ⟨0, le_rfl, P, hP, (representsN_iff_representsZ_zero P A).mp hrep⟩
  · rintro ⟨r, hr, P, hP, hrep⟩
    obtain rfl : r = 0 := Nat.le_zero.mp hr
    exact ⟨0, le_rfl, P, hP, (representsN_iff_representsZ_zero P A).mpr hrep⟩

theorem graphAchievableN_zero_iff_Z (n d : ℕ) :
    GraphAchievableN n 0 d ↔ GraphAchievableZ n 0 d := by
  constructor
  · rintro ⟨e, he, hw⟩
    exact ⟨e, he, (withinN_zero_iff_withinZ _).mp hw⟩
  · rintro ⟨e, he, hw⟩
    exact ⟨e, he, (withinN_zero_iff_withinZ _).mpr hw⟩

/-! ### Degree 1: G_ℤ(r, 1) = 1 -/

theorem graph_degree_one_achievable_Z (r : ℕ) : GraphAchievableZ 1 r 1 :=
  graphAchievableZ_mono (Nat.zero_le r) le_rfl
    ((graphAchievableN_zero_iff_Z 1 1).mp (graph_degree_one_achievable_N 0))

theorem graph_degree_one_exact_N (r : ℕ) :
    (∀ n, GraphAchievableN n r 1 → n ≤ 1) ∧ GraphAchievableN 1 r 1 :=
  ⟨fun _ h => graph_degree_one_le_one_N h, graph_degree_one_achievable_N r⟩

theorem graph_degree_one_exact_Z (r : ℕ) :
    (∀ n, GraphAchievableZ n r 1 → n ≤ 1) ∧ GraphAchievableZ 1 r 1 :=
  ⟨fun _ h => graph_degree_one_le_one_Z h, graph_degree_one_achievable_Z r⟩

/-! ### No witness: G_ℤ(0, d) = d (d ≥ 1) -/

theorem graph_no_witness_le_Z {n d : ℕ} (h : GraphAchievableZ n 0 d) : n ≤ d :=
  graph_no_witness_le ((graphAchievableN_zero_iff_Z n d).mpr h)

theorem graph_no_witness_achievable_Z (d : ℕ) (hd : 1 ≤ d) : GraphAchievableZ d 0 d :=
  (graphAchievableN_zero_iff_Z d d).mp (graph_no_witness_achievable d hd)

theorem graph_no_witness_exact_Z (d : ℕ) (hd : 1 ≤ d) :
    (∀ n, GraphAchievableZ n 0 d → n ≤ d) ∧ GraphAchievableZ d 0 d :=
  ⟨fun _ h => graph_no_witness_le_Z h, graph_no_witness_achievable_Z d hd⟩

end DiophCompression

#print axioms DiophCompression.representsN_iff_representsZ_zero
#print axioms DiophCompression.withinN_zero_iff_withinZ
#print axioms DiophCompression.graphAchievableN_zero_iff_Z
#print axioms DiophCompression.graph_degree_one_achievable_Z
#print axioms DiophCompression.graph_degree_one_exact_N
#print axioms DiophCompression.graph_degree_one_exact_Z
#print axioms DiophCompression.graph_no_witness_le_Z
#print axioms DiophCompression.graph_no_witness_achievable_Z
#print axioms DiophCompression.graph_no_witness_exact_Z
