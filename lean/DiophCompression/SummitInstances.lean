/-
  DiophCompression/SummitInstances.lean — worked instances and negative controls for the summit
  (s29, 2026-09-02, claude.ai direct). These discharge the instance-level homework of Gate 5:
  the B4 sign edge cases, the overlap of the two output halves, the five fibre shapes the summit
  theorem must cover, and a negative control for the branch table.
  Nothing here is used by any other file; the point is that each shape is exhibited, not assumed.
  No sorry; std-3 expected.
-/
import DiophCompression.SummitClosure

namespace DiophCompression

open MvPolynomial MPUP SemanticQuadraticGeneral SemanticQuadraticSingular

/-! ### B4 sign edge cases (the negative-slope instance is the positive-slope one) -/

section B4
variable {k : ℕ} (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
  (l : ℤ) (m : Fin k → ℤ) (q : ℤ)

/-- Edge case `b = -1, μ = 0`: the reflection is the identity on the data. -/
theorem b4_edge_neg_one_zero :
    fiberSetSG A B C (-1) l m 0 q = fiberSetSG A B C 1 l m 0 q := by
  simpa using fiberSetSG_negSlope A B C (-1) l m 0 q

/-- Case `b < 0, μ > 0`. -/
theorem b4_edge_neg_b_pos_mu :
    fiberSetSG A B C (-2) l m 3 q = fiberSetSG A B C 2 l m (-3) q := by
  simpa using fiberSetSG_negSlope A B C (-2) l m 3 q

/-- Case `b < 0, μ < 0`. -/
theorem b4_edge_neg_b_neg_mu :
    fiberSetSG A B C (-2) l m (-3) q = fiberSetSG A B C 2 l m 3 q := by
  simpa using fiberSetSG_negSlope A B C (-2) l m (-3) q

end B4

/-! ### The two output halves overlap exactly in zero -/

/-- The nonnegative and nonpositive halves of a set of integers meet exactly in its zero, so the
    half-splitting of the summit proof double-counts nothing but `0`. -/
theorem halves_inter (S : Set ℤ) :
    {c ∈ S | 0 ≤ c} ∩ {c ∈ S | c ≤ 0} = {c ∈ S | c = 0} := by
  ext c
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hc, h1⟩, ⟨_, h2⟩⟩
    exact ⟨hc, le_antisymm h2 h1⟩
  · rintro ⟨hc, rfl⟩
    exact ⟨⟨hc, le_rfl⟩, ⟨hc, le_rfl⟩⟩

/-! ### The five fibre shapes -/

/-- With no parameters, the output slot of `Fin.snoc` is the output itself. -/
theorem snoc_zero_eval (a : Fin 0 → ℤ) (c : ℤ) : (Fin.snoc a c : Fin 1 → ℤ) 0 = c := by
  simp [Fin.snoc]

/-- Empty fibre: the constant equation `1 = 0`. -/
theorem fibre_empty (a : Fin 0 → ℤ) : fiberZZ (C 1 : Poly 1 0) a = ∅ := by
  ext c
  simp [fiberZZ, evalAtZZ]

/-- Two-sided infinite fibre: the zero equation, whose fibre is everything. -/
theorem fibre_univ (a : Fin 0 → ℤ) : fiberZZ (0 : Poly 1 0) a = Set.univ := by
  ext c
  simp [fiberZZ, evalAtZZ]

/-- Fibre consisting of the output zero alone: the equation `c = 0`. -/
theorem fibre_zero_only (a : Fin 0 → ℤ) :
    fiberZZ (X (Sum.inl 0) : Poly 1 0) a = {0} := by
  ext c
  simp [fiberZZ, evalAtZZ, Fin.snoc]

/-- Finite nonempty fibre with two points: the equation `c² = 4`. -/
theorem fibre_two_points (a : Fin 0 → ℤ) :
    fiberZZ ((X (Sum.inl 0)) ^ 2 - C 4 : Poly 1 0) a = {2, -2} := by
  ext c
  simp only [fiberZZ, evalAtZZ, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    map_sub, map_pow, eval_X, eval_C, Sum.elim_inl, snoc_zero_eval]
  constructor
  · rintro ⟨u, hu⟩
    have h : (c - 2) * (c + 2) = 0 := by nlinarith [hu]
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> exact ⟨fun i => i.elim0, by norm_num [Sum.elim_inl, snoc_zero_eval]⟩

/-- Infinite fibre on the nonpositive side only: the equation `c + u² = 0`, whose fibre is `{-t²}`. -/
theorem fibre_neg_only (a : Fin 0 → ℤ) :
    (∀ c ∈ fiberZZ (X (Sum.inl 0) + (X (Sum.inr 0)) ^ 2 : Poly 1 1) a, c ≤ 0) ∧
      (fiberZZ (X (Sum.inl 0) + (X (Sum.inr 0)) ^ 2 : Poly 1 1) a).Infinite := by
  have hmem : ∀ c : ℤ, c ∈ fiberZZ (X (Sum.inl 0) + (X (Sum.inr 0)) ^ 2 : Poly 1 1) a
      ↔ ∃ u : ℤ, c + u ^ 2 = 0 := by
    intro c
    simp only [fiberZZ, evalAtZZ, Set.mem_setOf_eq, map_add, map_pow, eval_X, Sum.elim_inl,
      Sum.elim_inr, snoc_zero_eval]
    constructor
    · rintro ⟨u, hu⟩; exact ⟨u 0, by simpa using hu⟩
    · rintro ⟨u, hu⟩; exact ⟨fun _ => u, by simpa using hu⟩
  constructor
  · intro c hc
    obtain ⟨u, hu⟩ := (hmem c).mp hc
    nlinarith [sq_nonneg u]
  · refine Set.infinite_of_injective_forall_mem
      (f := fun t : ℕ => -((t : ℤ) ^ 2)) ?_ ?_
    · intro s t hst
      simp only [neg_inj] at hst
      have : (s : ℤ) = t := by nlinarith [hst, Int.natCast_nonneg s, Int.natCast_nonneg t]
      exact_mod_cast this
    · intro t
      exact (hmem _).mpr ⟨(t : ℤ), by ring⟩

/-! ### Negative control for the branch table -/

/-- A truncated kind table that forgets branch `B2`. -/
def kindOmitB2 : QuadraticBranch → Option StructuredKind
  | .B2 => none
  | b => b.kind

/-- Negative control: with `B2` omitted the branch table no longer classifies every unbounded leaf —
    `B2` is not a bounded branch, yet the truncated table assigns it no kind. The real table
    (`QuadraticBranch.kind`) does assign it one, which is what `branch_kind_iff_not_bounded` asserts. -/
theorem kindOmitB2_breaks_partition :
    kindOmitB2 .B2 = none ∧ QuadraticBranch.bounded .B2 = false ∧
      QuadraticBranch.kind .B2 = some StructuredKind.movingModulusStepOrbit := by
  refine ⟨rfl, ?_, rfl⟩
  rfl

end DiophCompression

#print axioms DiophCompression.b4_edge_neg_one_zero
#print axioms DiophCompression.b4_edge_neg_b_pos_mu
#print axioms DiophCompression.b4_edge_neg_b_neg_mu
#print axioms DiophCompression.halves_inter
#print axioms DiophCompression.fibre_empty
#print axioms DiophCompression.fibre_univ
#print axioms DiophCompression.fibre_zero_only
#print axioms DiophCompression.fibre_two_points
#print axioms DiophCompression.fibre_neg_only
#print axioms DiophCompression.kindOmitB2_breaks_partition
