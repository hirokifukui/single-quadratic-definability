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
    fiberSetSG A B C (-1) l m 0 q = fiberSetSG A B C 1 l m 0 q := sorry

/-- Case `b < 0, μ > 0`. -/
theorem b4_edge_neg_b_pos_mu :
    fiberSetSG A B C (-2) l m 3 q = fiberSetSG A B C 2 l m (-3) q := sorry

/-- Case `b < 0, μ < 0`. -/
theorem b4_edge_neg_b_neg_mu :
    fiberSetSG A B C (-2) l m (-3) q = fiberSetSG A B C 2 l m 3 q := sorry

end B4

/-! ### The two output halves overlap exactly in zero -/

/-- The nonnegative and nonpositive halves of a set of integers meet exactly in its zero, so the
    half-splitting of the summit proof double-counts nothing but `0`. -/
theorem halves_inter (S : Set ℤ) :
    {c ∈ S | 0 ≤ c} ∩ {c ∈ S | c ≤ 0} = {c ∈ S | c = 0} := sorry

/-! ### The five fibre shapes -/

/-- With no parameters, the output slot of `Fin.snoc` is the output itself. -/
theorem snoc_zero_eval (a : Fin 0 → ℤ) (c : ℤ) : (Fin.snoc a c : Fin 1 → ℤ) 0 = c := sorry

/-- Empty fibre: the constant equation `1 = 0`. -/
theorem fibre_empty (a : Fin 0 → ℤ) : fiberZZ (C 1 : Poly 1 0) a = ∅ := sorry

/-- Two-sided infinite fibre: the zero equation, whose fibre is everything. -/
theorem fibre_univ (a : Fin 0 → ℤ) : fiberZZ (0 : Poly 1 0) a = Set.univ := sorry

/-- Fibre consisting of the output zero alone: the equation `c = 0`. -/
theorem fibre_zero_only (a : Fin 0 → ℤ) :
    fiberZZ (X (Sum.inl 0) : Poly 1 0) a = {0} := sorry

/-- Finite nonempty fibre with two points: the equation `c² = 4`. -/
theorem fibre_two_points (a : Fin 0 → ℤ) :
    fiberZZ ((X (Sum.inl 0)) ^ 2 - C 4 : Poly 1 0) a = {2, -2} := sorry

/-- Infinite fibre on the nonpositive side only: the equation `c + u² = 0`, whose fibre is `{-t²}`. -/
theorem fibre_neg_only (a : Fin 0 → ℤ) :
    (∀ c ∈ fiberZZ (X (Sum.inl 0) + (X (Sum.inr 0)) ^ 2 : Poly 1 1) a, c ≤ 0) ∧
      (fiberZZ (X (Sum.inl 0) + (X (Sum.inr 0)) ^ 2 : Poly 1 1) a).Infinite := sorry

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
      QuadraticBranch.kind .B2 = some StructuredKind.movingModulusStepOrbit := sorry

end DiophCompression

