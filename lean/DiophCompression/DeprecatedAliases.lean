/-
  DeprecatedAliases.lean — r11 (GPT r10 §3.4 / §4.9): preferred names for theorems whose original
  names were over-specific or stale. No new mathematics: each statement below is a verbatim copy of
  the original theorem's statement, each proof is exactly the original theorem. The original names
  are KEPT (sealed r10 claims reference them; reference stability over naming aesthetics) and are
  hereby documented as deprecated in favour of the names in this file.
  Fixed-modulus API note (GPT r10 §3.4): the primary fixed-modulus API is
  `fixed_radical_modulus_fiber_periodic` / `fixed_modulus_dichotomy` (PeriodicModulus.lean);
  `rank_two_fixed_modulus_periodic` / `rank_two_fixed_modulus_dichotomy` are deprecated wrappers
  whose rank hypothesis `hN` is vestigial (not consumed by the proofs).
-/
import DiophCompression.SemanticQuadraticMatrix.FullRankGeneric
import DiophCompression.SemanticQuadraticSingular.Unimodular3

namespace DiophCompression.SemanticQuadraticMatrix

open Matrix

variable {r : ℕ}

/-- Preferred name for `full_rank_projection_dichotomy_of_direction_property` (GPT r10 §4.9): the
theorem takes no direction hypothesis — the direction property is derived internally. -/
theorem full_rank_projection_dichotomy (hr : 2 ≤ r) :
    ∀ (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ), (witnessGram C).det ≠ 0 → DichotomyM A B C :=
  full_rank_projection_dichotomy_of_direction_property hr

end DiophCompression.SemanticQuadraticMatrix

namespace DiophCompression.SemanticQuadraticSingular

open Matrix

/-- Preferred name for `congruent_block_form_rank_two` (GPT r10 §4.9): the theorem holds for every
singular symmetric 3×3 integer matrix, with no rank hypothesis. -/
theorem congruent_block_form_singular_three (G : Matrix (Fin 3) (Fin 3) ℤ) (hs : Gᵀ = G) (hG : G.det = 0) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℤ, U.det = 1 ∧ (∀ i, (Uᵀ * G * U) i 2 = 0) ∧ (∀ j, (Uᵀ * G * U) 2 j = 0) :=
  congruent_block_form_rank_two G hs hG

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticMatrix.full_rank_projection_dichotomy
#print axioms DiophCompression.SemanticQuadraticSingular.congruent_block_form_singular_three
