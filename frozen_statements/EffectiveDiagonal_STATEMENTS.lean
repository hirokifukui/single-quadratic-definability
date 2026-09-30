/-
  frozen_statements/EffectiveDiagonal_STATEMENTS.lean — APAL Structural Theory Gate 3, 宿題群2 (frozen s26, 2026-09-01). The Effective Fragment Diagonalization Lemma (any Primcodable code type, coded family, uniformly decidable membership ⇒ the diagonal is recursive and outside the family; coded_family_ssubset_rec) and its SE_2 instance with the standard quadratic codes.
-/
import DiophCompression.QuadraticCodes

namespace DiophCompression

open MvPolynomial MPUP

/-- The effective diagonal of a coded family: `v ∈ D` iff the code decoded from `v 0` (if any) does not
    accept `v`. -/
def effDiagonal {C : Type} [Primcodable C] (k : ℕ) (interp : C → Set (Fin (k + 1) → ℤ)) :
    Set (Fin (k + 1) → ℤ) :=
  {v | ∀ e : C, (Encodable.decode (Encodable.encode (v 0)) : Option C) = some e → v ∉ interp e}

/-- A coded family: every member of `F` is `interp e` for some code `e`. -/
def CodedFamily {C : Type} (k : ℕ) (interp : C → Set (Fin (k + 1) → ℤ))
    (F : Set (Set (Fin (k + 1) → ℤ))) : Prop :=
  ∀ A ∈ F, ∃ e : C, interp e = A

/-- Uniform membership decidability of a coded family. -/
def UniformlyDecidable {C : Type} [Primcodable C] (k : ℕ) (interp : C → Set (Fin (k + 1) → ℤ)) : Prop :=
  ComputablePred fun p : C × (Fin (k + 1) → ℤ) => p.2 ∈ interp p.1

/-- Effective diagonalization, part 1: the diagonal is recursive under uniform decidability. -/
theorem effDiagonal_computablePred {C : Type} [Primcodable C] (k : ℕ) (interp : C → Set (Fin (k + 1) → ℤ))
    (h : UniformlyDecidable k interp) : ComputablePred fun v => v ∈ effDiagonal k interp := by
  sorry

/-- Effective diagonalization, part 2: the diagonal is not in any coded family (self-application). -/
theorem effDiagonal_not_mem {C : Type} [Primcodable C] (k : ℕ) (interp : C → Set (Fin (k + 1) → ℤ))
    (F : Set (Set (Fin (k + 1) → ℤ))) (hF : CodedFamily k interp F) : effDiagonal k interp ∉ F := by
  sorry

/-- Effective Fragment Diagonalization Lemma: a coded family with uniformly decidable membership that
    contains every recursive relation is impossible — i.e. it is a proper subfamily of REC. -/
theorem coded_family_ssubset_rec {C : Type} [Primcodable C] (k : ℕ) (interp : C → Set (Fin (k + 1) → ℤ))
    (F : Set (Set (Fin (k + 1) → ℤ))) (hF : CodedFamily k interp F) (h : UniformlyDecidable k interp)
    (hsub : F ⊆ RecFragmentZZ (k + 1)) : F ⊂ RecFragmentZZ (k + 1) := by
  sorry

/-! ### Instance: SE_2 with the standard quadratic codes -/

/-- Interpretation of a standard quadratic code as a relation on ℤ^{k+1} (parameter arity k+1). -/
def quadraticCodeRel (k : ℕ) (c : QuadraticCode) : Set (Fin (k + 1) → ℤ) :=
  {v | QuadraticCode.solvableZZ (k + 1) c v}

theorem singleEqFragment_two_codedFamily (k : ℕ) :
    CodedFamily k (quadraticCodeRel k) (SingleEqFragmentZZ 2 (k + 1)) := by
  sorry

theorem quadraticCodeRel_uniformlyDecidable (h : UniformQuadraticSolvabilityOnCodes) (k : ℕ) :
    UniformlyDecidable k (quadraticCodeRel k) := by
  sorry

/-- Re-derivation of the diagonal theorem through the generic lemma with the STANDARD codes:
    SE_2(k+1) ⊊ REC(k+1) under the code-uniform Grunewald–Segal hypothesis on standard codes. -/
theorem singleQuadratic_strict_recursive_of_codes (h : UniformQuadraticSolvabilityOnCodes) (k : ℕ) :
    SingleEqFragmentZZ 2 (k + 1) ⊂ RecFragmentZZ (k + 1) := by
  sorry

end DiophCompression
