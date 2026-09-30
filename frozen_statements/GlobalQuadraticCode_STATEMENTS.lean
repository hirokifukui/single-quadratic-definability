/-
  Gate 4 必須B: global Grunewald–Segal form (s27, 2026-09-01). Statement freeze of DiophCompression/GlobalQuadraticCode.lean.
-/
import DiophCompression.QuadraticCodes

namespace DiophCompression

open Primrec

/-! ### The global instance and the global solvability predicate -/

/-- A global Grunewald–Segal instance: a quadratic code (witness arity + coefficient table) and the parameter
    tuple as a list. The parameter arity is the length of the list. `Primcodable` as a product. -/
abbrev GlobalQuadraticInstance : Type := QuadraticCode × List ℤ

/-- The parameter arity of a global instance (= length of the parameter list). -/
def GlobalQuadraticInstance.parameterArity (I : GlobalQuadraticInstance) : ℕ := I.2.length

/-- Solvability of a global instance: some unknown list of the declared witness arity is a root of the code
    evaluated on the environment `parameters ++ unknowns`. -/
def GlobalQuadraticInstance.solvable (I : GlobalQuadraticInstance) : Prop :=
  ∃ u : List ℤ, u.length = I.1.1 ∧ I.1.evalW (I.2 ++ u) = 0

/-- The global (literature-form) Grunewald–Segal hypothesis: ONE decider for the solvability of arbitrary
    instances, the variable count, the coefficient table and the parameter tuple all being part of the input. -/
def GlobalQuadraticSolvabilityDecidable : Prop := ComputablePred GlobalQuadraticInstance.solvable

/-- The fixed-arity instance of a code and a parameter vector. -/
def fixedArityInstance (k : ℕ) (p : QuadraticCode × (Fin k → ℤ)) : GlobalQuadraticInstance :=
  (p.1, List.ofFn p.2)

theorem fixedArityInstance_parameterArity (k : ℕ) (p : QuadraticCode × (Fin k → ℤ)) :
    (fixedArityInstance k p).parameterArity = k := by
  sorry

/-- The fixed-arity specialisation uses the SAME code type: solvability of the global instance built from
    `(c, a)` is solvability of `c` at `a` in the sense of `QuadraticCodes.lean`. -/
theorem fixedArityCode_matches_QuadraticCode (k : ℕ) (p : QuadraticCode × (Fin k → ℤ)) :
    (fixedArityInstance k p).solvable ↔ QuadraticCode.solvableZZ k p.1 p.2 := by
  sorry

theorem primrec_fixedArityInstance (k : ℕ) : Primrec (fixedArityInstance k) := by
  sorry

/-! ### Global ⇒ fixed-arity (the direction the paper uses) -/

/-- 必須B: the global Grunewald–Segal decider specialises to the fixed-arity hypothesis of the paper. -/
theorem globalGS_implies_fixedArityGS (h : GlobalQuadraticSolvabilityDecidable) :
    UniformQuadraticSolvabilityOnCodes := by
  sorry

/-- The full chain from the literature form: global ⇒ codes-uniform ⇒ list-code-uniform. -/
theorem globalGS_implies_uniformGS (h : GlobalQuadraticSolvabilityDecidable) :
    UniformQuadraticSolvabilityDecidableZZ := by
  sorry

/-- The full chain from the literature form: global ⇒ per-equation Grunewald–Segal. -/
theorem globalGS_implies_perEquationGS (h : GlobalQuadraticSolvabilityDecidable) :
    QuadraticSolvabilityDecidableZZ := by
  sorry

end DiophCompression
