/-
  DiophCompression/GlobalQuadraticCode.lean — APAL Structural Theory Gate 4, 必須B (global Grunewald–Segal form)
  (session 27, 2026-09-01, claude.ai direct). Statements frozen in frozen_statements/GlobalQuadraticCode_STATEMENTS.lean.

  Gate-3 review, §2: `UniformQuadraticSolvabilityOnCodes` is the FIXED-ARITY form (∀ k, a decider for parameter
  arity k). The literature form of Grunewald–Segal (1981) is ONE algorithm whose finite input is the whole
  instance: the coefficient table (the code, which carries the witness arity) together with the parameter tuple
  (whose length is the parameter arity). This file states that global form and proves the only direction the
  paper needs: global ⇒ fixed-arity. The global instance is the finite datum (code, parameter list); GPT's
  explicit `parameterArity` field with a length proof is the same datum, the arity being the list length.
  `Primcodable` is inherited from the product, so no subtype coding is needed. No sorry; std-3.
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
  simp [fixedArityInstance, GlobalQuadraticInstance.parameterArity]

/-- The fixed-arity specialisation uses the SAME code type: solvability of the global instance built from
    `(c, a)` is solvability of `c` at `a` in the sense of `QuadraticCodes.lean`. -/
theorem fixedArityCode_matches_QuadraticCode (k : ℕ) (p : QuadraticCode × (Fin k → ℤ)) :
    (fixedArityInstance k p).solvable ↔ QuadraticCode.solvableZZ k p.1 p.2 :=
  Iff.rfl

theorem primrec_fixedArityInstance (k : ℕ) : Primrec (fixedArityInstance k) := by
  have hofn : Primrec fun p : QuadraticCode × (Fin k → ℤ) => List.ofFn p.2 :=
    (Primrec.list_ofFn (f := fun (i : Fin k) (p : QuadraticCode × (Fin k → ℤ)) => p.2 i)
      fun i => Primrec.fin_app.comp Primrec.snd (Primrec.const i)).of_eq fun p => rfl
  exact Primrec.fst.pair hofn

/-! ### Global ⇒ fixed-arity (the direction the paper uses) -/

/-- 必須B: the global Grunewald–Segal decider specialises to the fixed-arity hypothesis of the paper. -/
theorem globalGS_implies_fixedArityGS (h : GlobalQuadraticSolvabilityDecidable) :
    UniformQuadraticSolvabilityOnCodes := by
  intro k
  exact computablePred_comp_computable h (f := fixedArityInstance k) (primrec_fixedArityInstance k).to_comp

/-- The full chain from the literature form: global ⇒ codes-uniform ⇒ list-code-uniform. -/
theorem globalGS_implies_uniformGS (h : GlobalQuadraticSolvabilityDecidable) :
    UniformQuadraticSolvabilityDecidableZZ :=
  uniformGS_of_uniformOnCodes (globalGS_implies_fixedArityGS h)

/-- The full chain from the literature form: global ⇒ per-equation Grunewald–Segal. -/
theorem globalGS_implies_perEquationGS (h : GlobalQuadraticSolvabilityDecidable) :
    QuadraticSolvabilityDecidableZZ :=
  uniformCodeGS_implies_perEquationGS (globalGS_implies_fixedArityGS h)

end DiophCompression

#print axioms DiophCompression.fixedArityCode_matches_QuadraticCode
#print axioms DiophCompression.fixedArityInstance_parameterArity
#print axioms DiophCompression.globalGS_implies_fixedArityGS
#print axioms DiophCompression.globalGS_implies_uniformGS
#print axioms DiophCompression.globalGS_implies_perEquationGS
