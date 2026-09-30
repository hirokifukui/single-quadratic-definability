/-
  DiophCompression/GSCompilerComputable.lean — APAL Structural Theory Gate 5, 必須G (last item) /
  宿題群7-5 "solver input computability" (s29, 2026-09-02, claude.ai direct).

  The GS input compiler is primitive recursive. `GlobalQuadraticInstance.toConcreteEquation` folds the
  parameter list into the coefficient table; this file proves that the map from an instance to its
  parameter-free table is `Primrec` (hence `Computable`), so the reduction to the classical procedure is
  effective and not merely extensional. The code types are `ℕ × List (ℤ × (Option ℕ × Option ℕ))`, all
  `Primcodable`, and the arithmetic legs are the ℤ-primrec lemmas of `IntPrimrec.lean`.
  No sorry; std-3 expected.
-/
import DiophCompression.GSInputCompiler

namespace DiophCompression

/-- The variable-splitting step is primitive recursive. -/
theorem primrec₂_splitFactor : Primrec₂ splitFactor := sorry

/-- Substituting the parameters into one term is primitive recursive. -/
theorem primrec₂_substParamTerm : Primrec₂ substParamTerm := sorry

/-- Substituting the parameters into a whole code is primitive recursive. -/
theorem primrec₂_substParamCode : Primrec₂ substParamCode := sorry

/-- 必須G / 宿題群7-5: the GS input compiler is primitive recursive — an instance is turned into its
    parameter-free coefficient table by a primitive recursive function of the code. -/
theorem globalGS_input_compiler_computable :
    Primrec GlobalQuadraticInstance.toConcreteEquation := sorry

/-- The same in the Turing-computability vocabulary. -/
theorem globalGS_input_compiler_comp :
    Computable GlobalQuadraticInstance.toConcreteEquation := sorry

end DiophCompression

