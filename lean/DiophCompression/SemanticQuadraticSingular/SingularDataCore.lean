/-
  DiophCompression/SemanticQuadraticSingular/SingularDataCore.lean — APAL Structural Theory Gate 5,
  必須F step 3 (singular block, first layer) (s28, 2026-09-02, claude.ai direct).

  The singular-block dichotomy in data-carrying form, and the reduction of the matrix level to it at
  `b = 0` (a set equality, so the certificate transports by rewriting).

  Note for the next step: the two remaining pieces of the singular assembly — `singular_block_dichotomy`
  and `leaf_dichotomySG` — are PRIVATE lemmas of `SingularAssembly.lean` and depend on five further
  private helpers (`sum_split2`, `fiberSetM_block_iff`, `fiberSetSG_neg_b`, `fboundSG_neg_mu`,
  `nonzero_minor_periodic`). Their data versions therefore have to be APPENDED INSIDE that file rather
  than built here; copying them out would duplicate ~200 sealed lines and invite drift. No sorry; std-3.
-/
import DiophCompression.SemanticQuadraticSingular.SingularAssembly
import DiophCompression.StructuredFamilyCore
import DiophCompression.SemanticQuadraticMatrix.FullRankAssemblyData

namespace DiophCompression.SemanticQuadraticSingular

open DiophCompression.SemanticQuadraticMatrix

variable {k : ℕ}

/-- The data form implies the sealed one. -/
theorem dichotomySG_of_dichotomySGData {A : ℤ} {B : Fin k → ℤ}
    {C : Matrix (Fin k) (Fin k) ℤ} {b : ℤ} (h : DichotomySGData A B C b) : DichotomySG A B C b := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun l m μ q => ?_⟩
  rcases hK l m μ q with hF | hb
  · exact Or.inl (hF.elim fun F => DiophCompression.infinite_of_structuredFamily F)
  · exact Or.inr hb

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.dichotomySG_of_dichotomySGData
