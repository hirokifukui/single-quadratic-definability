/-
  Shadow/DefsSingularGeneralR.lean — ray-carrying shadow of the singular/matrix dichotomy-data
  predicates. Verbatim transplant of the `*Data` predicates in
  DiophCompression/SemanticQuadraticSingular/DefsSingularGeneral.lean (`DichotomySGData`, and the
  b = 0 reduction) and DiophCompression/SemanticQuadraticMatrix/DefsMatrix.lean (`DichotomyMData`),
  with `StructuredFamily` → `StructuredFamilyR`.
-/
import ResearchUpgrade.Shadow.FamilyR
import DiophCompression.SemanticQuadraticSingular.DefsSingularGeneral
import DiophCompression.SemanticQuadraticMatrix.DefsMatrix

namespace DiophCompression.ResearchUpgrade

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticSingular

variable {k : ℕ}

/-- s28 必須F step 3, ray-carrying: the singular dichotomy in ray-carrying data form. -/
def DichotomySGDataR (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ) (b : ℤ) : Prop :=
  ∃ K : ℕ, ∀ (l : ℤ) (m : Fin k → ℤ) (μ q : ℤ),
    Nonempty (StructuredFamilyR (fiberSetSG A B C b l m μ q)) ∨
      ∀ c ∈ fiberSetSG A B C b l m μ q, (c : ℤ) ≤ fboundSG K l m μ q

/-- s28 必須F step 3, ray-carrying: the matrix-level dichotomy in ray-carrying data form. -/
def DichotomyMDataR (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ) : Prop :=
  ∃ K : ℕ, ∀ (l : ℤ) (m : Fin k → ℤ) (q : ℤ),
    Nonempty (StructuredFamilyR (fiberSetM A B C l m q)) ∨
      ∀ c ∈ fiberSetM A B C l m q, (c : ℤ) ≤ (K : ℤ) * ((1 + |l| + ∑ i, |m i|) ^ 2 + |q|)

/-- s28: the b = 0 reduction of the matrix level to the singular block, in ray-carrying data form
    (a set equality). -/
theorem dichotomyMDataR_of_dichotomySGDataR_zero (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (h : DichotomySGDataR A B C 0) :
    DichotomyMDataR A B C := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun l m q => ?_⟩
  have hset : fiberSetSG A B C 0 l m 0 q
      = DiophCompression.SemanticQuadraticMatrix.fiberSetM A B C l m q := by
    ext c
    simp only [fiberSetSG, DiophCompression.SemanticQuadraticMatrix.fiberSetM,
      Set.mem_setOf_eq, fqSG]
    constructor
    · rintro ⟨u, w, hh⟩; exact ⟨u, by simpa using hh⟩
    · rintro ⟨u, hh⟩; exact ⟨u, 0, by simpa using hh⟩
  rcases hK l m 0 q with hF | hbnd
  · left; rwa [hset] at hF
  · right
    intro c hc
    rw [← hset] at hc
    have := hbnd c hc
    unfold fboundSG at this
    simpa using this

end DiophCompression.ResearchUpgrade
