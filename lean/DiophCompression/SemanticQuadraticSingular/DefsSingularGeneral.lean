/-
  DefsSingularGeneral.lean — r11 (GPT r10 必須F/G/H/J/K substrate): the general-k singular normal
  form with ONE coupled radical variable, F_k(c,u) + (b c + μ) w = 0. Definitions only, no theorems.
  (session 11, 2026-08-28, claude.ai). The k = 2 instance recovers the r10 shape fq3S up to the
  explicit-coefficient spelling; the k = 0 instance is 必須G's object.
-/
import DiophCompression.SemanticQuadraticMatrix.FullRankGeneric
import DiophCompression.StructuredFamilyCore
import DiophCompression.SemanticQuadraticMatrix.DefsMatrix

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix

variable {k : ℕ}

/-- The general singular fiber polynomial: fqM on the nondegenerate block plus (b c + μ) w. -/
def fqSG (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ)
    (μ q : ℤ) (c : ℤ) (u : Fin k → ℤ) (w : ℤ) : ℤ :=
  fqM A B C l m q c u + (b * c + μ) * w

/-- Naturals c with integer witnesses (u, w). -/
def fiberSetSG (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ)
    (m : Fin k → ℤ) (μ q : ℤ) : Set ℕ :=
  {c | ∃ (u : Fin k → ℤ) (w : ℤ), fqSG A B C b l m μ q (c : ℤ) u w = 0}

/-- The bound shape K·((1 + |l| + Σ|mᵢ| + |μ|)² + |q|). -/
def fboundSG (K : ℕ) (l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) : ℤ :=
  (K : ℤ) * ((1 + |l| + ∑ i, |m i| + |μ|) ^ 2 + |q|)

/-- Projection dichotomy for the fixed data (A, B, C, b) in general singular coordinates. -/
def DichotomySG (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ) (b : ℤ) : Prop :=
  ∃ K : ℕ, ∀ (l : ℤ) (m : Fin k → ℤ) (μ q : ℤ),
    (fiberSetSG A B C b l m μ q).Infinite ∨
      ∀ c ∈ fiberSetSG A B C b l m μ q, (c : ℤ) ≤ fboundSG K l m μ q


/-- s28 必須F step 3: the same dichotomy in data-carrying form (the infinite side carries a structured
    family instead of bare `Set.Infinite`). Placed here, next to `DichotomySG`, because the assembly
    files above depend on this one. -/
def DichotomySGData (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ) (b : ℤ) : Prop :=
  ∃ K : ℕ, ∀ (l : ℤ) (m : Fin k → ℤ) (μ q : ℤ),
    Nonempty (DiophCompression.StructuredFamily (fiberSetSG A B C b l m μ q)) ∨
      ∀ c ∈ fiberSetSG A B C b l m μ q, (c : ℤ) ≤ fboundSG K l m μ q


/-- s28: the b = 0 reduction of the matrix level to the singular block, in data form (a set equality). -/
theorem dichotomyMData_of_dichotomySGData_zero (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (h : DichotomySGData A B C 0) :
    DiophCompression.SemanticQuadraticMatrix.DichotomyMData A B C := by
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

end DiophCompression.SemanticQuadraticSingular
