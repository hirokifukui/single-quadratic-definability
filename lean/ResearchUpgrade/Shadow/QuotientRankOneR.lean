/-
  Shadow/QuotientRankOneR.lean — ray-carrying shadow of the quotient-rank-1 leaf.
  Verbatim transplant of the two data theorems of
  DiophCompression/SemanticQuadraticSingular/QuotientRankOne.lean, with `StructuredFamily`
  → `StructuredFamilyR`. The analytic core (`dichotomy2_rank_one_normal_dataR`) already carries
  the rank-one coupled ray; this file is the translation layer (pure set-equality transport).
  The family-free helper `quotient_rank_one_normal_form` is reused verbatim from the baseline.
-/
import ResearchUpgrade.Shadow.FamilyR
import ResearchUpgrade.Shadow.DefsSingularGeneralR
import ResearchUpgrade.Shadow.RankOneNormalDataR
import DiophCompression.SemanticQuadraticSingular.QuotientRankOne

namespace DiophCompression.ResearchUpgrade

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticSingular
open DiophCompression.SemanticQuadraticTwoWitness


/-- The coupled rank-one quotient, in data form. -/
theorem quotient_rank_one_coupled_dichotomy_dataR (A B₁ C₁₁ b : ℤ) (hC : C₁₁ ≠ 0) :
    ∃ K : ℕ, ∀ l m₁ μ q : ℤ,
      Nonempty (StructuredFamilyR ({c : ℕ | ∃ u w : ℤ,
        A * (c : ℤ) ^ 2 + B₁ * ((c : ℤ) * u) + C₁₁ * u ^ 2 + l * c + m₁ * u + q
          + (b * c + μ) * w = 0} : Set ℕ)) ∨
      ∀ c ∈ ({c : ℕ | ∃ u w : ℤ,
        A * (c : ℤ) ^ 2 + B₁ * ((c : ℤ) * u) + C₁₁ * u ^ 2 + l * c + m₁ * u + q
          + (b * c + μ) * w = 0} : Set ℕ),
        (c : ℤ) ≤ (K : ℤ) * ((1 + |l| + |m₁| + |μ|) ^ 2 + |q|) := by
  obtain ⟨K, hK⟩ := dichotomy2_rank_one_normal_dataR A B₁ b C₁₁ hC
  refine ⟨K, fun l m₁ μ q => ?_⟩
  have hset : ({c : ℕ | ∃ u w : ℤ,
      A * (c : ℤ) ^ 2 + B₁ * ((c : ℤ) * u) + C₁₁ * u ^ 2 + l * c + m₁ * u + q
        + (b * c + μ) * w = 0} : Set ℕ) = fiberSet2 A B₁ b C₁₁ 0 0 l m₁ μ q := by
    ext c
    simp only [Set.mem_setOf_eq, fiberSet2, fq2]
    constructor
    · rintro ⟨u, w, h⟩
      exact ⟨u, w, by linear_combination h⟩
    · rintro ⟨u, v, h⟩
      exact ⟨u, v, by linear_combination h⟩
  rcases hK l m₁ μ q with h | h
  · left
    rw [hset]
    exact h
  · right
    intro c hc
    rw [hset] at hc
    have hb := h c hc
    simpa [fbound2] using hb

/-- The `k₀ = 1` leaf of the singular block, in data form. -/
theorem quotient_rank_one_dichotomy_dataR (A : ℤ) (B : Fin 1 → ℤ) (C : Matrix (Fin 1) (Fin 1) ℤ)
    (b : ℤ) (hC : C 0 0 ≠ 0) : DichotomySGDataR A B C b := by
  obtain ⟨K, hK⟩ := quotient_rank_one_coupled_dichotomy_dataR A (B 0) (C 0 0) b hC
  refine ⟨K, fun l m μ q => ?_⟩
  have hset : fiberSetSG A B C b l m μ q = ({c : ℕ | ∃ u w : ℤ,
      A * (c : ℤ) ^ 2 + B 0 * ((c : ℤ) * u) + C 0 0 * u ^ 2 + l * c + m 0 * u + q
        + (b * c + μ) * w = 0} : Set ℕ) := by
    ext c
    simp only [fiberSetSG, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, w, h⟩
      refine ⟨u 0, w, ?_⟩
      rw [quotient_rank_one_normal_form] at h
      linear_combination h
    · rintro ⟨u0, w, h⟩
      refine ⟨fun _ => u0, w, ?_⟩
      rw [quotient_rank_one_normal_form]
      linear_combination h
  have hfb : fboundSG K l m μ q = (K : ℤ) * ((1 + |l| + |m 0| + |μ|) ^ 2 + |q|) := by
    simp [fboundSG, Fin.sum_univ_one]
  rcases hK l (m 0) μ q with h | h
  · left
    rw [hset]
    exact h
  · right
    intro c hc
    rw [hset] at hc
    rw [hfb]
    exact h c hc

end DiophCompression.ResearchUpgrade
