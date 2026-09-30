/-
  QuotientRankOne.lean — r11 (GPT r10 必須H): the quotient-rank-1 leaf. Statements frozen in
  QuotientRankOne_STATEMENTS.lean before proofs. (s11, claude.ai direct.)
  The analytic core is the r08 theorem `dichotomy2_rank_one_normal` (Dichotomy2 A B₁ B₂ k 0 0,
  B₂ free, (l, m₁, m₂, q) quantified): identifying B₂ = b, m₂ = μ, v = w gives exactly the
  coupled rank-1 moving-modulus dichotomy. This file is the translation layer.
-/
import DiophCompression.SemanticQuadraticSingular.DefsSingularGeneral
import DiophCompression.SemanticQuadraticTwoWitness.RankOne
import DiophCompression.SemanticQuadraticTwoWitness.RankOneNormalData

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix
open DiophCompression.SemanticQuadraticTwoWitness

/-- GPT r10 必須H theorem 1 (name verbatim): the k = 1 singular fiber polynomial in scalar
normal form. -/
theorem quotient_rank_one_normal_form (A : ℤ) (B : Fin 1 → ℤ) (C : Matrix (Fin 1) (Fin 1) ℤ)
    (b l : ℤ) (m : Fin 1 → ℤ) (μ q c : ℤ) (u : Fin 1 → ℤ) (w : ℤ) :
    fqSG A B C b l m μ q c u w
      = A * c ^ 2 + B 0 * (c * u 0) + C 0 0 * u 0 ^ 2 + l * c + m 0 * u 0 + q
        + (b * c + μ) * w := by
  simp only [fqSG, fqM, witnessQuad, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
  ring

/-- GPT r10 必須H theorem 2 (name verbatim): the scalar coupled rank-1 dichotomy, uniform in the
moving-modulus slope b, with no r = 2 / r = 3 tuple dependence. -/
theorem quotient_rank_one_coupled_dichotomy (A B₁ C₁₁ b : ℤ) (hC : C₁₁ ≠ 0) :
    ∃ K : ℕ, ∀ l m₁ μ q : ℤ,
      ({c : ℕ | ∃ u w : ℤ,
        A * (c : ℤ) ^ 2 + B₁ * ((c : ℤ) * u) + C₁₁ * u ^ 2 + l * c + m₁ * u + q
          + (b * c + μ) * w = 0} : Set ℕ).Infinite ∨
      ∀ c ∈ ({c : ℕ | ∃ u w : ℤ,
        A * (c : ℤ) ^ 2 + B₁ * ((c : ℤ) * u) + C₁₁ * u ^ 2 + l * c + m₁ * u + q
          + (b * c + μ) * w = 0} : Set ℕ),
        (c : ℤ) ≤ (K : ℤ) * ((1 + |l| + |m₁| + |μ|) ^ 2 + |q|) := by
  obtain ⟨K, hK⟩ := dichotomy2_rank_one_normal A B₁ b C₁₁ hC
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

/-- GPT r10 必須H theorem 3 (name verbatim): the quotient-rank-1 dichotomy, i.e. `DichotomySG`
at k = 1 for every (A, B, C, b) with nondegenerate block. -/
theorem quotient_rank_one_dichotomy (A : ℤ) (B : Fin 1 → ℤ) (C : Matrix (Fin 1) (Fin 1) ℤ)
    (b : ℤ) (hC : C 0 0 ≠ 0) : DichotomySG A B C b := by
  obtain ⟨K, hK⟩ := quotient_rank_one_coupled_dichotomy A (B 0) (C 0 0) b hC
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


/-! ### s28 必須F step 3 -/

/-- The coupled rank-one quotient, in data form. -/
theorem quotient_rank_one_coupled_dichotomy_data (A B₁ C₁₁ b : ℤ) (hC : C₁₁ ≠ 0) :
    ∃ K : ℕ, ∀ l m₁ μ q : ℤ,
      Nonempty (DiophCompression.StructuredFamily ({c : ℕ | ∃ u w : ℤ,
        A * (c : ℤ) ^ 2 + B₁ * ((c : ℤ) * u) + C₁₁ * u ^ 2 + l * c + m₁ * u + q
          + (b * c + μ) * w = 0} : Set ℕ)) ∨
      ∀ c ∈ ({c : ℕ | ∃ u w : ℤ,
        A * (c : ℤ) ^ 2 + B₁ * ((c : ℤ) * u) + C₁₁ * u ^ 2 + l * c + m₁ * u + q
          + (b * c + μ) * w = 0} : Set ℕ),
        (c : ℤ) ≤ (K : ℤ) * ((1 + |l| + |m₁| + |μ|) ^ 2 + |q|) := by
  obtain ⟨K, hK⟩ := dichotomy2_rank_one_normal_data A B₁ b C₁₁ hC
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
theorem quotient_rank_one_dichotomy_data (A : ℤ) (B : Fin 1 → ℤ) (C : Matrix (Fin 1) (Fin 1) ℤ)
    (b : ℤ) (hC : C 0 0 ≠ 0) : DichotomySGData A B C b := by
  obtain ⟨K, hK⟩ := quotient_rank_one_coupled_dichotomy_data A (B 0) (C 0 0) b hC
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

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.quotient_rank_one_normal_form
#print axioms DiophCompression.SemanticQuadraticSingular.quotient_rank_one_coupled_dichotomy
#print axioms DiophCompression.SemanticQuadraticSingular.quotient_rank_one_dichotomy
