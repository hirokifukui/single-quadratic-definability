/-
  DiophCompression/SemanticQuadraticTwoWitness/RankOneUncoupledData.lean — APAL Structural Theory Gate 5,
  必須F step 3 (rank-one uncoupled layer) (s28, 2026-09-02, claude.ai direct).

  The first assembly layer above the leaves, in data-carrying form, and the first place where the
  set-generic family type pays off: the `m₂ = 0` branch is the one-witness fibre under a set EQUALITY, so
  the certificate travels by rewriting the set, and the `m₂ ≠ 0` branch is the periodic family already
  proved in s28. Nothing here re-does arithmetic; the layer is pure transport. No sorry; std-3.
-/
import DiophCompression.SemanticQuadraticTwoWitness.RankOne
import DiophCompression.SemanticQuadratic.DegenerateDichotomyData
import DiophCompression.PeriodicProgressionData

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadratic

/-- The two-witness dichotomy in data-carrying form. -/
def Dichotomy2Data (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) : Prop :=
  ∃ K : ℕ, ∀ l m₁ m₂ q : ℤ,
    Nonempty (DiophCompression.StructuredFamily (fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q)) ∨
      ∀ c ∈ fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q, (c : ℤ) ≤ fbound2 K l m₁ m₂ q

/-- The data form implies the sealed one. -/
theorem dichotomy2_of_dichotomy2Data {A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ}
    (h : Dichotomy2Data A B₁ B₂ C₁₁ C₁₂ C₂₂) : Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun l m₁ m₂ q => ?_⟩
  rcases hK l m₁ m₂ q with hF | hb
  · exact Or.inl (hF.elim fun F => DiophCompression.infinite_of_structuredFamily F)
  · exact Or.inr hb

/-- Branch B1b, complete: `m₂ = 0` transports the (now unconditional) one-witness certificate along the
    set equality; `m₂ ≠ 0` is the periodic family. -/
theorem rank_one_uncoupled_data (A B₁ k : ℤ) : Dichotomy2Data A B₁ 0 k 0 0 := by
  obtain ⟨K, hK⟩ := fiber_dichotomy_data_full A B₁ k
  refine ⟨K, fun l m₁ m₂ q => ?_⟩
  by_cases hm₂ : m₂ = 0
  · subst hm₂
    have hset : fiberSet2 A B₁ 0 k 0 0 l m₁ 0 q = fiberSet A B₁ k l m₁ q := by
      ext c
      simp only [fiberSet2, fiberSet, Set.mem_setOf_eq]
      constructor
      · rintro ⟨u, v, huv⟩; exact ⟨u, by rw [fq2_rank_one] at huv; unfold fq qOne at *; linear_combination huv⟩
      · rintro ⟨u, hu⟩; exact ⟨u, 0, by rw [fq2_rank_one]; unfold fq qOne at *; linear_combination hu⟩
    rw [hset]
    rcases hK l m₁ q with hF | hbd
    · exact Or.inl (hF.elim fun F => ⟨F.toStructuredFamily⟩)
    · refine Or.inr (fun c hc => ?_)
      have := hbd c hc
      unfold fbound at this; unfold fbound2
      simpa using this
  · rcases rank_one_uncoupled_periodic_data A B₁ k l m₁ m₂ q hm₂ with hF | hemp
    · exact Or.inl (hF.elim fun F => ⟨DiophCompression.PeriodicProgression.toStructuredFamily F⟩)
    · right
      intro c hc
      rw [hemp] at hc
      exact absurd hc (Set.notMem_empty c)

/-- And it still implies the sealed `rank_one_uncoupled`. -/
theorem rank_one_uncoupled_of_data (A B₁ k : ℤ) : Dichotomy2 A B₁ 0 k 0 0 :=
  dichotomy2_of_dichotomy2Data (rank_one_uncoupled_data A B₁ k)

end DiophCompression.SemanticQuadraticTwoWitness

#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_of_dichotomy2Data
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_one_uncoupled_data
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_one_uncoupled_of_data
