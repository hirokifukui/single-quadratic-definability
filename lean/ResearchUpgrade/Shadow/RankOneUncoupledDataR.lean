/-
  Shadow/RankOneUncoupledDataR.lean — ray-carrying shadow of the rank-one uncoupled layer.
  Verbatim transplant of DiophCompression/SemanticQuadraticTwoWitness/RankOneUncoupledData.lean,
  with `StructuredFamily` → `StructuredFamilyR`. Pure transport: the `m₂ = 0` branch reuses the
  one-witness certificate (now ray-carrying, non-moving) along a set equality; the `m₂ ≠ 0` branch
  is the periodic family, which lifts for free.
-/
import ResearchUpgrade.Shadow.FamilyR
import ResearchUpgrade.Shadow.OneWitnessFamilyDataR
import DiophCompression.SemanticQuadraticTwoWitness.RankOne
import DiophCompression.SemanticQuadratic.DegenerateDichotomyData
import DiophCompression.PeriodicProgressionData

namespace DiophCompression.ResearchUpgrade

open DiophCompression.SemanticQuadratic DiophCompression.SemanticQuadraticTwoWitness

/-- The two-witness dichotomy in ray-carrying data-carrying form. -/
def Dichotomy2DataR (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) : Prop :=
  ∃ K : ℕ, ∀ l m₁ m₂ q : ℤ,
    Nonempty (StructuredFamilyR (fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q)) ∨
      ∀ c ∈ fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q, (c : ℤ) ≤ fbound2 K l m₁ m₂ q

/-- Branch B1b, complete: `m₂ = 0` transports the (now unconditional) one-witness certificate along the
    set equality; `m₂ ≠ 0` is the periodic family. -/
theorem rank_one_uncoupled_dataR (A B₁ k : ℤ) : Dichotomy2DataR A B₁ 0 k 0 0 := by
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
    · exact Or.inl (hF.elim fun F => ⟨OneWitnessFamilyData.toStructuredFamilyR F⟩)
    · refine Or.inr (fun c hc => ?_)
      have := hbd c hc
      unfold fbound at this; unfold fbound2
      simpa using this
  · rcases rank_one_uncoupled_periodic_data A B₁ k l m₁ m₂ q hm₂ with hF | hemp
    · exact Or.inl (hF.elim fun F => ⟨StructuredFamilyR.ofPeriodic F⟩)
    · right
      intro c hc
      rw [hemp] at hc
      exact absurd hc (Set.notMem_empty c)

end DiophCompression.ResearchUpgrade
