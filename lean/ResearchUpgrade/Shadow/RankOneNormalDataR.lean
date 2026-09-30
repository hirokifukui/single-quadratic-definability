/-
  Shadow/RankOneNormalDataR.lean — ray-carrying shadow of the rank-one normal form.
  Verbatim transplant of DiophCompression/SemanticQuadraticTwoWitness/RankOneNormalData.lean,
  with `StructuredFamily` → `StructuredFamilyR`. The moving-modulus branch B1c now carries the
  rank-one coupled production ray `rankOneRay2W`; the base point/witness/divisibility feeding the
  ray come from the same `hex`/`mem_rank_one_iff` data the baseline already had.
  The family-free helper `b1c_orbit` is reused verbatim from the baseline.
-/
import ResearchUpgrade.Shadow.FamilyR
import ResearchUpgrade.Shadow.RankOneUncoupledDataR
import ResearchUpgrade.RankOnePowerRay
import DiophCompression.SemanticQuadraticTwoWitness.RankOneNormalData

namespace DiophCompression.ResearchUpgrade

open DiophCompression.SemanticQuadratic DiophCompression.SemanticQuadraticTwoWitness

theorem dichotomy2DataR_of_unimodular (A B₁ B₂ C₁₁ C₁₂ C₂₂ p r s t : ℤ) (hdet : p * t - r * s = 1 ∨ p * t - r * s = -1)
    (h : Dichotomy2DataR A (B₁ * p + B₂ * s) (B₁ * r + B₂ * t)
          (C₁₁ * p ^ 2 + C₁₂ * p * s + C₂₂ * s ^ 2)
          (2 * C₁₁ * p * r + C₁₂ * (p * t + r * s) + 2 * C₂₂ * s * t)
          (C₁₁ * r ^ 2 + C₁₂ * r * t + C₂₂ * t ^ 2)) :
    Dichotomy2DataR A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K * (1 + p.natAbs + r.natAbs + s.natAbs + t.natAbs) ^ 2, ?_⟩
  intro l m₁ m₂ q
  have hEq : fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q =
      fiberSet2 A (B₁ * p + B₂ * s) (B₁ * r + B₂ * t)
        (C₁₁ * p ^ 2 + C₁₂ * p * s + C₂₂ * s ^ 2)
        (2 * C₁₁ * p * r + C₁₂ * (p * t + r * s) + 2 * C₂₂ * s * t)
        (C₁₁ * r ^ 2 + C₁₂ * r * t + C₂₂ * t ^ 2)
        l (m₁ * p + m₂ * s) (m₁ * r + m₂ * t) q := by
    ext c
    simp only [fiberSet2, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, v, huv⟩
      rcases hdet with hε | hε
      · refine ⟨t * u - r * v, p * v - s * u, ?_⟩
        have key := fq2_subst A B₁ B₂ C₁₁ C₁₂ C₂₂ p r s t l m₁ m₂ q (c : ℤ) (t * u - r * v) (p * v - s * u)
        rw [← key]
        have hu : p * (t * u - r * v) + r * (p * v - s * u) = u := by linear_combination u * hε
        have hv : s * (t * u - r * v) + t * (p * v - s * u) = v := by linear_combination v * hε
        rw [hu, hv]; exact huv
      · refine ⟨r * v - t * u, s * u - p * v, ?_⟩
        have key := fq2_subst A B₁ B₂ C₁₁ C₁₂ C₂₂ p r s t l m₁ m₂ q (c : ℤ) (r * v - t * u) (s * u - p * v)
        rw [← key]
        have hu : p * (r * v - t * u) + r * (s * u - p * v) = u := by linear_combination (-u) * hε
        have hv : s * (r * v - t * u) + t * (s * u - p * v) = v := by linear_combination (-v) * hε
        rw [hu, hv]; exact huv
    · rintro ⟨u, v, huv⟩
      exact ⟨p * u + r * v, s * u + t * v, by rw [fq2_subst]; exact huv⟩
  rcases hK l (m₁ * p + m₂ * s) (m₁ * r + m₂ * t) q with hF | hBd
  · left; rw [hEq]; exact hF
  · right; intro c hc
    rw [hEq] at hc
    exact le_trans (hBd c hc) (fbound2_mono K p r s t l m₁ m₂ q)
/-! ### Branch B1c: the step data iterated into an orbit (with its production ray) -/

/-- Branch B1c in ray-carrying data form: either every fibre point has non-positive modulus (bounded, the
    sealed argument), or the orbit is a moving-modulus family carrying the rank-one coupled ray. -/
theorem rank_one_coupled_pos_dataR (A B₁ B₂ k : ℤ) (hk : k ≠ 0) (hB₂ : 0 < B₂) :
    Dichotomy2DataR A B₁ B₂ k 0 0 := by
  refine ⟨1, fun l m₁ m₂ q => ?_⟩
  by_cases hex : ∃ c ∈ fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q, 0 < B₂ * (c : ℤ) + m₂
  · left
    obtain ⟨c₀, hc₀, ht₀⟩ := hex
    obtain ⟨cf, pr, hprime, hrec, hmem, hmono, hmpos, hpgt, hpmod⟩ :=
      b1c_orbit A B₁ B₂ k l m₁ m₂ q hB₂ hk c₀ hc₀ ht₀
    have hmf : (0 : ℤ) < 8 * max 1 |dPrime A B₁ B₂ k l m₁ m₂ q| * |2 * k| := by
      have h1 : (1 : ℤ) ≤ max 1 |dPrime A B₁ B₂ k l m₁ m₂ q| := le_max_left _ _
      have h2 : (0 : ℤ) < |2 * k| := abs_pos.mpr (mul_ne_zero two_ne_zero hk)
      positivity
    obtain ⟨u₀, hdiv₀⟩ := (mem_rank_one_iff A B₁ B₂ k l m₁ m₂ q c₀).mp hc₀
    exact ⟨StructuredFamilyR.ofMoving B₂ m₂
      (8 * max 1 |dPrime A B₁ B₂ k l m₁ m₂ q| * |2 * k|) hB₂ hmf cf pr hprime hmpos hpgt hpmod
      hrec hmem hmono
      (rankOneRay2W A B₁ B₂ k l m₁ m₂ q hB₂ hk c₀ u₀ ht₀ hdiv₀)
      (rankOne_exponentialInjection_castSet A B₁ B₂ k l m₁ m₂ q c₀ u₀ hB₂ hk ht₀ hdiv₀)⟩
  · right
    push Not at hex
    intro c hc
    have h := hex c hc
    have hc0 : (0 : ℤ) ≤ c := by positivity
    have h1 : (c : ℤ) ≤ B₂ * c := le_mul_of_one_le_left hc0 (by omega)
    have h2 : (c : ℤ) ≤ |m₂| := by linarith [neg_le_abs m₂]
    unfold fbound2
    have hl := abs_nonneg l; have hm₁ := abs_nonneg m₁; have hm₂ := abs_nonneg m₂; have hq := abs_nonneg q
    push_cast
    nlinarith
/-! ### Assembly of the rank-one normal form, in ray-carrying data form -/

theorem dichotomy2_rank_one_normal_dataR (A B₁ B₂ k : ℤ) (hk : k ≠ 0) :
    Dichotomy2DataR A B₁ B₂ k 0 0 := by
  rcases lt_trichotomy B₂ 0 with hneg | hzero | hpos
  · -- branch B1a: the witness reflection v ↦ −v
    have h := rank_one_coupled_pos_dataR A B₁ (-B₂) k hk (by linarith)
    refine dichotomy2DataR_of_unimodular A B₁ B₂ k 0 0 1 0 0 (-1) (Or.inr (by norm_num)) ?_
    norm_num
    exact h
  · subst hzero; exact rank_one_uncoupled_dataR A B₁ k
  · exact rank_one_coupled_pos_dataR A B₁ B₂ k hk hpos

theorem dichotomy2_rank_one_dataR (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ = 0)
    (hne : ¬ (C₁₁ = 0 ∧ C₁₂ = 0 ∧ C₂₂ = 0)) : Dichotomy2DataR A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  obtain ⟨p, r, s, t, k, hdet, hk, h1, h2, h3⟩ := rank_one_normal_form C₁₁ C₁₂ C₂₂ hd hne
  refine dichotomy2DataR_of_unimodular A B₁ B₂ C₁₁ C₁₂ C₂₂ p r s t hdet ?_
  rw [h1, h2, h3]
  exact dichotomy2_rank_one_normal_dataR A _ _ k hk

end DiophCompression.ResearchUpgrade
