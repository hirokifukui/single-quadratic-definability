/-
  Shadow/MovingModulusGeneralR.lean — ray-carrying shadow of the k₀ ≥ 2 moving-modulus leaf.
  Verbatim transplant of MovingModulusGeneral.lean:675–793, with `StructuredFamily`
  → `StructuredFamilyR` and `DichotomySGData` → `DichotomySGDataR`.

  The b > 0 branch (`dichotomySG_pos_dataR`) is the only place a moving-modulus (kind 2) family is
  emitted, so it carries the production ray `movingRaySG` built from the same base point/witness the
  `hex` obtain already supplies. The b < 0 branch is a witness-reflection set equality; the b = 0
  branch never moves (matrix fibre via the full-rank shadow, or the μ-periodic family), so both lift
  for free. The three private baseline helpers this file needs (`aux_nonpositive_bound`,
  `mem_fiberSetSG_iff_dvd`, `aux_fiberSetSG_neg`) are re-declared verbatim with a `ru_` prefix.
  `sg_pos_orbit` and `dichotomySG_zero_periodic_data` are public and family-free, so reused as is.
-/
import ResearchUpgrade.Shadow.FamilyR
import ResearchUpgrade.Shadow.DefsSingularGeneralR
import ResearchUpgrade.Shadow.FullRankAssemblyDataR
import ResearchUpgrade.MovingPowerRay
import DiophCompression.SemanticQuadraticSingular.MovingModulusGeneral

namespace DiophCompression.ResearchUpgrade

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticSingular
open DiophCompression.SemanticQuadraticTwoWitness (periodic_infinite_or_empty)

variable {k : ℕ}

theorem ru_aux_nonpositive_bound (b μ c : ℤ) (hb : 0 < b) (h : b * c + μ ≤ 0) : c ≤ |μ| := by
  have hμ : -μ ≤ |μ| := neg_le_abs μ
  rcases le_or_gt c 0 with hc | hc
  · exact le_trans hc (abs_nonneg μ)
  · have : c ≤ b * c := by nlinarith
    linarith

theorem ru_mem_fiberSetSG_iff_dvd (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (c : ℕ) :
    c ∈ fiberSetSG A B C b l m μ q ↔
      ∃ u : Fin k → ℤ, (b * (c : ℤ) + μ) ∣ fqM A B C l m q (c : ℤ) u := by
  simp only [fiberSetSG, Set.mem_setOf_eq, fqSG]
  constructor
  · rintro ⟨u, w, hw⟩
    exact ⟨u, (exists_w_iff_dvd _ _).mp ⟨w, hw⟩⟩
  · rintro ⟨u, hu⟩
    obtain ⟨w, hw⟩ := (exists_w_iff_dvd _ _).mpr hu
    exact ⟨u, w, hw⟩

theorem ru_aux_fiberSetSG_neg (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) :
    fiberSetSG A B C b l m μ q = fiberSetSG A B C (-b) l m (-μ) q := by
  ext c
  simp only [fiberSetSG, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, w, h⟩
    exact ⟨u, -w, by simp only [fqSG] at h ⊢; linear_combination h⟩
  · rintro ⟨u, w, h⟩
    exact ⟨u, -w, by simp only [fqSG] at h ⊢; linear_combination h⟩

theorem dichotomySG_pos_dataR (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b : ℤ) (hk : 2 ≤ k) (hN : (C + Cᵀ).det ≠ 0) (hb : 0 < b) : DichotomySGDataR A B C b := by
  refine ⟨1, fun l m μ q => ?_⟩
  by_cases hex : ∃ c₀ : ℕ,
      (∃ u : Fin k → ℤ, (b * (c₀ : ℤ) + μ) ∣ fqM A B C l m q (c₀ : ℤ) u)
        ∧ 0 < b * (c₀ : ℤ) + μ
  · left
    obtain ⟨c₀, ⟨u₀, hdiv₀⟩, hpos₀⟩ := hex
    obtain ⟨cf, pr, hprime, hrec, hmem, hmono, hmpos, hpgt, hpmod⟩ :=
      sg_pos_orbit hk A B C b l m μ q hb hN c₀ u₀ hdiv₀ hpos₀
    have hmf : (0 : ℤ) < 2 * |(C + Cᵀ).det| := by
      have : (0 : ℤ) < |(C + Cᵀ).det| := abs_pos.mpr hN
      positivity
    exact ⟨StructuredFamilyR.ofMoving b μ (2 * |(C + Cᵀ).det|) hb hmf
      cf pr hprime hmpos hpgt hpmod hrec hmem hmono (movingRaySG hk A B C b l m μ q hb hN c₀ u₀ hdiv₀ hpos₀)
      (moving_exponentialInjection_castSet hk A B C b l m μ q c₀ u₀ hb hN hpos₀ hdiv₀)⟩
  · right
    push_neg at hex
    intro c hc
    rw [ru_mem_fiberSetSG_iff_dvd] at hc
    have hle : b * (c : ℤ) + μ ≤ 0 := hex c hc
    have h1 := ru_aux_nonpositive_bound b μ c hb hle
    unfold fboundSG
    have hsum : (0 : ℤ) ≤ ∑ i, |m i| := Finset.sum_nonneg (fun i _ => abs_nonneg (m i))
    have h2 : |μ| ≤ (1 + |l| + ∑ i, |m i| + |μ|) ^ 2 + |q| := by
      nlinarith [abs_nonneg l, hsum, abs_nonneg μ, abs_nonneg q]
    simp only [Nat.cast_one, one_mul]
    linarith

/-- Branch b < 0, in data form: the witness reflection `w ↦ −w` is a set equality. -/
theorem aux_dichotomySG_neg_dataR (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b : ℤ) (h : DichotomySGDataR A B C (-b)) : DichotomySGDataR A B C b := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun l m μ q => ?_⟩
  rw [ru_aux_fiberSetSG_neg]
  rcases hK l m (-μ) q with hF | hBd
  · exact Or.inl hF
  · right
    intro c hc
    have := hBd c hc
    unfold fboundSG at this ⊢
    rw [abs_neg] at this
    exact this


/-- Branch b = 0, in data form: `μ = 0` is the matrix-level fibre (a set equality, and the full-rank
    block is unconditional since s28), `μ ≠ 0` is the periodic family. -/
theorem dichotomySG_zero_dataR (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (hk : 2 ≤ k) (hN : (C + Cᵀ).det ≠ 0) : DichotomySGDataR A B C 0 := by
  have hNw : (DiophCompression.SemanticQuadraticMatrix.witnessGram C).det ≠ 0 := by
    simpa [DiophCompression.SemanticQuadraticMatrix.witnessGram] using hN
  have hij : (⟨0, by omega⟩ : Fin k) ≠ (⟨1, by omega⟩ : Fin k) := by
    simp [Fin.ext_iff]
  obtain ⟨K₀, hK₀⟩ :=
    full_rank_dichotomy_all_data_full A B C hNw
      (⟨0, by omega⟩ : Fin k) (⟨1, by omega⟩ : Fin k) hij
  refine ⟨K₀ + 1, fun l m μ q => ?_⟩
  by_cases hμ : μ = 0
  · subst hμ
    have hset : fiberSetSG A B C 0 l m 0 q
        = DiophCompression.SemanticQuadraticMatrix.fiberSetM A B C l m q := by
      ext c
      simp only [fiberSetSG, DiophCompression.SemanticQuadraticMatrix.fiberSetM,
        Set.mem_setOf_eq, fqSG]
      constructor
      · rintro ⟨u, w, h⟩; exact ⟨u, by simpa using h⟩
      · rintro ⟨u, h⟩; exact ⟨u, 0, by simpa using h⟩
    rw [hset]
    rcases hK₀ l m q with hF | hBd
    · exact Or.inl hF
    · right
      intro c hc
      have hcb := hBd c hc
      have hb1 : (K₀ : ℤ) * ((1 + |l| + ∑ i, |m i|) ^ 2 + |q|)
          ≤ fboundSG (K₀ + 1) l m 0 q := by
        unfold fboundSG
        simp only [abs_zero, add_zero]
        have hshape : (0 : ℤ) ≤ (1 + |l| + ∑ i, |m i|) ^ 2 + |q| := by positivity
        push_cast
        nlinarith [hshape, Int.natCast_nonneg K₀]
      linarith [hcb, hb1]
  · rcases dichotomySG_zero_periodic_data A B C l m μ q hμ with hF | hE
    · exact Or.inl (hF.elim fun F => ⟨StructuredFamilyR.ofPeriodic F⟩)
    · right
      rw [hE]
      intro c hc
      exact absurd hc (Set.notMem_empty c)

/-! ### s28 必須F step 3: the k₀ ≥ 2 quotient, at the data level.

    `dichotomySG_pos`, `aux_dichotomySG_neg` and `dichotomySG_zero` are private to this file, so their
    data versions have to live here too. The dispatch is proved now and the three sub-branches are
    exposed as hypotheses; `dichotomySG_zero_periodic_data` (B3, s28) already supplies the material for
    the `b = 0` one. -/

theorem quotient_rank_ge_two_moving_dichotomy_dataR (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b : ℤ) (hC : (C + Cᵀ).det ≠ 0) :
    DichotomySGDataR A B C b := by
  rcases lt_trichotomy b 0 with hn | hz | hp
  · exact aux_dichotomySG_neg_dataR A B C b (dichotomySG_pos_dataR A B C (-b) hk hC (by linarith))
  · subst hz; exact dichotomySG_zero_dataR A B C hk hC
  · exact dichotomySG_pos_dataR A B C b hk hC hp


end DiophCompression.ResearchUpgrade
