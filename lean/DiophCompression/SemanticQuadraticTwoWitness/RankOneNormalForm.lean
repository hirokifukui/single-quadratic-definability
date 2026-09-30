/-
  DiophCompression/SemanticQuadraticTwoWitness/RankOneNormalForm.lean — rank-1 unimodular normal form (2W swarm
  2026-08-27 worker W3a, PASS; re-audited by claude.ai s8). Body verbatim from the swarm file; only this header added.
-/
import DiophCompression.SemanticQuadraticTwoWitness.Bridge2W

namespace DiophCompression.SemanticQuadraticTwoWitness
open DiophCompression.SemanticQuadraticGeneral

theorem rank_one_normal_form (C₁₁ C₁₂ C₂₂ : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ = 0)
    (hne : ¬ (C₁₁ = 0 ∧ C₁₂ = 0 ∧ C₂₂ = 0)) :
    ∃ p r s t k : ℤ, (p * t - r * s = 1 ∨ p * t - r * s = -1) ∧ k ≠ 0 ∧
      C₁₁ * p ^ 2 + C₁₂ * p * s + C₂₂ * s ^ 2 = k ∧
      2 * C₁₁ * p * r + C₁₂ * (p * t + r * s) + 2 * C₂₂ * s * t = 0 ∧
      C₁₁ * r ^ 2 + C₁₂ * r * t + C₂₂ * t ^ 2 = 0 := by
  unfold discW at hd
  by_cases hC11 : C₁₁ = 0
  · -- C₁₁ = 0 ⇒ C₁₂ = 0 ⇒ C₂₂ ≠ 0
    subst hC11
    have hmul : C₁₂ * C₁₂ = 0 := by linear_combination hd
    have hC12 : C₁₂ = 0 := by rcases mul_eq_zero.mp hmul with h | h <;> exact h
    subst hC12
    have hC22 : C₂₂ ≠ 0 := fun h => hne ⟨rfl, rfl, h⟩
    exact ⟨0, 1, 1, 0, C₂₂, Or.inr (by ring), hC22, by ring, by ring, by ring⟩
  · -- C₁₁ ≠ 0.  Radical vector (r₀, t₀) = (C₁₂, -2 C₁₁).
    have ht0 : (-2 * C₁₁) ≠ 0 := fun h => hC11 (by omega)
    have hgcdpos : 0 < Int.gcd C₁₂ (-2 * C₁₁) := Int.gcd_pos_iff.mpr (Or.inr ht0)
    obtain ⟨g, r, t, hg, hrt, hr₀, ht₀⟩ := Int.exists_gcd_one' hgcdpos
    -- hr₀ : C₁₂ = r * ↑g ,  ht₀ : -2 * C₁₁ = t * ↑g ,  hrt : Int.gcd r t = 1
    set G : ℤ := (g : ℤ) with hG
    have hGne : G ≠ 0 := by rw [hG]; exact_mod_cast hg.ne'
    have e1 : r * G = C₁₂ := by rw [hG]; linarith [hr₀]
    have e2 : t * G = -2 * C₁₁ := by rw [hG]; linarith [ht₀]
    -- W(r,t) = 0
    have hW2 : C₁₁ * r ^ 2 + C₁₂ * r * t + C₂₂ * t ^ 2 = 0 := by
      have hrad : C₁₁ * (r * G) ^ 2 + C₁₂ * (r * G) * (t * G) + C₂₂ * (t * G) ^ 2 = 0 := by
        rw [e1, e2]; linear_combination (-C₁₁) * hd
      have hfac : G ^ 2 * (C₁₁ * r ^ 2 + C₁₂ * r * t + C₂₂ * t ^ 2) = 0 := by
        linear_combination hrad
      exact (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 hGne)
    -- radial direction:  2 C₁₁ r + C₁₂ t = 0
    have hdir : 2 * C₁₁ * r + C₁₂ * t = 0 := by
      have hrad2 : G * (2 * C₁₁ * r + C₁₂ * t) = 0 := by
        linear_combination (2 * C₁₁) * e1 + C₁₂ * e2
      exact (mul_eq_zero.mp hrad2).resolve_left hGne
    -- Bezout:  r*a + t*b = 1
    have hbez : (Int.gcd r t : ℤ) = r * Int.gcdA r t + t * Int.gcdB r t := Int.gcd_eq_gcd_ab r t
    rw [hrt] at hbez
    set a : ℤ := Int.gcdA r t with ha
    set b : ℤ := Int.gcdB r t with hb
    push_cast at hbez
    -- hbez : (1 : ℤ) = r * a + t * b
    have hdet : b * t - r * (-a) = 1 := by linarith [hbez]
    -- mixed term = 0
    have hmix : 2 * C₁₁ * b * r + C₁₂ * (b * t + r * (-a)) + 2 * C₂₂ * (-a) * t = 0 := by
      have hid : 4 * C₁₁ * (2 * C₁₁ * b * r + C₁₂ * (b * t + r * (-a)) + 2 * C₂₂ * (-a) * t)
          = 2 * (2 * C₁₁ * b + C₁₂ * (-a)) * (2 * C₁₁ * r + C₁₂ * t)
            - 2 * (-a) * t * (C₁₂ ^ 2 - 4 * C₁₁ * C₂₂) := by ring
      rw [hdir, hd] at hid
      have h4 : (4 * C₁₁) * (2 * C₁₁ * b * r + C₁₂ * (b * t + r * (-a)) + 2 * C₂₂ * (-a) * t) = 0 := by
        linear_combination hid
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd (show C₁₁ = 0 by omega) hC11
      · exact h
    -- k := W(b, -a)
    refine ⟨b, r, -a, t, C₁₁ * b ^ 2 + C₁₂ * b * (-a) + C₂₂ * (-a) ^ 2,
      Or.inl hdet, ?_, rfl, hmix, hW2⟩
    -- k ≠ 0
    intro hk
    apply hC11
    have hrec : C₁₁ * (b * t - r * (-a)) ^ 2
        = (C₁₁ * b ^ 2 + C₁₂ * b * (-a) + C₂₂ * (-a) ^ 2) * t ^ 2
          - (2 * C₁₁ * b * r + C₁₂ * (b * t + r * (-a)) + 2 * C₂₂ * (-a) * t) * t * (-a)
          + (C₁₁ * r ^ 2 + C₁₂ * r * t + C₂₂ * t ^ 2) * (-a) ^ 2 := by ring
    rw [hdet, hk, hmix, hW2] at hrec
    simpa using hrec

end DiophCompression.SemanticQuadraticTwoWitness
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_one_normal_form
