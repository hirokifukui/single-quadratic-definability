/-
  DiophCompression/SemanticQuadraticTwoWitness/SignNormalisation.lean — GPT r07 必須2 (s8, claude.ai direct).
  Negating all coefficients preserves the fiber set and the bound, and negates the Schur complement;
  hence `Dichotomy2` is negation-invariant (orientation of the witness block is free).
  Frozen statements: `TwoWitness_STATEMENTS_v2.lean` (md5 3e2c4c02).
-/
import DiophCompression.SemanticQuadraticTwoWitness.DefsScaled

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadraticGeneral

theorem fq2_neg (A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v : ℤ) :
    fq2 (-A) (-B₁) (-B₂) (-C₁₁) (-C₁₂) (-C₂₂) (-l) (-m₁) (-m₂) (-q) c u v
      = - fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v := by
  unfold fq2; ring

theorem fiberSet2_neg (A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q : ℤ) :
    fiberSet2 (-A) (-B₁) (-B₂) (-C₁₁) (-C₁₂) (-C₂₂) (-l) (-m₁) (-m₂) (-q)
      = fiberSet2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q := by
  ext c
  simp only [fiberSet2, Set.mem_setOf_eq, fq2_neg, neg_eq_zero]

theorem schur_neg (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) :
    schur (-A) (-B₁) (-B₂) (-C₁₁) (-C₁₂) (-C₂₂) = - schur A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  unfold schur; ring

theorem fbound2_neg (K : ℕ) (l m₁ m₂ q : ℤ) :
    fbound2 K (-l) (-m₁) (-m₂) (-q) = fbound2 K l m₁ m₂ q := by
  unfold fbound2; rw [abs_neg, abs_neg, abs_neg, abs_neg]

theorem dichotomy2_neg_iff (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) :
    Dichotomy2 (-A) (-B₁) (-B₂) (-C₁₁) (-C₁₂) (-C₂₂) ↔ Dichotomy2 A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, fun l m₁ m₂ q => ?_⟩
    have h := hK (-l) (-m₁) (-m₂) (-q)
    rw [fiberSet2_neg, fbound2_neg] at h
    exact h
  · rintro ⟨K, hK⟩
    refine ⟨K, fun l m₁ m₂ q => ?_⟩
    have hs := fiberSet2_neg A B₁ B₂ C₁₁ C₁₂ C₂₂ (-l) (-m₁) (-m₂) (-q)
    simp only [neg_neg] at hs
    rw [hs]
    have h := hK (-l) (-m₁) (-m₂) (-q)
    rw [fbound2_neg] at h
    exact h

/-- `orientedSchur` is negation-invariant (sign(−C₁₁)·(−schur) = sign(C₁₁)·schur). -/
theorem orientedSchur_neg (A B₁ B₂ C₁₁ C₁₂ C₂₂ : ℤ) :
    orientedSchur (-A) (-B₁) (-B₂) (-C₁₁) (-C₁₂) (-C₂₂) = orientedSchur A B₁ B₂ C₁₁ C₁₂ C₂₂ := by
  unfold orientedSchur; rw [schur_neg, Int.sign_neg]; ring

end DiophCompression.SemanticQuadraticTwoWitness
#print axioms DiophCompression.SemanticQuadraticTwoWitness.fiberSet2_neg
#print axioms DiophCompression.SemanticQuadraticTwoWitness.schur_neg
#print axioms DiophCompression.SemanticQuadraticTwoWitness.dichotomy2_neg_iff
#print axioms DiophCompression.SemanticQuadraticTwoWitness.orientedSchur_neg
