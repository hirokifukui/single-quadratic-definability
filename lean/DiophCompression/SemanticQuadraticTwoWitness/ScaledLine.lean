/-
  DiophCompression/SemanticQuadraticTwoWitness/ScaledLine.lean — GPT r07 必須3 (s8, claude.ai direct).
  The rank-2 completing-the-square identity 2N·fq2 = wt(Y) + αc² + βc + γ, the scaled line
  c' = c + M z, Y' = Y + M s w, coset preservation N·ℤ² ⊆ G·ℤ², the discriminant and the
  Class_D7 quantity at the origin, and the transfer of a scaled-line solution back to a fiber witness.
  Frozen statements: `TwoWitness_STATEMENTS_v2.lean` (md5 3e2c4c02). Mathematics: CLASSIFICATION_2W.md §3.1.
-/
import DiophCompression.SemanticQuadraticTwoWitness.DefsScaled
import DiophCompression.SemanticQuadratic.FiberDefs

namespace DiophCompression.SemanticQuadraticTwoWitness

open DiophCompression.SemanticQuadraticGeneral

theorem rank_two_identity (A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v : ℤ) :
    2 * nW C₁₁ C₁₂ C₂₂ * fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v
      = wt C₁₁ C₁₂ C₂₂ (y1 B₁ C₁₁ C₁₂ m₁ c u v) (y2 B₂ C₁₂ C₂₂ m₂ c u v)
        + schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * c ^ 2 + betaR B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ * c
        + gammaR C₁₁ C₁₂ C₂₂ m₁ m₂ q := by
  unfold fq2 wt y1 y2 schur betaR gammaR nW; ring

theorem scaled_line_identity (α β γ C₁₁ C₁₂ C₂₂ M Y₁ Y₂ w₁ w₂ c z s : ℤ) :
    wt C₁₁ C₁₂ C₂₂ (Y₁ + M * s * w₁) (Y₂ + M * s * w₂) + (α * (c + M * z) ^ 2 + β * (c + M * z) + γ)
      - (wt C₁₁ C₁₂ C₂₂ Y₁ Y₂ + (α * c ^ 2 + β * c + γ))
      = M * (M * α * z ^ 2 + (2 * α * c + β) * z
          + 2 * wtBil C₁₁ C₁₂ C₂₂ Y₁ Y₂ w₁ w₂ * s + M * wt C₁₁ C₁₂ C₂₂ w₁ w₂ * s ^ 2) := by
  unfold wt wtBil; ring

/-- N·ℤ² ⊆ G·ℤ²: for every d the vector x = (adj G)·d satisfies G x = N d (r = 2 instance of
    `det_smul_mem_gramRange`). The name records its use on the scaled line; the statement is the lattice
    containment, not a coset statement (E-r09-2, GPT r08 §3.5). -/
theorem scaled_line_preserves_coset (C₁₁ C₁₂ C₂₂ d₁ d₂ : ℤ) :
    ∃ x₁ x₂ : ℤ, 2 * C₁₁ * x₁ + C₁₂ * x₂ = nW C₁₁ C₁₂ C₂₂ * d₁
      ∧ C₁₂ * x₁ + 2 * C₂₂ * x₂ = nW C₁₁ C₁₂ C₂₂ * d₂ :=
  ⟨2 * C₂₂ * d₁ - C₁₂ * d₂, -C₁₂ * d₁ + 2 * C₁₁ * d₂, by unfold nW; ring, by unfold nW; ring⟩

theorem scaled_line_discriminant (α C₁₁ C₁₂ C₂₂ w₁ w₂ : ℤ) :
    DiophCompression.SemanticQuadratic.disc (nW C₁₁ C₁₂ C₂₂ * α) 0 (nW C₁₁ C₁₂ C₂₂ * wt C₁₁ C₁₂ C₂₂ w₁ w₂)
      = -4 * nW C₁₁ C₁₂ C₂₂ ^ 2 * α * wt C₁₁ C₁₂ C₂₂ w₁ w₂ := by
  unfold DiophCompression.SemanticQuadratic.disc; ring

theorem scaled_line_X_at_origin (α β C₁₁ C₁₂ C₂₂ Y₁ Y₂ w₁ w₂ c : ℤ) :
    2 * 0 * (2 * wtBil C₁₁ C₁₂ C₂₂ Y₁ Y₂ w₁ w₂)
      - 4 * (nW C₁₁ C₁₂ C₂₂ * wt C₁₁ C₁₂ C₂₂ w₁ w₂) * (2 * α * c + β)
      = -4 * nW C₁₁ C₁₂ C₂₂ * wt C₁₁ C₁₂ C₂₂ w₁ w₂ * (2 * α * c + β) := by
  ring

theorem scaled_line_solution (A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c₀ u₀ v₀ w₁ w₂ z s : ℤ)
    (hN : nW C₁₁ C₁₂ C₂₂ ≠ 0)
    (h0 : fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c₀ u₀ v₀ = 0)
    (hzs : nW C₁₁ C₁₂ C₂₂ * schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * z ^ 2
        + (2 * schur A B₁ B₂ C₁₁ C₁₂ C₂₂ * c₀ + betaR B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂) * z
        + 2 * wtBil C₁₁ C₁₂ C₂₂ (y1 B₁ C₁₁ C₁₂ m₁ c₀ u₀ v₀) (y2 B₂ C₁₂ C₂₂ m₂ c₀ u₀ v₀) w₁ w₂ * s
        + nW C₁₁ C₁₂ C₂₂ * wt C₁₁ C₁₂ C₂₂ w₁ w₂ * s ^ 2 = 0) :
    ∃ u v : ℤ, fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q (c₀ + nW C₁₁ C₁₂ C₂₂ * z) u v = 0 := by
  obtain ⟨N, hNdef⟩ : ∃ N : ℤ, N = nW C₁₁ C₁₂ C₂₂ := ⟨_, rfl⟩
  obtain ⟨x₁, x₂, hx1, hx2⟩ := scaled_line_preserves_coset C₁₁ C₁₂ C₂₂ (s * w₁ - z * B₁) (s * w₂ - z * B₂)
  refine ⟨u₀ + x₁, v₀ + x₂, ?_⟩
  have hy1 : y1 B₁ C₁₁ C₁₂ m₁ (c₀ + nW C₁₁ C₁₂ C₂₂ * z) (u₀ + x₁) (v₀ + x₂)
      = y1 B₁ C₁₁ C₁₂ m₁ c₀ u₀ v₀ + nW C₁₁ C₁₂ C₂₂ * s * w₁ := by
    unfold y1; linear_combination hx1
  have hy2 : y2 B₂ C₁₂ C₂₂ m₂ (c₀ + nW C₁₁ C₁₂ C₂₂ * z) (u₀ + x₁) (v₀ + x₂)
      = y2 B₂ C₁₂ C₂₂ m₂ c₀ u₀ v₀ + nW C₁₁ C₁₂ C₂₂ * s * w₂ := by
    unfold y2; linear_combination hx2
  have key := rank_two_identity A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q (c₀ + nW C₁₁ C₁₂ C₂₂ * z) (u₀ + x₁) (v₀ + x₂)
  rw [hy1, hy2] at key
  have base := rank_two_identity A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c₀ u₀ v₀
  rw [h0, mul_zero] at base
  have sl := scaled_line_identity (schur A B₁ B₂ C₁₁ C₁₂ C₂₂) (betaR B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂)
    (gammaR C₁₁ C₁₂ C₂₂ m₁ m₂ q) C₁₁ C₁₂ C₂₂ (nW C₁₁ C₁₂ C₂₂)
    (y1 B₁ C₁₁ C₁₂ m₁ c₀ u₀ v₀) (y2 B₂ C₁₂ C₂₂ m₂ c₀ u₀ v₀) w₁ w₂ c₀ z s
  have h2 : 2 * nW C₁₁ C₁₂ C₂₂
      * fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q (c₀ + nW C₁₁ C₁₂ C₂₂ * z) (u₀ + x₁) (v₀ + x₂) = 0 := by
    linear_combination key + sl + nW C₁₁ C₁₂ C₂₂ * hzs - base
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h (mul_ne_zero two_ne_zero hN)
  · exact h

end DiophCompression.SemanticQuadraticTwoWitness
#print axioms DiophCompression.SemanticQuadraticTwoWitness.rank_two_identity
#print axioms DiophCompression.SemanticQuadraticTwoWitness.scaled_line_identity
#print axioms DiophCompression.SemanticQuadraticTwoWitness.scaled_line_preserves_coset
#print axioms DiophCompression.SemanticQuadraticTwoWitness.scaled_line_discriminant
#print axioms DiophCompression.SemanticQuadraticTwoWitness.scaled_line_X_at_origin
#print axioms DiophCompression.SemanticQuadraticTwoWitness.scaled_line_solution
