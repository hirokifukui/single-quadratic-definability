/-
  DiophCompression/SemanticQuadraticMatrix/AdjugateIdentity.lean — r09 必須D (GPT r08 §6): the arbitrary-r
  adjugate identity 2N·F = Yᵀ(adj G)Y + αc² + βc + γ (Y = Gu + cB + m), N·ℤʳ ⊆ G·ℤʳ, and the scaled line
  c = c₀ + Nt, u = u₀ + s(adj G)w − t(adj G)B along which Y = Y₀ + (Ns)w and 2N·F is a binary quadratic in (t, s).
  Statements frozen first in the frozen statement file `MatrixForm_STATEMENTS.lean` (md5 74995c63); fidelity gate
  scout_s9/s9_matrix_identity_check.sage (6000 runs, bad 0). Session 9, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticMatrix.DefsMatrix

namespace DiophCompression.SemanticQuadraticMatrix

open Matrix

variable {r : ℕ}

/-! ## structural facts -/

theorem witnessGram_transpose (C : Matrix (Fin r) (Fin r) ℤ) : (witnessGram C)ᵀ = witnessGram C := by
  unfold witnessGram
  rw [transpose_add, transpose_transpose, add_comm]

theorem witnessGram_diag (C : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : witnessGram C i i = 2 * C i i := by
  unfold witnessGram
  rw [add_apply, transpose_apply]
  ring

theorem adjugate_witnessGram_transpose (C : Matrix (Fin r) (Fin r) ℤ) :
    (adjugate (witnessGram C))ᵀ = adjugate (witnessGram C) := by
  rw [adjugate_transpose, witnessGram_transpose]

theorem dotProduct_witnessGram_mulVec (C : Matrix (Fin r) (Fin r) ℤ) (u : Fin r → ℤ) :
    u ⬝ᵥ (witnessGram C *ᵥ u) = 2 * witnessQuad C u := by
  have h : u ⬝ᵥ (Cᵀ *ᵥ u) = u ⬝ᵥ (C *ᵥ u) := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  unfold witnessGram witnessQuad
  rw [add_mulVec, dotProduct_add, h]
  ring

/-- Symmetry of the adjugate pairing: x·(adj G)y = y·(adj G)x. -/
theorem adjugate_pairing_comm (C : Matrix (Fin r) (Fin r) ℤ) (x y : Fin r → ℤ) :
    x ⬝ᵥ (adjugate (witnessGram C) *ᵥ y) = y ⬝ᵥ (adjugate (witnessGram C) *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, adjugate_witnessGram_transpose, dotProduct_comm]

/-- G (adj G) d = N d: the vector (adj G) d witnesses N·ℤʳ ⊆ G·ℤʳ. -/
theorem witnessGram_mulVec_adjugate (C : Matrix (Fin r) (Fin r) ℤ) (d : Fin r → ℤ) :
    witnessGram C *ᵥ (adjugate (witnessGram C) *ᵥ d) = (witnessGram C).det • d := by
  rw [mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]

theorem adjugate_mulVec_witnessGram (C : Matrix (Fin r) (Fin r) ℤ) (d : Fin r → ℤ) :
    adjugate (witnessGram C) *ᵥ (witnessGram C *ᵥ d) = (witnessGram C).det • d := by
  rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]

theorem det_smul_mem_gramRange (C : Matrix (Fin r) (Fin r) ℤ) (d : Fin r → ℤ) :
    ∃ x : Fin r → ℤ, witnessGram C *ᵥ x = (witnessGram C).det • d :=
  ⟨_, witnessGram_mulVec_adjugate C d⟩

theorem adjugateQuad_add (C : Matrix (Fin r) (Fin r) ℤ) (x y : Fin r → ℤ) :
    adjugateQuad (witnessGram C) (x + y) =
      adjugateQuad (witnessGram C) x + 2 * (x ⬝ᵥ (adjugate (witnessGram C) *ᵥ y))
        + adjugateQuad (witnessGram C) y := by
  unfold adjugateQuad
  simp only [mulVec_add, dotProduct_add, add_dotProduct]
  rw [adjugate_pairing_comm C y x]
  ring

theorem adjugateQuad_smul (C : Matrix (Fin r) (Fin r) ℤ) (w : Fin r → ℤ) (k : ℤ) :
    adjugateQuad (witnessGram C) (k • w) = k ^ 2 * adjugateQuad (witnessGram C) w := by
  unfold adjugateQuad
  rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

theorem dotProduct_adjugate_smul (C : Matrix (Fin r) (Fin r) ℤ) (x w : Fin r → ℤ) (k : ℤ) :
    x ⬝ᵥ (adjugate (witnessGram C) *ᵥ (k • w)) = k * (x ⬝ᵥ (adjugate (witnessGram C) *ᵥ w)) := by
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

/-- The adjugate form along a line: W̃(Y + k w) = W̃(Y) + 2k·(Y·(adj G)w) + k²·W̃(w). -/
theorem adjugateQuad_add_smul (C : Matrix (Fin r) (Fin r) ℤ) (Y w : Fin r → ℤ) (k : ℤ) :
    adjugateQuad (witnessGram C) (Y + k • w) =
      adjugateQuad (witnessGram C) Y + 2 * k * (Y ⬝ᵥ (adjugate (witnessGram C) *ᵥ w))
        + k ^ 2 * adjugateQuad (witnessGram C) w := by
  rw [adjugateQuad_add, dotProduct_adjugate_smul, adjugateQuad_smul]
  ring

/-! ## the identity -/

/-- 2N·F(c,u) = Yᵀ(adj G)Y + αc² + βc + γ with Y = Gu + cB + m. -/
theorem general_rank_identity (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ)
    (m : Fin r → ℤ) (q c : ℤ) (u : Fin r → ℤ) :
    2 * (witnessGram C).det * fqM A B C l m q c u =
      adjugateQuad (witnessGram C) (completedVector B C m c u)
        + alphaMatrix A B C * c ^ 2 + betaMatrix B C l m * c + gammaMatrix C m q := by
  have h1 : adjugateQuad (witnessGram C) (witnessGram C *ᵥ u)
      = 2 * (witnessGram C).det * witnessQuad C u := by
    unfold adjugateQuad
    rw [adjugate_mulVec_witnessGram, dotProduct_smul, smul_eq_mul, dotProduct_comm,
      dotProduct_witnessGram_mulVec]
    ring
  have h2 : ∀ z : Fin r → ℤ, (witnessGram C *ᵥ u) ⬝ᵥ (adjugate (witnessGram C) *ᵥ z)
      = (witnessGram C).det * (z ⬝ᵥ u) := by
    intro z
    rw [adjugate_pairing_comm, adjugate_mulVec_witnessGram, dotProduct_smul, smul_eq_mul]
  have h3 : adjugateQuad (witnessGram C) (c • B + m)
      = c ^ 2 * (B ⬝ᵥ (adjugate (witnessGram C) *ᵥ B))
        + 2 * c * (B ⬝ᵥ (adjugate (witnessGram C) *ᵥ m)) + m ⬝ᵥ (adjugate (witnessGram C) *ᵥ m) := by
    rw [adjugateQuad_add, adjugateQuad_smul, smul_dotProduct, smul_eq_mul]
    unfold adjugateQuad
    ring
  have hY : completedVector B C m c u = witnessGram C *ᵥ u + (c • B + m) := by
    unfold completedVector; rw [add_assoc]
  rw [hY, adjugateQuad_add, h1, h2, h3]
  unfold fqM alphaMatrix betaMatrix gammaMatrix
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

/-! ## the scaled line -/

/-- Along the scaled line the completed vector moves by (N s)·w only. -/
theorem general_scaled_line_preserves_lattice (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ)
    (m u₀ w : Fin r → ℤ) (c₀ t s : ℤ) :
    completedVector B C m (c₀ + (witnessGram C).det * t) (scaledLineU B C u₀ w t s) =
      completedVector B C m c₀ u₀ + ((witnessGram C).det * s) • w := by
  unfold completedVector scaledLineU
  rw [mulVec_sub, mulVec_add, mulVec_smul, mulVec_smul, witnessGram_mulVec_adjugate,
    witnessGram_mulVec_adjugate]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- On the scaled line, 2N·F is a binary quadratic in (t, s): no ts term, t²-coefficient αN²,
    s²-coefficient N²·W̃(w). -/
theorem general_scaled_line_identity (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ)
    (m u₀ w : Fin r → ℤ) (q c₀ t s : ℤ) :
    2 * (witnessGram C).det * fqM A B C l m q (c₀ + (witnessGram C).det * t) (scaledLineU B C u₀ w t s) =
      adjugateQuad (witnessGram C) (completedVector B C m c₀ u₀)
        + 2 * ((witnessGram C).det * s) * (completedVector B C m c₀ u₀ ⬝ᵥ (adjugate (witnessGram C) *ᵥ w))
        + ((witnessGram C).det * s) ^ 2 * adjugateQuad (witnessGram C) w
        + alphaMatrix A B C * (c₀ + (witnessGram C).det * t) ^ 2
        + betaMatrix B C l m * (c₀ + (witnessGram C).det * t) + gammaMatrix C m q := by
  rw [general_rank_identity, general_scaled_line_preserves_lattice, adjugateQuad_add_smul]

/-- A zero of F on the scaled line with c₀ + N t ≥ 0 is a fiber element. -/
theorem general_scaled_line_solution (A : ℤ) (B : Fin r → ℤ) (C : Matrix (Fin r) (Fin r) ℤ) (l : ℤ)
    (m u₀ w : Fin r → ℤ) (q c₀ t s : ℤ)
    (hF : fqM A B C l m q (c₀ + (witnessGram C).det * t) (scaledLineU B C u₀ w t s) = 0)
    (hc : 0 ≤ c₀ + (witnessGram C).det * t) :
    (c₀ + (witnessGram C).det * t).toNat ∈ fiberSetM A B C l m q := by
  show ∃ u : Fin r → ℤ, fqM A B C l m q (((c₀ + (witnessGram C).det * t).toNat : ℕ) : ℤ) u = 0
  refine ⟨scaledLineU B C u₀ w t s, ?_⟩
  rw [Int.toNat_of_nonneg hc]
  exact hF

end DiophCompression.SemanticQuadraticMatrix

#print axioms DiophCompression.SemanticQuadraticMatrix.witnessGram_transpose
#print axioms DiophCompression.SemanticQuadraticMatrix.witnessGram_diag
#print axioms DiophCompression.SemanticQuadraticMatrix.adjugate_witnessGram_transpose
#print axioms DiophCompression.SemanticQuadraticMatrix.dotProduct_witnessGram_mulVec
#print axioms DiophCompression.SemanticQuadraticMatrix.adjugate_pairing_comm
#print axioms DiophCompression.SemanticQuadraticMatrix.witnessGram_mulVec_adjugate
#print axioms DiophCompression.SemanticQuadraticMatrix.det_smul_mem_gramRange
#print axioms DiophCompression.SemanticQuadraticMatrix.adjugateQuad_add_smul
#print axioms DiophCompression.SemanticQuadraticMatrix.general_rank_identity
#print axioms DiophCompression.SemanticQuadraticMatrix.general_scaled_line_preserves_lattice
#print axioms DiophCompression.SemanticQuadraticMatrix.general_scaled_line_identity
#print axioms DiophCompression.SemanticQuadraticMatrix.general_scaled_line_solution
