/-
  Fidelity3W.lean — r11 (GPT r10 必須B): nine fidelity examples for the r = 3 dichotomy.
  Each example records a concrete coefficient tuple, verifies its discriminant/rank condition
  in the kernel, names the applicable leaf theorem in its docstring, and connects the tuple to
  `dichotomy3_all`. (s11, claude.ai direct.)
-/
import DiophCompression.SemanticQuadraticSingular.Assembly3W

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix

/-! ## Full-rank examples (leaf: `dichotomy3_full_rank` via `(witnessGram C).det ≠ 0`) -/

/-- (1) positive definite: C = I₃, Gram = 2·I₃, det = 8. -/
def C_fr_pos : Matrix (Fin 3) (Fin 3) ℤ := !![1,0,0; 0,1,0; 0,0,1]

theorem C_fr_pos_gram_det : (witnessGram C_fr_pos).det = 8 := by decide

/-- Leaf: `dichotomy3_full_rank` (det = 8 ≠ 0, positive definite Gram). -/
theorem example_full_rank_positive_definite : DichotomyM 1 ![1,0,0] C_fr_pos :=
  dichotomy3_all 1 ![1,0,0] C_fr_pos

/-- (2) negative definite: C = −I₃, Gram = −2·I₃, det = −8. -/
def C_fr_neg : Matrix (Fin 3) (Fin 3) ℤ := !![-1,0,0; 0,-1,0; 0,0,-1]

theorem C_fr_neg_gram_det : (witnessGram C_fr_neg).det = -8 := by decide

/-- Leaf: `dichotomy3_full_rank` (det = −8 ≠ 0, negative definite Gram). -/
theorem example_full_rank_negative_definite : DichotomyM 1 ![0,1,0] C_fr_neg :=
  dichotomy3_all 1 ![0,1,0] C_fr_neg

/-- (3) split signature: C = diag(1,−1,1), Gram = diag(2,−2,2), det = −8. -/
def C_fr_split : Matrix (Fin 3) (Fin 3) ℤ := !![1,0,0; 0,-1,0; 0,0,1]

theorem C_fr_split_gram_det : (witnessGram C_fr_split).det = -8 := by decide

/-- Leaf: `dichotomy3_full_rank` (det = −8 ≠ 0, indefinite split Gram). -/
theorem example_full_rank_split : DichotomyM 0 ![1,1,1] C_fr_split :=
  dichotomy3_all 0 ![1,1,1] C_fr_split

/-- (4) anisotropic-type off-diagonal: C = upper bidiagonal, Gram tridiagonal, det = 4. -/
def C_fr_aniso : Matrix (Fin 3) (Fin 3) ℤ := !![1,1,0; 0,1,1; 0,0,1]

theorem C_fr_aniso_gram_det : (witnessGram C_fr_aniso).det = 4 := by decide

/-- Leaf: `dichotomy3_full_rank` (det = 4 ≠ 0, anisotropic-type Gram). -/
theorem example_full_rank_anisotropic : DichotomyM 2 ![1,0,1] C_fr_aniso :=
  dichotomy3_all 2 ![1,0,1] C_fr_aniso

/-! ## Singular rank-two examples (Gram = diag(2,2,0), det = 0; leaf via `dichotomy3_singular`) -/

/-- rank-two singular block: C = diag(1,1,0). -/
def C_sg_r2 : Matrix (Fin 3) (Fin 3) ℤ := !![1,0,0; 0,1,0; 0,0,0]

theorem C_sg_r2_gram_det : (witnessGram C_sg_r2).det = 0 := by decide

/-- (5) fixed modulus: radical slope B₂ = 0 (the radical coefficient is the constant m₂ alone).
Leaf: the fixed-modulus branch of `dichotomyS_all` inside `dichotomy3_singular`. -/
theorem example_singular_rank_two_fixed_modulus : DichotomyM 1 ![1,1,0] C_sg_r2 :=
  dichotomy3_all 1 ![1,1,0] C_sg_r2

/-- (6) moving modulus, positive slope: radical slope B₂ = 1 > 0.
Leaf: `moving_modulus_prime_step` branch of `dichotomyS_all` inside `dichotomy3_singular`. -/
theorem example_singular_rank_two_moving_positive : DichotomyM 1 ![1,1,1] C_sg_r2 :=
  dichotomy3_all 1 ![1,1,1] C_sg_r2

/-- (7) moving modulus, nonpositive slope: radical slope B₂ = −1 < 0.
Leaf: the sign-flip reduction (w ↦ −w) to the positive-slope branch inside `dichotomy3_singular`. -/
theorem example_singular_rank_two_moving_nonpositive : DichotomyM 1 ![1,1,-1] C_sg_r2 :=
  dichotomy3_all 1 ![1,1,-1] C_sg_r2

/-! ## Singular lower-rank examples -/

/-- (8) rank one: C = diag(1,0,0), Gram = diag(2,0,0), det = 0.
Leaf: `singular_rank_one_dichotomy` inside `dichotomy3_singular`. -/
def C_sg_r1 : Matrix (Fin 3) (Fin 3) ℤ := !![1,0,0; 0,0,0; 0,0,0]

theorem C_sg_r1_gram_det : (witnessGram C_sg_r1).det = 0 := by decide

theorem example_singular_rank_one : DichotomyM 1 ![0,1,1] C_sg_r1 :=
  dichotomy3_all 1 ![0,1,1] C_sg_r1

/-- (9) rank zero: C = 0, Gram = 0, det = 0.
Leaf: `singular_rank_zero_dichotomy` inside `dichotomy3_singular`. -/
def C_sg_r0 : Matrix (Fin 3) (Fin 3) ℤ := !![0,0,0; 0,0,0; 0,0,0]

theorem C_sg_r0_gram_det : (witnessGram C_sg_r0).det = 0 := by decide

theorem example_singular_rank_zero : DichotomyM 1 ![1,2,3] C_sg_r0 :=
  dichotomy3_all 1 ![1,2,3] C_sg_r0

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.example_full_rank_positive_definite
#print axioms DiophCompression.SemanticQuadraticSingular.example_full_rank_negative_definite
#print axioms DiophCompression.SemanticQuadraticSingular.example_full_rank_split
#print axioms DiophCompression.SemanticQuadraticSingular.example_full_rank_anisotropic
#print axioms DiophCompression.SemanticQuadraticSingular.example_singular_rank_two_fixed_modulus
#print axioms DiophCompression.SemanticQuadraticSingular.example_singular_rank_two_moving_positive
#print axioms DiophCompression.SemanticQuadraticSingular.example_singular_rank_two_moving_nonpositive
#print axioms DiophCompression.SemanticQuadraticSingular.example_singular_rank_one
#print axioms DiophCompression.SemanticQuadraticSingular.example_singular_rank_zero
