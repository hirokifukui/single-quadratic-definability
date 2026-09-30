/-
  DiophCompression/SemanticQuadraticSingular/FiniteFieldQuadratic.lean — r10 必須J (GPT r09 §4.2, §8): over F_p
  (p odd) a nondegenerate binary quadratic form represents every element, hence every affine binary quadratic
  with nondegenerate quadratic part has a root. Route: explicit completion of the square (no QuadraticForm API),
  the diagonal case α X² + β Y² = ρ from mathlib's `FiniteField.exists_root_sum_quadratic`. Statements frozen in
  `Singular_STATEMENTS.lean` (md5 281708fb). Session 10, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticSingular.DefsSingular

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticTwoWitness
  DiophCompression.SemanticQuadraticGeneral

theorem aux_two_ne_zero (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℤ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
  have h'' : p ∣ 2 := by exact_mod_cast h'
  have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h''
  exact hp2 this

theorem exists_weighted_sq_add_sq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (α β ρ : ZMod p)
    (hα : α ≠ 0) (hβ : β ≠ 0) : ∃ X Y : ZMod p, α * X ^ 2 + β * Y ^ 2 = ρ := by
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hf : (Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C (0 : ZMod p) * Polynomial.X
      + Polynomial.C (-ρ)).degree = 2 := Polynomial.degree_quadratic hα
  have hg : (Polynomial.C β * Polynomial.X ^ 2 + Polynomial.C (0 : ZMod p) * Polynomial.X
      + Polynomial.C (0 : ZMod p)).degree = 2 := Polynomial.degree_quadratic hβ
  obtain ⟨X, Y, hXY⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  refine ⟨X, Y, ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at hXY
  linear_combination hXY

theorem nondegenerate_binary_quad_universal_zmod (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a b c : ZMod p)
    (hD : b ^ 2 - 4 * a * c ≠ 0) (ρ : ZMod p) : ∃ x y : ZMod p, a * x ^ 2 + b * x * y + c * y ^ 2 = ρ := by
  have h2 := aux_two_ne_zero p hp2
  have hD' : 4 * a * c - b ^ 2 ≠ 0 := by
    intro h; apply hD; linear_combination -h
  by_cases ha : a ≠ 0
  · obtain ⟨X, Y, hXY⟩ := exists_weighted_sq_add_sq p hp2 1 (4 * a * c - b ^ 2) (4 * a * ρ) one_ne_zero hD'
    have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha
    have h4 : (4 : ZMod p) ≠ 0 := by
      rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    have h4a : 4 * a ≠ 0 := mul_ne_zero h4 ha
    refine ⟨(X - b * Y) / (2 * a), Y, ?_⟩
    have hx : 2 * a * ((X - b * Y) / (2 * a)) = X - b * Y := mul_div_cancel₀ _ h2a
    apply mul_left_cancel₀ h4a
    linear_combination (2 * a * ((X - b * Y) / (2 * a)) + b * Y + X) * hx + hXY
  · push Not at ha
    subst ha
    by_cases hc : c ≠ 0
    · obtain ⟨X, Y, hXY⟩ := exists_weighted_sq_add_sq p hp2 1 (4 * 0 * c - b ^ 2) (4 * c * ρ) one_ne_zero hD'
      have h2c : 2 * c ≠ 0 := mul_ne_zero h2 hc
      have h4 : (4 : ZMod p) ≠ 0 := by
        rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
      have h4c : 4 * c ≠ 0 := mul_ne_zero h4 hc
      refine ⟨Y, (X - b * Y) / (2 * c), ?_⟩
      have hy : 2 * c * ((X - b * Y) / (2 * c)) = X - b * Y := mul_div_cancel₀ _ h2c
      apply mul_left_cancel₀ h4c
      linear_combination (2 * c * ((X - b * Y) / (2 * c)) + b * Y + X) * hy + hXY
    · push Not at hc
      subst hc
      have hb : b ≠ 0 := by
        intro h; apply hD; rw [h]; ring
      refine ⟨ρ / b, 1, ?_⟩
      field_simp
      ring

theorem nondegenerate_affine_binary_quad_has_root (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (a b c d e f : ZMod p) (hD : b ^ 2 - 4 * a * c ≠ 0) :
    ∃ x y : ZMod p, a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + f = 0 := by
  have hD' : 4 * a * c - b ^ 2 ≠ 0 := by
    intro h; apply hD; linear_combination -h
  -- centre of the quadric
  have hDinv : (4 * a * c - b ^ 2) * (4 * a * c - b ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hD'
  set x₀ : ZMod p := (-2 * c * d + b * e) * (4 * a * c - b ^ 2)⁻¹ with hx₀
  set y₀ : ZMod p := (b * d - 2 * a * e) * (4 * a * c - b ^ 2)⁻¹ with hy₀
  have hx : 2 * a * x₀ + b * y₀ + d = 0 := by
    rw [hx₀, hy₀]; linear_combination (-d) * hDinv
  have hy : b * x₀ + 2 * c * y₀ + e = 0 := by
    rw [hx₀, hy₀]; linear_combination (-e) * hDinv
  obtain ⟨x, y, hQ⟩ := nondegenerate_binary_quad_universal_zmod p hp2 a b c hD
    (-(a * x₀ ^ 2 + b * x₀ * y₀ + c * y₀ ^ 2 + d * x₀ + e * y₀ + f))
  refine ⟨x + x₀, y + y₀, ?_⟩
  linear_combination hQ + x * hx + y * hy

theorem moving_remainder_root_mod_prime (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q : ℤ) (hD : ¬ (p : ℤ) ∣ discW C₁₁ C₁₂ C₂₂) :
    ∃ x y : ℤ, (p : ℤ) ∣ movingRemainderPoly A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q x y := by
  haveI := Fact.mk hp
  have hDz : ((C₁₂ : ZMod p)) ^ 2 - 4 * (C₁₁ : ZMod p) * (C₂₂ : ZMod p) ≠ 0 := by
    intro h
    apply hD
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    unfold discW
    push_cast
    exact h
  obtain ⟨x, y, hxy⟩ := nondegenerate_affine_binary_quad_has_root p hp2 (C₁₁ : ZMod p) (C₁₂ : ZMod p)
    (C₂₂ : ZMod p) ((b * m₁ - μ * B₁ : ℤ) : ZMod p) ((b * m₂ - μ * B₂ : ℤ) : ZMod p)
    ((A * μ ^ 2 - b * l * μ + b ^ 2 * q : ℤ) : ZMod p) hDz
  refine ⟨(x.cast : ℤ), (y.cast : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold movingRemainderPoly
  push_cast
  push_cast at hxy
  linear_combination hxy

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.exists_weighted_sq_add_sq
#print axioms DiophCompression.SemanticQuadraticSingular.nondegenerate_binary_quad_universal_zmod
#print axioms DiophCompression.SemanticQuadraticSingular.nondegenerate_affine_binary_quad_has_root
#print axioms DiophCompression.SemanticQuadraticSingular.moving_remainder_root_mod_prime
