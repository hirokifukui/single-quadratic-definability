/-
  CosetWrapper.lean — Gate-20 Packet N3, the exact wrapper back to the SE₂ vocabulary.

  `Rgen_affine_solution` produces a rational affine SOLUTION FAMILY of the relation.  The reviewer's
  N3.3 asks for a statement about the relation's OUTPUT: on one full coset the output of the
  function is an affine polynomial, i.e. `WeakScalarCosetNF (rgenOut …)` in the sealed vocabulary
  of `CosetNormalForm.lean`.

  Uniqueness is what turns one into the other: the affine family lands on integer points of the
  progression `t₀ + M ℤ`, each of those is a solution of the relation there, and `RelUnique` forces
  the relation's output at that input to BE that integer.  (Reviewer P0 #2 the other way round:
  unique output does not give a unique witness, but it does pin the output once one solution is
  exhibited — which is all that is used here.)

  Claim tags: [P] (std-3), with `CharacterSeparation` (= N1.1b) an explicit [OPEN] hypothesis.
  Baseline read-only.
-/
import ResearchUpgrade.AffineSolution
import ResearchUpgrade.CosetNormalForm

namespace DiophCompression.ResearchUpgrade

open Matrix

/-- **N3.3, in the sealed vocabulary.**  A total, unique-output, positive-definite one-input /
one-witness quadratic relation has its output affine on one full coset. -/
theorem rgen_weakCosetNF_of_definite (hCS : CharacterSeparation) (a b c d e f g h i j : ℤ)
    (ha : 0 < a) (hΔ : 0 < 4 * a * c - b ^ 2)
    (hT : RelTotal (Rgen a b c d e f g h i j))
    (hUq : RelUnique (Rgen a b c d e f g h i j)) :
    WeakScalarCosetNF (rgenOut a b c d e f g h i j hT) := by
  obtain ⟨t₀, y₁, y₀, u₁, u₀, M, hM, hident, hAP⟩ :=
    Rgen_affine_solution hCS a b c d e f g h i j ha hΔ hT
  refine ⟨M, fun _ => t₀, ⟨y₁ * (t₀ : ℚ) + y₀, fun _ => y₁ * (M : ℚ), 0⟩, hM, fun t => ?_⟩
  obtain ⟨Y, U, hY, hU⟩ := hAP (t 0)
  have hx : ((fun _ => t₀ : Fin 1 → ℤ) + (M : ℤ) • t) 0 = t₀ + (M : ℤ) * (t 0) := by
    simp [Pi.add_apply]
  have hxQ : ((t₀ + (M : ℤ) * (t 0) : ℤ) : ℚ) = (t₀ : ℚ) + (M : ℚ) * ((t 0 : ℤ) : ℚ) := by
    push_cast; ring
  -- the affine family lands on `(Y, U)` at this point of the progression
  have hPQ : PQ (a : ℚ) b c d e f g h i j ((t₀ + (M : ℤ) * (t 0) : ℤ) : ℚ) (Y : ℚ) (U : ℚ) = 0 := by
    have hz := hident (((t₀ + (M : ℤ) * (t 0) : ℤ) : ℚ))
    rw [hxQ] at hz ⊢
    rw [show y₁ * ((t₀ : ℚ) + (M : ℚ) * ((t 0 : ℤ) : ℚ)) + y₀ = (Y : ℚ) from hY,
      show u₁ * ((t₀ : ℚ) + (M : ℚ) * ((t 0 : ℤ) : ℚ)) + u₀ = (U : ℚ) from hU] at hz
    exact hz
  have hsol : Pgen a b c d e f g h i j (t₀ + (M : ℤ) * (t 0)) Y U = 0 := by
    have hc := PQ_cast a b c d e f g h i j (t₀ + (M : ℤ) * (t 0)) Y U
    rw [hPQ] at hc
    exact_mod_cast hc
  have hmem : Rgen a b c d e f g h i j (t₀ + (M : ℤ) * (t 0)) Y := ⟨U, hsol⟩
  -- uniqueness pins the relation's output
  have hspec := Classical.choose_spec (hT (((fun _ => t₀ : Fin 1 → ℤ) + (M : ℤ) • t) 0))
  rw [hx] at hspec
  have hchoose : Classical.choose (hT (((fun _ => t₀ : Fin 1 → ℤ) + (M : ℤ) • t) 0)) = Y :=
    hUq (t₀ + (M : ℤ) * (t 0)) _ Y hspec hmem
  simp only [rgenOut]
  rw [hchoose]
  simp only [QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one, Matrix.zero_apply,
    mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
  push_cast
  linear_combination -hY

end DiophCompression.ResearchUpgrade
