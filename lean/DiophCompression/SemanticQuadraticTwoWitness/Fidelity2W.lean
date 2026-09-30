/-
  DiophCompression/SemanticQuadraticTwoWitness/Fidelity2W.lean — r09 必須B (GPT r08 §6): statement-fidelity
  examples. One explicit ternary quadratic H per witness-block class; each theorem records the class
  predicate with explicit values and reaches Dichotomy2 through the matching leaf theorem, so no leaf
  hypothesis is vacuous. Statements frozen first in the frozen statement file `Fidelity2W_STATEMENTS.lean`
  (md5 1dd733fa). Session 9, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticTwoWitness.Assembly2W

namespace DiophCompression.SemanticQuadraticTwoWitness

/-- rank 0: W = 0, H = c². -/
theorem example_rank_zero :
    discW 0 0 0 = 0 ∧ (0 : ℤ) = 0 ∧ (0 : ℤ) = 0 ∧ (0 : ℤ) = 0 ∧ Dichotomy2 1 0 0 0 0 0 :=
  ⟨by norm_num [discW], rfl, rfl, rfl, dichotomy2_rank_zero 1 0 0⟩

/-- rank 1: W = u², H = c² + u². -/
theorem example_rank_one :
    discW 1 0 0 = 0 ∧ ¬ ((1 : ℤ) = 0 ∧ (0 : ℤ) = 0 ∧ (0 : ℤ) = 0) ∧ Dichotomy2 1 0 0 1 0 0 :=
  ⟨by norm_num [discW], by norm_num, dichotomy2_rank_one 1 0 0 1 0 0 (by norm_num [discW]) (by norm_num)⟩

/-- definite, oriented Schur complement > 0: H = c² + u² + v² (discW = −4, α_or = 8). -/
theorem example_definite_positive_schur :
    discW 1 0 1 = -4 ∧ orientedSchur 1 0 0 1 0 1 = 8 ∧ Dichotomy2 1 0 0 1 0 1 :=
  ⟨by norm_num [discW], by norm_num [orientedSchur, schur],
    dichotomy2_definite_pos_oriented 1 0 0 1 0 1 (by norm_num [discW]) (by norm_num [orientedSchur, schur])⟩

/-- definite, oriented Schur complement = 0: H = c² + 2cu + u² + v² = (c + u)² + v². -/
theorem example_definite_zero_schur :
    discW 1 0 1 = -4 ∧ orientedSchur 1 2 0 1 0 1 = 0 ∧ Dichotomy2 1 2 0 1 0 1 :=
  ⟨by norm_num [discW], by norm_num [orientedSchur, schur],
    dichotomy2_definite_zero_oriented 1 2 0 1 0 1 (by norm_num [discW]) (by norm_num [orientedSchur, schur])⟩

/-- definite, oriented Schur complement < 0: H = −c² + u² + v² (signature (2,1); Pythagorean fibers). -/
theorem example_definite_negative_schur :
    discW 1 0 1 = -4 ∧ orientedSchur (-1) 0 0 1 0 1 = -8 ∧ Dichotomy2 (-1) 0 0 1 0 1 :=
  ⟨by norm_num [discW], by norm_num [orientedSchur, schur],
    dichotomy2_definite_neg_oriented (-1) 0 0 1 0 1 (by norm_num [discW]) (by norm_num [orientedSchur, schur])⟩

/-- split: W = uv, H = c² + uv (discW = 1 = 1²). -/
theorem example_split :
    discW 0 1 0 = 1 ∧ IsSquare (discW 0 1 0) ∧ Dichotomy2 1 0 0 0 1 0 :=
  ⟨by norm_num [discW], ⟨1, by norm_num [discW]⟩,
    dichotomy2_split 1 0 0 0 1 0 (by norm_num [discW]) ⟨1, by norm_num [discW]⟩⟩

theorem not_isSquare_eight : ¬ IsSquare (8 : ℤ) := by
  rintro ⟨r, hr⟩
  have h1 : -3 ≤ r ∧ r ≤ 3 := by constructor <;> nlinarith
  obtain ⟨h1, h2⟩ := h1
  interval_cases r <;> omega

/-- anisotropic: W = u² − 2v², H = c² + u² − 2v² (discW = 8, not a square). -/
theorem example_anisotropic :
    discW 1 0 (-2) = 8 ∧ ¬ IsSquare (discW 1 0 (-2)) ∧ Dichotomy2 1 0 0 1 0 (-2) := by
  have hd : discW 1 0 (-2) = 8 := by norm_num [discW]
  refine ⟨hd, by rw [hd]; exact not_isSquare_eight, ?_⟩
  exact dichotomy2_anisotropic 1 0 0 1 0 (-2) (by rw [hd]; norm_num) (by rw [hd]; exact not_isSquare_eight)

/-- The bounded branch is realised: for H = c² + u² + v² (l = m = q = 0) the fiber set is {0}. -/
theorem example_fiber_bounded : fiberSet2 1 0 0 1 0 1 0 0 0 0 = {0} := by
  ext c
  simp only [fiberSet2, fq2, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, v, h⟩
    have hc : (c : ℤ) = 0 := by nlinarith [sq_nonneg (c : ℤ), sq_nonneg u, sq_nonneg v]
    exact_mod_cast hc
  · rintro rfl; exact ⟨0, 0, by norm_num⟩

/-- The infinite branch is realised: for H = −c² + u² + v² (l = m = q = 0) every c is in the fiber set. -/
theorem example_fiber_infinite : (fiberSet2 (-1) 0 0 1 0 1 0 0 0 0).Infinite :=
  Set.infinite_of_injective_forall_mem Function.injective_id
    (fun c => ⟨(c : ℤ), 0, by unfold fq2; simp only [id]; ring⟩)

end DiophCompression.SemanticQuadraticTwoWitness

#print axioms DiophCompression.SemanticQuadraticTwoWitness.example_rank_zero
#print axioms DiophCompression.SemanticQuadraticTwoWitness.example_rank_one
#print axioms DiophCompression.SemanticQuadraticTwoWitness.example_definite_positive_schur
#print axioms DiophCompression.SemanticQuadraticTwoWitness.example_definite_zero_schur
#print axioms DiophCompression.SemanticQuadraticTwoWitness.example_definite_negative_schur
#print axioms DiophCompression.SemanticQuadraticTwoWitness.example_split
#print axioms DiophCompression.SemanticQuadraticTwoWitness.example_anisotropic
#print axioms DiophCompression.SemanticQuadraticTwoWitness.example_fiber_bounded
#print axioms DiophCompression.SemanticQuadraticTwoWitness.example_fiber_infinite
