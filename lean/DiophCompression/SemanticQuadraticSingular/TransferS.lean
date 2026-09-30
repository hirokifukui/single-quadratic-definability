/-
  DiophCompression/SemanticQuadraticSingular/TransferS.lean — r10 必須E/F (GPT r09 §8) and the unimodular
  transfers of DichotomyS: a GL₂(ℤ) change on the block (u,v) and, when the block is diagonal-in-u
  (C₁₂ = C₂₂ = 0), a GL₂(ℤ) change on the radical pair (v,w). Rank 0 and rank 1 blocks with b ≠ 0 reduce by
  the (v,w) change (B₂, b) ↦ (gcd, 0) to the fixed-modulus leaf b = 0 (r08 `rank_zero_caseB` pattern) — no
  pair-minor split, no prime step. Statements frozen in `Singular_STATEMENTS.lean` (md5 281708fb).
  Session 10, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticSingular.PeriodicModulus
import DiophCompression.SemanticQuadraticTwoWitness.RankOneNormalForm

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticTwoWitness
  DiophCompression.SemanticQuadraticGeneral

theorem fbound3S_mono (K M : ℕ) (l m₁ m₂ μ q l' m₁' m₂' μ' : ℤ)
    (h : 1 + |l'| + |m₁'| + |m₂'| + |μ'| ≤ (M : ℤ) * (1 + |l| + |m₁| + |m₂| + |μ|)) :
    fbound3S K l' m₁' m₂' μ' q ≤ fbound3S (K * M ^ 2) l m₁ m₂ μ q := by
  unfold fbound3S
  push_cast
  have hX0 : (0 : ℤ) ≤ 1 + |l'| + |m₁'| + |m₂'| + |μ'| := by positivity
  have hY0 : (0 : ℤ) ≤ 1 + |l| + |m₁| + |m₂| + |μ| := by positivity
  have hM0 : (0 : ℤ) ≤ (M : ℤ) := by positivity
  have hMY : (0 : ℤ) ≤ (M : ℤ) * (1 + |l| + |m₁| + |m₂| + |μ|) := mul_nonneg hM0 hY0
  have hM1 : (1 : ℤ) ≤ (M : ℤ) := by
    by_contra hcon
    push Not at hcon
    have hM : (M : ℤ) = 0 := by omega
    rw [hM, zero_mul] at h
    have : (1 : ℤ) ≤ 1 + |l'| + |m₁'| + |m₂'| + |μ'| := by
      have := abs_nonneg l'; have := abs_nonneg m₁'; have := abs_nonneg m₂'; have := abs_nonneg μ'
      linarith
    linarith
  have hsq := mul_le_mul h h hX0 hMY
  have hq : |q| ≤ (M : ℤ) ^ 2 * |q| := by
    have : (1 : ℤ) ≤ (M : ℤ) ^ 2 := by nlinarith
    exact le_mul_of_one_le_left (abs_nonneg q) this
  have hKz : (0 : ℤ) ≤ (K : ℤ) := by positivity
  calc (K : ℤ) * ((1 + |l'| + |m₁'| + |m₂'| + |μ'|) ^ 2 + |q|)
      ≤ (K : ℤ) * ((M : ℤ) ^ 2 * (1 + |l| + |m₁| + |m₂| + |μ|) ^ 2 + (M : ℤ) ^ 2 * |q|) := by
        apply mul_le_mul_of_nonneg_left _ hKz
        nlinarith [hsq, hq]
    _ = (K : ℤ) * (M : ℤ) ^ 2 * ((1 + |l| + |m₁| + |m₂| + |μ|) ^ 2 + |q|) := by ring

theorem fq3S_subst_uv (A B₁ B₂ C₁₁ C₁₂ C₂₂ b p r s t l m₁ m₂ μ q c u v w : ℤ) :
    fq3S A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q c (p * u + r * v) (s * u + t * v) w =
    fq3S A (B₁ * p + B₂ * s) (B₁ * r + B₂ * t)
      (C₁₁ * p ^ 2 + C₁₂ * p * s + C₂₂ * s ^ 2)
      (2 * C₁₁ * p * r + C₁₂ * (p * t + r * s) + 2 * C₂₂ * s * t)
      (C₁₁ * r ^ 2 + C₁₂ * r * t + C₂₂ * t ^ 2)
      b l (m₁ * p + m₂ * s) (m₁ * r + m₂ * t) μ q c u v w := by
  unfold fq3S fq2; ring

/-- The linear-part inequality behind both transfers: |x p + y s| + |x r + y t| ≤ (|x|+|y|)(|p|+|r|+|s|+|t|). -/
theorem aux_abs_pair_le (x y p r s t : ℤ) :
    |x * p + y * s| + |x * r + y * t| ≤ (|x| + |y|) * (|p| + |r| + |s| + |t|) := by
  have hA : |x * p + y * s| ≤ |x| * |p| + |y| * |s| := by
    calc |x * p + y * s| ≤ |x * p| + |y * s| := abs_add_le _ _
      _ = |x| * |p| + |y| * |s| := by rw [abs_mul, abs_mul]
  have hB : |x * r + y * t| ≤ |x| * |r| + |y| * |t| := by
    calc |x * r + y * t| ≤ |x * r| + |y * t| := abs_add_le _ _
      _ = |x| * |r| + |y| * |t| := by rw [abs_mul, abs_mul]
  nlinarith [hA, hB, abs_nonneg x, abs_nonneg y, abs_nonneg p, abs_nonneg r, abs_nonneg s, abs_nonneg t,
    mul_nonneg (abs_nonneg x) (abs_nonneg s), mul_nonneg (abs_nonneg x) (abs_nonneg t),
    mul_nonneg (abs_nonneg y) (abs_nonneg p), mul_nonneg (abs_nonneg y) (abs_nonneg r)]

theorem aux_M_cast (p r s t : ℤ) :
    ((1 + p.natAbs + r.natAbs + s.natAbs + t.natAbs : ℕ) : ℤ) = 1 + |p| + |r| + |s| + |t| := by
  push_cast
  rfl

theorem dichotomyS_of_unimodular_uv (A B₁ B₂ C₁₁ C₁₂ C₂₂ b p r s t : ℤ)
    (hdet : p * t - r * s = 1 ∨ p * t - r * s = -1)
    (h : DichotomyS A (B₁ * p + B₂ * s) (B₁ * r + B₂ * t)
          (C₁₁ * p ^ 2 + C₁₂ * p * s + C₂₂ * s ^ 2)
          (2 * C₁₁ * p * r + C₁₂ * (p * t + r * s) + 2 * C₂₂ * s * t)
          (C₁₁ * r ^ 2 + C₁₂ * r * t + C₂₂ * t ^ 2) b) :
    DichotomyS A B₁ B₂ C₁₁ C₁₂ C₂₂ b := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K * (1 + p.natAbs + r.natAbs + s.natAbs + t.natAbs) ^ 2, ?_⟩
  intro l m₁ m₂ μ q
  have hEq : fiberSet3S A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q =
      fiberSet3S A (B₁ * p + B₂ * s) (B₁ * r + B₂ * t)
        (C₁₁ * p ^ 2 + C₁₂ * p * s + C₂₂ * s ^ 2)
        (2 * C₁₁ * p * r + C₁₂ * (p * t + r * s) + 2 * C₂₂ * s * t)
        (C₁₁ * r ^ 2 + C₁₂ * r * t + C₂₂ * t ^ 2)
        b l (m₁ * p + m₂ * s) (m₁ * r + m₂ * t) μ q := by
    ext c
    simp only [fiberSet3S, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, v, w, huv⟩
      rcases hdet with hε | hε
      · refine ⟨t * u - r * v, p * v - s * u, w, ?_⟩
        have key := fq3S_subst_uv A B₁ B₂ C₁₁ C₁₂ C₂₂ b p r s t l m₁ m₂ μ q (c : ℤ)
          (t * u - r * v) (p * v - s * u) w
        rw [← key]
        have hu : p * (t * u - r * v) + r * (p * v - s * u) = u := by linear_combination u * hε
        have hv : s * (t * u - r * v) + t * (p * v - s * u) = v := by linear_combination v * hε
        rw [hu, hv]; exact huv
      · refine ⟨r * v - t * u, s * u - p * v, w, ?_⟩
        have key := fq3S_subst_uv A B₁ B₂ C₁₁ C₁₂ C₂₂ b p r s t l m₁ m₂ μ q (c : ℤ)
          (r * v - t * u) (s * u - p * v) w
        rw [← key]
        have hu : p * (r * v - t * u) + r * (s * u - p * v) = u := by linear_combination (-u) * hε
        have hv : s * (r * v - t * u) + t * (s * u - p * v) = v := by linear_combination (-v) * hε
        rw [hu, hv]; exact huv
    · rintro ⟨u, v, w, huv⟩
      exact ⟨p * u + r * v, s * u + t * v, w, by rw [fq3S_subst_uv]; exact huv⟩
  rcases hK l (m₁ * p + m₂ * s) (m₁ * r + m₂ * t) μ q with hInf | hBd
  · left; rw [hEq]; exact hInf
  · right
    intro c hc
    rw [hEq] at hc
    refine le_trans (hBd c hc) ?_
    apply fbound3S_mono
    rw [aux_M_cast]
    have := aux_abs_pair_le m₁ m₂ p r s t
    nlinarith [this, abs_nonneg l, abs_nonneg μ, abs_nonneg m₁, abs_nonneg m₂, abs_nonneg p, abs_nonneg r,
      abs_nonneg s, abs_nonneg t, mul_nonneg (abs_nonneg l) (abs_nonneg p),
      mul_nonneg (abs_nonneg l) (abs_nonneg r), mul_nonneg (abs_nonneg l) (abs_nonneg s),
      mul_nonneg (abs_nonneg l) (abs_nonneg t), mul_nonneg (abs_nonneg μ) (abs_nonneg p),
      mul_nonneg (abs_nonneg μ) (abs_nonneg r), mul_nonneg (abs_nonneg μ) (abs_nonneg s),
      mul_nonneg (abs_nonneg μ) (abs_nonneg t)]

theorem fq3S_subst_vw (A B₁ B₂ C₁₁ b p r s t l m₁ m₂ μ q c u v w : ℤ) :
    fq3S A B₁ B₂ C₁₁ 0 0 b l m₁ m₂ μ q c u (p * v + r * w) (s * v + t * w) =
    fq3S A B₁ (B₂ * p + b * s) C₁₁ 0 0 (B₂ * r + b * t) l m₁ (m₂ * p + μ * s) (m₂ * r + μ * t) q c u v w := by
  unfold fq3S fq2; ring

theorem dichotomyS_of_unimodular_vw (A B₁ B₂ C₁₁ b p r s t : ℤ)
    (hdet : p * t - r * s = 1 ∨ p * t - r * s = -1)
    (h : DichotomyS A B₁ (B₂ * p + b * s) C₁₁ 0 0 (B₂ * r + b * t)) :
    DichotomyS A B₁ B₂ C₁₁ 0 0 b := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K * (1 + p.natAbs + r.natAbs + s.natAbs + t.natAbs) ^ 2, ?_⟩
  intro l m₁ m₂ μ q
  have hEq : fiberSet3S A B₁ B₂ C₁₁ 0 0 b l m₁ m₂ μ q =
      fiberSet3S A B₁ (B₂ * p + b * s) C₁₁ 0 0 (B₂ * r + b * t) l m₁ (m₂ * p + μ * s) (m₂ * r + μ * t) q := by
    ext c
    simp only [fiberSet3S, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, v, w, huv⟩
      rcases hdet with hε | hε
      · refine ⟨u, t * v - r * w, p * w - s * v, ?_⟩
        have key := fq3S_subst_vw A B₁ B₂ C₁₁ b p r s t l m₁ m₂ μ q (c : ℤ) u (t * v - r * w) (p * w - s * v)
        rw [← key]
        have hv : p * (t * v - r * w) + r * (p * w - s * v) = v := by linear_combination v * hε
        have hw : s * (t * v - r * w) + t * (p * w - s * v) = w := by linear_combination w * hε
        rw [hv, hw]; exact huv
      · refine ⟨u, r * w - t * v, s * v - p * w, ?_⟩
        have key := fq3S_subst_vw A B₁ B₂ C₁₁ b p r s t l m₁ m₂ μ q (c : ℤ) u (r * w - t * v) (s * v - p * w)
        rw [← key]
        have hv : p * (r * w - t * v) + r * (s * v - p * w) = v := by linear_combination (-v) * hε
        have hw : s * (r * w - t * v) + t * (s * v - p * w) = w := by linear_combination (-w) * hε
        rw [hv, hw]; exact huv
    · rintro ⟨u, v, w, huv⟩
      exact ⟨u, p * v + r * w, s * v + t * w, by rw [fq3S_subst_vw]; exact huv⟩
  rcases hK l m₁ (m₂ * p + μ * s) (m₂ * r + μ * t) q with hInf | hBd
  · left; rw [hEq]; exact hInf
  · right
    intro c hc
    rw [hEq] at hc
    refine le_trans (hBd c hc) ?_
    apply fbound3S_mono
    rw [aux_M_cast]
    have := aux_abs_pair_le m₂ μ p r s t
    nlinarith [this, abs_nonneg l, abs_nonneg μ, abs_nonneg m₁, abs_nonneg m₂, abs_nonneg p, abs_nonneg r,
      abs_nonneg s, abs_nonneg t, mul_nonneg (abs_nonneg l) (abs_nonneg p),
      mul_nonneg (abs_nonneg l) (abs_nonneg r), mul_nonneg (abs_nonneg l) (abs_nonneg s),
      mul_nonneg (abs_nonneg l) (abs_nonneg t), mul_nonneg (abs_nonneg m₁) (abs_nonneg p),
      mul_nonneg (abs_nonneg m₁) (abs_nonneg r), mul_nonneg (abs_nonneg m₁) (abs_nonneg s),
      mul_nonneg (abs_nonneg m₁) (abs_nonneg t)]

/-- A block with C₁₂ = C₂₂ = 0 (rank ≤ 1 in normal form) satisfies the dichotomy for every b: the radical
    pair (B₂, b) is moved to (gcd, 0) by a unimodular change of (v, w), landing in the fixed-modulus leaf. -/
theorem aux_dichotomyS_diag_u (A B₁ B₂ C₁₁ b : ℤ) : DichotomyS A B₁ B₂ C₁₁ 0 0 b := by
  by_cases hB : B₂ = 0 ∧ b = 0
  · obtain ⟨h1, h2⟩ := hB
    subst h1; subst h2
    exact fixed_modulus_dichotomy A B₁ 0 C₁₁ 0 0
  · have hgpos : 0 < Int.gcd B₂ b := by
      rcases Nat.eq_zero_or_pos (Int.gcd B₂ b) with h | h
      · exfalso; apply hB
        exact ⟨Int.natAbs_eq_zero.mp (Nat.eq_zero_of_gcd_eq_zero_left h),
          Int.natAbs_eq_zero.mp (Nat.eq_zero_of_gcd_eq_zero_right h)⟩
      · exact h
    obtain ⟨g, b₁, b₂, _hgpos, hcop, hB2, hb⟩ := Int.exists_gcd_one' hgpos
    have hbez : b₁ * Int.gcdA b₁ b₂ + b₂ * Int.gcdB b₁ b₂ = 1 := by
      have h := Int.gcd_eq_gcd_ab b₁ b₂
      rw [hcop] at h; push_cast at h; linarith
    refine dichotomyS_of_unimodular_vw A B₁ B₂ C₁₁ b (Int.gcdA b₁ b₂) (-b₂) (Int.gcdB b₁ b₂) b₁
      (Or.inl (by linear_combination hbez)) ?_
    have e1 : B₂ * Int.gcdA b₁ b₂ + b * Int.gcdB b₁ b₂ = (g : ℤ) := by
      rw [hB2, hb]; linear_combination (g : ℤ) * hbez
    have e2 : B₂ * (-b₂) + b * b₁ = 0 := by rw [hB2, hb]; ring
    rw [e1, e2]
    exact fixed_modulus_dichotomy A B₁ (g : ℤ) C₁₁ 0 0

theorem singular_rank_one_normal_dichotomy (A B₁ B₂ k b : ℤ) (hk : k ≠ 0) : DichotomyS A B₁ B₂ k 0 0 b :=
  aux_dichotomyS_diag_u A B₁ B₂ k b

theorem singular_rank_one_dichotomy (A B₁ B₂ C₁₁ C₁₂ C₂₂ b : ℤ) (hd : discW C₁₁ C₁₂ C₂₂ = 0)
    (hne : ¬ (C₁₁ = 0 ∧ C₁₂ = 0 ∧ C₂₂ = 0)) : DichotomyS A B₁ B₂ C₁₁ C₁₂ C₂₂ b := by
  obtain ⟨p, r, s, t, k, hdet, hk, h1, h2, h3⟩ := rank_one_normal_form C₁₁ C₁₂ C₂₂ hd hne
  refine dichotomyS_of_unimodular_uv A B₁ B₂ C₁₁ C₁₂ C₂₂ b p r s t hdet ?_
  rw [h1, h2, h3]
  exact singular_rank_one_normal_dichotomy A _ _ k b hk

theorem singular_rank_zero_dichotomy (A B₁ B₂ b : ℤ) : DichotomyS A B₁ B₂ 0 0 0 b :=
  aux_dichotomyS_diag_u A B₁ B₂ 0 b

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.fbound3S_mono
#print axioms DiophCompression.SemanticQuadraticSingular.fq3S_subst_uv
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomyS_of_unimodular_uv
#print axioms DiophCompression.SemanticQuadraticSingular.fq3S_subst_vw
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomyS_of_unimodular_vw
#print axioms DiophCompression.SemanticQuadraticSingular.singular_rank_one_normal_dichotomy
#print axioms DiophCompression.SemanticQuadraticSingular.singular_rank_one_dichotomy
#print axioms DiophCompression.SemanticQuadraticSingular.singular_rank_zero_dichotomy
