/-
  DiophCompression/SemanticQuadraticTwoWitness/Directions.lean — GPT r07 必須4 (+ split, ours), s8 claude.ai direct.
  Explicit non-square directions for binary integral forms: definite (even cross coefficient, w ∈ {(1,0),(0,1),(1,p²)}),
  anisotropic (Q(k−b, 2a) = a(k²−D), k ∈ {0,1,D,D+1}, gcd argument), split (adjugate direction, value n(n+1)).
  No search, no real numbers. Frozen statements: `TwoWitness_STATEMENTS_v2.lean` (md5 3e2c4c02). Mathematics: CLASSIFICATION_2W.md §3.3.
-/
import DiophCompression.SemanticQuadraticTwoWitness.DefsScaled

namespace DiophCompression.SemanticQuadraticTwoWitness

/-! ### Elementary non-square helpers -/

/-- No square strictly between n² and (n+1)². -/
theorem not_isSquare_of_between (n X : ℤ) (h1 : n ^ 2 < X) (h2 : X < (n + 1) ^ 2) : ¬ IsSquare X := by
  rintro ⟨s, hs⟩
  have hX : X = |s| ^ 2 := by rw [sq_abs, hs]; ring
  have hn : 0 ≤ n := by nlinarith
  have ht : 0 ≤ |s| := abs_nonneg s
  have h3 : n < |s| := by
    by_contra hc; push Not at hc
    have := mul_le_mul hc hc ht hn
    nlinarith
  have h4 : |s| < n + 1 := by
    by_contra hc; push Not at hc
    have := mul_le_mul hc hc (by linarith) ht
    nlinarith
  omega

/-- n(n+1) is not a square for n ≥ 1; used with n = t². -/
theorem not_isSquare_mul_succ (n : ℤ) (hn : 0 < n) : ¬ IsSquare (n * (n + 1)) :=
  not_isSquare_of_between n _ (by nlinarith) (by nlinarith)

/-- r² · X is a square only if X is. -/
theorem not_isSquare_sq_mul (r X : ℤ) (hr : r ≠ 0) (hX : ¬ IsSquare X) : ¬ IsSquare (r ^ 2 * X) := by
  rintro ⟨s, hs⟩
  have hdvd : r ^ 2 ∣ s ^ 2 := ⟨X, by rw [sq, ← hs]⟩
  obtain ⟨t, ht⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp hdvd
  apply hX
  refine ⟨t, ?_⟩
  have h2 : r ^ 2 * X = r ^ 2 * (t * t) := by rw [hs, ht]; ring
  exact mul_left_cancel₀ (pow_ne_zero 2 hr) h2

/-- If X > 0 is not a square and X, Y are coprime, then X·Y is not a square. -/
theorem not_isSquare_mul_of_coprime (X Y : ℤ) (hX : 0 < X) (hcop : IsCoprime X Y) (hXns : ¬ IsSquare X) :
    ¬ IsSquare (X * Y) := by
  rintro ⟨s, hs⟩
  obtain ⟨a0, h | h⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hcop) (by rw [hs]; ring : X * Y = s ^ 2)
  · exact hXns ⟨a0, by rw [h]; ring⟩
  · nlinarith [sq_nonneg a0]

/-- If X·Y is not a square then, for any hA ≠ 0, not both hA·X and hA·Y are squares. -/
theorem not_both_squares (hA X Y : ℤ) (hhA : hA ≠ 0) (hXY : ¬ IsSquare (X * Y)) :
    ¬ IsSquare (hA * X) ∨ ¬ IsSquare (hA * Y) := by
  by_contra hc; push Not at hc
  obtain ⟨⟨r₁, h₁⟩, ⟨r₂, h₂⟩⟩ := hc
  have hprod : hA ^ 2 * (X * Y) = (r₁ * r₂) ^ 2 := by
    calc hA ^ 2 * (X * Y) = (hA * X) * (hA * Y) := by ring
      _ = (r₁ * r₁) * (r₂ * r₂) := by rw [h₁, h₂]
      _ = (r₁ * r₂) ^ 2 := by ring
  have hdvd : hA ^ 2 ∣ (r₁ * r₂) ^ 2 := ⟨X * Y, hprod.symm⟩
  obtain ⟨t, ht⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp hdvd
  apply hXY
  refine ⟨t, ?_⟩
  have h2 : hA ^ 2 * (X * Y) = hA ^ 2 * (t * t) := by rw [hprod, ht]; ring
  exact mul_left_cancel₀ (pow_ne_zero 2 hhA) h2

/-! ### Definite direction (GPT r07 problem C) -/

theorem definite_nonsquare_direction (p h q : ℤ) (hp : 0 < p) (hq : 0 < q) (hdef : h ^ 2 < 4 * p * q)
    (heven : Even h) :
    ∃ x y : ℤ, 0 < p * x ^ 2 + h * x * y + q * y ^ 2 ∧ ¬ IsSquare (p * x ^ 2 + h * x * y + q * y ^ 2) := by
  by_cases hps : IsSquare p
  · by_cases hqs : IsSquare q
    · obtain ⟨r0, hr0⟩ := hps
      obtain ⟨t0, ht0⟩ := hqs
      obtain ⟨r, hr⟩ : ∃ r : ℤ, r = |r0| := ⟨_, rfl⟩
      obtain ⟨t, ht⟩ : ∃ t : ℤ, t = |t0| := ⟨_, rfl⟩
      have hpr : p = r ^ 2 := by rw [hr, sq_abs, hr0]; ring
      have hqt : q = t ^ 2 := by rw [ht, sq_abs, ht0]; ring
      have hr1 : 0 < r := by
        rcases lt_or_eq_of_le (abs_nonneg r0) with h1 | h1
        · rw [hr]; exact h1
        · rw [hpr, hr, ← h1] at hp; simp at hp
      have ht1 : 0 < t := by
        rcases lt_or_eq_of_le (abs_nonneg t0) with h1 | h1
        · rw [ht]; exact h1
        · rw [hqt, ht, ← h1] at hq; simp at hq
      obtain ⟨m, hm⟩ : ∃ m : ℤ, m = r * t := ⟨_, rfl⟩
      have hm0 : 0 < m := by rw [hm]; positivity
      have hlt : |h| < 2 * m := by
        apply abs_lt_of_sq_lt_sq _ (by linarith)
        rw [hpr, hqt] at hdef; rw [hm]; nlinarith
      have hlt' := abs_lt.mp hlt
      refine ⟨1, p, ?_, ?_⟩
      · have : p * 1 ^ 2 + h * 1 * p + q * p ^ 2 = r ^ 2 * (m ^ 2 + h + 1) := by
          rw [hpr, hqt, hm]; ring
        rw [this]
        have : (m - 1) ^ 2 < m ^ 2 + h + 1 := by nlinarith
        have : 0 < m ^ 2 + h + 1 := by nlinarith [sq_nonneg (m - 1)]
        positivity
      · have hval : p * 1 ^ 2 + h * 1 * p + q * p ^ 2 = r ^ 2 * (m ^ 2 + h + 1) := by
          rw [hpr, hqt, hm]; ring
        rw [hval]
        apply not_isSquare_sq_mul r _ hr1.ne'
        rintro ⟨s, hs⟩
        have hu : m ^ 2 + h + 1 = |s| ^ 2 := by rw [sq_abs, hs]; ring
        have hu0 : 0 ≤ |s| := abs_nonneg s
        have h3 : m - 1 < |s| := by
          by_contra hc; push Not at hc
          have := mul_le_mul hc hc hu0 (by linarith)
          nlinarith
        have h4 : |s| < m + 1 := by
          by_contra hc; push Not at hc
          have := mul_le_mul hc hc (by linarith) hu0
          nlinarith
        have hsm : |s| = m := by omega
        have hh1 : h = -1 := by rw [hsm] at hu; nlinarith
        rw [Int.even_iff] at heven
        omega
    · exact ⟨0, 1, by norm_num; exact hq, by norm_num; exact hqs⟩
  · exact ⟨1, 0, by norm_num; exact hp, by norm_num; exact hps⟩

/-! ### Anisotropic direction (GPT r07 problem D) -/

theorem anisotropic_signed_nonsquare_direction (a b c h σ : ℤ) (hD : 0 < b ^ 2 - 4 * a * c)
    (hns : ¬ IsSquare (b ^ 2 - 4 * a * c)) (hh : 0 < h) (hσ : σ = 1 ∨ σ = -1) :
    ∃ x y : ℤ, 0 < σ * (a * x ^ 2 + b * x * y + c * y ^ 2)
      ∧ ¬ IsSquare (h * |a * x ^ 2 + b * x * y + c * y ^ 2|) := by
  obtain ⟨D, hDdef⟩ : ∃ D : ℤ, D = b ^ 2 - 4 * a * c := ⟨_, rfl⟩
  rw [← hDdef] at hD hns
  have ha : a ≠ 0 := by
    rintro rfl; apply hns; exact ⟨b, by rw [hDdef]; ring⟩
  have hD1 : D ≠ 1 := by rintro rfl; exact hns ⟨1, by ring⟩
  have hD2 : 2 ≤ D := by omega
  have key : ∀ k : ℤ, a * (k - b) ^ 2 + b * (k - b) * (2 * a) + c * (2 * a) ^ 2 = a * (k ^ 2 - D) := by
    intro k; rw [hDdef]; ring
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hcop1 : IsCoprime D (D - 1) := ⟨1, -1, by ring⟩
  have hcop2 : IsCoprime D (D ^ 3 - 1) := ⟨D ^ 2, -1, by ring⟩
  have hns1 : ¬ IsSquare (D * (D - 1)) := not_isSquare_mul_of_coprime D (D - 1) hD hcop1 hns
  have hns2 : ¬ IsSquare ((D * (D - 1)) * (D ^ 2 + D + 1)) := by
    rw [show (D * (D - 1)) * (D ^ 2 + D + 1) = D * (D ^ 3 - 1) by ring]
    exact not_isSquare_mul_of_coprime D _ hD hcop2 hns
  have hA : h * |a| ≠ 0 := mul_ne_zero hh.ne' (abs_ne_zero.mpr ha)
  have hσa : σ * a ≠ 0 := by
    rcases hσ with rfl | rfl <;> simpa using ha
  rcases lt_or_gt_of_ne hσa with hneg | hpos
  · -- σ a < 0: k = 0 or k = 1
    rcases not_both_squares (h * |a|) D (D - 1) hA hns1 with h1 | h1
    · refine ⟨0 - b, 2 * a, ?_, ?_⟩
      · rw [key 0]; nlinarith
      · rw [key 0]
        have : |a * (0 ^ 2 - D)| = |a| * D := by
          rw [abs_mul, abs_of_neg (by linarith : (0 : ℤ) ^ 2 - D < 0)]; ring
        rw [this, ← mul_assoc]; exact h1
    · refine ⟨1 - b, 2 * a, ?_, ?_⟩
      · rw [key 1]; nlinarith
      · rw [key 1]
        have : |a * (1 ^ 2 - D)| = |a| * (D - 1) := by
          rw [abs_mul, abs_of_neg (by linarith : (1 : ℤ) ^ 2 - D < 0)]; ring
        rw [this, ← mul_assoc]; exact h1
  · -- σ a > 0: k = D or k = D + 1
    rcases not_both_squares (h * |a|) (D * (D - 1)) (D ^ 2 + D + 1) hA hns2 with h1 | h1
    · refine ⟨D - b, 2 * a, ?_, ?_⟩
      · rw [key D, show σ * (a * (D ^ 2 - D)) = (σ * a) * (D ^ 2 - D) by ring]
        exact mul_pos hpos (by nlinarith)
      · rw [key D]
        have : |a * (D ^ 2 - D)| = |a| * (D * (D - 1)) := by
          rw [abs_mul, abs_of_pos (by nlinarith : (0 : ℤ) < D ^ 2 - D)]; ring
        rw [this, ← mul_assoc]; exact h1
    · refine ⟨D + 1 - b, 2 * a, ?_, ?_⟩
      · rw [key (D + 1), show σ * (a * ((D + 1) ^ 2 - D)) = (σ * a) * ((D + 1) ^ 2 - D) by ring]
        exact mul_pos hpos (by nlinarith)
      · rw [key (D + 1)]
        have : |a * ((D + 1) ^ 2 - D)| = |a| * (D ^ 2 + D + 1) := by
          rw [abs_mul, abs_of_pos (by nlinarith : (0 : ℤ) < (D + 1) ^ 2 - D)]; ring
        rw [this, ← mul_assoc]; exact h1

/-! ### Split direction (ours; GPT r07 problem G / 必須6) -/

/-- Finisher: a value K·y₀ with y₀ = σKh(K²h²+1) has sign σ and h·|value| = n(n+1), n = (Kh)². -/
theorem split_finish (K σ h : ℤ) (hK : K ≠ 0) (hh : 0 < h) (hσ2 : σ * σ = 1) :
    0 < σ * (K * (σ * K * h * (K ^ 2 * h ^ 2 + 1)))
      ∧ ¬ IsSquare (h * |K * (σ * K * h * (K ^ 2 * h ^ 2 + 1))|) := by
  have hK2 : 0 < K ^ 2 := by positivity
  have hE : 0 < K ^ 2 * h ^ 2 + 1 := by positivity
  have e1 : σ * (K * (σ * K * h * (K ^ 2 * h ^ 2 + 1))) = K ^ 2 * h * (K ^ 2 * h ^ 2 + 1) := by
    linear_combination (K ^ 2 * h * (K ^ 2 * h ^ 2 + 1)) * hσ2
  constructor
  · rw [e1]; positivity
  · have e2 : |K * (σ * K * h * (K ^ 2 * h ^ 2 + 1))| = K ^ 2 * h * (K ^ 2 * h ^ 2 + 1) := by
      have hσabs : |σ| = 1 := by
        rcases (mul_self_eq_one_iff.mp hσ2) with rfl | rfl <;> norm_num
      rw [show K * (σ * K * h * (K ^ 2 * h ^ 2 + 1)) = σ * (K ^ 2 * h * (K ^ 2 * h ^ 2 + 1)) by ring,
        abs_mul, hσabs, one_mul, abs_of_pos (by positivity)]
    rw [e2, show h * (K ^ 2 * h * (K ^ 2 * h ^ 2 + 1)) = (K ^ 2 * h ^ 2) * (K ^ 2 * h ^ 2 + 1) by ring]
    exact not_isSquare_mul_succ _ (by positivity)

theorem split_signed_nonsquare_direction (a b c h σ : ℤ) (hD : 0 < b ^ 2 - 4 * a * c)
    (hsq : IsSquare (b ^ 2 - 4 * a * c)) (hh : 0 < h) (hσ : σ = 1 ∨ σ = -1) :
    ∃ x y : ℤ, 0 < σ * (a * x ^ 2 + b * x * y + c * y ^ 2)
      ∧ ¬ IsSquare (h * |a * x ^ 2 + b * x * y + c * y ^ 2|) := by
  obtain ⟨d0, hd0⟩ := hsq
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = |d0| := ⟨_, rfl⟩
  have hdd : b ^ 2 - 4 * a * c = d ^ 2 := by rw [hd, sq_abs, hd0]; ring
  have hdpos : 0 < d := by
    rcases lt_or_eq_of_le (abs_nonneg d0) with h1 | h1
    · rw [hd]; exact h1
    · rw [hdd, hd, ← h1] at hD; simp at hD
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  by_cases ha : a = 0
  · by_cases hc : c = 0
    · -- Q = b x y, d = |b|
      subst ha; subst hc
      have hb : b ≠ 0 := by rintro rfl; simp at hD
      obtain ⟨y0, hy0⟩ : ∃ y0 : ℤ, y0 = σ * b * h * (b ^ 2 * h ^ 2 + 1) := ⟨_, rfl⟩
      refine ⟨1, y0, ?_⟩
      have hQ : 0 * 1 ^ 2 + b * 1 * y0 + 0 * y0 ^ 2 = b * y0 := by ring
      rw [hQ, hy0]
      exact split_finish b σ h hb hh hσ2
    · -- c ≠ 0: w = (-2c + 2c y0, (b + d) - (b - d) y0), Q = 4 c d² y0
      obtain ⟨K, hK⟩ : ∃ K : ℤ, K = 4 * c * d ^ 2 := ⟨_, rfl⟩
      have hK0 : K ≠ 0 := by rw [hK]; exact mul_ne_zero (mul_ne_zero (by norm_num) hc) (pow_ne_zero 2 hdpos.ne')
      obtain ⟨y0, hy0⟩ : ∃ y0 : ℤ, y0 = σ * K * h * (K ^ 2 * h ^ 2 + 1) := ⟨_, rfl⟩
      refine ⟨-2 * c + 2 * c * y0, (b + d) - (b - d) * y0, ?_⟩
      have hQ : a * (-2 * c + 2 * c * y0) ^ 2 + b * (-2 * c + 2 * c * y0) * ((b + d) - (b - d) * y0)
          + c * ((b + d) - (b - d) * y0) ^ 2 = K * y0 := by
        subst ha
        have h4 : 4 * c * (0 * (-2 * c + 2 * c * y0) ^ 2 + b * (-2 * c + 2 * c * y0) * ((b + d) - (b - d) * y0)
            + c * ((b + d) - (b - d) * y0) ^ 2 - K * y0) = 0 := by
          rw [hK]; linear_combination (-((-2 * c + 2 * c * y0) ^ 2)) * hdd
        rcases mul_eq_zero.mp h4 with h0 | h0
        · exact absurd (by omega : c = 0) hc
        · linarith
      rw [hQ, hy0]
      exact split_finish K σ h hK0 hh hσ2
  · -- a ≠ 0: w = ((b + d) - (b - d) y0, -2a + 2a y0), Q = 4 a d² y0
    obtain ⟨K, hK⟩ : ∃ K : ℤ, K = 4 * a * d ^ 2 := ⟨_, rfl⟩
    have hK0 : K ≠ 0 := by rw [hK]; exact mul_ne_zero (mul_ne_zero (by norm_num) ha) (pow_ne_zero 2 hdpos.ne')
    obtain ⟨y0, hy0⟩ : ∃ y0 : ℤ, y0 = σ * K * h * (K ^ 2 * h ^ 2 + 1) := ⟨_, rfl⟩
    refine ⟨(b + d) - (b - d) * y0, -2 * a + 2 * a * y0, ?_⟩
    have hQ : a * ((b + d) - (b - d) * y0) ^ 2 + b * ((b + d) - (b - d) * y0) * (-2 * a + 2 * a * y0)
        + c * (-2 * a + 2 * a * y0) ^ 2 = K * y0 := by
      have h4 : 4 * a * (a * ((b + d) - (b - d) * y0) ^ 2 + b * ((b + d) - (b - d) * y0) * (-2 * a + 2 * a * y0)
          + c * (-2 * a + 2 * a * y0) ^ 2 - K * y0) = 0 := by
        rw [hK]; linear_combination (-((-2 * a + 2 * a * y0) ^ 2)) * hdd
      rcases mul_eq_zero.mp h4 with h0 | h0
      · exact absurd (by omega : a = 0) ha
      · linarith
    rw [hQ, hy0]
    exact split_finish K σ h hK0 hh hσ2

end DiophCompression.SemanticQuadraticTwoWitness
#print axioms DiophCompression.SemanticQuadraticTwoWitness.definite_nonsquare_direction
#print axioms DiophCompression.SemanticQuadraticTwoWitness.anisotropic_signed_nonsquare_direction
#print axioms DiophCompression.SemanticQuadraticTwoWitness.split_signed_nonsquare_direction
