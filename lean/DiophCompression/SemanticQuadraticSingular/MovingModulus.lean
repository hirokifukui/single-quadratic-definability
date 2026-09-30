/-
  DiophCompression/SemanticQuadraticSingular/MovingModulus.lean — r10 必須H/I/K/L (GPT r09 §5, §8): the
  moving-modulus branch b ≠ 0 of a nondegenerate block (discW ≠ 0). Prime-progression step (r08
  `rank_one_coupled_prime_step` pattern): from a fiber point c₀ with t₀ = b c₀ + μ > 0 pick a prime
  p ≡ 1 (mod 2·|discW|·b·t₀), set c = c₀ + t₀ (p−1)/b so that b c + μ = t₀ p; fixed part t₀ by congruence
  (c,u,v) ≡ (c₀,u₀,v₀), prime part p by a root of the c-free remainder R mod p (必須J) and b invertible mod p
  (p ∤ b since b ∣ p−1) — the gcd normalisation of 必須H is provided but not load-bearing. K = 1.
  Statements frozen in `Singular_STATEMENTS.lean` (md5 281708fb). Session 10, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticSingular.TransferS
import DiophCompression.SemanticQuadraticSingular.FiniteFieldQuadratic

namespace DiophCompression.SemanticQuadraticSingular

open Matrix DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticTwoWitness
  DiophCompression.SemanticQuadraticGeneral

/-! ## 必須H: normalisation (not load-bearing for the prime step; see header) -/

theorem aux_content_pos (b μ : ℤ) (hb : b ≠ 0) : 0 < modulusContent b μ := by
  unfold modulusContent
  exact_mod_cast Int.gcd_pos_of_ne_zero_left μ hb

theorem aux_content_dvd_b (b μ : ℤ) : modulusContent b μ ∣ b := Int.gcd_dvd_left b μ
theorem aux_content_dvd_μ (b μ : ℤ) : modulusContent b μ ∣ μ := Int.gcd_dvd_right b μ

theorem aux_slope_eq (b μ : ℤ) : normalizedSlope b μ = Int.sign b * (b / modulusContent b μ) := by
  unfold normalizedSlope
  have h : |b| = Int.sign b * b := by rw [mul_comm, Int.mul_sign_self, Int.natCast_natAbs]
  rw [h, Int.mul_ediv_assoc _ (aux_content_dvd_b b μ)]

theorem aux_offset_eq (b μ : ℤ) : normalizedOffset b μ = Int.sign b * (μ / modulusContent b μ) := by
  unfold normalizedOffset
  rw [Int.mul_ediv_assoc _ (aux_content_dvd_μ b μ)]

theorem normalizedSlope_pos (b μ : ℤ) (hb : b ≠ 0) : 0 < normalizedSlope b μ := by
  unfold normalizedSlope
  have hg := aux_content_pos b μ hb
  obtain ⟨k, hk⟩ : modulusContent b μ ∣ |b| := dvd_trans (aux_content_dvd_b b μ) (self_dvd_abs b)
  rw [hk, Int.mul_ediv_cancel_left _ hg.ne']
  have : 0 < |b| := abs_pos.mpr hb
  rw [hk] at this
  exact pos_of_mul_pos_right this hg.le

theorem normalizedSlope_offset_coprime (b μ : ℤ) (hb : b ≠ 0) :
    Int.gcd (normalizedSlope b μ) (normalizedOffset b μ) = 1 := by
  rw [aux_slope_eq, aux_offset_eq, Int.gcd_mul_left, Int.natAbs_sign, if_neg hb, one_mul]
  unfold modulusContent
  exact Int.gcd_div_gcd_div_gcd (Int.gcd_pos_of_ne_zero_left μ hb)

theorem normalizedSlope_coprime_modulus (b μ c : ℤ) (hb : b ≠ 0) :
    Int.gcd (normalizedSlope b μ) (normalizedLinearModulus b μ c) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  have h := Int.isCoprime_iff_gcd_eq_one.mpr (normalizedSlope_offset_coprime b μ hb)
  unfold normalizedLinearModulus
  exact h.mul_add_left_right c

theorem normalizedLinearModulus_mul_content (b μ c : ℤ) (hb : b ≠ 0) :
    modulusContent b μ * normalizedLinearModulus b μ c = Int.sign b * (b * c + μ) := by
  unfold normalizedLinearModulus
  rw [aux_slope_eq, aux_offset_eq]
  have h1 := Int.mul_ediv_cancel' (aux_content_dvd_b b μ)
  have h2 := Int.mul_ediv_cancel' (aux_content_dvd_μ b μ)
  linear_combination (Int.sign b * c) * h1 + Int.sign b * h2

/-! ## 必須I: remainder identity -/

theorem moving_remainder_identity (A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q c u v : ℤ) :
    b ^ 2 * fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v =
      movingRemainderPoly A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q (b * u) (b * v)
        + (b * c + μ) * (A * (b * c - μ) + b * (B₁ * u + B₂ * v) + b * l) := by
  unfold fq2 movingRemainderPoly; ring

theorem moving_divisibility_iff_remainder (A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q c u v : ℤ)
    (hcop : IsCoprime b (b * c + μ)) :
    (b * c + μ) ∣ fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v ↔
      (b * c + μ) ∣ movingRemainderPoly A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q (b * u) (b * v) := by
  have hid := moving_remainder_identity A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q c u v
  constructor
  · intro h
    have h1 : (b * c + μ) ∣ b ^ 2 * fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v := Dvd.dvd.mul_left h _
    have h2 : (b * c + μ) ∣ (b * c + μ) * (A * (b * c - μ) + b * (B₁ * u + B₂ * v) + b * l) :=
      Dvd.intro _ rfl
    have := dvd_sub h1 h2
    rw [hid] at this
    simpa using this
  · intro h
    have h2 : (b * c + μ) ∣ (b * c + μ) * (A * (b * c - μ) + b * (B₁ * u + B₂ * v) + b * l) :=
      Dvd.intro _ rfl
    have h1 : (b * c + μ) ∣ b ^ 2 * fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v := by
      rw [hid]; exact dvd_add h h2
    exact (hcop.symm.pow_right).dvd_of_dvd_mul_left h1

/-! ## Difference lemmas (congruence transport) -/

theorem aux_fq2_sub (A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v c₀ u₀ v₀ : ℤ) :
    fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v - fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c₀ u₀ v₀ =
      (c - c₀) * (A * (c + c₀) + B₁ * u + B₂ * v + l)
        + (u - u₀) * (B₁ * c₀ + C₁₁ * (u + u₀) + C₁₂ * v + m₁)
        + (v - v₀) * (B₂ * c₀ + C₁₂ * u₀ + C₂₂ * (v + v₀) + m₂) := by
  unfold fq2; ring

theorem aux_fq2_dvd_sub (A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v c₀ u₀ v₀ d : ℤ)
    (hc : d ∣ c - c₀) (hu : d ∣ u - u₀) (hv : d ∣ v - v₀) :
    d ∣ fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v - fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c₀ u₀ v₀ := by
  rw [aux_fq2_sub]
  exact dvd_add (dvd_add (Dvd.dvd.mul_right hc _) (Dvd.dvd.mul_right hu _)) (Dvd.dvd.mul_right hv _)

theorem aux_R_sub (A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q x y x₀ y₀ : ℤ) :
    movingRemainderPoly A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q x y
      - movingRemainderPoly A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q x₀ y₀ =
      (x - x₀) * (C₁₁ * (x + x₀) + C₁₂ * y + (b * m₁ - μ * B₁))
        + (y - y₀) * (C₁₂ * x₀ + C₂₂ * (y + y₀) + (b * m₂ - μ * B₂)) := by
  unfold movingRemainderPoly; ring

theorem aux_R_dvd_sub (A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q x y x₀ y₀ d : ℤ)
    (hx : d ∣ x - x₀) (hy : d ∣ y - y₀) :
    d ∣ movingRemainderPoly A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q x y
      - movingRemainderPoly A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q x₀ y₀ := by
  rw [aux_R_sub]
  exact dvd_add (Dvd.dvd.mul_right hx _) (Dvd.dvd.mul_right hy _)

/-- p ∣ (p − 1) forces p ∣ 1: a prime cannot divide a positive multiple of itself minus one. -/
theorem aux_prime_not_dvd_of_dvd_pred (p : ℕ) (hp : p.Prime) (x : ℤ) (hx : x ∣ (p : ℤ) - 1) :
    ¬ (p : ℤ) ∣ x := by
  intro hc
  have := dvd_trans hc hx
  have h1 : (p : ℤ) ∣ 1 := by
    have := dvd_sub (dvd_refl (p : ℤ)) this; simpa using this
  have := Int.eq_one_of_dvd_one (by positivity) h1
  have := hp.one_lt; omega

/-! ## 必須K: bound on the non-positive side, prime-progression step -/

theorem moving_modulus_nonpositive_bound (b μ c : ℤ) (hb : 0 < b) (h : b * c + μ ≤ 0) : c ≤ |μ| := by
  have hμ : -μ ≤ |μ| := neg_le_abs μ
  rcases le_or_gt c 0 with hc | hc
  · exact le_trans hc (abs_nonneg μ)
  · have : c ≤ b * c := by nlinarith
    linarith

theorem moving_modulus_prime_step (A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q c₀ u₀ v₀ : ℤ) (hb : 0 < b)
    (hN : discW C₁₁ C₁₂ C₂₂ ≠ 0) (ht₀ : 0 < b * c₀ + μ)
    (hdiv : (b * c₀ + μ) ∣ fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c₀ u₀ v₀) :
    ∃ c u v : ℤ, c₀ < c ∧ (b * c + μ) ∣ fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v := by
  obtain ⟨t₀, ht₀def⟩ : ∃ t₀ : ℤ, t₀ = b * c₀ + μ := ⟨_, rfl⟩
  rw [← ht₀def] at ht₀ hdiv
  obtain ⟨D', hD'⟩ : ∃ D' : ℤ, D' = discW C₁₁ C₁₂ C₂₂ := ⟨_, rfl⟩
  have hD'ne : D' ≠ 0 := by rw [hD']; exact hN
  -- the modulus of the prime progression
  obtain ⟨Mn, hMn⟩ : ∃ Mn : ℕ, Mn = 2 * D'.natAbs * b.natAbs * t₀.natAbs := ⟨_, rfl⟩
  have h1 : D'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD'ne
  have h2 : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb.ne'
  have h4 : t₀.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht₀.ne'
  have hM0 : Mn ≠ 0 := by rw [hMn]; positivity
  have hMpos : 0 < Mn := Nat.pos_of_ne_zero hM0
  obtain ⟨p, hp, hpM, hpmod⟩ := Nat.exists_prime_gt_modEq_one Mn hM0
  haveI := Fact.mk hp
  have hMdvd : (Mn : ℤ) ∣ (p : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd' (by omega : 1 ≤ p)).mp hpmod.symm
    have h' := Int.natCast_dvd_natCast.mpr h
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at h'
  have hMcast : (Mn : ℤ) = 2 * |D'| * b * t₀ := by
    rw [hMn]; push_cast
    rw [abs_of_pos hb, abs_of_pos ht₀]
  have hbdvd : b ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact ⟨2 * |D'| * t₀, by ring⟩
  have ht₀dvd : t₀ ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact ⟨2 * |D'| * b, by ring⟩
  have h2dvd : (2 : ℤ) ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact ⟨|D'| * b * t₀, by ring⟩
  have hD'dvd : D' ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact (self_dvd_abs D').trans ⟨2 * b * t₀, by ring⟩
  have hpb : ¬ (p : ℤ) ∣ b := aux_prime_not_dvd_of_dvd_pred p hp b hbdvd
  have hpt₀ : ¬ (p : ℤ) ∣ t₀ := aux_prime_not_dvd_of_dvd_pred p hp t₀ ht₀dvd
  have hp2' : ¬ (p : ℤ) ∣ 2 := aux_prime_not_dvd_of_dvd_pred p hp 2 h2dvd
  have hpD : ¬ (p : ℤ) ∣ discW C₁₁ C₁₂ C₂₂ := by
    rw [← hD']; exact aux_prime_not_dvd_of_dvd_pred p hp D' hD'dvd
  have hp2 : p ≠ 2 := by
    intro h; apply hp2'; rw [h]; norm_num
  -- the new output c = c₀ + t₀ (p−1)/b, so that b c + μ = t₀ p
  obtain ⟨j, hj⟩ := hbdvd
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = c₀ + t₀ * j := ⟨_, rfl⟩
  have hj1 : 1 ≤ j := by
    have hpB : b ≤ (p : ℤ) - 1 := by
      have : b.natAbs ≤ Mn := Nat.le_of_dvd hMpos ⟨2 * D'.natAbs * t₀.natAbs, by rw [hMn]; ring⟩
      have : (b.natAbs : ℤ) = b := by rw [Int.natCast_natAbs, abs_of_pos hb]
      omega
    by_contra hcon; push Not at hcon
    have : b * j ≤ b * 0 := mul_le_mul_of_nonneg_left (by omega) hb.le
    linarith
  have hct : b * c + μ = t₀ * p := by rw [hc]; linear_combination (-t₀) * hj - ht₀def
  have hc₀c : c₀ < c := by rw [hc]; nlinarith
  -- root of R mod p, pulled back through b (invertible mod p)
  obtain ⟨x, y, hxy⟩ := moving_remainder_root_mod_prime p hp hp2 A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q hpD
  have hcopbp : IsCoprime b (p : ℤ) := by
    have hnat : b.natAbs.Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hc'
      apply hpb
      have := Int.natCast_dvd_natCast.mpr hc'
      rwa [Int.natCast_natAbs, abs_of_pos hb] at this
    have := hnat.isCoprime
    rwa [Int.natCast_natAbs, abs_of_pos hb] at this
  obtain ⟨α, β, hαβ⟩ := hcopbp
  obtain ⟨up, hup⟩ : ∃ up : ℤ, up = α * x := ⟨_, rfl⟩
  obtain ⟨vp, hvp⟩ : ∃ vp : ℤ, vp = α * y := ⟨_, rfl⟩
  have hbup : (p : ℤ) ∣ b * up - x := ⟨-(β * x), by rw [hup]; linear_combination x * hαβ⟩
  have hbvp : (p : ℤ) ∣ b * vp - y := ⟨-(β * y), by rw [hvp]; linear_combination y * hαβ⟩
  -- CRT: (u, v) ≡ (u₀, v₀) (mod t₀), ≡ (up, vp) (mod p)
  have hcop : IsCoprime t₀ (p : ℤ) := by
    have hnat : t₀.natAbs.Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hc'
      apply hpt₀
      have := Int.natCast_dvd_natCast.mpr hc'
      rwa [Int.natCast_natAbs, abs_of_pos ht₀] at this
    have := hnat.isCoprime
    rwa [Int.natCast_natAbs, abs_of_pos ht₀] at this
  obtain ⟨a', b', hab⟩ := hcop
  obtain ⟨u, hu⟩ : ∃ u : ℤ, u = up * (a' * t₀) + u₀ * (b' * p) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℤ, v = vp * (a' * t₀) + v₀ * (b' * p) := ⟨_, rfl⟩
  have hu₀ : t₀ ∣ u - u₀ := ⟨a' * (up - u₀), by rw [hu]; linear_combination u₀ * hab⟩
  have hup' : (p : ℤ) ∣ u - up := ⟨b' * (u₀ - up), by rw [hu]; linear_combination up * hab⟩
  have hv₀ : t₀ ∣ v - v₀ := ⟨a' * (vp - v₀), by rw [hv]; linear_combination v₀ * hab⟩
  have hvp' : (p : ℤ) ∣ v - vp := ⟨b' * (v₀ - vp), by rw [hv]; linear_combination vp * hab⟩
  refine ⟨c, u, v, hc₀c, ?_⟩
  rw [hct]
  apply IsCoprime.mul_dvd ⟨a', b', hab⟩
  · -- t₀ ∣ F(c,u,v): congruent to F(c₀,u₀,v₀)
    have hcc : t₀ ∣ c - c₀ := ⟨j, by rw [hc]; ring⟩
    have := dvd_add hdiv (aux_fq2_dvd_sub A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v c₀ u₀ v₀ t₀ hcc hu₀ hv₀)
    simpa using this
  · -- p ∣ F(c,u,v): b² F = R(bu, bv) + (b c + μ)·Q, p ∣ b c + μ, p ∣ R(bu,bv) ≡ R(x,y)
    have hpR : (p : ℤ) ∣ movingRemainderPoly A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q (b * u) (b * v) := by
      have hx' : (p : ℤ) ∣ b * u - x := by
        have := dvd_add (Dvd.dvd.mul_left hup' b) hbup
        have e : b * (u - up) + (b * up - x) = b * u - x := by ring
        rwa [e] at this
      have hy' : (p : ℤ) ∣ b * v - y := by
        have := dvd_add (Dvd.dvd.mul_left hvp' b) hbvp
        have e : b * (v - vp) + (b * vp - y) = b * v - y := by ring
        rwa [e] at this
      have := dvd_add hxy (aux_R_dvd_sub A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q (b * u) (b * v) x y p hx' hy')
      simpa using this
    have hpt : (p : ℤ) ∣ b * c + μ := ⟨t₀, by rw [hct]; ring⟩
    have hpb2 : (p : ℤ) ∣ b ^ 2 * fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v := by
      rw [moving_remainder_identity A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q c u v]
      exact dvd_add hpR (Dvd.dvd.mul_right hpt _)
    have hcopb : IsCoprime (p : ℤ) b := ⟨β, α, by linear_combination hαβ⟩
    exact (hcopb.pow_right).dvd_of_dvd_mul_left hpb2

/-! ## 必須L: the moving-modulus dichotomy (K = 1) -/

theorem aux_fiberSet3S_neg_w (A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q : ℤ) :
    fiberSet3S A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q = fiberSet3S A B₁ B₂ C₁₁ C₁₂ C₂₂ (-b) l m₁ m₂ (-μ) q := by
  ext c
  simp only [fiberSet3S, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, v, w, h⟩
    exact ⟨u, v, -w, by unfold fq3S at h ⊢; linear_combination h⟩
  · rintro ⟨u, v, w, h⟩
    exact ⟨u, v, -w, by unfold fq3S at h ⊢; linear_combination h⟩

theorem aux_dichotomyS_neg_b (A B₁ B₂ C₁₁ C₁₂ C₂₂ b : ℤ) (h : DichotomyS A B₁ B₂ C₁₁ C₁₂ C₂₂ (-b)) :
    DichotomyS A B₁ B₂ C₁₁ C₁₂ C₂₂ b := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun l m₁ m₂ μ q => ?_⟩
  rw [aux_fiberSet3S_neg_w]
  rcases hK l m₁ m₂ (-μ) q with hInf | hBd
  · exact Or.inl hInf
  · right
    intro c hc
    have := hBd c hc
    unfold fbound3S at this ⊢
    rwa [abs_neg] at this

theorem rank_two_moving_modulus_pos (A B₁ B₂ C₁₁ C₁₂ C₂₂ b : ℤ) (hN : discW C₁₁ C₁₂ C₂₂ ≠ 0) (hb : 0 < b) :
    DichotomyS A B₁ B₂ C₁₁ C₁₂ C₂₂ b := by
  refine ⟨1, fun l m₁ m₂ μ q => ?_⟩
  rw [singular_fiberSet_eq_divisibility]
  by_cases hex : ∃ c₀ : ℕ, (∃ u v : ℤ, (b * (c₀ : ℤ) + μ) ∣ fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c₀ u v)
      ∧ 0 < b * (c₀ : ℤ) + μ
  · left
    obtain ⟨c₀, ⟨u₀, v₀, hdiv₀⟩, hpos₀⟩ := hex
    -- unbounded chain of fiber points with positive modulus
    have key : ∀ n : ℕ, ∃ c : ℕ, (n : ℤ) ≤ c ∧ 0 < b * (c : ℤ) + μ ∧
        ∃ u v : ℤ, (b * (c : ℤ) + μ) ∣ fq2 A B₁ B₂ C₁₁ C₁₂ C₂₂ l m₁ m₂ q c u v := by
      intro n
      induction n with
      | zero => exact ⟨c₀, by positivity, hpos₀, u₀, v₀, hdiv₀⟩
      | succ n ih =>
        obtain ⟨c, hnc, hpos, u, v, hdiv⟩ := ih
        obtain ⟨c', u', v', hlt, hdiv'⟩ := moving_modulus_prime_step A B₁ B₂ C₁₁ C₁₂ C₂₂ b l m₁ m₂ μ q
          c u v hb hN hpos hdiv
        have hc'nn : 0 ≤ c' := by
          have : (0 : ℤ) ≤ c := by positivity
          omega
        refine ⟨c'.toNat, ?_, ?_, u', v', ?_⟩
        · rw [Int.toNat_of_nonneg hc'nn]; push_cast; omega
        · rw [Int.toNat_of_nonneg hc'nn]; nlinarith
        · rw [Int.toNat_of_nonneg hc'nn]; exact hdiv'
    apply Set.infinite_of_forall_exists_gt
    intro n
    obtain ⟨c, hnc, _, hmem⟩ := key (n + 1)
    refine ⟨c, hmem, ?_⟩
    push_cast at hnc; omega
  · right
    push Not at hex
    intro c hc
    have hle : b * (c : ℤ) + μ ≤ 0 := hex c hc
    have h1 := moving_modulus_nonpositive_bound b μ c hb hle
    unfold fbound3S
    push_cast
    have h2 : |μ| ≤ (1 + |l| + |m₁| + |m₂| + |μ|) ^ 2 + |q| := by
      nlinarith [abs_nonneg l, abs_nonneg m₁, abs_nonneg m₂, abs_nonneg μ, abs_nonneg q]
    linarith

theorem rank_two_moving_modulus_dichotomy (A B₁ B₂ C₁₁ C₁₂ C₂₂ b : ℤ) (hN : discW C₁₁ C₁₂ C₂₂ ≠ 0)
    (hb : b ≠ 0) : DichotomyS A B₁ B₂ C₁₁ C₁₂ C₂₂ b := by
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · exact aux_dichotomyS_neg_b A B₁ B₂ C₁₁ C₁₂ C₂₂ b
      (rank_two_moving_modulus_pos A B₁ B₂ C₁₁ C₁₂ C₂₂ (-b) hN (by linarith))
  · exact rank_two_moving_modulus_pos A B₁ B₂ C₁₁ C₁₂ C₂₂ b hN hpos

/-- Every singular-coordinate block satisfies the dichotomy. -/
theorem dichotomyS_all (A B₁ B₂ C₁₁ C₁₂ C₂₂ b : ℤ) : DichotomyS A B₁ B₂ C₁₁ C₁₂ C₂₂ b := by
  by_cases hb : b = 0
  · subst hb; exact fixed_modulus_dichotomy A B₁ B₂ C₁₁ C₁₂ C₂₂
  · by_cases hN : discW C₁₁ C₁₂ C₂₂ = 0
    · by_cases hC : C₁₁ = 0 ∧ C₁₂ = 0 ∧ C₂₂ = 0
      · obtain ⟨h1, h2, h3⟩ := hC
        subst h1; subst h2; subst h3
        exact singular_rank_zero_dichotomy A B₁ B₂ b
      · exact singular_rank_one_dichotomy A B₁ B₂ C₁₁ C₁₂ C₂₂ b hN hC
    · exact rank_two_moving_modulus_dichotomy A B₁ B₂ C₁₁ C₁₂ C₂₂ b hN hb

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.normalizedSlope_pos
#print axioms DiophCompression.SemanticQuadraticSingular.normalizedSlope_offset_coprime
#print axioms DiophCompression.SemanticQuadraticSingular.normalizedSlope_coprime_modulus
#print axioms DiophCompression.SemanticQuadraticSingular.normalizedLinearModulus_mul_content
#print axioms DiophCompression.SemanticQuadraticSingular.moving_remainder_identity
#print axioms DiophCompression.SemanticQuadraticSingular.moving_divisibility_iff_remainder
#print axioms DiophCompression.SemanticQuadraticSingular.moving_modulus_nonpositive_bound
#print axioms DiophCompression.SemanticQuadraticSingular.moving_modulus_prime_step
#print axioms DiophCompression.SemanticQuadraticSingular.rank_two_moving_modulus_pos
#print axioms DiophCompression.SemanticQuadraticSingular.rank_two_moving_modulus_dichotomy
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomyS_all
