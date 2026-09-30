/-
  CertificateEnvelope.lean — Gate-18 research program, Packets A4-2 / A4-3 and the A3-4 leaf map.
  At the P-level (fiberZZ P a : Set ℤ, the baseline summit vocabulary — no ℕ→ℤ bridge is needed there):
  A4-2: a polynomial-progression certificate (deg ≤ 2, injective tail) gives `ExponentialInjection`
        with B = 4 (via (n+1)² ≤ 4ⁿ) — no polynomial constant can sneak in (nonconst + injective on tail).
  A4-3: a Pell-unit-orbit certificate gives `ExponentialInjection` by the row-sum norm induction
        max(|X_k|,|Y_k|) ≤ (|x₀| + D|y₀|)^k · max(|X_0|,|Y_0|); the affine projection with denominator
        keeps injectivity (a field of the certificate) and the envelope; |x₀| ≥ 2 is forced by the unit.
  LEAF MAP (A3-4, unconditional): for every quadratic P and every a, the fibre is bounded, or
  `ExponentialInjection (fiberZZ P a)` (hence LogLowerBound), or the certificate is of the
  moving-modulus kind. The moving kind is the ONLY leaf not yet covered: its P-level realization
  carries the step orbit (super-exponential growth), not the fixed-base ray; the ray requires the
  SG-level provenance (A1/A2) to travel through the assembly — the next packet.
-/
import ResearchUpgrade.Counting
import DiophCompression.SummitClosure

namespace DiophCompression.ResearchUpgrade

open DiophCompression MPUP

/-! ### Elementary envelopes -/

theorem sq_succ_le_four_pow (n : ℕ) : (n + 1) ^ 2 ≤ 4 ^ n := by
  have h : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  calc (n + 1) ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h 2
    _ = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- `|q(t)| ≤ (|c₀|+|c₁|+|c₂|)·(|t|+1)²` for a polynomial of degree ≤ 2. -/
theorem abs_eval_le_of_natDegree_le_two (q : Polynomial ℤ) (hq : q.natDegree ≤ 2) (t : ℤ) :
    |q.eval t| ≤ (|q.coeff 0| + |q.coeff 1| + |q.coeff 2|) * (|t| + 1) ^ 2 := by
  rw [Polynomial.eval_eq_sum_range' (by omega : q.natDegree < 3)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one]
  have ht : 0 ≤ |t| := abs_nonneg t
  have hs1 : 1 ≤ (|t| + 1) ^ 2 := by nlinarith
  have hst : |t| ≤ (|t| + 1) ^ 2 := by nlinarith
  have hst2 : |t| ^ 2 ≤ (|t| + 1) ^ 2 := by nlinarith
  have h0 : |q.coeff 0| ≤ |q.coeff 0| * (|t| + 1) ^ 2 := le_mul_of_one_le_right (abs_nonneg _) hs1
  have h1 : |q.coeff 1 * t| ≤ |q.coeff 1| * (|t| + 1) ^ 2 := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hst (abs_nonneg _)
  have h2 : |q.coeff 2 * t ^ 2| ≤ |q.coeff 2| * (|t| + 1) ^ 2 := by
    rw [abs_mul, abs_pow]; exact mul_le_mul_of_nonneg_left hst2 (abs_nonneg _)
  calc |q.coeff 0 + q.coeff 1 * t + q.coeff 2 * t ^ 2|
      ≤ |q.coeff 0 + q.coeff 1 * t| + |q.coeff 2 * t ^ 2| := abs_add_le _ _
    _ ≤ |q.coeff 0| + |q.coeff 1 * t| + |q.coeff 2 * t ^ 2| := by
        linarith [abs_add_le (q.coeff 0) (q.coeff 1 * t)]
    _ ≤ _ := by linarith

/-! ### A4-2: polynomial-progression certificates -/

theorem exponentialInjection_of_polynomialProgression {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : PolynomialProgressionRealization P a) : ExponentialInjection (fiberZZ P a) := by
  set K : ℤ := |c.q.coeff 0| + |c.q.coeff 1| + |c.q.coeff 2| with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨(K.toNat + 1) * (c.t₀ + 1) ^ 2, 4, fun k => c.q.eval ((c.t₀ + k : ℕ) : ℤ), ?_, by norm_num,
    ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · intro k k' h
    have := c.injective (c.t₀ + k) (c.t₀ + k') (by omega) (by omega) h
    omega
  · intro k; exact ⟨c.witness (c.t₀ + k), c.mem (c.t₀ + k) (by omega)⟩
  · intro k
    have hb := abs_eval_le_of_natDegree_le_two c.q c.deg_le_two ((c.t₀ + k : ℕ) : ℤ)
    rw [← hK] at hb
    have hKt : K ≤ (K.toNat + 1 : ℕ) := by
      have : K ≤ K.toNat := Int.self_le_toNat K
      push_cast; linarith
    have hle : |((c.t₀ + k : ℕ) : ℤ)| + 1 ≤ ((c.t₀ : ℤ) + 1) * ((k : ℤ) + 1) := by
      rw [abs_of_nonneg (by positivity)]; push_cast
      nlinarith [(Nat.cast_nonneg c.t₀ : (0 : ℤ) ≤ c.t₀), (Nat.cast_nonneg k : (0 : ℤ) ≤ k)]
    have hsq' : (|((c.t₀ + k : ℕ) : ℤ)| + 1) ^ 2 ≤ ((c.t₀ : ℤ) + 1) ^ 2 * ((k : ℤ) + 1) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hle 2
    have h4 : ((k : ℤ) + 1) ^ 2 ≤ (4 : ℤ) ^ k := by
      have := sq_succ_le_four_pow k; exact_mod_cast this
    have ht1 : (0 : ℤ) ≤ ((c.t₀ : ℤ) + 1) ^ 2 := by positivity
    calc |c.q.eval ((c.t₀ + k : ℕ) : ℤ)| ≤ K * (|((c.t₀ + k : ℕ) : ℤ)| + 1) ^ 2 := hb
      _ ≤ K * (((c.t₀ : ℤ) + 1) ^ 2 * ((k : ℤ) + 1) ^ 2) := mul_le_mul_of_nonneg_left hsq' hK0
      _ ≤ ((K.toNat + 1 : ℕ) : ℤ) * (((c.t₀ : ℤ) + 1) ^ 2 * (4 : ℤ) ^ k) := by
          apply mul_le_mul hKt _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left h4 ht1
      _ = _ := by push_cast; ring

/-! ### A4-3: Pell-unit-orbit certificates -/

/-- Row-sum norm growth of the orbit: `max(|X_k|,|Y_k|) ≤ (|x₀| + D|y₀|)^k · max(|X_0|,|Y_0|)`. -/
theorem pell_orbit_envelope {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : PellUnitOrbitRealization P a) (k : ℕ) :
    |c.X k| ≤ (|c.x₀| + c.D * |c.y₀|) ^ k * (|c.X 0| + |c.Y 0|) ∧
    |c.Y k| ≤ (|c.x₀| + c.D * |c.y₀|) ^ k * (|c.X 0| + |c.Y 0|) := by
  have hD := c.D_pos
  induction k with
  | zero =>
    simp only [pow_zero, one_mul]
    constructor <;> linarith [abs_nonneg (c.X 0), abs_nonneg (c.Y 0)]
  | succ k ih =>
    obtain ⟨hX, hY⟩ := ih
    set B := |c.x₀| + c.D * |c.y₀| with hB
    set M := (|c.X 0| + |c.Y 0|)
    have hM0 : 0 ≤ M := by positivity
    have hBk : 0 ≤ B ^ k := by positivity
    have hx : 0 ≤ |c.x₀| := abs_nonneg _
    have hy : 0 ≤ |c.y₀| := abs_nonneg _
    have hXk : 0 ≤ |c.X k| := abs_nonneg _
    have hYk : 0 ≤ |c.Y k| := abs_nonneg _
    rw [pow_succ]
    constructor
    · rw [c.succ_X]
      calc |c.x₀ * c.X k + c.D * c.y₀ * c.Y k| ≤ |c.x₀ * c.X k| + |c.D * c.y₀ * c.Y k| := abs_add_le _ _
        _ = |c.x₀| * |c.X k| + c.D * |c.y₀| * |c.Y k| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos hD]
        _ ≤ |c.x₀| * (B ^ k * M) + c.D * |c.y₀| * (B ^ k * M) := by
            gcongr
        _ = B ^ k * B * M := by rw [hB]; ring
    · rw [c.succ_Y]
      calc |c.y₀ * c.X k + c.x₀ * c.Y k| ≤ |c.y₀ * c.X k| + |c.x₀ * c.Y k| := abs_add_le _ _
        _ = |c.y₀| * |c.X k| + |c.x₀| * |c.Y k| := by rw [abs_mul, abs_mul]
        _ ≤ |c.y₀| * (B ^ k * M) + |c.x₀| * (B ^ k * M) := by gcongr
        _ ≤ c.D * |c.y₀| * (B ^ k * M) + |c.x₀| * (B ^ k * M) := by
            have : |c.y₀| * (B ^ k * M) ≤ c.D * |c.y₀| * (B ^ k * M) := by
              have h1 : (1 : ℤ) ≤ c.D := hD
              nlinarith [mul_nonneg hy (mul_nonneg hBk hM0)]
            linarith
        _ = B ^ k * B * M := by rw [hB]; ring

theorem exponentialInjection_of_pellUnitOrbit {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : PellUnitOrbitRealization P a) : ExponentialInjection (fiberZZ P a) := by
  have hD := c.D_pos
  set B : ℤ := |c.x₀| + c.D * |c.y₀| with hB
  set M : ℤ := |c.X 0| + |c.Y 0| with hM
  -- |x₀| ≥ 2 from the unit equation with y₀ ≠ 0
  have hx2 : 2 ≤ |c.x₀| := by
    have hu := c.unit
    have hy : 1 ≤ c.y₀ ^ 2 := by
      have : c.y₀ ^ 2 ≠ 0 := pow_ne_zero 2 c.y₀_ne
      have : 0 ≤ c.y₀ ^ 2 := sq_nonneg _
      omega
    have hx : 2 ≤ c.x₀ ^ 2 := by nlinarith
    have : |c.x₀| ^ 2 = c.x₀ ^ 2 := sq_abs _
    nlinarith [abs_nonneg c.x₀]
  have hB2 : 2 ≤ B := by
    have : 0 ≤ c.D * |c.y₀| := by positivity
    linarith
  have hd1 : 1 ≤ |c.denom| := Int.one_le_abs c.denom_ne
  set K : ℤ := |c.pc| + (|c.px| + |c.py|) * M with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K.toNat + 1, B.toNat, c.output, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_,
    c.injective, fun k => ⟨c.witness k, c.mem k⟩, ?_⟩
  · have : (2 : ℤ) ≤ B.toNat := by rw [Int.toNat_of_nonneg (by linarith)]; exact hB2
    exact_mod_cast this
  · intro k
    obtain ⟨hX, hY⟩ := pell_orbit_envelope c k
    have hBtoNat : ((B.toNat : ℕ) : ℤ) = B := Int.toNat_of_nonneg (by linarith)
    have hKt : K ≤ ((K.toNat + 1 : ℕ) : ℤ) := by
      have : K ≤ K.toNat := Int.self_le_toNat K
      push_cast; linarith
    have hout := c.output_eq k
    have hBk : 0 ≤ B ^ k := by positivity
    have hM0 : 0 ≤ M := by positivity
    have h1 : |c.denom| * |c.output k| = |c.pc + c.px * c.X k + c.py * c.Y k| := by
      rw [← abs_mul, hout]
    have h2 : |c.pc + c.px * c.X k + c.py * c.Y k| ≤ |c.pc| + |c.px| * |c.X k| + |c.py| * |c.Y k| := by
      calc |c.pc + c.px * c.X k + c.py * c.Y k| ≤ |c.pc + c.px * c.X k| + |c.py * c.Y k| := abs_add_le _ _
        _ ≤ |c.pc| + |c.px * c.X k| + |c.py * c.Y k| := by linarith [abs_add_le c.pc (c.px * c.X k)]
        _ = _ := by rw [abs_mul, abs_mul]
    have h3 : |c.pc| + |c.px| * |c.X k| + |c.py| * |c.Y k| ≤ K * B ^ k := by
      have hBk1 : 1 ≤ B ^ k := one_le_pow₀ (by linarith)
      have e1 : |c.px| * |c.X k| ≤ |c.px| * (B ^ k * M) := mul_le_mul_of_nonneg_left hX (abs_nonneg _)
      have e2 : |c.py| * |c.Y k| ≤ |c.py| * (B ^ k * M) := mul_le_mul_of_nonneg_left hY (abs_nonneg _)
      have e0 : |c.pc| ≤ |c.pc| * B ^ k := by nlinarith [abs_nonneg c.pc]
      rw [hK]; nlinarith [abs_nonneg c.px, abs_nonneg c.py]
    have hout_le : |c.output k| ≤ K * B ^ k := by
      have := le_trans h2 h3
      rw [← h1] at this
      nlinarith [abs_nonneg (c.output k)]
    calc |c.output k| ≤ K * B ^ k := hout_le
      _ ≤ ((K.toNat + 1 : ℕ) : ℤ) * ((B.toNat : ℕ) : ℤ) ^ k := by
          rw [hBtoNat]; exact mul_le_mul_of_nonneg_right hKt hBk

/-! ### A3-4 leaf map (unconditional) -/

/-- Every structured certificate is exponential-injective, or of the moving-modulus kind. -/
theorem exponentialInjection_or_moving {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : StructuredCertificate P a) :
    ExponentialInjection (fiberZZ P a) ∨ c.kind = StructuredKind.movingModulusStepOrbit := by
  cases c with
  | polynomialProgression c => exact Or.inl (exponentialInjection_of_polynomialProgression c)
  | pellUnitOrbit c => exact Or.inl (exponentialInjection_of_pellUnitOrbit c)
  | movingModulusStepOrbit c => exact Or.inr rfl

/-- LEAF MAP for the log barrier (unconditional, from the baseline summit): for every quadratic `P`
and every parameter point `a`, the scalar fibre is bounded, or satisfies `LogLowerBound`, or carries
a moving-modulus step-orbit certificate. The third alternative is the only remaining gap. -/
theorem fiber_bounded_or_logLowerBound_or_moving {n r : ℕ} (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) (a : Fin n → ℤ) :
    (∃ B : ℕ, ∀ c ∈ fiberZZ P a, |c| ≤ B) ∨ LogLowerBound (fiberZZ P a) ∨
      ∃ c : StructuredCertificate P a, c.kind = StructuredKind.movingModulusStepOrbit := by
  rcases singleQuadratic_fiber_bounded_or_structurallyInfinite P hP a with hb | hc
  · exact Or.inl hb
  · obtain ⟨c⟩ := hc
    rcases exponentialInjection_or_moving c with h | h
    · exact Or.inr (Or.inl (logLowerBound_of_exponentialInjection h))
    · exact Or.inr (Or.inr ⟨c, h⟩)

end DiophCompression.ResearchUpgrade
