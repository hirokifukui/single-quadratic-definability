/-
  Shadow/SummitClosureR.lean — ray-carrying shadow of the summit and the log-barrier leaf closure.
  Baseline: DiophCompression/SummitClosure.lean. The family-free lemmas of the baseline
  (`fiberNatSigned`, `exists_fiberSetG_eq_fiberNatSigned`, `infinite_integer_set_pos_or_neg`,
  `weak_target_trivial_on_finite_fibre`) are reused unchanged; only the family → certificate joint is
  shadowed so the moving-modulus leaf is peeled off as a `FixedBasePrimeRay (fiberZZ P a)` (via
  `StructuredFamilyR`), rather than sunk into a bare certificate. The projection dichotomy is taken in
  its ray-carrying form `quadraticProjectionDichotomyZ_all_dataR`. `exponentialInjection_or_moving`
  turns a NON-moving certificate into `ExponentialInjection`; the ray branch feeds `logLowerBound_of_ray`
  (conditional on the `FixedAPPrimeLowerBound` HYPOTHESIS — visible in the type, never an axiom).
  No sorry; std-3 expected.
-/
import ResearchUpgrade.Shadow.FamilyR
import ResearchUpgrade.Shadow.TopDichotomyDataR
import ResearchUpgrade.CertificateEnvelope
import ResearchUpgrade.RayCounting

namespace DiophCompression.ResearchUpgrade

open MvPolynomial MPUP DiophCompression.SemanticQuadraticGeneral

variable {n r : ℕ}

/-! ### 必須F step 4 (ray-carrying): family → certificate-or-ray -/

/-- A ray-carrying structured family inside a signed half of the fibre is EITHER a non-moving structured
    certificate for `P` at `a`, OR a fixed-base prime ray in the integer fibre. The moving-modulus leaf
    is the one that surrenders the ray. -/
theorem structuredCertificate_of_familyR (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (ε : ℤ) (hε : ε * ε = 1) (R : StructuredFamilyR (fiberNatSigned P a ε)) :
    (∃ c : StructuredCertificate P a, c.kind ≠ StructuredKind.movingModulusStepOrbit) ∨
      Nonempty (FixedBasePrimeRay (fiberZZ P a)) := by
  classical
  have hεne : ε ≠ 0 := by
    intro h
    rw [h, mul_zero] at hε
    exact zero_ne_one hε
  rcases R.ray_or_nonmoving with hray | hk
  · obtain ⟨ray⟩ := hray
    refine Or.inr ⟨ray.mapMul ε hεne (fun c hc => ?_)⟩
    obtain ⟨m, hm, rfl⟩ := hc
    exact hm
  · left
    set F := R.F with hFdef
    clear_value F
    cases F with
    | progression c₀ s hs mem =>
        clear hk hFdef
        simp only [fiberNatSigned, fiberZZ, Set.mem_setOf_eq] at mem
        choose w hw using mem
        have hs0 : 0 < s := hs
        have hsne : ε * (s : ℤ) ≠ 0 := mul_ne_zero hεne (by exact_mod_cast hs0.ne')
        have heq : ∀ t : ℕ,
            (Polynomial.C (ε * (s : ℤ)) * Polynomial.X + Polynomial.C (ε * (c₀ : ℤ))).eval (t : ℤ)
              = ε * ((c₀ + s * t : ℕ) : ℤ) := by
          intro t
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
          push_cast
          ring
        exact ⟨.polynomialProgression
          { q := Polynomial.C (ε * (s : ℤ)) * Polynomial.X + Polynomial.C (ε * (c₀ : ℤ))
            deg_le_two := by rw [Polynomial.natDegree_linear hsne]; norm_num
            nonconst := by rw [Polynomial.natDegree_linear hsne]; norm_num
            t₀ := 0
            witness := w
            mem := fun t _ => by rw [heq t]; exact hw t
            injective := fun t t' _ _ h => by
              rw [heq t, heq t'] at h
              have h2 : ((c₀ + s * t : ℕ) : ℤ) = ((c₀ + s * t' : ℕ) : ℤ) := mul_left_cancel₀ hεne h
              have h3 : c₀ + s * t = c₀ + s * t' := by exact_mod_cast h2
              exact Nat.eq_of_mul_eq_mul_left hs (Nat.add_left_cancel h3) },
          fun h => StructuredKind.noConfusion h⟩
    | quadratic α β γ hα cf out mem mono =>
        clear hk hFdef
        simp only [fiberNatSigned, fiberZZ, Set.mem_setOf_eq] at mem
        choose w hw using mem
        have hαne : ε * α ≠ 0 := mul_ne_zero hεne hα
        have heq : ∀ t : ℕ,
            (Polynomial.C (ε * α) * Polynomial.X ^ 2 + Polynomial.C (ε * β) * Polynomial.X
              + Polynomial.C (ε * γ)).eval (t : ℤ) = ε * (cf t : ℤ) := by
          intro t
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_C, Polynomial.eval_X]
          rw [out t]
          ring
        exact ⟨.polynomialProgression
          { q := Polynomial.C (ε * α) * Polynomial.X ^ 2 + Polynomial.C (ε * β) * Polynomial.X
              + Polynomial.C (ε * γ)
            deg_le_two := by rw [Polynomial.natDegree_quadratic hαne]
            nonconst := by rw [Polynomial.natDegree_quadratic hαne]; norm_num
            t₀ := 0
            witness := w
            mem := fun t _ => by rw [heq t]; exact hw t
            injective := fun t t' _ _ h => by
              rw [heq t, heq t'] at h
              exact mono.injective (Nat.cast_injective (mul_left_cancel₀ hεne h)) },
          fun h => StructuredKind.noConfusion h⟩
    | pell D x0 y0 unit hx0 XX YY recX recY denom px pc hdenom cf out mem mono =>
        clear hk hFdef
        simp only [fiberNatSigned, fiberZZ, Set.mem_setOf_eq] at mem
        choose w hw using mem
        have hy0 : y0 ≠ 0 := by
          intro h
          subst h
          have hx2 : x0 ^ 2 = 1 := by linear_combination unit
          nlinarith [hx0]
        have hy2 : 0 < y0 ^ 2 := lt_of_le_of_ne (sq_nonneg y0) (Ne.symm (pow_ne_zero 2 hy0))
        have hD : 0 < D := by nlinarith [unit, hy2, hx0, sq_nonneg (x0 - 2)]
        have hDns : ¬ IsSquare D := by
          rintro ⟨d, rfl⟩
          have h1 : (x0 - d * y0) * (x0 + d * y0) = 1 := by linear_combination unit
          rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> linarith
        exact ⟨.pellUnitOrbit
          { D := D
            D_pos := hD
            D_nonsquare := hDns
            x₀ := x0
            y₀ := y0
            unit := unit
            y₀_ne := hy0
            N₀ := XX 0 ^ 2 - D * YY 0 ^ 2
            X := XX
            Y := YY
            base_norm := rfl
            succ_X := fun k => by rw [recX k]; ring
            succ_Y := fun k => by rw [recY k]; ring
            pc := ε * pc
            px := ε * px
            py := 0
            denom := denom
            denom_ne := hdenom
            output := fun k => ε * (cf k : ℤ)
            output_eq := fun k => by linear_combination ε * out k
            witness := w
            mem := hw
            injective := fun k k' h =>
              mono.injective (Nat.cast_injective (mul_left_cancel₀ hεne h)) },
          fun h => StructuredKind.noConfusion h⟩
    | movingModulus b μ f hb hf cf pr hprime hmpos hpgt hpmod hsucc mem mono =>
        exact absurd rfl hk

/-! ### 必須F, half-infinite (ray-carrying) -/

/-- An infinite HALF of the fibre of a quadratic `P` either carries a NON-moving structured certificate,
    or a fixed-base prime ray in the fibre. -/
theorem structuredCertificate_of_half_infinite_R (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2)
    (a : Fin n → ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hinf : {c ∈ fiberZZ P a | 0 ≤ ε * c}.Infinite) :
    (∃ c : StructuredCertificate P a, c.kind ≠ StructuredKind.movingModulusStepOrbit) ∨
      Nonempty (FixedBasePrimeRay (fiberZZ P a)) := by
  classical
  have hεsq : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεne : ε ≠ 0 := by
    intro h
    rw [h, mul_zero] at hεsq
    exact zero_ne_one hεsq
  obtain ⟨H, L, Q, hH, hset⟩ := exists_fiberSetG_eq_fiberNatSigned P hP a ε hε
  obtain ⟨K, hK⟩ := quadraticProjectionDichotomyZ_all_dataR r H hH
  rcases hK L Q with hF | hb
  · obtain ⟨F⟩ := hF
    exact structuredCertificate_of_familyR P a ε hεsq (F.transport hset)
  · exfalso
    have hbnd : ∀ m ∈ fiberNatSigned P a ε, (m : ℤ) ≤ fboundG K L Q := by
      intro m hm
      exact hb m (by rw [hset]; exact hm)
    have hfinN : (fiberNatSigned P a ε).Finite := by
      apply Set.Finite.subset (Set.finite_Icc 0 (fboundG K L Q).toNat)
      intro m hm
      have h := hbnd m hm
      simp only [Set.mem_Icc]
      exact ⟨Nat.zero_le _, by omega⟩
    have hsub : {c ∈ fiberZZ P a | 0 ≤ ε * c} ⊆ (fun m : ℕ => ε * (m : ℤ)) '' fiberNatSigned P a ε := by
      rintro c ⟨hc, h0⟩
      refine ⟨(ε * c).toNat, ?_, ?_⟩
      · show ε * (((ε * c).toNat : ℕ) : ℤ) ∈ fiberZZ P a
        rw [Int.toNat_of_nonneg h0, ← mul_assoc, hεsq, one_mul]
        exact hc
      · simp only
        rw [Int.toNat_of_nonneg h0, ← mul_assoc, hεsq, one_mul]
    exact hinf ((hfinN.image _).subset hsub)

/-! ### The ray-carrying summit and the log barrier -/

/-- 必須F (ray-carrying): for every quadratic `P` and every parameter point `a`, the scalar fibre is
    bounded, or exponential-injective, or carries a fixed-base prime ray. -/
theorem fiber_bounded_or_expInj_or_ray (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2) (a : Fin n → ℤ) :
    (∃ B : ℕ, ∀ c ∈ fiberZZ P a, |c| ≤ B) ∨ ExponentialInjection (fiberZZ P a) ∨
      Nonempty (FixedBasePrimeRay (fiberZZ P a)) := by
  by_cases hfin : (fiberZZ P a).Finite
  · exact Or.inl (weak_target_trivial_on_finite_fibre P a hfin)
  · have hinf := Set.not_finite.mp hfin
    have hcertray :
        (∃ c : StructuredCertificate P a, c.kind ≠ StructuredKind.movingModulusStepOrbit) ∨
          Nonempty (FixedBasePrimeRay (fiberZZ P a)) := by
      rcases infinite_integer_set_pos_or_neg _ hinf with h1 | h2
      · refine structuredCertificate_of_half_infinite_R P hP a 1 (Or.inl rfl) ?_
        simpa using h1
      · refine structuredCertificate_of_half_infinite_R P hP a (-1) (Or.inr rfl) ?_
        have hset : {c ∈ fiberZZ P a | 0 ≤ (-1 : ℤ) * c} = {c ∈ fiberZZ P a | c ≤ 0} := by
          ext c
          simp only [Set.mem_setOf_eq, neg_one_mul, neg_nonneg]
        rw [hset]
        exact h2
    rcases hcertray with ⟨c, hc⟩ | hray
    · rcases exponentialInjection_or_moving c with h | h
      · exact Or.inr (Or.inl h)
      · exact absurd h hc
    · exact Or.inr (Or.inr hray)

/-- THE LOG BARRIER (conditional on the analytic HYPOTHESIS `FixedAPPrimeLowerBound`): for every
    quadratic `P` and every parameter point `a`, the scalar fibre is bounded, or satisfies
    `LogLowerBound`. Both the exponential-injection leaf and the ray leaf feed the log bound. -/
theorem logBarrier_of_quadratic (hAP : FixedAPPrimeLowerBound) (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) (a : Fin n → ℤ) :
    (∃ B : ℕ, ∀ c ∈ fiberZZ P a, |c| ≤ B) ∨ LogLowerBound (fiberZZ P a) := by
  rcases fiber_bounded_or_expInj_or_ray P hP a with hb | he | hr
  · exact Or.inl hb
  · exact Or.inr (logLowerBound_of_exponentialInjection he)
  · obtain ⟨R⟩ := hr
    exact Or.inr (logLowerBound_of_ray R hAP)

/-! ### Unconditional variant: carry the ExponentialInjection through the sign map, drop the ray leaf -/

/-- Push an exponential injection through the scalar map `c ↦ ε·c` (`ε = ±1`) into a target set. -/
theorem ExponentialInjection.mapMul {S T : Set ℤ} (ε : ℤ) (hε : ε * ε = 1)
    (h : ∀ c ∈ S, ε * c ∈ T) (hInj : ExponentialInjection S) : ExponentialInjection T := by
  have hor : ε = 1 ∨ ε = -1 := mul_self_eq_one_iff.mp hε
  have hεne : ε ≠ 0 := by rcases hor with rfl | rfl <;> norm_num
  have hεabs : |ε| = 1 := by rcases hor with rfl | rfl <;> norm_num
  obtain ⟨A, B, g, hA, hB, hginj, hmem, hbd⟩ := hInj
  refine ⟨A, B, fun n => ε * g n, hA, hB, ?_, ?_, ?_⟩
  · intro a b hab
    exact hginj (mul_left_cancel₀ hεne hab)
  · intro n; exact h _ (hmem n)
  · intro n; rw [abs_mul, hεabs, one_mul]; exact hbd n

/-- 必須F step 4 (unconditional): a ray-carrying structured family inside a signed half of the fibre
is EITHER a non-moving structured certificate for `P` at `a`, OR yields an exponential injection in
the integer fibre (the moving-modulus leaf now surrenders its `ExponentialInjection`, not just a ray). -/
theorem expInj_of_familyR (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (ε : ℤ) (hε : ε * ε = 1) (R : StructuredFamilyR (fiberNatSigned P a ε)) :
    (∃ c : StructuredCertificate P a, c.kind ≠ StructuredKind.movingModulusStepOrbit) ∨
      ExponentialInjection (fiberZZ P a) := by
  classical
  have hεne : ε ≠ 0 := by
    intro h
    rw [h, mul_zero] at hε
    exact zero_ne_one hε
  rcases R.expInj_or_nonmoving with hexp | hk
  · refine Or.inr (hexp.mapMul ε hε (fun c hc => ?_))
    obtain ⟨m, hm, rfl⟩ := hc
    exact hm
  · left
    set F := R.F with hFdef
    clear_value F
    cases F with
    | progression c₀ s hs mem =>
        clear hk hFdef
        simp only [fiberNatSigned, fiberZZ, Set.mem_setOf_eq] at mem
        choose w hw using mem
        have hs0 : 0 < s := hs
        have hsne : ε * (s : ℤ) ≠ 0 := mul_ne_zero hεne (by exact_mod_cast hs0.ne')
        have heq : ∀ t : ℕ,
            (Polynomial.C (ε * (s : ℤ)) * Polynomial.X + Polynomial.C (ε * (c₀ : ℤ))).eval (t : ℤ)
              = ε * ((c₀ + s * t : ℕ) : ℤ) := by
          intro t
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
          push_cast
          ring
        exact ⟨.polynomialProgression
          { q := Polynomial.C (ε * (s : ℤ)) * Polynomial.X + Polynomial.C (ε * (c₀ : ℤ))
            deg_le_two := by rw [Polynomial.natDegree_linear hsne]; norm_num
            nonconst := by rw [Polynomial.natDegree_linear hsne]; norm_num
            t₀ := 0
            witness := w
            mem := fun t _ => by rw [heq t]; exact hw t
            injective := fun t t' _ _ h => by
              rw [heq t, heq t'] at h
              have h2 : ((c₀ + s * t : ℕ) : ℤ) = ((c₀ + s * t' : ℕ) : ℤ) := mul_left_cancel₀ hεne h
              have h3 : c₀ + s * t = c₀ + s * t' := by exact_mod_cast h2
              exact Nat.eq_of_mul_eq_mul_left hs (Nat.add_left_cancel h3) },
          fun h => StructuredKind.noConfusion h⟩
    | quadratic α β γ hα cf out mem mono =>
        clear hk hFdef
        simp only [fiberNatSigned, fiberZZ, Set.mem_setOf_eq] at mem
        choose w hw using mem
        have hαne : ε * α ≠ 0 := mul_ne_zero hεne hα
        have heq : ∀ t : ℕ,
            (Polynomial.C (ε * α) * Polynomial.X ^ 2 + Polynomial.C (ε * β) * Polynomial.X
              + Polynomial.C (ε * γ)).eval (t : ℤ) = ε * (cf t : ℤ) := by
          intro t
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_C, Polynomial.eval_X]
          rw [out t]
          ring
        exact ⟨.polynomialProgression
          { q := Polynomial.C (ε * α) * Polynomial.X ^ 2 + Polynomial.C (ε * β) * Polynomial.X
              + Polynomial.C (ε * γ)
            deg_le_two := by rw [Polynomial.natDegree_quadratic hαne]
            nonconst := by rw [Polynomial.natDegree_quadratic hαne]; norm_num
            t₀ := 0
            witness := w
            mem := fun t _ => by rw [heq t]; exact hw t
            injective := fun t t' _ _ h => by
              rw [heq t, heq t'] at h
              exact mono.injective (Nat.cast_injective (mul_left_cancel₀ hεne h)) },
          fun h => StructuredKind.noConfusion h⟩
    | pell D x0 y0 unit hx0 XX YY recX recY denom px pc hdenom cf out mem mono =>
        clear hk hFdef
        simp only [fiberNatSigned, fiberZZ, Set.mem_setOf_eq] at mem
        choose w hw using mem
        have hy0 : y0 ≠ 0 := by
          intro h
          subst h
          have hx2 : x0 ^ 2 = 1 := by linear_combination unit
          nlinarith [hx0]
        have hy2 : 0 < y0 ^ 2 := lt_of_le_of_ne (sq_nonneg y0) (Ne.symm (pow_ne_zero 2 hy0))
        have hD : 0 < D := by nlinarith [unit, hy2, hx0, sq_nonneg (x0 - 2)]
        have hDns : ¬ IsSquare D := by
          rintro ⟨d, rfl⟩
          have h1 : (x0 - d * y0) * (x0 + d * y0) = 1 := by linear_combination unit
          rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> linarith
        exact ⟨.pellUnitOrbit
          { D := D
            D_pos := hD
            D_nonsquare := hDns
            x₀ := x0
            y₀ := y0
            unit := unit
            y₀_ne := hy0
            N₀ := XX 0 ^ 2 - D * YY 0 ^ 2
            X := XX
            Y := YY
            base_norm := rfl
            succ_X := fun k => by rw [recX k]; ring
            succ_Y := fun k => by rw [recY k]; ring
            pc := ε * pc
            px := ε * px
            py := 0
            denom := denom
            denom_ne := hdenom
            output := fun k => ε * (cf k : ℤ)
            output_eq := fun k => by linear_combination ε * out k
            witness := w
            mem := hw
            injective := fun k k' h =>
              mono.injective (Nat.cast_injective (mul_left_cancel₀ hεne h)) },
          fun h => StructuredKind.noConfusion h⟩
    | movingModulus b μ f hb hf cf pr hprime hmpos hpgt hpmod hsucc mem mono =>
        exact absurd rfl hk

/-- 必須F, half-infinite (unconditional): an infinite HALF of the fibre of a quadratic `P` either
carries a NON-moving structured certificate, or yields an exponential injection in the fibre. -/
theorem expInj_of_half_infinite_R (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2)
    (a : Fin n → ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hinf : {c ∈ fiberZZ P a | 0 ≤ ε * c}.Infinite) :
    (∃ c : StructuredCertificate P a, c.kind ≠ StructuredKind.movingModulusStepOrbit) ∨
      ExponentialInjection (fiberZZ P a) := by
  classical
  have hεsq : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεne : ε ≠ 0 := by
    intro h
    rw [h, mul_zero] at hεsq
    exact zero_ne_one hεsq
  obtain ⟨H, L, Q, hH, hset⟩ := exists_fiberSetG_eq_fiberNatSigned P hP a ε hε
  obtain ⟨K, hK⟩ := quadraticProjectionDichotomyZ_all_dataR r H hH
  rcases hK L Q with hF | hb
  · obtain ⟨F⟩ := hF
    exact expInj_of_familyR P a ε hεsq (F.transport hset)
  · exfalso
    have hbnd : ∀ m ∈ fiberNatSigned P a ε, (m : ℤ) ≤ fboundG K L Q := by
      intro m hm
      exact hb m (by rw [hset]; exact hm)
    have hfinN : (fiberNatSigned P a ε).Finite := by
      apply Set.Finite.subset (Set.finite_Icc 0 (fboundG K L Q).toNat)
      intro m hm
      have h := hbnd m hm
      simp only [Set.mem_Icc]
      exact ⟨Nat.zero_le _, by omega⟩
    have hsub : {c ∈ fiberZZ P a | 0 ≤ ε * c} ⊆ (fun m : ℕ => ε * (m : ℤ)) '' fiberNatSigned P a ε := by
      rintro c ⟨hc, h0⟩
      refine ⟨(ε * c).toNat, ?_, ?_⟩
      · show ε * (((ε * c).toNat : ℕ) : ℤ) ∈ fiberZZ P a
        rw [Int.toNat_of_nonneg h0, ← mul_assoc, hεsq, one_mul]
        exact hc
      · simp only
        rw [Int.toNat_of_nonneg h0, ← mul_assoc, hεsq, one_mul]
    exact hinf ((hfinN.image _).subset hsub)

/-- 必須F (unconditional): for every quadratic `P` and every parameter point `a`, the scalar fibre is
bounded, or exponential-injective. NO ray leaf, NO `FixedAPPrimeLowerBound`. -/
theorem fiber_bounded_or_expInj (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2) (a : Fin n → ℤ) :
    (∃ B : ℕ, ∀ c ∈ fiberZZ P a, |c| ≤ B) ∨ ExponentialInjection (fiberZZ P a) := by
  by_cases hfin : (fiberZZ P a).Finite
  · exact Or.inl (weak_target_trivial_on_finite_fibre P a hfin)
  · have hinf := Set.not_finite.mp hfin
    have hcert :
        (∃ c : StructuredCertificate P a, c.kind ≠ StructuredKind.movingModulusStepOrbit) ∨
          ExponentialInjection (fiberZZ P a) := by
      rcases infinite_integer_set_pos_or_neg _ hinf with h1 | h2
      · refine expInj_of_half_infinite_R P hP a 1 (Or.inl rfl) ?_
        simpa using h1
      · refine expInj_of_half_infinite_R P hP a (-1) (Or.inr rfl) ?_
        have hset : {c ∈ fiberZZ P a | 0 ≤ (-1 : ℤ) * c} = {c ∈ fiberZZ P a | c ≤ 0} := by
          ext c
          simp only [Set.mem_setOf_eq, neg_one_mul, neg_nonneg]
        rw [hset]
        exact h2
    rcases hcert with ⟨c, hc⟩ | hexp
    · rcases exponentialInjection_or_moving c with h | h
      · exact Or.inr h
      · exact absurd h hc
    · exact Or.inr hexp

/-- THE UNCONDITIONAL LOG BARRIER: for every quadratic `P` and every parameter point `a`, the scalar
fibre is bounded, or satisfies `LogLowerBound`. The exponential-injection leaf feeds the log bound;
NO `FixedAPPrimeLowerBound` anywhere in the type or the proof. -/
theorem logBarrier_of_quadratic_unconditional (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) (a : Fin n → ℤ) :
    (∃ B : ℕ, ∀ c ∈ fiberZZ P a, |c| ≤ B) ∨ LogLowerBound (fiberZZ P a) := by
  rcases fiber_bounded_or_expInj P hP a with hb | he
  · exact Or.inl hb
  · exact Or.inr (logLowerBound_of_exponentialInjection he)

end DiophCompression.ResearchUpgrade
