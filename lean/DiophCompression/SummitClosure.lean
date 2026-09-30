/-
  DiophCompression/SummitClosure.lean — APAL Structural Theory Gate 5, 必須F steps 3–4
  (s29, 2026-09-02, claude.ai direct).

  The last joint of the summit. `quadraticProjectionDichotomyZ_all_data` speaks about `fiberSetG H ℓ q`
  (a homogeneous quadratic part plus a linear part, unknowns in `Fin (r+1)`); the summit target speaks
  about `fiberZZ P a` (a degree-≤2 polynomial in parameters and unknowns, output = last parameter).
  The two are the same set: `normal_form_general_quadratic` splits the relabelled `P` into `H + ℓ·x + q`
  and specialising the parameters at `a` turns `ℓ, q` into integers. The output sign is carried by a
  parameter `ε` with `ε·ε = 1`: `ε = 1` is the nonnegative half, `ε = -1` the nonpositive half, and the
  flip is `flipZero H` — so no degree bound for `negOutputPoly` is needed. Converting the family into a
  certificate is kind-preserving (progression/quadratic → PP, pell → PU, movingModulus → MM).
  No sorry; std-3 expected.
-/
import DiophCompression.SummitReduction
import DiophCompression.SemanticQuadraticGeneral.TopDichotomyData

namespace DiophCompression

open MvPolynomial MPUP SemanticQuadraticGeneral

variable {n r : ℕ}

/-! ### The signed ℕ-fibre -/

/-- The naturals `m` with `ε·m` in the integer fibre (`ε = ±1` selects the half). -/
def fiberNatSigned (P : Poly (n + 1) r) (a : Fin n → ℤ) (ε : ℤ) : Set ℕ :=
  {m : ℕ | ε * (m : ℤ) ∈ fiberZZ P a}

/-- 必須F step 3 (homogenisation + parameter specialisation): each half of the fibre of a quadratic `P`
    IS a `fiberSetG` fibre of a homogeneous quadratic part. -/
theorem exists_fiberSetG_eq_fiberNatSigned (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2)
    (a : Fin n → ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ (H : MvPolynomial (Fin (r + 1)) ℤ) (L : Fin (r + 1) → ℤ) (Q : ℤ),
      H.IsHomogeneous 2 ∧ fiberSetG H L Q = fiberNatSigned P a ε := by
  classical
  obtain ⟨H, ℓ, q, hH, _, _, _, heval⟩ :=
    normal_form_general_quadratic (r + 1) (rename (relabelG n r) P)
      ((totalDegree_rename_le _ _).trans hP)
  have hfib : ∀ (c : ℤ) (u : Fin r → ℤ),
      fiberVal H (fun i => eval a (ℓ i)) (eval a q) (Fin.cons c u)
        = evalAtZZ P (Fin.snoc a c) u := by
    intro c u
    rw [← eval_relabelG_ZZ, heval]
    rfl
  rcases hε with rfl | rfl
  · refine ⟨H, fun i => eval a (ℓ i), eval a q, hH, ?_⟩
    ext m
    simp only [fiberSetG, fiberNatSigned, fiberZZ, Set.mem_setOf_eq, one_mul]
    exact exists_congr fun u => by rw [hfib]
  · refine ⟨flipZero H, fun i => if i = 0 then -(eval a (ℓ i)) else eval a (ℓ i), eval a q,
      flipZero_isHomogeneous H hH, ?_⟩
    ext m
    simp only [fiberSetG, fiberNatSigned, fiberZZ, Set.mem_setOf_eq]
    refine exists_congr fun u => ?_
    rw [fiberVal_flip, hfib, neg_one_mul]

/-! ### 必須F step 4: family → certificate (kind-preserving) -/

/-- A structured family inside a signed half of the fibre is a structured certificate for `P` at `a`.
    The sign travels into the polynomial coefficients (PP), into the affine projection (PU), and into
    the `sign` field (MM). -/
noncomputable def structuredCertificate_of_family (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (ε : ℤ) (hε : ε * ε = 1) (F : StructuredFamily (fiberNatSigned P a ε)) :
    StructuredCertificate P a := by
  classical
  have hεne : ε ≠ 0 := by
    intro h
    rw [h, mul_zero] at hε
    exact zero_ne_one hε
  cases F with
  | progression c₀ s hs mem =>
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
      exact .polynomialProgression
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
            exact Nat.eq_of_mul_eq_mul_left hs (Nat.add_left_cancel h3) }
  | quadratic α β γ hα cf out mem mono =>
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
      exact .polynomialProgression
        { q := Polynomial.C (ε * α) * Polynomial.X ^ 2 + Polynomial.C (ε * β) * Polynomial.X
            + Polynomial.C (ε * γ)
          deg_le_two := by rw [Polynomial.natDegree_quadratic hαne]
          nonconst := by rw [Polynomial.natDegree_quadratic hαne]; norm_num
          t₀ := 0
          witness := w
          mem := fun t _ => by rw [heq t]; exact hw t
          injective := fun t t' _ _ h => by
            rw [heq t, heq t'] at h
            exact mono.injective (Nat.cast_injective (mul_left_cancel₀ hεne h)) }
  | pell D x0 y0 unit hx0 XX YY recX recY denom px pc hdenom cf out mem mono =>
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
      exact .pellUnitOrbit
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
            mono.injective (Nat.cast_injective (mul_left_cancel₀ hεne h)) }
  | movingModulus b μ f hb hf cf pr hprime hmpos hpgt hpmod hsucc mem mono =>
      simp only [fiberNatSigned, fiberZZ, Set.mem_setOf_eq] at mem
      choose w hw using mem
      exact .movingModulusStepOrbit
        { b := b
          μ := μ
          modulusFactor := f
          b_pos := hb
          modulusFactor_pos := hf
          sign := ε
          sign_sq := hε
          c := fun k => (cf k : ℤ)
          prime := pr
          modulus_pos := hmpos
          prime_prime := hprime
          prime_gt := hpgt
          prime_modEq := hpmod
          modulus_succ := hsucc
          witness := w
          mem := hw }

/-! ### The summit -/

/-- 必須F: an infinite HALF of the fibre of a quadratic `P` carries a structured certificate. -/
theorem structuredCertificate_of_half_infinite (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2)
    (a : Fin n → ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hinf : {c ∈ fiberZZ P a | 0 ≤ ε * c}.Infinite) : Nonempty (StructuredCertificate P a) := by
  classical
  have hεsq : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεne : ε ≠ 0 := by
    intro h
    rw [h, mul_zero] at hεsq
    exact zero_ne_one hεsq
  obtain ⟨H, L, Q, hH, hset⟩ := exists_fiberSetG_eq_fiberNatSigned P hP a ε hε
  obtain ⟨K, hK⟩ := quadraticProjectionDichotomyZ_all_data r H hH
  rcases hK L Q with hF | hb
  · obtain ⟨F⟩ := hF
    exact ⟨structuredCertificate_of_family P a ε hεsq (F.transport hset)⟩
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

/-- 必須F, closed: every infinite fibre of a quadratic `P` carries a structured certificate. -/
theorem infiniteFiberStructured_of_quadratic (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2) :
    InfiniteFiberStructured P := by
  intro a hinf
  rcases infinite_integer_set_pos_or_neg _ hinf with h1 | h2
  · refine structuredCertificate_of_half_infinite P hP a 1 (Or.inl rfl) ?_
    simpa using h1
  · refine structuredCertificate_of_half_infinite P hP a (-1) (Or.inr rfl) ?_
    have hset : {c ∈ fiberZZ P a | 0 ≤ (-1 : ℤ) * c} = {c ∈ fiberZZ P a | c ≤ 0} := by
      ext c
      simp only [Set.mem_setOf_eq, neg_one_mul, neg_nonneg]
    rw [hset]
    exact h2

/-- THE SUMMIT (Gate 4 必須B, strong form): for every quadratic `P` there is ONE constant `C` such that
    at every parameter point the fibre is bounded by `C·(1+|a|)²` or carries a structured certificate. -/
theorem uniformQuadraticFiberStructureZZ_of_quadratic (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) : UniformQuadraticFiberStructureZZ P :=
  uniformQuadraticFiberStructureZZ_of_infiniteFiberStructured P hP
    (infiniteFiberStructured_of_quadratic P hP)

/-- The Gate-4 summit target in its bounded-or-structured shape. -/
theorem quadraticFiberBoundedOrStructured_of_quadratic (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) : QuadraticFiberBoundedOrStructured P := by
  intro a
  by_cases hfin : (fiberZZ P a).Finite
  · exact Or.inl (weak_target_trivial_on_finite_fibre P a hfin)
  · exact Or.inr (infiniteFiberStructured_of_quadratic P hP a (Set.not_finite.mp hfin))

/-! ### The two names GPT's Gate-5 必須F asks for (thin aliases; the content is above) -/

/-- 必須F name 1: the projection dichotomy in structured (family-carrying) form, all `r`. -/
theorem quadraticProjectionDichotomyZ_structured :
    ∀ r : ℕ, SemanticQuadraticGeneral.QuadraticProjectionDichotomyZData r :=
  SemanticQuadraticGeneral.quadraticProjectionDichotomyZ_all_data

/-- 必須F name 2: every scalar fibre of a quadratic is bounded, or structurally infinite. -/
theorem singleQuadratic_fiber_bounded_or_structurallyInfinite (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) : QuadraticFiberBoundedOrStructured P :=
  quadraticFiberBoundedOrStructured_of_quadratic P hP

end DiophCompression

#print axioms DiophCompression.exists_fiberSetG_eq_fiberNatSigned
#print axioms DiophCompression.structuredCertificate_of_family
#print axioms DiophCompression.structuredCertificate_of_half_infinite
#print axioms DiophCompression.infiniteFiberStructured_of_quadratic
#print axioms DiophCompression.uniformQuadraticFiberStructureZZ_of_quadratic
#print axioms DiophCompression.quadraticFiberBoundedOrStructured_of_quadratic
#print axioms DiophCompression.quadraticProjectionDichotomyZ_structured
#print axioms DiophCompression.singleQuadratic_fiber_bounded_or_structurallyInfinite
