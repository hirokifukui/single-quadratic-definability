/-
  frozen_statements/OutputNegation_STATEMENTS.lean — statement freeze (s28) of DiophCompression/OutputNegation.lean — APAL Structural Theory Gate 5, 必須C (s28, 2026-09-02, claude.ai direct).

  OUTPUT-negation transport (c ↦ -c), to be kept strictly apart from the branch-B4 WITNESS reflection
  (w ↦ -w, MovingModulusGeneral.lean, s28 erratum). The engine produces certificates whose outputs grow
  upwards; an infinite integer fibre may be infinite only on its negative half. The remedy is the flipped
  polynomial `negOutputPoly P` (substitution `c ↦ -c` in the output slot), whose fibre is the reflection of
  the fibre of `P`; a certificate for the flipped polynomial becomes a certificate for `P` with negated
  outputs. This is where the `sign = ±1` field of `MovingModulusStepOrbitRealization` earns its keep.
  No sorry; std-3.
-/
import DiophCompression.StructuredCertificates

namespace DiophCompression

open MvPolynomial MPUP Matrix

variable {n r r' : ℕ}

/-! ### The flipped polynomial -/

/-- Substitution acting as `c ↦ -c` on the OUTPUT variable (the last parameter slot) and as the identity
    on the remaining parameters and on the unknowns. -/
noncomputable def negOutputSub (n r : ℕ) : Fin (n + 1) ⊕ Fin r → Poly (n + 1) r
  | Sum.inl i => if i = Fin.last n then -X (Sum.inl i) else X (Sum.inl i)
  | Sum.inr j => X (Sum.inr j)

/-- `negOutputPoly P (a, c, u) = P (a, -c, u)`. -/
noncomputable def negOutputPoly (P : Poly (n + 1) r) : Poly (n + 1) r := bind₁ (negOutputSub n r) P

theorem evalAtZZ_negOutputPoly (P : Poly (n + 1) r) (a : Fin n → ℤ) (c : ℤ) (u : Fin r → ℤ) :
    evalAtZZ (negOutputPoly P) (Fin.snoc a c) u = evalAtZZ P (Fin.snoc a (-c)) u := by
  sorry

theorem mem_fiberZZ_negOutputPoly (P : Poly (n + 1) r) (a : Fin n → ℤ) (c : ℤ) :
    c ∈ fiberZZ (negOutputPoly P) a ↔ -c ∈ fiberZZ P a := by
  sorry

/-- The flipped fibre is the reflection of the fibre. -/
theorem fiberZZ_negOutputPoly (P : Poly (n + 1) r) (a : Fin n → ℤ) :
    fiberZZ (negOutputPoly P) a = Neg.neg '' fiberZZ P a := by
  sorry

/-- The flip is an involution on solutions: applying it twice restores the original polynomial's fibre. -/
theorem mem_fiberZZ_negOutputPoly_neg (P : Poly (n + 1) r) (a : Fin n → ℤ) (c : ℤ) :
    -c ∈ fiberZZ (negOutputPoly P) a ↔ c ∈ fiberZZ P a := by
  sorry

/-! ### Output negation on the three realizations -/

/-- Output negation for the polynomial-progression kind: the output polynomial is negated (same degree). -/
noncomputable def PolynomialProgressionRealization.negOutput {P : Poly (n + 1) r} {P' : Poly (n + 1) r'}
    {a : Fin n → ℤ} (T : (Fin r' → ℤ) → (Fin r → ℤ))
    (hT : ∀ (c : ℤ) (u : Fin r' → ℤ), evalAtZZ P' (Fin.snoc a c) u = 0 →
      evalAtZZ P (Fin.snoc a (-c)) (T u) = 0)
    (o : PolynomialProgressionRealization P' a) : PolynomialProgressionRealization P a where
  q := -o.q
  deg_le_two := by rw [Polynomial.natDegree_neg]; exact o.deg_le_two
  nonconst := by rw [Polynomial.natDegree_neg]; exact o.nonconst
  t₀ := o.t₀
  witness := fun t => T (o.witness t)
  mem := fun t ht => by
    have := hT _ _ (o.mem t ht)
    simpa using this
  injective := fun t t' ht ht' h => by
    refine o.injective t t' ht ht' ?_
    simpa using h

/-- Output negation for the Pell-unit-orbit kind: the affine projection is negated (`pc, px, py ↦ -pc, -px, -py`);
    the orbit, the unit and the norm are untouched. -/
def PellUnitOrbitRealization.negOutput {P : Poly (n + 1) r} {P' : Poly (n + 1) r'}
    {a : Fin n → ℤ} (T : (Fin r' → ℤ) → (Fin r → ℤ))
    (hT : ∀ (c : ℤ) (u : Fin r' → ℤ), evalAtZZ P' (Fin.snoc a c) u = 0 →
      evalAtZZ P (Fin.snoc a (-c)) (T u) = 0)
    (o : PellUnitOrbitRealization P' a) : PellUnitOrbitRealization P a where
  toPellOrbitData := o.toPellOrbitData
  N₀ := o.N₀
  X := o.X
  Y := o.Y
  base_norm := o.base_norm
  succ_X := o.succ_X
  succ_Y := o.succ_Y
  pc := -o.pc
  px := -o.px
  py := -o.py
  denom := o.denom
  denom_ne := o.denom_ne
  output := fun k => -o.output k
  output_eq := fun k => by have := o.output_eq k; linarith
  witness := fun k => T (o.witness k)
  mem := fun k => hT _ _ (o.mem k)
  injective := neg_injective.comp o.injective

/-- Output negation for the moving-modulus step-orbit kind: ONLY the `sign` field flips. The modulus
    recurrence, the primes, the CRT data and the strict growth of `c` are untouched — this is the outer
    transport, not branch B4. -/
def MovingModulusStepOrbitRealization.negOutput {P : Poly (n + 1) r} {P' : Poly (n + 1) r'}
    {a : Fin n → ℤ} (T : (Fin r' → ℤ) → (Fin r → ℤ))
    (hT : ∀ (c : ℤ) (u : Fin r' → ℤ), evalAtZZ P' (Fin.snoc a c) u = 0 →
      evalAtZZ P (Fin.snoc a (-c)) (T u) = 0)
    (o : MovingModulusStepOrbitRealization P' a) : MovingModulusStepOrbitRealization P a where
  b := o.b
  μ := o.μ
  modulusFactor := o.modulusFactor
  b_pos := o.b_pos
  modulusFactor_pos := o.modulusFactor_pos
  sign := -o.sign
  sign_sq := by rw [neg_mul_neg]; exact o.sign_sq
  c := o.c
  prime := o.prime
  modulus_pos := o.modulus_pos
  prime_prime := o.prime_prime
  prime_gt := o.prime_gt
  prime_modEq := o.prime_modEq
  modulus_succ := o.modulus_succ
  witness := fun k => T (o.witness k)
  mem := fun k => by
    have := hT _ _ (o.mem k)
    simpa [neg_mul] using this

/-- Output negation on the whole taxonomy; the KIND is preserved. -/
noncomputable def StructuredCertificate.negOutput {P : Poly (n + 1) r} {P' : Poly (n + 1) r'}
    {a : Fin n → ℤ} (T : (Fin r' → ℤ) → (Fin r → ℤ))
    (hT : ∀ (c : ℤ) (u : Fin r' → ℤ), evalAtZZ P' (Fin.snoc a c) u = 0 →
      evalAtZZ P (Fin.snoc a (-c)) (T u) = 0)
    (cert : StructuredCertificate P' a) : StructuredCertificate P a :=
  match cert with
  | .polynomialProgression o => .polynomialProgression (o.negOutput T hT)
  | .pellUnitOrbit o => .pellUnitOrbit (o.negOutput T hT)
  | .movingModulusStepOrbit o => .movingModulusStepOrbit (o.negOutput T hT)

theorem StructuredCertificate.negOutput_kind {P : Poly (n + 1) r} {P' : Poly (n + 1) r'}
    {a : Fin n → ℤ} (T : (Fin r' → ℤ) → (Fin r → ℤ))
    (hT : ∀ (c : ℤ) (u : Fin r' → ℤ), evalAtZZ P' (Fin.snoc a c) u = 0 →
      evalAtZZ P (Fin.snoc a (-c)) (T u) = 0)
    (cert : StructuredCertificate P' a) : (cert.negOutput T hT).kind = cert.kind := by
  sorry

/-- The transport hypothesis is inhabited by the flipped polynomial itself (`T = id`). -/
theorem negOutputPoly_transport (P : Poly (n + 1) r) (a : Fin n → ℤ) :
    ∀ (c : ℤ) (u : Fin r → ℤ), evalAtZZ (negOutputPoly P) (Fin.snoc a c) u = 0 →
      evalAtZZ P (Fin.snoc a (-c)) (id u) = 0 := by
  sorry

/-- A structured certificate for the flipped polynomial is a structured certificate for `P` itself,
    of the same kind. -/
noncomputable def structuredCertificate_of_flipZero {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (cert : StructuredCertificate (negOutputPoly P) a) : StructuredCertificate P a :=
  cert.negOutput id (negOutputPoly_transport P a)

theorem structuredCertificate_of_flipZero_kind {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (cert : StructuredCertificate (negOutputPoly P) a) :
    (structuredCertificate_of_flipZero cert).kind = cert.kind := by
  sorry

/-! ### Splitting an infinite integer fibre -/

/-- An infinite set of integers is infinite on its nonnegative half or on its nonpositive half. -/
theorem infinite_integer_set_pos_or_neg (S : Set ℤ) (hS : S.Infinite) :
    {c ∈ S | 0 ≤ c}.Infinite ∨ {c ∈ S | c ≤ 0}.Infinite := by
  sorry

/-- 必須C: an infinite integer fibre is infinite on the nonnegative side either for `P` or for the
    flipped polynomial. Combined with a certificate theorem for nonnegative outputs, this reaches the
    whole integer fibre. -/
theorem infinite_integer_fiber_pos_or_neg (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (h : (fiberZZ P a).Infinite) :
    {c ∈ fiberZZ P a | 0 ≤ c}.Infinite ∨ {c ∈ fiberZZ (negOutputPoly P) a | 0 ≤ c}.Infinite := by
  sorry

end DiophCompression
