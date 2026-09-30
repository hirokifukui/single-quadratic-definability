/-
  frozen_statements/InfiniteFiberCertificate_STATEMENTS.lean — APAL Structural Theory Gate 3, 必須F kernel layer (frozen s26, 2026-09-01; re-frozen after the s26 ruling adding the stepFamily kind). Generic infinite-fibre certificate + soundness/unboundedness/pullback; FOUR kinds as DEPENDENT data (polynomial progression / Pell orbit / prime progression / step family); Dirichlet-backed prime index set; typed certificate InfiniteFiberCertificate with per-kind soundness; placeholder-free target predicate QuadraticFiberBoundedOrCertified (summit theorem stays a draft).
-/
import DiophCompression.FiniteFiberGrowth
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Generic certificate and soundness -/

/-- Generic certificate that the scalar fibre of `P` over `a` is infinite: an infinite index type, an output
    map into the fibre, a witness map, membership, output injectivity. -/
structure InfiniteSubsetCertificate {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) where
  index : Type
  infinite_index : Infinite index
  output : index → ℤ
  witness : index → Fin r → ℤ
  mem : ∀ i, evalAtZZ P (Fin.snoc a (output i)) (witness i) = 0
  output_injective : Function.Injective output

/-- Soundness: a certificate proves the fibre infinite. -/
theorem fiber_infinite_of_certificate {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (c : InfiniteSubsetCertificate P a) : (fiberZZ P a).Infinite := by
  sorry

/-- A bounded set of integers is finite. -/
theorem fiber_finite_of_bounded {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) (B : ℕ)
    (hB : ∀ c ∈ fiberZZ P a, |c| ≤ B) : (fiberZZ P a).Finite := by
  sorry

/-- Output unboundedness: a certified fibre exceeds every bound. -/
theorem fiber_unbounded_of_certificate {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (c : InfiniteSubsetCertificate P a) : ∀ B : ℕ, ∃ x ∈ fiberZZ P a, (B : ℤ) < |x| := by
  sorry

/-- Witness-coordinate pullback: an integral change of witness coordinates `T` that carries solutions of `P'`
    to solutions of `P` transports certificates (the singular branch works in transformed coordinates). -/
theorem certificate_pullback {n r r' : ℕ} (P : Poly (n + 1) r) (P' : Poly (n + 1) r') (a : Fin n → ℤ)
    (T : (Fin r' → ℤ) → (Fin r → ℤ))
    (hT : ∀ (c : ℤ) (u : Fin r' → ℤ), evalAtZZ P' (Fin.snoc a c) u = 0 → evalAtZZ P (Fin.snoc a c) (T u) = 0)
    (cert : InfiniteSubsetCertificate P' a) : Nonempty (InfiniteSubsetCertificate P a) := by
  sorry

/-! ### The three kinds: metadata + realization (dependent constructors) -/

/-- The three certificate kinds produced by the projection-dichotomy engine. -/
inductive CertificateKind
  | polynomialProgression
  | pellOrbit
  | primeProgressionCRT
  | stepFamily

/-- Kind metadata: polynomial progression of degree ≤ 2 (degree 1 = arithmetic progression). -/
structure PolynomialProgressionData where
  q : Polynomial ℤ
  deg_le_two : q.natDegree ≤ 2
  nonconst : 0 < q.natDegree

/-- Kind metadata: Pell-unit orbit — a fundamental unit `x₀ + y₀√D` of `x² − D y² = 1`. -/
structure PellOrbitData where
  D : ℤ
  D_pos : 0 < D
  D_nonsquare : ¬ IsSquare D
  x₀ : ℤ
  y₀ : ℤ
  unit : x₀ ^ 2 - D * y₀ ^ 2 = 1
  y₀_ne : y₀ ≠ 0

/-- Kind metadata: primes in an arithmetic progression above a threshold (moving-modulus branch): modulus `M`,
    residue `a₀` coprime to `M`, threshold `P₀`. -/
structure PrimeProgressionCRTData where
  M : ℕ
  M_pos : 0 < M
  a₀ : ℕ
  coprime : Nat.Coprime a₀ M
  P₀ : ℕ

/-- Index set of the prime kind. -/
def PrimeProgressionCRTData.indexSet (d : PrimeProgressionCRTData) : Set ℕ :=
  {p | p.Prime ∧ p % d.M = d.a₀ % d.M ∧ d.P₀ ≤ p}

/-- Dirichlet-backed: the index set of the prime kind is infinite. -/
theorem primeProgression_index_infinite (d : PrimeProgressionCRTData) : d.indexSet.Infinite := by
  sorry

/-- Realization of the polynomial-progression kind: outputs `q(t)` for `t ≥ t₀`, injective on that tail. -/
structure PolynomialProgressionRealization {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ)
    extends PolynomialProgressionData where
  t₀ : ℕ
  witness : ℕ → Fin r → ℤ
  mem : ∀ t : ℕ, t₀ ≤ t → evalAtZZ P (Fin.snoc a (q.eval (t : ℤ))) (witness t) = 0
  injective : ∀ t t' : ℕ, t₀ ≤ t → t₀ ≤ t' → q.eval (t : ℤ) = q.eval (t' : ℤ) → t = t'

/-- Realization of the Pell-orbit kind: the `c`-projection of the `k`-th orbit point, `k ∈ ℕ`. -/
structure PellOrbitRealization {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) extends PellOrbitData where
  output : ℕ → ℤ
  witness : ℕ → Fin r → ℤ
  mem : ∀ k, evalAtZZ P (Fin.snoc a (output k)) (witness k) = 0
  injective : Function.Injective output

/-- Realization of the prime-progression kind: outputs indexed by the primes of the progression above the
    threshold, injective on that index set. -/
structure PrimeProgressionRealization {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ)
    extends PrimeProgressionCRTData where
  output : ℕ → ℤ
  witness : ℕ → Fin r → ℤ
  mem : ∀ p ∈ toPrimeProgressionCRTData.indexSet, evalAtZZ P (Fin.snoc a (output p)) (witness p) = 0
  injective : ∀ p ∈ toPrimeProgressionCRTData.indexSet, ∀ p' ∈ toPrimeProgressionCRTData.indexSet,
    output p = output p' → p = p'

/-- Realization of the step-family kind (moving-modulus branch, ruling s26): a strictly increasing sequence of
    fibre elements produced by iterating an explicit step (from a fibre element and its witness, a larger fibre
    element and its witness). The data are the base point and the step; the sequence is `Nat.rec`. -/
structure StepFamilyRealization {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) where
  base : ℤ × (Fin r → ℤ)
  base_mem : evalAtZZ P (Fin.snoc a base.1) base.2 = 0
  step : ℤ × (Fin r → ℤ) → ℤ × (Fin r → ℤ)
  step_mem : ∀ cu, evalAtZZ P (Fin.snoc a cu.1) cu.2 = 0 → evalAtZZ P (Fin.snoc a (step cu).1) (step cu).2 = 0
  step_gt : ∀ cu, evalAtZZ P (Fin.snoc a cu.1) cu.2 = 0 → cu.1 < (step cu).1

/-- The `k`-th point of a step family. -/
def StepFamilyRealization.point {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : StepFamilyRealization P a) (k : ℕ) : ℤ × (Fin r → ℤ) :=
  Nat.rec c.base (fun _ cu => c.step cu) k

theorem StepFamilyRealization.point_mem {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : StepFamilyRealization P a) (k : ℕ) :
    evalAtZZ P (Fin.snoc a (c.point k).1) (c.point k).2 = 0 := by
  sorry

theorem StepFamilyRealization.point_strictMono {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : StepFamilyRealization P a) : StrictMono fun k => (c.point k).1 := by
  sorry

/-- A typed certificate: one of the four kinds, WITH its realization (no placeholder). -/
inductive InfiniteFiberCertificate {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) : Type
  | polynomialProgression (c : PolynomialProgressionRealization P a)
  | pellOrbit (c : PellOrbitRealization P a)
  | primeProgressionCRT (c : PrimeProgressionRealization P a)
  | stepFamily (c : StepFamilyRealization P a)

/-- The kind tag of a typed certificate. -/
def InfiniteFiberCertificate.kind {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : InfiniteFiberCertificate P a) : CertificateKind :=
  match c with
  | .polynomialProgression _ => .polynomialProgression
  | .pellOrbit _ => .pellOrbit
  | .primeProgressionCRT _ => .primeProgressionCRT
  | .stepFamily _ => .stepFamily

/-- Soundness of the polynomial-progression kind (index ℕ, shifted by the threshold). -/
def PolynomialProgressionRealization.toCertificate {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : PolynomialProgressionRealization P a) : InfiniteSubsetCertificate P a where
  index := ℕ
  infinite_index := inferInstance
  output := fun t => c.q.eval ((c.t₀ + t : ℕ) : ℤ)
  witness := fun t => c.witness (c.t₀ + t)
  mem := fun t => c.mem (c.t₀ + t) (Nat.le_add_right _ _)
  output_injective := fun t t' h => by
    have := c.injective (c.t₀ + t) (c.t₀ + t') (Nat.le_add_right _ _) (Nat.le_add_right _ _) h
    omega

/-- Soundness of the Pell-orbit kind. -/
def PellOrbitRealization.toCertificate {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : PellOrbitRealization P a) : InfiniteSubsetCertificate P a where
  index := ℕ
  infinite_index := inferInstance
  output := c.output
  witness := c.witness
  mem := c.mem
  output_injective := c.injective

/-- Soundness of the prime-progression kind (index = the Dirichlet-infinite set of primes). -/
def PrimeProgressionRealization.toCertificate {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : PrimeProgressionRealization P a) : InfiniteSubsetCertificate P a where
  index := c.toPrimeProgressionCRTData.indexSet
  infinite_index := Set.infinite_coe_iff.2 (primeProgression_index_infinite c.toPrimeProgressionCRTData)
  output := fun p => c.output p.1
  witness := fun p => c.witness p.1
  mem := fun p => c.mem p.1 p.2
  output_injective := fun p p' h => Subtype.ext (c.injective p.1 p.2 p'.1 p'.2 h)

/-- Soundness of the step-family kind (index ℕ, strictly increasing outputs). -/
def StepFamilyRealization.toCertificate {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : StepFamilyRealization P a) : InfiniteSubsetCertificate P a where
  index := ℕ
  infinite_index := inferInstance
  output := fun k => (c.point k).1
  witness := fun k => (c.point k).2
  mem := c.point_mem
  output_injective := c.point_strictMono.injective

/-- Every typed certificate is a generic certificate. -/
def InfiniteFiberCertificate.toSubset {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : InfiniteFiberCertificate P a) : InfiniteSubsetCertificate P a :=
  match c with
  | .polynomialProgression c => c.toCertificate
  | .pellOrbit c => c.toCertificate
  | .primeProgressionCRT c => c.toCertificate
  | .stepFamily c => c.toCertificate

/-- 必須F: soundness of the typed certificates. -/
theorem fiber_infinite_of_typedCertificate {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (c : InfiniteFiberCertificate P a) : (fiberZZ P a).Infinite := by
  sorry

/-! ### The target predicate (placeholder-free) -/

/-- TARGET predicate: every scalar fibre is bounded, or carries a typed certificate. -/
def QuadraticFiberBoundedOrCertified {n r : ℕ} (P : Poly (n + 1) r) : Prop :=
  ∀ a : Fin n → ℤ, (∃ B : ℕ, ∀ c ∈ fiberZZ P a, |c| ≤ B) ∨ Nonempty (InfiniteFiberCertificate P a)

/-- The target predicate is a genuine dichotomy: the two alternatives are exclusive. -/
theorem boundedOrCertified_exclusive {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) (B : ℕ)
    (hB : ∀ c ∈ fiberZZ P a, |c| ≤ B) (c : InfiniteFiberCertificate P a) : False := by
  sorry

/-- Consequence of the target predicate: every fibre is finite or infinite-with-certificate. -/
theorem finite_or_infinite_of_boundedOrCertified {n r : ℕ} (P : Poly (n + 1) r)
    (h : QuadraticFiberBoundedOrCertified P) (a : Fin n → ℤ) :
    (fiberZZ P a).Finite ∨ ((fiberZZ P a).Infinite ∧ Nonempty (InfiniteFiberCertificate P a)) := by
  sorry

end DiophCompression
