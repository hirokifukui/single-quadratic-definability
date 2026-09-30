/-
  DiophCompression/InfiniteFiberCertificate.lean — APAL Structural Theory Gate 3, 必須F kernel layer
  (certificate taxonomy redesign; session 26, 2026-09-01, claude.ai direct). Statements frozen in
  frozen_statements/InfiniteFiberCertificate_STATEMENTS.lean. Supersedes drafts/InfiniteFiberCertificate_STATEMENTS_v1
  (whose `∃ _k : CertificateKind, True` placeholder is REMOVED here).

  Ruling s26 (Dr. Fukui, after GATE3_F_BRANCH_INVENTORY B2): a fourth kind `stepFamily` for the moving-modulus branch.
  Certificates that the scalar fibre of a quadratic equation over a parameter point is infinite, as DEPENDENT
  data: each kind carries its metadata (polynomial progression / Pell-unit orbit / primes in a progression
  above a threshold) TOGETHER with a realization (output map, witness map, membership, injectivity on the
  index set). Soundness is proved per kind; the prime kind's index set is infinite by Dirichlet
  (mathlib `Nat.infinite_setOf_prime_and_eq_mod`). The summit theorem (every quadratic fibre is bounded or
  certified) is NOT here — it stays a draft (drafts/InfiniteFiberCertificate_STATEMENTS_v2.lean).
  No sorry; std-3 expected.
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
  haveI := c.infinite_index
  exact Set.infinite_of_injective_forall_mem c.output_injective (fun i => ⟨c.witness i, c.mem i⟩)

/-- A bounded set of integers is finite. -/
theorem fiber_finite_of_bounded {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) (B : ℕ)
    (hB : ∀ c ∈ fiberZZ P a, |c| ≤ B) : (fiberZZ P a).Finite := by
  refine (Set.finite_Icc (-(B : ℤ)) B).subset fun c hc => ?_
  exact Set.mem_Icc.2 (abs_le.1 (hB c hc))

/-- Output unboundedness: a certified fibre exceeds every bound. -/
theorem fiber_unbounded_of_certificate {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (c : InfiniteSubsetCertificate P a) : ∀ B : ℕ, ∃ x ∈ fiberZZ P a, (B : ℤ) < |x| := by
  intro B
  by_contra h
  have hB : ∀ x ∈ fiberZZ P a, |x| ≤ B := fun x hx => not_lt.1 fun hlt => h ⟨x, hx, hlt⟩
  exact fiber_infinite_of_certificate P a c (fiber_finite_of_bounded P a B hB)

/-- Witness-coordinate pullback: an integral change of witness coordinates `T` that carries solutions of `P'`
    to solutions of `P` transports certificates (the singular branch works in transformed coordinates). -/
theorem certificate_pullback {n r r' : ℕ} (P : Poly (n + 1) r) (P' : Poly (n + 1) r') (a : Fin n → ℤ)
    (T : (Fin r' → ℤ) → (Fin r → ℤ))
    (hT : ∀ (c : ℤ) (u : Fin r' → ℤ), evalAtZZ P' (Fin.snoc a c) u = 0 → evalAtZZ P (Fin.snoc a c) (T u) = 0)
    (cert : InfiniteSubsetCertificate P' a) : Nonempty (InfiniteSubsetCertificate P a) :=
  ⟨{ index := cert.index, infinite_index := cert.infinite_index, output := cert.output,
     witness := fun i => T (cert.witness i), mem := fun i => hT _ _ (cert.mem i),
     output_injective := cert.output_injective }⟩

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
  haveI : NeZero d.M := ⟨by have := d.M_pos; omega⟩
  have h1 : {p : ℕ | p.Prime ∧ (p : ZMod d.M) = (d.a₀ : ZMod d.M)}.Infinite := by
    have hu : IsUnit ((d.a₀ : ℕ) : ZMod d.M) := by
      rw [← ZMod.coe_unitOfCoprime d.a₀ d.coprime]
      exact Units.isUnit _
    exact Nat.infinite_setOf_prime_and_eq_mod hu
  refine (h1.diff (Set.finite_lt_nat d.P₀)).mono fun p hp => ?_
  obtain ⟨⟨hpr, hmod⟩, hlt⟩ := hp
  refine ⟨hpr, (ZMod.natCast_eq_natCast_iff' p d.a₀ d.M).1 hmod, ?_⟩
  simp only [Set.mem_setOf_eq, not_lt] at hlt
  exact hlt

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
  induction k with
  | zero => exact c.base_mem
  | succ k ih => exact c.step_mem _ ih

theorem StepFamilyRealization.point_strictMono {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : StepFamilyRealization P a) : StrictMono fun k => (c.point k).1 := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  exact c.step_gt _ (c.point_mem k)

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
    (c : InfiniteFiberCertificate P a) : (fiberZZ P a).Infinite :=
  fiber_infinite_of_certificate P a c.toSubset

/-! ### The target predicate (placeholder-free) -/

/-- TARGET predicate: every scalar fibre is bounded, or carries a typed certificate. -/
def QuadraticFiberBoundedOrCertified {n r : ℕ} (P : Poly (n + 1) r) : Prop :=
  ∀ a : Fin n → ℤ, (∃ B : ℕ, ∀ c ∈ fiberZZ P a, |c| ≤ B) ∨ Nonempty (InfiniteFiberCertificate P a)

/-- The target predicate is a genuine dichotomy: the two alternatives are exclusive. -/
theorem boundedOrCertified_exclusive {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) (B : ℕ)
    (hB : ∀ c ∈ fiberZZ P a, |c| ≤ B) (c : InfiniteFiberCertificate P a) : False :=
  fiber_infinite_of_typedCertificate P a c (fiber_finite_of_bounded P a B hB)

/-- Consequence of the target predicate: every fibre is finite or infinite-with-certificate. -/
theorem finite_or_infinite_of_boundedOrCertified {n r : ℕ} (P : Poly (n + 1) r)
    (h : QuadraticFiberBoundedOrCertified P) (a : Fin n → ℤ) :
    (fiberZZ P a).Finite ∨ ((fiberZZ P a).Infinite ∧ Nonempty (InfiniteFiberCertificate P a)) := by
  rcases h a with ⟨B, hB⟩ | hc
  · exact Or.inl (fiber_finite_of_bounded P a B hB)
  · obtain ⟨c⟩ := hc
    exact Or.inr ⟨fiber_infinite_of_typedCertificate P a c, ⟨c⟩⟩

end DiophCompression

#print axioms DiophCompression.fiber_infinite_of_certificate
#print axioms DiophCompression.fiber_unbounded_of_certificate
#print axioms DiophCompression.certificate_pullback
#print axioms DiophCompression.primeProgression_index_infinite
#print axioms DiophCompression.StepFamilyRealization.point_strictMono
#print axioms DiophCompression.fiber_infinite_of_typedCertificate
#print axioms DiophCompression.boundedOrCertified_exclusive
#print axioms DiophCompression.finite_or_infinite_of_boundedOrCertified
