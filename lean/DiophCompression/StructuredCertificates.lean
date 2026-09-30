/-
  DiophCompression/StructuredCertificates.lean — APAL Structural Theory Gate 4, 必須E (certificate semantics)
  (session 27, 2026-09-01, claude.ai direct). Statements frozen in frozen_statements/StructuredCertificates_STATEMENTS.lean.

  Gate-3 review §5/§7: the r24 kinds `pellOrbit` / `primeProgressionCRT` carried metadata next to an ARBITRARY output
  map, and `stepFamily` was generic (classical choice produces one from any fibre unbounded above). This file replaces
  them by realizations whose output is PINNED by the arithmetic data:
    * `PolynomialProgressionRealization` (unchanged, InfiniteFiberCertificate.lean): output = q(t).
    * `PellUnitOrbitRealization`: an explicit orbit (X k, Y k) of a base point under the unit x₀ + y₀√D (recurrence as
      data; norm preservation PROVED), output an affine projection of the orbit point (with a denominator).
    * `MovingModulusStepOrbitRealization` (the fourth kind of ruling s27, name `movingModulusStepOrbit`): the branch-B2
      family — moving modulus t_k = b c_k + μ, a good prime p_k ≡ 1 mod 2|D'| b t_k above it at every stage, and the
      recurrence t_{k+1} = t_k p_k; strict growth is PROVED from the recurrence. The `sign` field is NOT for branch B4
      (s28 erratum below): it carries the OUTER output negation used to reach negative integer outputs.
      Its SG-level form `MovingModulusStepOrbitSG` carries in addition the finite-field root and the CRT congruences of
      each stage, and is CONSTRUCTED from any base point by iterating `moving_modulus_prime_step_data` (the B2
      extraction at the singular-block level).
  The prime–CRT mechanism is therefore a per-stage COMPONENT of the moving-modulus orbit, not a standalone family:
  no branch of the engine emits a fixed prime progression (GATE3_F_BRANCH_INVENTORY). The r24 four-constructor type
  `InfiniteFiberCertificate` and `StepFamilyRealization` are kept unchanged (sealed names) but are SUPERSEDED as the
  summit target: `stepFamily` is a TAG, not structure — Classical.choice turns any fibre unbounded above into one
  (Gate-3 ERRATA E7). ERRATUM (s28, GPT Gate-4 review): the reason previously given here — that branch B4 is a
  DECREASING family — was WRONG. Branch B4 negates the radical witness, not the output
  (`movingModulus_negSlope_witnessEquiv`, `fiberSetSG_negSlope`), the fibre is a `Set ℕ`, and B4 outputs increase.
  No sorry; std-3 expected.
-/
import DiophCompression.InfiniteFiberCertificate
import DiophCompression.SemanticQuadraticSingular.MovingModulusGeneral

namespace DiophCompression

open MvPolynomial MPUP Matrix
open DiophCompression.SemanticQuadraticMatrix (fqM)
open DiophCompression.SemanticQuadraticSingular (movingRemainderPolyG moving_modulus_prime_step_data)

/-! ### Pell-unit orbits with the orbit as data -/

/-- Strengthened Pell kind: the orbit `(X k, Y k)` of a base point under the unit is DATA (recurrence), the output is
    an affine projection `denom · output k = pc + px · X k + py · Y k`, and membership/injectivity are on that output. -/
structure PellUnitOrbitRealization {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) extends PellOrbitData where
  N₀ : ℤ
  X : ℕ → ℤ
  Y : ℕ → ℤ
  base_norm : X 0 ^ 2 - D * Y 0 ^ 2 = N₀
  succ_X : ∀ k, X (k + 1) = x₀ * X k + D * y₀ * Y k
  succ_Y : ∀ k, Y (k + 1) = y₀ * X k + x₀ * Y k
  pc : ℤ
  px : ℤ
  py : ℤ
  denom : ℤ
  denom_ne : denom ≠ 0
  output : ℕ → ℤ
  output_eq : ∀ k, denom * output k = pc + px * X k + py * Y k
  witness : ℕ → Fin r → ℤ
  mem : ∀ k, evalAtZZ P (Fin.snoc a (output k)) (witness k) = 0
  injective : Function.Injective output

/-- Norm preservation along the orbit (a THEOREM of the data, not a field). -/
theorem PellUnitOrbitRealization.orbit_norm {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : PellUnitOrbitRealization P a) (k : ℕ) : c.X k ^ 2 - c.D * c.Y k ^ 2 = c.N₀ := by
  induction k with
  | zero => exact c.base_norm
  | succ k ih =>
    rw [c.succ_X, c.succ_Y]
    have hu := c.unit
    linear_combination (c.X k ^ 2 - c.D * c.Y k ^ 2) * hu + ih

/-- Forgetful map to the r24 Pell realization (metadata + output; the orbit data are dropped). -/
def PellUnitOrbitRealization.toPellOrbitRealization {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : PellUnitOrbitRealization P a) : PellOrbitRealization P a :=
  { c.toPellOrbitData with output := c.output, witness := c.witness, mem := c.mem, injective := c.injective }

/-! ### Moving-modulus step orbits (SG level: full arithmetic data of every stage) -/

/-- A point of the singular-block fibre in the moving-modulus vocabulary: `(c, u)` with positive moving modulus
    `b c + μ` dividing the quadratic form `fqM(c, u)`. -/
structure SGPoint {k : ℕ} (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ)
    (μ q : ℤ) where
  c : ℤ
  u : Fin k → ℤ
  pos : 0 < b * c + μ
  mem : (b * c + μ) ∣ fqM A B C l m q c u

/-- One arithmetic step from a point `P₀`: the good prime, the new point, the finite-field root, and the facts
    relating them (the conclusion of `moving_modulus_prime_step_data` as a record). -/
structure SGStep {k : ℕ} {A : ℤ} {B : Fin k → ℤ} {C : Matrix (Fin k) (Fin k) ℤ} {b l : ℤ} {m : Fin k → ℤ}
    {μ q : ℤ} (P₀ : SGPoint A B C b l m μ q) where
  p : ℕ
  c : ℤ
  u : Fin k → ℤ
  x : Fin k → ℤ
  prime : p.Prime
  gt : (2 * |(C + Cᵀ).det| * b * (b * P₀.c + μ) : ℤ) < p
  modEq : (p : ℤ) ≡ 1 [ZMOD 2 * |(C + Cᵀ).det| * b * (b * P₀.c + μ)]
  modulus_rec : b * c + μ = (b * P₀.c + μ) * p
  root_dvd : (p : ℤ) ∣ movingRemainderPolyG A B C b l m μ q x
  crt_old : ∀ i, (b * P₀.c + μ) ∣ u i - P₀.u i
  crt_new : ∀ i, (p : ℤ) ∣ b * u i - x i
  mem : (b * c + μ) ∣ fqM A B C l m q c u

theorem SGStep.pos {k : ℕ} {A : ℤ} {B : Fin k → ℤ} {C : Matrix (Fin k) (Fin k) ℤ} {b l : ℤ} {m : Fin k → ℤ}
    {μ q : ℤ} {P₀ : SGPoint A B C b l m μ q} (s : SGStep P₀) : 0 < b * s.c + μ := by
  rw [s.modulus_rec]
  exact mul_pos P₀.pos (by exact_mod_cast s.prime.pos)

/-- The new point of a step. -/
def SGStep.toPoint {k : ℕ} {A : ℤ} {B : Fin k → ℤ} {C : Matrix (Fin k) (Fin k) ℤ} {b l : ℤ} {m : Fin k → ℤ}
    {μ q : ℤ} {P₀ : SGPoint A B C b l m μ q} (s : SGStep P₀) : SGPoint A B C b l m μ q :=
  ⟨s.c, s.u, s.pos, s.mem⟩

/-- The step exists at every point (B2 engine, data form). -/
noncomputable def sgStep {k : ℕ} (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (hb : 0 < b) (hN : (C + Cᵀ).det ≠ 0)
    (P₀ : SGPoint A B C b l m μ q) : SGStep P₀ :=
  let h := moving_modulus_prime_step_data hk A B C b l m μ q P₀.c P₀.u hb hN P₀.pos P₀.mem
  let p := Classical.choose h
  let h1 := Classical.choose_spec h
  let c := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let u := Classical.choose h2
  let h3 := Classical.choose_spec h2
  let x := Classical.choose h3
  let h4 := Classical.choose_spec h3
  ⟨p, c, u, x, h4.1, h4.2.1, h4.2.2.1, h4.2.2.2.1, h4.2.2.2.2.1, h4.2.2.2.2.2.1, h4.2.2.2.2.2.2.1,
    h4.2.2.2.2.2.2.2⟩

/-- The orbit of a base point under iterated steps. -/
noncomputable def sgOrbit {k : ℕ} (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (hb : 0 < b) (hN : (C + Cᵀ).det ≠ 0)
    (base : SGPoint A B C b l m μ q) : ℕ → SGPoint A B C b l m μ q :=
  fun j => Nat.rec base (fun _ Pj => (sgStep hk A B C b l m μ q hb hN Pj).toPoint) j

/-- The moving-modulus step orbit at the singular-block level: all arithmetic data of every stage. -/
structure MovingModulusStepOrbitSG {k : ℕ} (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ)
    (m : Fin k → ℤ) (μ q : ℤ) where
  b_pos : 0 < b
  disc_ne : (C + Cᵀ).det ≠ 0
  c : ℕ → ℤ
  u : ℕ → Fin k → ℤ
  prime : ℕ → ℕ
  root : ℕ → Fin k → ℤ
  modulus_pos : ∀ j, 0 < b * c j + μ
  mem : ∀ j, (b * c j + μ) ∣ fqM A B C l m q (c j) (u j)
  prime_prime : ∀ j, (prime j).Prime
  prime_gt : ∀ j, (2 * |(C + Cᵀ).det| * b * (b * c j + μ) : ℤ) < prime j
  prime_modEq : ∀ j, (prime j : ℤ) ≡ 1 [ZMOD 2 * |(C + Cᵀ).det| * b * (b * c j + μ)]
  modulus_succ : ∀ j, b * c (j + 1) + μ = (b * c j + μ) * prime j
  root_dvd : ∀ j, (prime j : ℤ) ∣ movingRemainderPolyG A B C b l m μ q (root j)
  crt_old : ∀ j i, (b * c j + μ) ∣ u (j + 1) i - u j i
  crt_new : ∀ j i, (prime j : ℤ) ∣ b * u (j + 1) i - root j i

/-- B2 extraction at the SG level: every base point generates a full moving-modulus step orbit. -/
noncomputable def movingModulusStepOrbitSG_of_base {k : ℕ} (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (hb : 0 < b) (hN : (C + Cᵀ).det ≠ 0)
    (base : SGPoint A B C b l m μ q) : MovingModulusStepOrbitSG A B C b l m μ q :=
  let O := sgOrbit hk A B C b l m μ q hb hN base
  let S := fun j => sgStep hk A B C b l m μ q hb hN (O j)
  { b_pos := hb, disc_ne := hN,
    c := fun j => (O j).c, u := fun j => (O j).u, prime := fun j => (S j).p, root := fun j => (S j).x,
    modulus_pos := fun j => (O j).pos, mem := fun j => (O j).mem,
    prime_prime := fun j => (S j).prime, prime_gt := fun j => (S j).gt, prime_modEq := fun j => (S j).modEq,
    modulus_succ := fun j => (S j).modulus_rec, root_dvd := fun j => (S j).root_dvd,
    crt_old := fun j => (S j).crt_old, crt_new := fun j => (S j).crt_new }

theorem movingModulusStepOrbitSG_of_base_zero {k : ℕ} (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (hb : 0 < b) (hN : (C + Cᵀ).det ≠ 0)
    (base : SGPoint A B C b l m μ q) :
    (movingModulusStepOrbitSG_of_base hk A B C b l m μ q hb hN base).c 0 = base.c := rfl

/-- Strict growth of the moving modulus and of the output (a THEOREM of the recurrence). -/
theorem MovingModulusStepOrbitSG.c_lt_succ {k : ℕ} {A : ℤ} {B : Fin k → ℤ} {C : Matrix (Fin k) (Fin k) ℤ}
    {b l : ℤ} {m : Fin k → ℤ} {μ q : ℤ} (o : MovingModulusStepOrbitSG A B C b l m μ q) (j : ℕ) :
    o.c j < o.c (j + 1) := by
  have h := o.modulus_succ j
  have hp : (2 : ℤ) ≤ o.prime j := by exact_mod_cast (o.prime_prime j).two_le
  have ht := o.modulus_pos j
  have : b * o.c j + μ < b * o.c (j + 1) + μ := by rw [h]; nlinarith
  have hb := o.b_pos
  nlinarith

theorem MovingModulusStepOrbitSG.c_strictMono {k : ℕ} {A : ℤ} {B : Fin k → ℤ} {C : Matrix (Fin k) (Fin k) ℤ}
    {b l : ℤ} {m : Fin k → ℤ} {μ q : ℤ} (o : MovingModulusStepOrbitSG A B C b l m μ q) : StrictMono o.c :=
  strictMono_nat_of_lt_succ o.c_lt_succ

/-! ### Moving-modulus step orbits at the fibre level -/

/-- The fourth certificate kind (ruling s27): a moving-modulus step orbit over the parameter point `a`. The output
    `sign · c k` is pinned by the recurrence `b c_{k+1} + μ = (b c_k + μ) · p_k` with `p_k` a prime ≡ 1 modulo
    `modulusFactor · b · (b c_k + μ)` above that modulus, for a fixed positive `modulusFactor` whose value is branch
    dependent: branch B2 gives `2|det(C+Cᵀ)|` (MovingModulusGeneral.lean, `moving_modulus_prime_step_data`), branch
    B1c (rank-one coupled) gives `8·max(1,|D'|)·|2k|` (RankOneCoupled.lean). It is NOT a discriminant, hence the
    neutral name (GPT Gate-4 Q3). `sign = ±1` carries the OUTER output negation (negative integer outputs), NOT
    branch B4: B4 reflects the radical witness only (`movingModulus_negSlope_witnessEquiv`). -/
structure MovingModulusStepOrbitRealization {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) where
  b : ℤ
  μ : ℤ
  modulusFactor : ℤ
  b_pos : 0 < b
  modulusFactor_pos : 0 < modulusFactor
  sign : ℤ
  sign_sq : sign * sign = 1
  c : ℕ → ℤ
  prime : ℕ → ℕ
  modulus_pos : ∀ k, 0 < b * c k + μ
  prime_prime : ∀ k, (prime k).Prime
  prime_gt : ∀ k, (modulusFactor * b * (b * c k + μ) : ℤ) < prime k
  prime_modEq : ∀ k, (prime k : ℤ) ≡ 1 [ZMOD modulusFactor * b * (b * c k + μ)]
  modulus_succ : ∀ k, b * c (k + 1) + μ = (b * c k + μ) * prime k
  witness : ℕ → Fin r → ℤ
  mem : ∀ k, evalAtZZ P (Fin.snoc a (sign * c k)) (witness k) = 0

namespace MovingModulusStepOrbitRealization

variable {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}

/-- The output map. -/
def output (o : MovingModulusStepOrbitRealization P a) (k : ℕ) : ℤ := o.sign * o.c k

theorem c_lt_succ (o : MovingModulusStepOrbitRealization P a) (k : ℕ) : o.c k < o.c (k + 1) := by
  have h := o.modulus_succ k
  have hp : (2 : ℤ) ≤ o.prime k := by exact_mod_cast (o.prime_prime k).two_le
  have ht := o.modulus_pos k
  have : o.b * o.c k + o.μ < o.b * o.c (k + 1) + o.μ := by rw [h]; nlinarith
  have hb := o.b_pos
  nlinarith

theorem c_strictMono (o : MovingModulusStepOrbitRealization P a) : StrictMono o.c :=
  strictMono_nat_of_lt_succ o.c_lt_succ

theorem sign_ne_zero (o : MovingModulusStepOrbitRealization P a) : o.sign ≠ 0 := by
  intro h; have := o.sign_sq; rw [h] at this; simp at this

theorem output_injective (o : MovingModulusStepOrbitRealization P a) : Function.Injective o.output := by
  intro k k' h
  have := mul_left_cancel₀ o.sign_ne_zero h
  exact o.c_strictMono.injective this

/-- Soundness: a moving-modulus step orbit is a generic certificate. -/
def toCertificate (o : MovingModulusStepOrbitRealization P a) : InfiniteSubsetCertificate P a where
  index := ℕ
  infinite_index := inferInstance
  output := o.output
  witness := o.witness
  mem := o.mem
  output_injective := o.output_injective

end MovingModulusStepOrbitRealization

/-- Soundness of the strengthened Pell kind. -/
def PellUnitOrbitRealization.toCertificate {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : PellUnitOrbitRealization P a) : InfiniteSubsetCertificate P a where
  index := ℕ
  infinite_index := inferInstance
  output := c.output
  witness := c.witness
  mem := c.mem
  output_injective := c.injective

/-! ### The structured taxonomy (three kinds, outputs pinned by the data) -/

/-- The three families the projection-dichotomy engine emits. -/
inductive StructuredKind
  | polynomialProgression
  | pellUnitOrbit
  | movingModulusStepOrbit

/-- A structured certificate: one of the three kinds WITH its realization. -/
inductive StructuredCertificate {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) : Type
  | polynomialProgression (c : PolynomialProgressionRealization P a)
  | pellUnitOrbit (c : PellUnitOrbitRealization P a)
  | movingModulusStepOrbit (c : MovingModulusStepOrbitRealization P a)

def StructuredCertificate.kind {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : StructuredCertificate P a) : StructuredKind :=
  match c with
  | .polynomialProgression _ => .polynomialProgression
  | .pellUnitOrbit _ => .pellUnitOrbit
  | .movingModulusStepOrbit _ => .movingModulusStepOrbit

/-- Every structured certificate is a generic certificate. -/
def StructuredCertificate.toSubset {n r : ℕ} {P : Poly (n + 1) r} {a : Fin n → ℤ}
    (c : StructuredCertificate P a) : InfiniteSubsetCertificate P a :=
  match c with
  | .polynomialProgression c => c.toCertificate
  | .pellUnitOrbit c => c.toCertificate
  | .movingModulusStepOrbit c => c.toCertificate

/-- 必須E: soundness of the structured certificates. -/
theorem fiber_infinite_of_structuredCertificate {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (c : StructuredCertificate P a) : (fiberZZ P a).Infinite :=
  fiber_infinite_of_certificate P a c.toSubset

/-- The summit target (Gate 4 必須G): every scalar fibre is bounded, or carries a STRUCTURED certificate. -/
def QuadraticFiberBoundedOrStructured {n r : ℕ} (P : Poly (n + 1) r) : Prop :=
  ∀ a : Fin n → ℤ, (∃ B : ℕ, ∀ c ∈ fiberZZ P a, |c| ≤ B) ∨ Nonempty (StructuredCertificate P a)

theorem boundedOrStructured_exclusive {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) (B : ℕ)
    (hB : ∀ c ∈ fiberZZ P a, |c| ≤ B) (c : StructuredCertificate P a) : False :=
  fiber_infinite_of_structuredCertificate P a c (fiber_finite_of_bounded P a B hB)

theorem finite_or_infinite_of_boundedOrStructured {n r : ℕ} (P : Poly (n + 1) r)
    (h : QuadraticFiberBoundedOrStructured P) (a : Fin n → ℤ) :
    (fiberZZ P a).Finite ∨ ((fiberZZ P a).Infinite ∧ Nonempty (StructuredCertificate P a)) := by
  rcases h a with ⟨B, hB⟩ | hc
  · exact Or.inl (fiber_finite_of_bounded P a B hB)
  · obtain ⟨c⟩ := hc
    exact Or.inr ⟨fiber_infinite_of_structuredCertificate P a c, ⟨c⟩⟩

/-- Structured-certificate pullback along an integral change of witness coordinates (the singular branch works in
    transformed coordinates): the output and all arithmetic data are unchanged, only the witnesses are transported. -/
def MovingModulusStepOrbitRealization.pullback {n r r' : ℕ} {P : Poly (n + 1) r} {P' : Poly (n + 1) r'}
    {a : Fin n → ℤ} (T : (Fin r' → ℤ) → (Fin r → ℤ))
    (hT : ∀ (c : ℤ) (u : Fin r' → ℤ), evalAtZZ P' (Fin.snoc a c) u = 0 → evalAtZZ P (Fin.snoc a c) (T u) = 0)
    (o : MovingModulusStepOrbitRealization P' a) : MovingModulusStepOrbitRealization P a :=
  { o with witness := fun k => T (o.witness k), mem := fun k => hT _ _ (o.mem k) }

def PellUnitOrbitRealization.pullback {n r r' : ℕ} {P : Poly (n + 1) r} {P' : Poly (n + 1) r'}
    {a : Fin n → ℤ} (T : (Fin r' → ℤ) → (Fin r → ℤ))
    (hT : ∀ (c : ℤ) (u : Fin r' → ℤ), evalAtZZ P' (Fin.snoc a c) u = 0 → evalAtZZ P (Fin.snoc a c) (T u) = 0)
    (o : PellUnitOrbitRealization P' a) : PellUnitOrbitRealization P a :=
  { o with witness := fun k => T (o.witness k), mem := fun k => hT _ _ (o.mem k) }

def PolynomialProgressionRealization.pullback {n r r' : ℕ} {P : Poly (n + 1) r} {P' : Poly (n + 1) r'}
    {a : Fin n → ℤ} (T : (Fin r' → ℤ) → (Fin r → ℤ))
    (hT : ∀ (c : ℤ) (u : Fin r' → ℤ), evalAtZZ P' (Fin.snoc a c) u = 0 → evalAtZZ P (Fin.snoc a c) (T u) = 0)
    (o : PolynomialProgressionRealization P' a) : PolynomialProgressionRealization P a :=
  { o with witness := fun t => T (o.witness t), mem := fun t ht => hT _ _ (o.mem t ht) }

/-- Kind-preserving pullback of structured certificates. -/
def StructuredCertificate.pullback {n r r' : ℕ} {P : Poly (n + 1) r} {P' : Poly (n + 1) r'} {a : Fin n → ℤ}
    (T : (Fin r' → ℤ) → (Fin r → ℤ))
    (hT : ∀ (c : ℤ) (u : Fin r' → ℤ), evalAtZZ P' (Fin.snoc a c) u = 0 → evalAtZZ P (Fin.snoc a c) (T u) = 0)
    (c : StructuredCertificate P' a) : StructuredCertificate P a :=
  match c with
  | .polynomialProgression c => .polynomialProgression (c.pullback T hT)
  | .pellUnitOrbit c => .pellUnitOrbit (c.pullback T hT)
  | .movingModulusStepOrbit c => .movingModulusStepOrbit (c.pullback T hT)

theorem StructuredCertificate.pullback_kind {n r r' : ℕ} {P : Poly (n + 1) r} {P' : Poly (n + 1) r'}
    {a : Fin n → ℤ} (T : (Fin r' → ℤ) → (Fin r → ℤ))
    (hT : ∀ (c : ℤ) (u : Fin r' → ℤ), evalAtZZ P' (Fin.snoc a c) u = 0 → evalAtZZ P (Fin.snoc a c) (T u) = 0)
    (c : StructuredCertificate P' a) : (c.pullback T hT).kind = c.kind := by
  cases c <;> rfl

/-! ### Leaf-level extraction lemmas -/

/-- Witnessed periodicity ⇒ an arithmetic-progression certificate (branches A3, B3, B1b (m₂ ≠ 0), and the r06
    leaves D3/D4/D6): from one fibre point and a witness shift `c ↦ c + T`, the progression `c₀ + T·t` lies in the
    fibre with explicitly iterated witnesses. -/
theorem polynomialProgression_of_periodic_shift {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (T : ℕ) (hT : 0 < T) (c₀ : ℤ) (u₀ : Fin r → ℤ) (h₀ : evalAtZZ P (Fin.snoc a c₀) u₀ = 0)
    (shift : ℤ → (Fin r → ℤ) → (Fin r → ℤ))
    (hshift : ∀ (c : ℤ) (u : Fin r → ℤ), evalAtZZ P (Fin.snoc a c) u = 0 →
      evalAtZZ P (Fin.snoc a (c + T)) (shift c u) = 0) :
    ∃ cert : PolynomialProgressionRealization P a, cert.q = Polynomial.C c₀ + Polynomial.C (T : ℤ) * Polynomial.X ∧ cert.t₀ = 0 := by
  let q : Polynomial ℤ := Polynomial.C c₀ + Polynomial.C (T : ℤ) * Polynomial.X
  have hTz : (T : ℤ) ≠ 0 := by exact_mod_cast hT.ne'
  have hq : q.natDegree = 1 := by
    simp only [q]
    rw [add_comm, Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul_X _ hTz]
  have hev : ∀ t : ℕ, q.eval (t : ℤ) = c₀ + T * t := by
    intro t; simp [q]
  let w : ℕ → Fin r → ℤ := fun t => Nat.rec u₀ (fun t u => shift (c₀ + T * t) u) t
  have hw : ∀ t : ℕ, evalAtZZ P (Fin.snoc a (c₀ + T * t)) (w t) = 0 := by
    intro t
    induction t with
    | zero =>
      show evalAtZZ P (Fin.snoc a (c₀ + (T : ℤ) * ((0 : ℕ) : ℤ))) u₀ = 0
      simpa using h₀
    | succ t ih =>
      have := hshift _ _ ih
      have e : c₀ + (T : ℤ) * ((t + 1 : ℕ) : ℤ) = c₀ + T * t + T := by push_cast; ring
      rw [e]; exact this
  refine ⟨⟨⟨q, by omega, by omega⟩, 0, w, ?_, ?_⟩, rfl, rfl⟩
  · intro t _; rw [hev]; exact hw t
  · intro t t' _ _ h
    rw [hev, hev] at h
    have : (T : ℤ) * t = T * t' := by linarith
    exact_mod_cast mul_left_cancel₀ hTz this


/-! ### 必須A (Gate 5): branch B4 packaged at the orbit level -/

/-- B4 packaging. An SG step orbit of the POSITIVE-slope instance `(-b, -μ)` is a family of solutions of the
    ORIGINAL instance `(b, μ)` with the SAME, strictly INCREASING outputs and the SAME block witnesses; only the
    radical witness is supplied by the transport. This replaces the withdrawn claim that B4 produces a decreasing
    family (s28 erratum). -/
theorem movingModulusStepOrbitSG_of_negSlope {k : ℕ} {A : ℤ} {B : Fin k → ℤ}
    {C : Matrix (Fin k) (Fin k) ℤ} {b l : ℤ} {m : Fin k → ℤ} {μ q : ℤ}
    (o : MovingModulusStepOrbitSG A B C (-b) l m (-μ) q) :
    StrictMono o.c ∧ ∀ j, ∃ w : ℤ,
      SemanticQuadraticSingular.fqSG A B C b l m μ q (o.c j) (o.u j) w = 0 := by
  refine ⟨o.c_strictMono, fun j => ?_⟩
  obtain ⟨t, ht⟩ := o.mem j
  exact ⟨t, SemanticQuadraticSingular.movingModulus_negSlope_dvd_transfer A B C b l m μ q
    (o.c j) (o.u j) t ht⟩

/-- B4 extraction: from a base point of the positive-slope partner of a `b < 0` instance, the moving-modulus step
    orbit of branch B2 is available verbatim; no separate decreasing machinery is needed. -/
noncomputable def extract_B4_movingStep {k : ℕ} (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (hb : b < 0)
    (hN : (C + Cᵀ).det ≠ 0) (base : SGPoint A B C (-b) l m (-μ) q) :
    MovingModulusStepOrbitSG A B C (-b) l m (-μ) q :=
  movingModulusStepOrbitSG_of_base hk A B C (-b) l m (-μ) q (by linarith) hN base

/-- Specification of `extract_B4_movingStep`: the extracted orbit starts at the given base point, its outputs are
    strictly increasing, and every output solves the ORIGINAL `b < 0` instance. -/
theorem extract_B4_movingStep_spec {k : ℕ} (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (hb : b < 0)
    (hN : (C + Cᵀ).det ≠ 0) (base : SGPoint A B C (-b) l m (-μ) q) :
    (extract_B4_movingStep hk A B C b l m μ q hb hN base).c 0 = base.c ∧
      StrictMono (extract_B4_movingStep hk A B C b l m μ q hb hN base).c ∧
      ∀ j, ∃ w : ℤ, SemanticQuadraticSingular.fqSG A B C b l m μ q
        ((extract_B4_movingStep hk A B C b l m μ q hb hN base).c j)
        ((extract_B4_movingStep hk A B C b l m μ q hb hN base).u j) w = 0 :=
  ⟨movingModulusStepOrbitSG_of_base_zero hk A B C (-b) l m (-μ) q (by linarith) hN base,
    (movingModulusStepOrbitSG_of_negSlope (b := b) _).1,
    (movingModulusStepOrbitSG_of_negSlope (b := b) _).2⟩

end DiophCompression

#print axioms DiophCompression.PellUnitOrbitRealization.orbit_norm
#print axioms DiophCompression.MovingModulusStepOrbitSG.c_strictMono
#print axioms DiophCompression.movingModulusStepOrbitSG_of_base_zero
#print axioms DiophCompression.MovingModulusStepOrbitRealization.output_injective
#print axioms DiophCompression.fiber_infinite_of_structuredCertificate
#print axioms DiophCompression.boundedOrStructured_exclusive
#print axioms DiophCompression.finite_or_infinite_of_boundedOrStructured
#print axioms DiophCompression.StructuredCertificate.pullback_kind
#print axioms DiophCompression.polynomialProgression_of_periodic_shift
#print axioms DiophCompression.movingModulusStepOrbitSG_of_negSlope
#print axioms DiophCompression.extract_B4_movingStep_spec
