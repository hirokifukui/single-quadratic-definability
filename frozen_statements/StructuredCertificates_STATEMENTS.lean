/-
  Gate 4 必須E: structured certificates (s27, 2026-09-01). Statement freeze of DiophCompression/StructuredCertificates.lean.
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
  sorry

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
  sorry

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
    (movingModulusStepOrbitSG_of_base hk A B C b l m μ q hb hN base).c 0 = base.c := by
  sorry

/-- Strict growth of the moving modulus and of the output (a THEOREM of the recurrence). -/
theorem MovingModulusStepOrbitSG.c_lt_succ {k : ℕ} {A : ℤ} {B : Fin k → ℤ} {C : Matrix (Fin k) (Fin k) ℤ}
    {b l : ℤ} {m : Fin k → ℤ} {μ q : ℤ} (o : MovingModulusStepOrbitSG A B C b l m μ q) (j : ℕ) :
    o.c j < o.c (j + 1) := by
  sorry

theorem MovingModulusStepOrbitSG.c_strictMono {k : ℕ} {A : ℤ} {B : Fin k → ℤ} {C : Matrix (Fin k) (Fin k) ℤ}
    {b l : ℤ} {m : Fin k → ℤ} {μ q : ℤ} (o : MovingModulusStepOrbitSG A B C b l m μ q) : StrictMono o.c := by
  sorry

/-! ### Moving-modulus step orbits at the fibre level -/

/-- The fourth certificate kind (ruling s27): a moving-modulus step orbit over the parameter point `a`. The output
    `sign · c k` is pinned by the recurrence `b c_{k+1} + μ = (b c_k + μ) · p_k` with `p_k` a prime ≡ 1 modulo
    `modulusFactor · b · (b c_k + μ)` above that modulus, for a fixed positive `modulusFactor` (branch B2:
    `2|det(C+Cᵀ)|`; branch B1c, rank-one coupled: `8·max(1,|D'|)·|2k|`). `sign = ±1` carries the OUTER output
    negation, NOT branch B4 (s28 erratum, GPT Gate-4 Q3). -/
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
  sorry

theorem c_strictMono (o : MovingModulusStepOrbitRealization P a) : StrictMono o.c := by
  sorry

theorem sign_ne_zero (o : MovingModulusStepOrbitRealization P a) : o.sign ≠ 0 := by
  sorry

theorem output_injective (o : MovingModulusStepOrbitRealization P a) : Function.Injective o.output := by
  sorry

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
    (c : StructuredCertificate P a) : (fiberZZ P a).Infinite := by
  sorry

/-- The summit target (Gate 4 必須G): every scalar fibre is bounded, or carries a STRUCTURED certificate. -/
def QuadraticFiberBoundedOrStructured {n r : ℕ} (P : Poly (n + 1) r) : Prop :=
  ∀ a : Fin n → ℤ, (∃ B : ℕ, ∀ c ∈ fiberZZ P a, |c| ≤ B) ∨ Nonempty (StructuredCertificate P a)

theorem boundedOrStructured_exclusive {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) (B : ℕ)
    (hB : ∀ c ∈ fiberZZ P a, |c| ≤ B) (c : StructuredCertificate P a) : False := by
  sorry

theorem finite_or_infinite_of_boundedOrStructured {n r : ℕ} (P : Poly (n + 1) r)
    (h : QuadraticFiberBoundedOrStructured P) (a : Fin n → ℤ) :
    (fiberZZ P a).Finite ∨ ((fiberZZ P a).Infinite ∧ Nonempty (StructuredCertificate P a)) := by
  sorry

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
  sorry

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
  sorry


/-! ### 必須A (Gate 5): branch B4 packaged at the orbit level -/

/-- B4 packaging: an SG step orbit of `(-b, -μ)` solves the original `(b, μ)` instance with the same,
    strictly increasing outputs. -/
theorem movingModulusStepOrbitSG_of_negSlope {k : ℕ} {A : ℤ} {B : Fin k → ℤ}
    {C : Matrix (Fin k) (Fin k) ℤ} {b l : ℤ} {m : Fin k → ℤ} {μ q : ℤ}
    (o : MovingModulusStepOrbitSG A B C (-b) l m (-μ) q) :
    StrictMono o.c ∧ ∀ j, ∃ w : ℤ,
      SemanticQuadraticSingular.fqSG A B C b l m μ q (o.c j) (o.u j) w = 0 := by
  sorry

/-- Specification of the B4 extraction. -/
theorem extract_B4_movingStep_spec {k : ℕ} (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (hb : b < 0)
    (hN : (C + Cᵀ).det ≠ 0) (base : SGPoint A B C (-b) l m (-μ) q) :
    (extract_B4_movingStep hk A B C b l m μ q hb hN base).c 0 = base.c ∧
      StrictMono (extract_B4_movingStep hk A B C b l m μ q hb hN base).c ∧
      ∀ j, ∃ w : ℤ, SemanticQuadraticSingular.fqSG A B C b l m μ q
        ((extract_B4_movingStep hk A B C b l m μ q hb hN base).c j)
        ((extract_B4_movingStep hk A B C b l m μ q hb hN base).u j) w = 0 := by
  sorry

end DiophCompression
