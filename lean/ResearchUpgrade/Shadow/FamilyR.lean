/-
  Shadow/FamilyR.lean — the ray-carrying family (A3-4 shadow chain, API layer; claude.ai direct).
  `StructuredFamilyR S` = a baseline `StructuredFamily S` PLUS, when its kind is the moving-modulus
  one (kind = 2), a fixed-base prime ray into `Nat.cast '' S`. Non-moving families lift for free;
  transport along set equalities is `subst`; the sign map ε = ±1 moves rays into the ℤ-fibre.
  The two production rays (rank ≥ 2 moving branch at the SG level, rank-one coupled branch at the
  2W level) are built here from A1/A2 (PrimeRay.lean), landing in the baseline's own fibre sets.
-/
import ResearchUpgrade.PrimeRay
import DiophCompression.StructuredFamilyCore
import DiophCompression.SemanticQuadraticSingular.DefsSingularGeneral
import DiophCompression.SemanticQuadraticTwoWitness.Defs2W

namespace DiophCompression.ResearchUpgrade

open DiophCompression Matrix
open DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticSingular
  DiophCompression.SemanticQuadraticTwoWitness

/-- The cast image of a set of naturals. -/
def castSet (S : Set ℕ) : Set ℤ := (fun m : ℕ => (m : ℤ)) '' S

theorem mem_castSet {S : Set ℕ} {m : ℕ} (h : m ∈ S) : (m : ℤ) ∈ castSet S := ⟨m, h, rfl⟩

/-- A structured family that carries a fixed-base prime ray AND an exponential injection whenever it
is of the moving kind. -/
structure StructuredFamilyR (S : Set ℕ) where
  F : StructuredFamily S
  ray : F.kind = 2 → Nonempty (FixedBasePrimeRay (castSet S))
  expInj : F.kind = 2 → ExponentialInjection (castSet S)

namespace StructuredFamilyR

/-- Lift a non-moving family. -/
def lift {S : Set ℕ} (F : StructuredFamily S) (h : F.kind ≠ 2) : StructuredFamilyR S :=
  ⟨F, fun h2 => absurd h2 h, fun h2 => absurd h2 h⟩

def ofProgression {S : Set ℕ} (c₀ s : ℕ) (hs : 1 ≤ s) (mem : ∀ t : ℕ, c₀ + s * t ∈ S) :
    StructuredFamilyR S :=
  lift (.progression c₀ s hs mem) (by simp [StructuredFamily.kind])

def ofPeriodic {S : Set ℕ} (F : PeriodicProgression S) : StructuredFamilyR S :=
  lift F.toStructuredFamily (by simp [PeriodicProgression.toStructuredFamily, StructuredFamily.kind])

/-- Transport along a set equality. -/
def transport {S T : Set ℕ} (h : S = T) (R : StructuredFamilyR S) : StructuredFamilyR T := h ▸ R

/-- A moving-modulus family together with its ray. -/
def ofMoving {S : Set ℕ} (b μ f : ℤ) (hb : 0 < b) (hf : 0 < f) (cf : ℕ → ℕ) (prime : ℕ → ℕ)
    (prime_prime : ∀ k, (prime k).Prime)
    (modulus_pos : ∀ k, 0 < b * (cf k : ℤ) + μ)
    (prime_gt : ∀ k, (f * b * (b * (cf k : ℤ) + μ) : ℤ) < (prime k : ℤ))
    (prime_modEq : ∀ k, ((prime k : ℤ)) ≡ 1 [ZMOD f * b * (b * (cf k : ℤ) + μ)])
    (modulus_succ : ∀ k, b * (cf (k + 1) : ℤ) + μ = (b * (cf k : ℤ) + μ) * (prime k))
    (mem : ∀ t : ℕ, cf t ∈ S) (mono : StrictMono cf)
    (R : FixedBasePrimeRay (castSet S)) (EI : ExponentialInjection (castSet S)) :
    StructuredFamilyR S :=
  ⟨.movingModulus b μ f hb hf cf prime prime_prime modulus_pos prime_gt prime_modEq modulus_succ
    mem mono, fun _ => ⟨R⟩, fun _ => EI⟩

/-- Extract: a ray, or a non-moving family. -/
theorem ray_or_nonmoving {S : Set ℕ} (R : StructuredFamilyR S) :
    Nonempty (FixedBasePrimeRay (castSet S)) ∨ R.F.kind ≠ 2 := by
  by_cases h : R.F.kind = 2
  · exact Or.inl (R.ray h)
  · exact Or.inr h

/-- Extract: an exponential injection, or a non-moving family. -/
theorem expInj_or_nonmoving {S : Set ℕ} (R : StructuredFamilyR S) :
    ExponentialInjection (castSet S) ∨ R.F.kind ≠ 2 := by
  by_cases h : R.F.kind = 2
  · exact Or.inl (R.expInj h)
  · exact Or.inr h

end StructuredFamilyR

/-! ### Ray transport -/

/-- Push a ray through a map `c ↦ ε·c` (`ε ≠ 0`) into a target set. -/
def FixedBasePrimeRay.mapMul {S T : Set ℤ} (R : FixedBasePrimeRay S) (ε : ℤ) (hε : ε ≠ 0)
    (h : ∀ c ∈ S, ε * c ∈ T) : FixedBasePrimeRay T where
  M := R.M
  hM := R.hM
  α := ε * R.α
  β := ε * R.β
  d := R.d
  hα := mul_ne_zero hε R.hα
  hd := R.hd
  c := fun p => ε * R.c p
  affine := fun p hp => by have := R.affine p hp; linear_combination ε * this
  mem := fun p hp => h _ (R.mem p hp)

/-- Monotonicity in the set. -/
def FixedBasePrimeRay.mono {S T : Set ℤ} (R : FixedBasePrimeRay S) (h : S ⊆ T) :
    FixedBasePrimeRay T :=
  R.mapMul 1 one_ne_zero (fun c hc => by simpa using h hc)

/-! ### Production rays into the baseline fibre sets -/

/-- Membership in `fiberSetSG` from the moving divisibility (the `w`-witness is the quotient). -/
theorem mem_fiberSetSG_of_dvd {k : ℕ} (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (c : ℕ) (u : Fin k → ℤ)
    (h : (b * (c : ℤ) + μ) ∣ fqM A B C l m q (c : ℤ) u) : c ∈ fiberSetSG A B C b l m μ q := by
  obtain ⟨w, hw⟩ := h
  refine ⟨u, -w, ?_⟩
  simp only [fqSG]; rw [hw]; ring

/-- A ray with non-negative outputs into a set that meets the cast image on ℕ. -/
def FixedBasePrimeRay.restrictNat {S : Set ℤ} {T : Set ℕ} (R : FixedBasePrimeRay S)
    (hnn : ∀ p, GoodPrime R.M p → 0 ≤ R.c p) (hT : ∀ c ∈ S, 0 ≤ c → c ∈ castSet T) :
    FixedBasePrimeRay (castSet T) where
  M := R.M
  hM := R.hM
  α := R.α
  β := R.β
  d := R.d
  hα := R.hα
  hd := R.hd
  c := R.c
  affine := R.affine
  mem := fun p hp => hT _ (R.mem p hp) (hnn p hp)

/-- `(p−1)/b ≥ 0` for a prime `p` and `b > 0`. -/
theorem ediv_pred_nonneg (p : ℕ) (hp : p.Prime) (b : ℤ) (hb : 0 < b) : 0 ≤ ((p : ℤ) - 1) / b :=
  Int.ediv_nonneg (by have := hp.two_le; omega) hb.le

/-- The rank ≥ 2 moving branch: a base point `c₀ : ℕ` with positive moving modulus gives a ray in
`castSet (fiberSetSG …)`. -/
noncomputable def movingRaySG {k : ℕ} (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (hb : 0 < b)
    (hN : (C + Cᵀ).det ≠ 0) (c₀ : ℕ) (u₀ : Fin k → ℤ)
    (hdiv : (b * (c₀ : ℤ) + μ) ∣ fqM A B C l m q (c₀ : ℤ) u₀) (hpos : 0 < b * (c₀ : ℤ) + μ) :
    FixedBasePrimeRay (castSet (fiberSetSG A B C b l m μ q)) :=
  (movingRay hk A B C b l m μ q (c₀ : ℤ) u₀ hb hN hpos hdiv).restrictNat
    (fun p hp => by
      show 0 ≤ (c₀ : ℤ) + (b * (c₀ : ℤ) + μ) * (((p : ℤ) - 1) / b)
      have := ediv_pred_nonneg p hp.1 b hb
      positivity)
    (fun c hc h0 => by
      obtain ⟨u, hu⟩ := hc
      refine ⟨c.toNat, ?_, Int.toNat_of_nonneg h0⟩
      apply mem_fiberSetSG_of_dvd A B C b l m μ q c.toNat u
      rw [Int.toNat_of_nonneg h0]; exact hu)

/-- Membership in `fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q` from the rank-one divisibility
(the `v`-witness is minus the quotient). -/
theorem mem_fiberSet2_of_dvd (A B₁ B₂ k l m₁ m₂ q : ℤ) (c : ℕ) (u : ℤ)
    (h : (B₂ * (c : ℤ) + m₂) ∣ qOne A B₁ k l m₁ q (c : ℤ) u) :
    c ∈ fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q := by
  obtain ⟨w, hw⟩ := h
  refine ⟨u, -w, ?_⟩
  simp only [fq2]
  have : qOne A B₁ k l m₁ q (c : ℤ) u = A * (c : ℤ) ^ 2 + B₁ * c * u + k * u ^ 2 + l * c + m₁ * u + q := by
    simp [qOne]
  linear_combination hw - this

/-- The rank-one coupled branch: a base point `c₀ : ℕ` with positive modulus gives a ray in
`castSet (fiberSet2 A B₁ B₂ k 0 0 …)`. -/
noncomputable def rankOneRay2W (A B₁ B₂ k l m₁ m₂ q : ℤ) (hB₂ : 0 < B₂) (hk : k ≠ 0)
    (c₀ : ℕ) (u₀ : ℤ) (ht₀ : 0 < B₂ * (c₀ : ℤ) + m₂)
    (hdiv : (B₂ * (c₀ : ℤ) + m₂) ∣ qOne A B₁ k l m₁ q (c₀ : ℤ) u₀) :
    FixedBasePrimeRay (castSet (fiberSet2 A B₁ B₂ k 0 0 l m₁ m₂ q)) :=
  (rankOneRay A B₁ B₂ k l m₁ m₂ q (c₀ : ℤ) u₀ hB₂ hk ht₀ hdiv).restrictNat
    (fun p hp => by
      show 0 ≤ (c₀ : ℤ) + (B₂ * (c₀ : ℤ) + m₂) * (((p : ℤ) - 1) / B₂)
      have := ediv_pred_nonneg p hp.1 B₂ hB₂
      positivity)
    (fun c hc h0 => by
      obtain ⟨u, hu⟩ := hc
      refine ⟨c.toNat, ?_, Int.toNat_of_nonneg h0⟩
      apply mem_fiberSet2_of_dvd A B₁ B₂ k l m₁ m₂ q c.toNat u
      rw [Int.toNat_of_nonneg h0]; exact hu)

end DiophCompression.ResearchUpgrade
