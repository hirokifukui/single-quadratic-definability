/-
  DiophCompression/StructuredFamilyCore.lean — APAL Structural Theory Gate 5, 必須F step 3
  (the assembly-level family type) (s28, 2026-09-02, claude.ai direct).

  The layers above the leaves (rank-one normal form, singular block, full-rank block, the top dichotomy)
  each speak about a DIFFERENT fibre set, and each currently discards the family into `Set.Infinite`.
  Making the family type generic in the set is what lets a single certificate travel through all of them:
  transport along a set equality becomes `▸`, and each layer only has to say which set it works in.
  The constructors carry the data (progression step, quadratic coefficients, Pell unit); soundness is
  proved once, here. No sorry; std-3.
-/
import DiophCompression.PeriodicProgressionCore

namespace DiophCompression

/-- A structured family inside a set of naturals — the three shapes the projection engine emits. -/
inductive StructuredFamily (S : Set ℕ) : Type
  /-- an arithmetic progression `c₀ + s·t` with `s ≥ 1` (the PP kind, degree 1). -/
  | progression (c₀ s : ℕ) (hs : 1 ≤ s) (mem : ∀ t : ℕ, c₀ + s * t ∈ S)
  /-- a degree-2 progression with nonzero leading coefficient (the PP kind, degree 2). -/
  | quadratic (α β γ : ℤ) (hα : α ≠ 0) (cf : ℕ → ℕ)
      (out : ∀ t : ℕ, (cf t : ℤ) = α * (t : ℤ) ^ 2 + β * (t : ℤ) + γ)
      (mem : ∀ t : ℕ, cf t ∈ S) (mono : StrictMono cf)
  /-- the orbit of a unit of `x² − D y² = 1` (the PU kind), with the orbit coordinates and the affine
      projection with denominator that reads the output off them — the data the `PellUnitOrbitRealization`
      of `StructuredCertificates.lean` requires. -/
  | pell (D P Q : ℤ) (unit : P ^ 2 - D * Q ^ 2 = 1) (hP : 2 ≤ P)
      (X Y : ℕ → ℤ)
      (recX : ∀ k, X (k + 1) = X k * P + D * Y k * Q)
      (recY : ∀ k, Y (k + 1) = X k * Q + Y k * P)
      (denom px pc : ℤ) (hdenom : denom ≠ 0)
      (cf : ℕ → ℕ) (out : ∀ k, denom * (cf k : ℤ) = px * X k + pc)
      (mem : ∀ t : ℕ, cf t ∈ S) (mono : StrictMono cf)
  /-- a moving-modulus step orbit: outputs pinned by the recurrence `b c_{k+1} + μ = (b c_k + μ)·p_k`
      with primes `p_k` above the branch's modulus factor (the MM kind). -/
  | movingModulus (b μ modulusFactor : ℤ) (hb : 0 < b) (hf : 0 < modulusFactor)
      (cf : ℕ → ℕ) (prime : ℕ → ℕ)
      (prime_prime : ∀ k, (prime k).Prime)
      (modulus_pos : ∀ k, 0 < b * (cf k : ℤ) + μ)
      (prime_gt : ∀ k, (modulusFactor * b * (b * (cf k : ℤ) + μ) : ℤ) < (prime k : ℤ))
      (prime_modEq : ∀ k, ((prime k : ℤ)) ≡ 1 [ZMOD modulusFactor * b * (b * (cf k : ℤ) + μ)])
      (modulus_succ : ∀ k, b * (cf (k + 1) : ℤ) + μ = (b * (cf k : ℤ) + μ) * (prime k))
      (mem : ∀ t : ℕ, cf t ∈ S) (mono : StrictMono cf)

/-- The kind reported, in the taxonomy of `StructuredCertificates.lean`
    (0 = polynomial progression, 1 = Pell unit orbit, 2 = moving-modulus step orbit). -/
def StructuredFamily.kind {S : Set ℕ} : StructuredFamily S → ℕ
  | .progression .. => 0
  | .quadratic .. => 0
  | .pell .. => 1
  | .movingModulus .. => 2

/-- Transport along an equality of sets — the operation every assembly layer needs. -/
def StructuredFamily.transport {S T : Set ℕ} (h : S = T) (F : StructuredFamily S) :
    StructuredFamily T := h ▸ F

/-- Soundness, proved once for all layers: a structured family makes its set infinite. -/
theorem infinite_of_structuredFamily {S : Set ℕ} (F : StructuredFamily S) : S.Infinite := by
  cases F with
  | progression c₀ s hs mem =>
      apply Set.infinite_of_not_bddAbove
      rintro ⟨M, hM⟩
      have := hM (mem (M + 1))
      nlinarith
  | quadratic α β γ hα cf out mem mono =>
      exact Set.infinite_of_injective_forall_mem mono.injective mem
  | pell D P Q unit hP X Y recX recY denom px pc hdenom cf out mem mono =>
      exact Set.infinite_of_injective_forall_mem mono.injective mem
  | movingModulus b μ f hb hf cf prime hp hmpos hpgt hpmod hsucc mem mono =>
      exact Set.infinite_of_injective_forall_mem mono.injective mem

/-- A witnessed period gives a progression family. -/
def PeriodicProgression.toStructuredFamily {S : Set ℕ} (F : PeriodicProgression S) :
    StructuredFamily S :=
  .progression F.c₀ F.T F.T_pos (fun t => by
    have := F.mem t
    rwa [Nat.mul_comm t F.T] at this)

end DiophCompression

#print axioms DiophCompression.infinite_of_structuredFamily
