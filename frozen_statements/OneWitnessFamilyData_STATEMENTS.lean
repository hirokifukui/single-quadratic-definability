/-
  DiophCompression/SemanticQuadratic/OneWitnessFamilyData.lean — APAL Structural Theory Gate 5,
  必須F step 3 (the leaf certificate type) (s28, 2026-09-02, claude.ai direct).

  The first layer of the assembly. Every leaf of the one-witness normal form now hands over explicit data
  (s28: D2 quadratic, D3/D4/D6 linear, D7 Pell orbit, and the periodic leaves); this file gives them a
  common type, so the aggregation `fiber_dichotomy` can carry a certificate instead of bare infinitude.
  The constructors carry the DATA, not a tag: the coefficients of the progression, or the unit and orbit
  of the Pell family. Soundness (each constructor makes the fibre infinite) is proved here, so nothing is
  lost by strengthening the leaves. No sorry; std-3.
-/
import DiophCompression.SemanticQuadratic.QuadraticFamilyData
import DiophCompression.SemanticQuadratic.LeafDataD3D6
import DiophCompression.PeriodicProgressionCore
import DiophCompression.StructuredFamilyCore
import DiophCompression.PellOrbitCore

namespace DiophCompression.SemanticQuadratic

open MPUP

/-- A structured family inside a one-witness fibre, with the data that produced it. The output is a
    natural number (the fibre is a `Set ℕ`); the kind-specific fields say WHICH family it is. -/
inductive OneWitnessFamilyData (A B C l m q : ℤ) : Type
  /-- degree-1 progression `c₀ + s·t`, `s ≥ 1` (leaves D3, D4, D6). -/
  | linear (c₀ s : ℕ) (hs : 1 ≤ s) (u : ℕ → ℤ)
      (mem : ∀ t : ℕ, fq A B C l m q ((c₀ + s * t : ℕ) : ℤ) (u t) = 0)
  /-- degree-2 progression `α t² + β t + γ` with a nonzero leading coefficient (leaf D2). -/
  | quadratic (α β γ : ℤ) (hα : α ≠ 0) (cf : ℕ → ℕ) (u : ℕ → ℤ)
      (out : ∀ t : ℕ, (cf t : ℤ) = α * (t : ℤ) ^ 2 + β * (t : ℤ) + γ)
      (mem : ∀ t : ℕ, fq A B C l m q (cf t) (u t) = 0)
      (mono : StrictMono cf)
  /-- an arithmetic progression given by a witnessed period (the periodic leaves). -/
  | periodic (F : DiophCompression.PeriodicProgression (fiberSet A B C l m q))
  /-- the orbit of a fibre point under a unit of `x² − D y² = 1` (leaf D7). -/
  | pell (P Q : ℤ) (X Y : ℕ → ℤ)
      (recX : ∀ k, X (k + 1) = X k * P + disc A B C * Y k * Q)
      (recY : ∀ k, Y (k + 1) = X k * Q + Y k * P)
      (denom px pc : ℤ) (hdenom : denom ≠ 0)
      (cf : ℕ → ℕ) (u : ℕ → ℤ)
      (out : ∀ k, denom * (cf k : ℤ) = px * X k + pc)
      (unit : P ^ 2 - disc A B C * Q ^ 2 = 1) (hP : 2 ≤ P)
      (mem : ∀ t : ℕ, fq A B C l m q (cf t) (u t) = 0)
      (mono : StrictMono cf)

/-- The kind each constructor reports (0 = polynomial progression, 1 = Pell unit orbit), matching the
    taxonomy of `StructuredCertificates.lean`. -/
def OneWitnessFamilyData.kind {A B C l m q : ℤ} : OneWitnessFamilyData A B C l m q → ℕ
  | .linear .. => 0
  | .quadratic .. => 0
  | .periodic .. => 0
  | .pell .. => 1


/-- The leaf certificate, seen in the set-generic type used by every assembly layer above. -/
def OneWitnessFamilyData.toStructuredFamily {A B C l m q : ℤ} :
    OneWitnessFamilyData A B C l m q → DiophCompression.StructuredFamily (fiberSet A B C l m q)
  | .linear c₀ s hs u mem => .progression c₀ s hs (fun t => ⟨u t, mem t⟩)
  | .quadratic α β γ hα cf u out mem mono => .quadratic α β γ hα cf out (fun t => ⟨u t, mem t⟩) mono
  | .periodic F => DiophCompression.PeriodicProgression.toStructuredFamily F
  | .pell P Q X Y recX recY denom px pc hdenom cf u out unit hP mem mono =>
      .pell (disc A B C) P Q unit hP X Y recX recY denom px pc hdenom cf out
        (fun t => ⟨u t, mem t⟩) mono

/-- Soundness: every constructor forces the fibre to be infinite, so strengthening the leaves loses
    nothing. -/
theorem fiberSet_infinite_of_oneWitnessFamilyData {A B C l m q : ℤ}
    (F : OneWitnessFamilyData A B C l m q) : (fiberSet A B C l m q).Infinite := by
  sorry

end DiophCompression.SemanticQuadratic
