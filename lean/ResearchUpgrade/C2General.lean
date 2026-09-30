/-
  C2General.lean — Gate-18 research program, Packet c2_general_reductions.
  Three deliverables (all honestly labelled):

    1. C2-2 SPLIT CASE, GENERAL (one input `x`, NO witness after factoring): the relation
       `(α₁ y + β₁ x + γ₁)·(α₂ y + β₂ x + γ₂) = 0` (`α₁ ≠ 0`, `α₂ ≠ 0`).  RelTotal ∧ RelUnique ⇒
       `FullCosetNF` of the output function, with modulus `M = |α₁ α₂|`, by the same branch-selection
       argument as `n_a_ne_zero_full`: integrality of branch `i` is constant on cosets mod `αᵢ`, so on
       a coset mod `M` at least one branch is integral throughout (totality) and uniqueness pins the
       output to that affine branch.  This generalises the `α₁ = 1`, `β₁ = β₂ = 0` sub-case of
       `C2DeltaZero.c33_split_fullCoset`.  Weak corollary included.

    2. C2-2 SPLIT CASE WITH WITNESS in one factor: `∃ u, (α y + β x + γ)·(α' y + β' x + γ' + m u) = 0`,
       `m ≠ 0`.  The second factor is killable iff `α' y + β' x + γ' ≡ 0 (mod m)`.
       (a) `split_witness_not_unique` under `IsCoprime α' m`: the fibre at `x = 0` contains a full
           residue class of `y`, so uniqueness FAILS.
       (b) Degenerate alternative `m ∣ α'`: the second factor's residue depends on `x` only.
           `split_witness_degenerate_branch`: on `x` with `m ∤ (β' x + γ')` the relation is exactly
           branch 1 (`α y + β x + γ = 0`) — the "reduce to case 1 with one branch" content.
           `split_witness_degenerate_not_unique`: on `x` with `m ∣ (β' x + γ')` every `y` is an output,
           so uniqueness fails.

    3. A3-3 PROVENANCE: `movingRaySG` is compatible with the SG-level witness reflection.
       `fiberSetSG_negSlope_ofWitness` derives the fibre-set equality `(b, μ) ↦ (−b, −μ)` from the
       baseline witness identity `movingModulus_negSlope_witnessEquiv`; `castSet_fiberSetSG_negSlope`
       transports it to the cast image; `movingRaySG_negSlope` transports the production ray
       `movingRaySG` along that equality (the `▸` transport pattern of `FixedBasePrimeRay.negSlope`).

  Baseline (mpup-lean r39) is read-only.  No sorry, no new axiom (std-3 only).
-/
import DiophCompression.SemanticQuadraticSingular.MovingModulusGeneral
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import ResearchUpgrade.C2DeltaZero
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.OneInputNoWitness
import ResearchUpgrade.Shadow.FamilyR
import ResearchUpgrade.SmallLeaves

namespace DiophCompression.ResearchUpgrade

open Matrix
open DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticSingular

/-! ## Part 1 — C2-2 split case, general (one input, no witness after factoring)

`Rsplit α₁ β₁ γ₁ α₂ β₂ γ₂ x y := (α₁ y + β₁ x + γ₁)·(α₂ y + β₂ x + γ₂) = 0`, `α₁ ≠ 0`, `α₂ ≠ 0`. -/

/-- The general split relation `(α₁ y + β₁ x + γ₁)·(α₂ y + β₂ x + γ₂) = 0`. -/
def Rsplit (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℤ) (x y : ℤ) : Prop :=
  (α₁ * y + β₁ * x + γ₁) * (α₂ * y + β₂ * x + γ₂) = 0

/-- The (choice-extracted) output function packaged for `CosetNormalForm`. -/
noncomputable def fsplitG (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℤ)
    (hT : RelTotal (Rsplit α₁ β₁ γ₁ α₂ β₂ γ₂)) : (Fin 1 → ℤ) → ℤ :=
  fun x => Classical.choose (hT (x 0))

/-- **Branch-coset assembly.** If, on the coset `ρ₀ + Mℤ`, the affine branch `α y + β x + γ = 0` is
integral throughout (guaranteed when `α ∣ M` and the branch is integral at `ρ₀`), and uniqueness
selects it (`hsel`), then the output is the degree-1 `QuadForm` `y = −(β x + γ)/α` on that coset. -/
private theorem rsplit_branch_quadform (α β γ : ℤ) (hα : α ≠ 0) (M : ℕ) (hMdvd : α ∣ (M : ℤ))
    (gfun : ℤ → ℤ)
    (hsel : ∀ x : ℤ, α ∣ (β * x + γ) → α * gfun x + (β * x + γ) = 0)
    (ρ₀ : ℤ) (hfac : α * gfun ρ₀ + (β * ρ₀ + γ) = 0) :
    ∃ q : QuadForm 1, ∀ t : Fin 1 → ℤ,
      ((gfun (ρ₀ + (M : ℤ) * t 0) : ℤ) : ℚ) = q.eval (castQ t) := by
  have hdvd0 : α ∣ (β * ρ₀ + γ) := ⟨-(gfun ρ₀), by linear_combination hfac⟩
  have hval : ∀ t₀ : ℤ,
      α * gfun (ρ₀ + (M : ℤ) * t₀) = -(β * ρ₀ + γ) - β * ((M : ℤ) * t₀) := by
    intro t₀
    have hdvd : α ∣ (β * (ρ₀ + (M : ℤ) * t₀) + γ) := by
      have he : β * (ρ₀ + (M : ℤ) * t₀) + γ = (β * ρ₀ + γ) + β * ((M : ℤ) * t₀) := by ring
      rw [he]
      exact dvd_add hdvd0 ((hMdvd.mul_right t₀).mul_left β)
    have hs := hsel (ρ₀ + (M : ℤ) * t₀) hdvd
    linear_combination hs
  have hαQ : ((α : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hα
  refine ⟨⟨((-(β * ρ₀ + γ) : ℤ) : ℚ) / ((α : ℤ) : ℚ),
           fun _ => ((-(β * (M : ℤ)) : ℤ) : ℚ) / ((α : ℤ) : ℚ), fun _ _ => 0⟩, fun t => ?_⟩
  have hgQ : ((α : ℤ) : ℚ) * ((gfun (ρ₀ + (M : ℤ) * t 0) : ℤ) : ℚ)
      = ((-(β * ρ₀ + γ) - β * ((M : ℤ) * t 0) : ℤ) : ℚ) := by
    exact_mod_cast hval (t 0)
  simp only [QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
  push_cast at hgQ ⊢
  field_simp
  linear_combination hgQ

/-- **Main split deliverable (general).** A total, unique general split family lands in the
full-residue coset normal form, modulus `M = |α₁ α₂|`. -/
theorem rsplit_fullCoset (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℤ) (hα₁ : α₁ ≠ 0) (hα₂ : α₂ ≠ 0)
    (hT : RelTotal (Rsplit α₁ β₁ γ₁ α₂ β₂ γ₂))
    (hU : RelUnique (Rsplit α₁ β₁ γ₁ α₂ β₂ γ₂)) :
    FullCosetNF (fsplitG α₁ β₁ γ₁ α₂ β₂ γ₂ hT) := by
  set gfun : ℤ → ℤ := fun n => Classical.choose (hT n) with hgfun
  have hf : ∀ x : Fin 1 → ℤ, fsplitG α₁ β₁ γ₁ α₂ β₂ γ₂ hT x = gfun (x 0) := fun _ => rfl
  have hspec : ∀ n : ℤ,
      (α₁ * gfun n + β₁ * n + γ₁) * (α₂ * gfun n + β₂ * n + γ₂) = 0 := by
    intro n; have h := Classical.choose_spec (hT n); simpa [Rsplit, hgfun] using h
  -- Uniqueness selects branch 1 wherever it is integral.
  have hsel1 : ∀ x : ℤ, α₁ ∣ (β₁ * x + γ₁) → α₁ * gfun x + (β₁ * x + γ₁) = 0 := by
    intro x hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hRk : Rsplit α₁ β₁ γ₁ α₂ β₂ γ₂ x (-k) := by
      show (α₁ * (-k) + β₁ * x + γ₁) * (α₂ * (-k) + β₂ * x + γ₂) = 0
      have hz : α₁ * (-k) + β₁ * x + γ₁ = 0 := by linear_combination hk
      rw [hz, zero_mul]
    have hout : Rsplit α₁ β₁ γ₁ α₂ β₂ γ₂ x (gfun x) := by
      have := Classical.choose_spec (hT x); simpa [hgfun] using this
    have hgx := hU x (gfun x) (-k) hout hRk
    rw [hgx]; linear_combination hk
  have hsel2 : ∀ x : ℤ, α₂ ∣ (β₂ * x + γ₂) → α₂ * gfun x + (β₂ * x + γ₂) = 0 := by
    intro x hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hRk : Rsplit α₁ β₁ γ₁ α₂ β₂ γ₂ x (-k) := by
      show (α₁ * (-k) + β₁ * x + γ₁) * (α₂ * (-k) + β₂ * x + γ₂) = 0
      have hz : α₂ * (-k) + β₂ * x + γ₂ = 0 := by linear_combination hk
      rw [hz, mul_zero]
    have hout : Rsplit α₁ β₁ γ₁ α₂ β₂ γ₂ x (gfun x) := by
      have := Classical.choose_spec (hT x); simpa [hgfun] using this
    have hgx := hU x (gfun x) (-k) hout hRk
    rw [hgx]; linear_combination hk
  -- The modulus `M = |α₁ α₂|` is divisible by both `α₁` and `α₂`.
  set M : ℕ := (α₁ * α₂).natAbs with hMdef
  have hMdvd1 : α₁ ∣ (M : ℤ) := by rw [hMdef]; exact Int.dvd_natAbs.mpr (dvd_mul_right α₁ α₂)
  have hMdvd2 : α₂ ∣ (M : ℤ) := by rw [hMdef]; exact Int.dvd_natAbs.mpr (dvd_mul_left α₂ α₁)
  refine ⟨M, ?_, fun ρ => ?_⟩
  · have hne : M ≠ 0 := by rw [hMdef]; exact Int.natAbs_ne_zero.mpr (mul_ne_zero hα₁ hα₂)
    omega
  · set ρ₀ : ℤ := ρ 0 with hρ0
    have hcoord : ∀ t : Fin 1 → ℤ, (ρ + (M : ℤ) • t) 0 = ρ₀ + (M : ℤ) * t 0 := by
      intro t; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hρ0]
    rcases mul_eq_zero.1 (hspec ρ₀) with hf1 | hf2
    · obtain ⟨q, hq⟩ :=
        rsplit_branch_quadform α₁ β₁ γ₁ hα₁ M hMdvd1 gfun hsel1 ρ₀ (by linear_combination hf1)
      refine ⟨q, fun t => ?_⟩
      rw [hf, hcoord t]; exact hq t
    · obtain ⟨q, hq⟩ :=
        rsplit_branch_quadform α₂ β₂ γ₂ hα₂ M hMdvd2 gfun hsel2 ρ₀ (by linear_combination hf2)
      refine ⟨q, fun t => ?_⟩
      rw [hf, hcoord t]; exact hq t

/-- **Main split deliverable (weak form).** Corollary of the full-residue form. -/
theorem rsplit_weak (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℤ) (hα₁ : α₁ ≠ 0) (hα₂ : α₂ ≠ 0)
    (hT : RelTotal (Rsplit α₁ β₁ γ₁ α₂ β₂ γ₂))
    (hU : RelUnique (Rsplit α₁ β₁ γ₁ α₂ β₂ γ₂)) :
    WeakScalarCosetNF (fsplitG α₁ β₁ γ₁ α₂ β₂ γ₂ hT) :=
  WeakScalarCosetNF.of_full (rsplit_fullCoset α₁ β₁ γ₁ α₂ β₂ γ₂ hα₁ hα₂ hT hU)

/-- Sanity control: the `α₁ = 1`, `β₁ = β₂ = 0` case of `Rsplit` is `C2DeltaZero.Psplit`. -/
example (a2 p1 q1 p2 q2 x y : ℤ) :
    Rsplit 1 p1 q1 a2 p2 q2 x y ↔ Psplit a2 p1 q1 p2 q2 x y := by
  simp only [Rsplit, Psplit]
  constructor <;> intro h <;> linear_combination h

/-! ## Part 2 — C2-2 split case with a witness in one factor

`Rwit α β γ α' β' γ' m x y := ∃ u, (α y + β x + γ)·(α' y + β' x + γ' + m u) = 0`, `m ≠ 0`. -/

/-- The split relation with a linearly-appearing witness `u` (coefficient `m`) in the second factor. -/
def Rwit (α β γ α' β' γ' m : ℤ) (x y : ℤ) : Prop :=
  ∃ u : ℤ, (α * y + β * x + γ) * (α' * y + β' * x + γ' + m * u) = 0

/-- The second factor can be killed at `(x, y)` iff `m ∣ (α' y + β' x + γ')`; the membership half. -/
theorem Rwit_of_dvd (α β γ α' β' γ' m : ℤ) (x y : ℤ) (h : m ∣ (α' * y + β' * x + γ')) :
    Rwit α β γ α' β' γ' m x y := by
  obtain ⟨w, hw⟩ := h
  refine ⟨-w, ?_⟩
  have h2 : α' * y + β' * x + γ' + m * (-w) = 0 := by rw [hw]; ring
  rw [h2, mul_zero]

/-- **Witness split, coprime case — uniqueness FAILS.** With `m ≠ 0` and `IsCoprime α' m`, the fibre
at `x = 0` contains the full residue class `{ y : α' y + γ' ≡ 0 (mod m) }`, in particular the two
distinct outputs `y₀` and `y₀ + m`. -/
theorem split_witness_not_unique (α β γ α' β' γ' m : ℤ) (hm : m ≠ 0) (hcop : IsCoprime α' m) :
    ¬ RelUnique (Rwit α β γ α' β' γ' m) := by
  intro hU
  obtain ⟨a, b, hab⟩ := hcop
  set y₀ : ℤ := -(a * γ') with hy0
  have hd0 : m ∣ (α' * y₀ + β' * 0 + γ') := by
    refine ⟨γ' * b, ?_⟩
    simp only [hy0, mul_zero, add_zero]
    linear_combination (-γ') * hab
  have hd1 : m ∣ (α' * (y₀ + m) + β' * 0 + γ') := by
    obtain ⟨w, hw⟩ := hd0
    exact ⟨w + α', by linear_combination hw⟩
  have r0 := Rwit_of_dvd α β γ α' β' γ' m 0 y₀ hd0
  have r1 := Rwit_of_dvd α β γ α' β' γ' m 0 (y₀ + m) hd1
  have heq : y₀ = y₀ + m := hU 0 y₀ (y₀ + m) r0 r1
  exact hm (by linarith)

/-- **Witness split, degenerate `m ∣ α'` — reduction to a single branch.** When `m ∣ α'`, the second
factor's residue mod `m` depends on `x` only.  On the inputs `x` where `m ∤ (β' x + γ')` the second
factor can never vanish, so the relation is exactly branch 1 `α y + β x + γ = 0` (case 1 with ONE
branch). -/
theorem split_witness_degenerate_branch (α β γ α' β' γ' m : ℤ) (hdvd : m ∣ α')
    (x : ℤ) (hx : ¬ m ∣ (β' * x + γ')) (y : ℤ) :
    Rwit α β γ α' β' γ' m x y ↔ α * y + β * x + γ = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    rcases mul_eq_zero.1 hu with h | h
    · exact h
    · exfalso; apply hx
      obtain ⟨α'', hα''⟩ := hdvd
      exact ⟨-(α'' * y) - u, by rw [hα''] at h; linear_combination h⟩
  · intro h; exact ⟨0, by rw [h]; ring⟩

/-- **Witness split, degenerate `m ∣ α'` — uniqueness fails on the killable inputs.** On the inputs
`x` where `m ∣ (β' x + γ')` the second factor can be killed for EVERY `y`, so every `y` is an output
and uniqueness fails. -/
theorem split_witness_degenerate_not_unique (α β γ α' β' γ' m : ℤ) (hdvd : m ∣ α')
    (x : ℤ) (hx : m ∣ (β' * x + γ')) :
    ¬ RelUnique (Rwit α β γ α' β' γ' m) := by
  intro hU
  have hmem : ∀ y : ℤ, Rwit α β γ α' β' γ' m x y := by
    intro y
    obtain ⟨α'', hα''⟩ := hdvd
    obtain ⟨w, hw⟩ := hx
    refine ⟨-(α'' * y) - w, ?_⟩
    have h2 : α' * y + β' * x + γ' + m * (-(α'' * y) - w) = 0 := by
      rw [hα'']; linear_combination hw
    rw [h2, mul_zero]
  exact absurd (hU x 0 1 (hmem 0) (hmem 1)) (by norm_num)

/-! ## Part 3 — A3-3 provenance: `movingRaySG` and the SG-level witness reflection

The baseline witness identity `movingModulus_negSlope_witnessEquiv` states that `fqSG` is invariant
under `(b, μ, w) ↦ (−b, −μ, −w)`.  We read off the fibre-set equality `(b, μ) ↦ (−b, −μ)` directly
from it, transport it to the cast image, and transport the production ray `movingRaySG` along it
(the `▸` transport pattern of `SmallLeaves.FixedBasePrimeRay.negSlope`). -/

/-- A3-3 provenance (fibre set).  The SG fibre set is unchanged by `(b, μ) ↦ (−b, −μ)`, proved
directly from the baseline witness identity `movingModulus_negSlope_witnessEquiv` (this matches the
baseline's own `fiberSetSG_negSlope`). -/
theorem fiberSetSG_negSlope_ofWitness {k : ℕ} (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) :
    fiberSetSG A B C b l m μ q = fiberSetSG A B C (-b) l m (-μ) q := by
  ext c
  simp only [fiberSetSG, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, w, hw⟩
    exact ⟨u, -w, by
      rw [← movingModulus_negSlope_witnessEquiv A B C b l m μ q (c : ℤ) u w]; exact hw⟩
  · rintro ⟨u, w, hw⟩
    refine ⟨u, -w, ?_⟩
    have hid := movingModulus_negSlope_witnessEquiv A B C (-b) l m (-μ) q (c : ℤ) u w
    rw [neg_neg, neg_neg] at hid
    rw [← hid]; exact hw

/-- A3-3 provenance (cast image).  The cast image of the SG fibre set is unchanged by
`(b, μ) ↦ (−b, −μ)`. -/
theorem castSet_fiberSetSG_negSlope {k : ℕ} (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) :
    castSet (fiberSetSG A B C b l m μ q) = castSet (fiberSetSG A B C (-b) l m (-μ) q) :=
  congrArg castSet (fiberSetSG_negSlope_ofWitness A B C b l m μ q)

/-- **A3-3 provenance (ray transport).**  The production ray `movingRaySG` built for `(b, μ)` is,
by the SG-level witness reflection, a ray into the fibre set of the sign-flipped instance
`(−b, −μ)` — transported along `castSet_fiberSetSG_negSlope` (the `▸` pattern of
`FixedBasePrimeRay.negSlope`). -/
noncomputable def movingRaySG_negSlope {k : ℕ} (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (hb : 0 < b)
    (hN : (C + Cᵀ).det ≠ 0) (c₀ : ℕ) (u₀ : Fin k → ℤ)
    (hdiv : (b * (c₀ : ℤ) + μ) ∣ fqM A B C l m q (c₀ : ℤ) u₀) (hpos : 0 < b * (c₀ : ℤ) + μ) :
    FixedBasePrimeRay (castSet (fiberSetSG A B C (-b) l m (-μ) q)) :=
  castSet_fiberSetSG_negSlope A B C b l m μ q ▸
    movingRaySG hk A B C b l m μ q hb hN c₀ u₀ hdiv hpos

end DiophCompression.ResearchUpgrade
