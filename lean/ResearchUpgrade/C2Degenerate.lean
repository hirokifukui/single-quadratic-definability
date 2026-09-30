/-
  C2Degenerate.lean — Gate-18 research program, Packet c2_degenerate_assembly.
  The last C2-2 leaf: the GLOBAL assembly of the degenerate witness-in-a-factor case
  (`m ∣ α'`), left open as REMAINING_LEAF in `reports/c2g_REPORT.md` (Part 2b).

  Setting (from `C2General.Rwit`):
    `Rwit α β γ α' β' γ' m x y := ∃ u, (α y + β x + γ)·(α' y + β' x + γ' + m u) = 0`,
  with `m ≠ 0` and `m ∣ α'`.  Because `m ∣ α'`, the second factor `α' y + β' x + γ' + m u`
  is killable (for some `u`) iff `m ∣ (α' y + β' x + γ')` iff `m ∣ (β' x + γ')` — a condition
  on `x` ALONE (independent of `y`).  This is exactly the dichotomy already recorded locally by
  `split_witness_degenerate_branch` (no-kill ⇒ single affine branch) and
  `split_witness_degenerate_not_unique` (kill ⇒ every `y` an output ⇒ non-unique).

  Global assembly proved here:
    * `rwit_degenerate_no_bad_x` : under `RelUnique`, NO input `x` can have `m ∣ (β' x + γ')`
      (such an `x` would make every `y` an output, killing uniqueness).  Consequences:
      `rwit_degenerate_m_not_dvd_gamma'` (`m ∤ γ'`, the `x = 0` instance) and
      `rwit_degenerate_gcd_not_dvd` (if `β' ≠ 0` the progression `β' x + γ'` avoids `0 (mod m)`,
      possible only when `gcd(β', m) ∤ γ'`).
    * On every `x` the relation is then EXACTLY the first factor `α y + β x + γ = 0`
      (`split_witness_degenerate_branch`), a single affine branch of rational slope `−β/α`,
      integral for all `x` by totality; so the output function is a single global degree-1
      polynomial (`rwit_degenerate_global : GlobalQuadratic …`) and hence
      `rwit_degenerate_fullCoset : FullCosetNF …` via `globalQuadratic_imp_fullCoset`
      (`NInputNoWitness.lean`), the `M = 1` witness.

  Totality CAN hold in this regime (e.g. `α = 1`), so the honest statement is the positive
  `FullCosetNF`, not an impossibility; the control `β' = 0, m ∤ γ'` (e.g. `m = 2, γ' = 1,
  α' = 2`) exhibits `Rwit` collapsing to `α y + β x + γ = 0`.

  Baseline (mpup-lean r39) is read-only.  No sorry, no new axiom (std-3 only).
-/
import Mathlib.Tactic.Ring.RingNF
import ResearchUpgrade.C2General
import ResearchUpgrade.NInputNoWitness

namespace DiophCompression.ResearchUpgrade

open Matrix

/-! ## The degenerate witness case `m ∣ α'` — global assembly

Throughout, `Rwit α β γ α' β' γ' m` is the C2General witness-split relation and `m ∣ α'`,
so the second factor's residue mod `m` is `β' x + γ'`, depending on `x` only. -/

/-- **No bad input.** Under `RelUnique`, no input `x` can satisfy `m ∣ (β' x + γ')`: such an `x`
would make the second factor killable for EVERY `y` (so every `y` is an output), contradicting
uniqueness (`split_witness_degenerate_not_unique`).  Hence a total-unique degenerate family lives
entirely on the single-branch regime `m ∤ (β' x + γ')`. -/
theorem rwit_degenerate_no_bad_x (α β γ α' β' γ' m : ℤ) (hdvd : m ∣ α')
    (hU : RelUnique (Rwit α β γ α' β' γ' m)) :
    ∀ x : ℤ, ¬ m ∣ (β' * x + γ') := by
  intro x hx
  exact split_witness_degenerate_not_unique α β γ α' β' γ' m hdvd x hx hU

/-- Consequence of `rwit_degenerate_no_bad_x` at `x = 0`: `m ∤ γ'`. -/
theorem rwit_degenerate_m_not_dvd_gamma' (α β γ α' β' γ' m : ℤ) (hdvd : m ∣ α')
    (hU : RelUnique (Rwit α β γ α' β' γ' m)) : ¬ m ∣ γ' := by
  have h := rwit_degenerate_no_bad_x α β γ α' β' γ' m hdvd hU 0
  simpa using h

/-- Consequence: the arithmetic progression `β' x + γ'` avoids `0 (mod m)` for all `x` — possible
only when `gcd(β', m) ∤ γ'`.  (If `gcd(β', m) ∣ γ'` the linear congruence `β' x ≡ −γ' (mod m)` is
solvable by Bézout, producing a bad `x`.)  This subsumes `m ∤ γ'` (the `β' = 0` case, where the
gcd is `|m|`). -/
theorem rwit_degenerate_gcd_not_dvd (α β γ α' β' γ' m : ℤ) (hdvd : m ∣ α')
    (hU : RelUnique (Rwit α β γ α' β' γ' m)) :
    ¬ ((Int.gcd β' m : ℤ) ∣ γ') := by
  intro hg
  obtain ⟨k, hk⟩ := hg
  have hbez := Int.gcd_eq_gcd_ab β' m
  set a := Int.gcdA β' m with ha
  set b := Int.gcdB β' m with hb
  have hbad : m ∣ (β' * (-a * k) + γ') := by
    refine ⟨b * k, ?_⟩
    rw [hk, hbez]; ring
  exact rwit_degenerate_no_bad_x α β γ α' β' γ' m hdvd hU (-a * k) hbad

/-- The (choice-extracted) output function packaged for `CosetNormalForm`. -/
noncomputable def fwitG (α β γ α' β' γ' m : ℤ)
    (hT : RelTotal (Rwit α β γ α' β' γ' m)) : (Fin 1 → ℤ) → ℤ :=
  fun x => Classical.choose (hT (x 0))

/-- **Global degree-1 form.** With `m ∣ α'`, `α ≠ 0`, and the family total & unique, every input
falls in the single-branch regime (`rwit_degenerate_no_bad_x`), so the relation is exactly
`α y + β x + γ = 0` (`split_witness_degenerate_branch`); the output function is therefore the single
affine (degree-1) polynomial `y = −(β x + γ)/α` on all of ℤ. -/
theorem rwit_degenerate_global (α β γ α' β' γ' m : ℤ) (hdvd : m ∣ α') (hα : α ≠ 0)
    (hT : RelTotal (Rwit α β γ α' β' γ' m))
    (hU : RelUnique (Rwit α β γ α' β' γ' m)) :
    GlobalQuadratic (fwitG α β γ α' β' γ' m hT) := by
  set gfun : ℤ → ℤ := fun n => Classical.choose (hT n) with hgfun
  have hf : ∀ x : Fin 1 → ℤ, fwitG α β γ α' β' γ' m hT x = gfun (x 0) := fun _ => rfl
  have hnobad := rwit_degenerate_no_bad_x α β γ α' β' γ' m hdvd hU
  -- On every input the relation is the lone affine branch, so its output satisfies it.
  have hbranch : ∀ n : ℤ, α * gfun n + β * n + γ = 0 := by
    intro n
    have hmem : Rwit α β γ α' β' γ' m n (gfun n) := by
      have := Classical.choose_spec (hT n); simpa [hgfun] using this
    exact (split_witness_degenerate_branch α β γ α' β' γ' m hdvd n (hnobad n) (gfun n)).1 hmem
  have hαQ : ((α : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hα
  refine ⟨⟨((-γ : ℤ) : ℚ) / ((α : ℤ) : ℚ), fun _ => ((-β : ℤ) : ℚ) / ((α : ℤ) : ℚ),
           fun _ _ => 0⟩, fun x => ?_⟩
  have hgQ : ((α : ℤ) : ℚ) * ((gfun (x 0) : ℤ) : ℚ) = ((-(β * x 0 + γ) : ℤ) : ℚ) := by
    have hz : α * gfun (x 0) = -(β * x 0 + γ) := by linear_combination hbranch (x 0)
    exact_mod_cast hz
  rw [hf]
  simp only [QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
  push_cast at hgQ ⊢
  field_simp
  linear_combination hgQ

/-- **Main degenerate-assembly deliverable.** A total, unique degenerate witness-split family
(`m ∣ α'`, `α ≠ 0`) lands in the full-residue coset normal form (`M = 1`).  This closes the
REMAINING_LEAF of `reports/c2g_REPORT.md` (Part 2b): via `rwit_degenerate_no_bad_x` the whole family
is the lone affine branch `α y + β x + γ = 0`, a single global degree-1 polynomial, and
`globalQuadratic_imp_fullCoset` lifts that to `FullCosetNF`. -/
theorem rwit_degenerate_fullCoset (α β γ α' β' γ' m : ℤ) (hm : m ≠ 0) (hdvd : m ∣ α') (hα : α ≠ 0)
    (hT : RelTotal (Rwit α β γ α' β' γ' m))
    (hU : RelUnique (Rwit α β γ α' β' γ' m)) :
    FullCosetNF (fwitG α β γ α' β' γ' m hT) :=
  globalQuadratic_imp_fullCoset (rwit_degenerate_global α β γ α' β' γ' m hdvd hα hT hU)

/-- **Main degenerate-assembly deliverable (weak form).** Corollary of the full-residue form. -/
theorem rwit_degenerate_weak (α β γ α' β' γ' m : ℤ) (hm : m ≠ 0) (hdvd : m ∣ α') (hα : α ≠ 0)
    (hT : RelTotal (Rwit α β γ α' β' γ' m))
    (hU : RelUnique (Rwit α β γ α' β' γ' m)) :
    WeakScalarCosetNF (fwitG α β γ α' β' γ' m hT) :=
  WeakScalarCosetNF.of_full (rwit_degenerate_fullCoset α β γ α' β' γ' m hm hdvd hα hT hU)

/-! ## Control: `β' = 0`, `m ∤ γ'`

With `β' = 0` the killability condition `m ∣ (β' x + γ')` is `m ∣ γ'` — independent of `x`.  When
`m ∤ γ'` (concretely `m = 2, γ' = 1, α' = 2`), the second factor never vanishes and `Rwit` reduces
to the lone affine branch `α y + β x + γ = 0` for every `x`, exactly as the assembly requires. -/

example (α β γ x y : ℤ) :
    Rwit α β γ 2 0 1 2 x y ↔ α * y + β * x + γ = 0 := by
  have hdvd : (2 : ℤ) ∣ 2 := ⟨1, by ring⟩
  have hx : ¬ (2 : ℤ) ∣ (0 * x + 1) := by norm_num
  exact split_witness_degenerate_branch α β γ 2 0 1 2 hdvd x hx y

end DiophCompression.ResearchUpgrade
