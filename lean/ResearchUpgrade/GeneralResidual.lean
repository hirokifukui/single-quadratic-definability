/-
  GeneralResidual.lean — Gate-20 Packet G3, task G3.2.

  The reviewer asks for the PRECISE UNPROVED PROPOSITIONS of the reduction to general `n` and `r`,
  not for a proof.  This file writes them as Lean `def`s — open statements in the sense of
  METHODOLOGY §5 (a predicate definition, proved neither way) — so that the residual is machine
  readable and cannot drift in prose.  Nothing here is claimed to be true; the only THEOREM in the
  file is the one direction that is free.

  Reviewer regression controls that bite here:
    #17 — one ray is not a full lattice coset;
    #2  — unique output gives neither unique witness nor finiteness;
    #18 — a conditional result never moves to an unconditional root name.

  What the s46 chain established, and how far each piece reaches (discussion in
  `docs/G32_RESIDUAL_s46.md`):

  * N1.1b, N2.1, N2.2, N2.3 are statements about a ONE-VARIABLE polynomial and a binary form.
    They do not see `n` at all and carry over verbatim.
  * The complete-square compiler (N3.1) uses only that the `(y,u)` quadratic part is
    input-independent, which at totalDegree ≤ 2 holds for every `n`.  It generalises.
  * What does NOT come for free is the last step: from an affine section on ONE LINE to a normal
    form on ONE FULL LATTICE COSET.  That is `LineToCoset` below, and it is the crux.

  Claim tags: the `def`s are [OPEN]; `lineRestrict_of_weakCosetNF` is [P] (std-3).
  Baseline read-only.
-/
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Init
import ResearchUpgrade.CosetNormalForm

namespace DiophCompression.ResearchUpgrade

open Matrix

/-! ## The free direction: a coset normal form restricts to every line -/

/-- If `f` has a weak scalar coset normal form, then along every integer direction `v` the
restriction to that coset is a degree-≤2 polynomial in the line parameter.  This is the direction
that costs nothing, and it is the one that must NOT be confused with its converse. -/
theorem lineRestrict_of_weakCosetNF {n : ℕ} {f : (Fin n → ℤ) → ℤ}
    (h : WeakScalarCosetNF f) (v : Fin n → ℤ) :
    ∃ (M : ℕ) (ρ : Fin n → ℤ) (c₂ c₁ c₀ : ℚ), 1 ≤ M ∧
      ∀ s : ℤ, (f (ρ + (M : ℤ) • (s • v)) : ℚ)
        = c₂ * (s : ℚ) ^ 2 + c₁ * (s : ℚ) + c₀ := by
  obtain ⟨M, ρ, q, hM, hq⟩ := h
  refine ⟨M, ρ, (fun w : Fin n → ℚ => w ⬝ᵥ (q.Q *ᵥ w)) (castQ v),
    q.l ⬝ᵥ castQ v, q.c, hM, fun s => ?_⟩
  rw [hq (s • v)]
  have hcast : castQ (s • v) = (s : ℚ) • castQ v := by
    funext i; simp [castQ, Pi.smul_apply]
  simp only [QuadForm.eval, hcast, dotProduct_smul, smul_dotProduct, Matrix.mulVec_smul,
    smul_eq_mul]
  ring

/-! ## The residual statements (OPEN — definitions only, proved neither way) -/

/-- `f` is AFFINE along every integer line, on some arithmetic progression of that line.  This is
what the `n = 1, r = 1` positive-definite chain delivers, line by line: the modulus `M` and the
coefficients are allowed to depend on the line. -/
def LineAffine {n : ℕ} (f : (Fin n → ℤ) → ℤ) : Prop :=
  ∀ ρ v : Fin n → ℤ, ∃ (M : ℕ) (c₁ c₀ : ℚ), 1 ≤ M ∧
    ∀ s : ℤ, (f (ρ + ((M : ℤ) * s) • v) : ℚ) = c₁ * (s : ℚ) + c₀

/-- The same with the line modulus UNIFORM in the direction `v` and the base point `ρ`. -/
def LineAffineUniform {n : ℕ} (f : (Fin n → ℤ) → ℤ) : Prop :=
  ∃ M : ℕ, 1 ≤ M ∧ ∀ ρ v : Fin n → ℤ, ∃ c₁ c₀ : ℚ,
    ∀ s : ℤ, (f (ρ + ((M : ℤ) * s) • v) : ℚ) = c₁ * (s : ℚ) + c₀

/-- **R1 (the crux, OPEN).**  Does line-wise affineness on arithmetic progressions give a normal
form on ONE FULL LATTICE COSET?  Regression control #17 is exactly the prohibition on assuming
this.  The suspect mechanism is that the line modulus in `LineAffine` may be unbounded as the
direction varies, in which case no single `M` can exist. -/
def LineToCoset : Prop :=
  ∀ (n : ℕ) (f : (Fin n → ℤ) → ℤ), LineAffine f → WeakScalarCosetNF f

/-- **R2 — NO LONGER OPEN (s47, Gate-20 task T28): PROVED as `lineToCosetUniform_holds` in
`ResearchUpgrade/LineToCosetUniform.lean`, std-3, no open hypothesis.**  With the uniformity
hypothesis the Jensen identity on the lattice forces additivity, hence ℤ-linearity, hence an
affine normal form on the coset.  The residual therefore moves, exactly as anticipated, to
proving `LineAffineUniform` for the fibres of a quadratic — a bound on the line moduli that is
uniform in the direction.  R1 (`LineToCoset`) remains OPEN and is NOT implied by this. -/
def LineToCosetUniform : Prop :=
  ∀ (n : ℕ) (f : (Fin n → ℤ) → ℤ), LineAffineUniform f → WeakScalarCosetNF f

/-!
**R3 — NOT YET A STATEMENT (deliberately not given a `def`), and a defect caught in this file.**

The intended residual is: *the output of a total, unique-output, positive-definite relation in `n`
variables is `LineAffine`.*  Restricting the relation to an integer line is free (at
totalDegree ≤ 2 the `(y,u)` quadratic part is input-independent, so positive definiteness is
inherited), and `rgen_weakCosetNF_definite` then applies on each line.  What is open is whether the
per-line data assembles into `LineAffine` of the GLOBAL output — in the s46 chain the modulus comes
from the DENOMINATORS of the affine section, which depend on the line.

It is not written as a `def` because the vocabulary for an `n`-input, `r`-witness relation does not
exist in this package yet (`Rgen` is one-input, one-witness), so any `def` written now would be
about the wrong object.  The first draft of this file DID write one, as

    ∀ n f, (∀ ρ v, ∃ M c₁ c₀, 1 ≤ M ∧ ∀ s, f(ρ + (M*s)•v) = c₁ s + c₀) → LineAffine f

whose hypothesis is literally the unfolding of `LineAffine`, i.e. `A → A` — trivially true.  A
residual that can be discharged by `fun _ h => h` is worse than no residual.  Recorded here rather
than silently deleted: two such vacuous placeholders (this one and R5) were written and removed in
the same session, which is why the shape of a residual must be checked, not just its prose.
-/

/-- **R4 — REFUTED (s47, Gate-20 task T03a): `not_multiWitnessInertObstruction` in
`ResearchUpgrade/RefutedResiduals.lean` proves this statement FALSE**, by the reviewer's
counterexample `r = 2, D₁ = D₂ = 1, p = 3, N = 3, x = z₁ = z₂ = 1`.  The `def` is kept so that
the refutation has a subject; it must not be used as a hypothesis anywhere.  The mathematics
behind the failure: the inert-prime argument is about a NORM form of a quadratic field, and
`x² + z₁² + z₂²` is not one — `3` has `v₃ = 1` and is still represented.  (The binary case
survives: `3` is not a sum of two rational squares.)  The witness direction, `r > 1`.  The `(y, u₁, …, u_r)` quadratic part is a form
in `r + 1` variables; positive definiteness still gives a rational diagonalisation, but the
diagonalised form is `v₀² + D₁v₁² + … + D_r v_r²`, not a binary `x² + D y²`, and N2.1/N2.2 are
statements about the BINARY form.  What is open is whether the multi-variable norm form admits the
same inert-prime obstruction.  Control #2: a relation may have infinitely many witnesses at one
output, so no finiteness may be assumed on the witness side. -/
def MultiWitnessInertObstruction : Prop :=
  ∀ (r : ℕ) (D : Fin r → ℤ), (∀ i, 0 < D i) →
    ∀ (p : ℕ), p.Prime → (∀ i, ¬ IsSquare (-((D i : ℤ) : ZMod p))) →
      ∀ N : ℤ, (p : ℤ) ∣ N → ¬ ((p : ℤ) ^ 2 ∣ N) →
        ¬ ∃ (x : ℚ) (z : Fin r → ℚ),
          (N : ℚ) = x ^ 2 + ∑ i, ((D i : ℤ) : ℚ) * (z i) ^ 2

/-!
**R5 — NOT YET A STATEMENT (deliberately not given a `def`).**  The indefinite and degenerate
branches at general `(n, r)`.  The s46 chain assumes the `(y,u)` part is positive definite
(`0 < a`, `0 < 4ac − b²`).  Nothing covers the indefinite case (Pell-type fibres, where C2-2 already
showed uniqueness fails) or the degenerate case (`4ac − b² = 0`).  A `def` is deliberately NOT
written for it: the enumeration of those branches is not yet precise enough to be a proposition,
and a placeholder `Prop` that is trivially true would be a residual that can be "discharged"
without doing anything.  Writing R5 as an actual statement is itself a task.
-/

end DiophCompression.ResearchUpgrade
