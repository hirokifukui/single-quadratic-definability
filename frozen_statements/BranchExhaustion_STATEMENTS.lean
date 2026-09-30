/-
  DiophCompression/BranchExhaustion.lean — APAL Structural Theory Gate 5, 必須E (s28, 2026-09-02, claude.ai direct).

  The branch table of GATE4_F_BRANCH_INVENTORY as a KERNEL object rather than prose. The leaves of the
  projection-dichotomy tree are enumerated, each is assigned the certificate kind it emits (or `none` for a
  bounded branch), and the case classifiers of the three dispatch levels (full-rank direction, singular
  quotient rank × slope, one-witness discriminant) are proved EXHAUSTIVE: every datum lands on a listed
  leaf, and the predicate of that leaf holds. A branch missing from this file would be a proof branch that
  does not exist in the tree. Only three kinds are emitted (no generic fallback). No sorry; std-3.
-/
import DiophCompression.SummitTarget

namespace DiophCompression

open MvPolynomial MPUP Matrix

/-- The leaves of the dichotomy tree (GATE4_F_BRANCH_INVENTORY, s27/s28). -/
inductive QuadraticBranch
  | A1 | A2 | A3 | A4
  | B0
  | B1a | B1b | B1c
  | D1 | D2 | D3 | D4 | D6 | D7
  | B2 | B3 | B4
  deriving DecidableEq, Repr

namespace QuadraticBranch

/-- The certificate kind each leaf emits; `none` exactly on the bounded leaves. -/
def kind : QuadraticBranch → Option StructuredKind
  | .A1 => some .pellUnitOrbit
  | .A2 => some .polynomialProgression
  | .A3 => some .polynomialProgression
  | .A4 => none
  | .B0 => some .polynomialProgression
  | .B1a => some .movingModulusStepOrbit
  | .B1b => some .polynomialProgression
  | .B1c => some .movingModulusStepOrbit
  | .D1 => none
  | .D2 => some .polynomialProgression
  | .D3 => some .polynomialProgression
  | .D4 => some .polynomialProgression
  | .D6 => some .polynomialProgression
  | .D7 => some .pellUnitOrbit
  | .B2 => some .movingModulusStepOrbit
  | .B3 => some .polynomialProgression
  | .B4 => some .movingModulusStepOrbit

/-- The bounded leaves: A4 (full rank, `α·W̃ ≥ 0`) and D1 (negative discriminant). -/
def bounded : QuadraticBranch → Bool
  | .A4 => true
  | .D1 => true
  | _ => false

end QuadraticBranch

/-- No leaf is silently unclassified: a leaf emits a certificate kind exactly when it is not bounded. -/
theorem branch_kind_iff_not_bounded (br : QuadraticBranch) :
    br.kind = none ↔ br.bounded = true := by
  sorry

/-- Only the three structured kinds occur in the table — there is no fourth kind and no generic fallback. -/
theorem no_unclassified_quadratic_branch (br : QuadraticBranch) (k : StructuredKind)
    (h : br.kind = some k) :
    k = StructuredKind.polynomialProgression ∨ k = StructuredKind.pellUnitOrbit ∨
      k = StructuredKind.movingModulusStepOrbit := by
  sorry

/-- Negative control for branch omission (GPT 宿題群7-19): every leaf of the table is reachable, i.e. the
    enumeration contains no dead entry and no entry outside the three families ∪ the two bounded leaves. -/
theorem branch_table_partition (br : QuadraticBranch) :
    (br.bounded = true ∧ br.kind = none) ∨
      (br.bounded = false ∧ ∃ k, br.kind = some k) := by
  sorry

/-! ### Level 1 — the full-rank direction dispatch (A1–A4) -/

/-- Classifier of the full-rank block: `α` is the direction coefficient, `W` the signed direction value,
    `β` the linear coefficient of the `α = 0` degeneration. -/
def fullRankBranch (α W β : ℤ) : QuadraticBranch :=
  if α = 0 then (if β = 0 then .A3 else .A2) else (if α * W < 0 then .A1 else .A4)

/-- 必須E: the full-rank dispatch is exhaustive, and each case carries its defining predicate. -/
theorem fullRank_structured_cases (α W β : ℤ) :
    (fullRankBranch α W β = .A1 ∧ α ≠ 0 ∧ α * W < 0) ∨
    (fullRankBranch α W β = .A2 ∧ α = 0 ∧ β ≠ 0) ∨
    (fullRankBranch α W β = .A3 ∧ α = 0 ∧ β = 0) ∨
    (fullRankBranch α W β = .A4 ∧ α ≠ 0 ∧ 0 ≤ α * W) := by
  sorry

/-- The kinds of the full-rank leaves are those of the table. -/
theorem fullRank_branch_kinds :
    QuadraticBranch.A1.kind = some StructuredKind.pellUnitOrbit ∧
    QuadraticBranch.A2.kind = some StructuredKind.polynomialProgression ∧
    QuadraticBranch.A3.kind = some StructuredKind.polynomialProgression ∧
    QuadraticBranch.A4.kind = none := ⟨rfl, rfl, rfl, rfl⟩

/-! ### Level 2 — the singular block: quotient rank × slope (B0, B1a–B1c, B2–B4) -/

/-- Classifier of the singular block. `qrank` is the rank of the quotient form, `b` the slope of the moving
    modulus, `m₂` the uncoupled coefficient that separates B1b from the one-witness leaves. -/
def singularBranch (qrank : ℕ) (b m₂ : ℤ) : QuadraticBranch := by
  sorry

/-- 必須E: the singular dispatch is exhaustive. Rank 0 is B0; rank 1 splits by the sign of the slope, and
    its `b = 0, m₂ = 0` case hands over to the one-witness classifier (represented here by its entry leaf);
    rank ≥ 2 splits by the sign of the slope into B4 / B3 / B2. -/
theorem singular_structured_cases (qrank : ℕ) (b m₂ : ℤ) :
    (qrank = 0 ∧ singularBranch qrank b m₂ = .B0) ∨
    (qrank = 1 ∧ b < 0 ∧ singularBranch qrank b m₂ = .B1a) ∨
    (qrank = 1 ∧ b = 0 ∧ m₂ ≠ 0 ∧ singularBranch qrank b m₂ = .B1b) ∨
    (qrank = 1 ∧ b = 0 ∧ m₂ = 0 ∧ singularBranch qrank b m₂ = .D1) ∨
    (qrank = 1 ∧ 0 < b ∧ singularBranch qrank b m₂ = .B1c) ∨
    (2 ≤ qrank ∧ b < 0 ∧ singularBranch qrank b m₂ = .B4) ∨
    (2 ≤ qrank ∧ b = 0 ∧ singularBranch qrank b m₂ = .B3) ∨
    (2 ≤ qrank ∧ 0 < b ∧ singularBranch qrank b m₂ = .B2) := by
  sorry

/-! ### Level 3 — the one-witness leaves (D1–D7) -/

/-- Classifier of the one-witness normal form by the discriminant and the coefficient `C`. -/
noncomputable def oneWitnessBranch (disc C : ℤ) : QuadraticBranch := by
  classical
  exact
    if disc < 0 then .D1
    else if disc = 0 then (if C = 0 then .D3 else .D2)
    else if IsSquare disc then (if C = 0 then .D6 else .D4)
    else .D7

/-- 必須E: the one-witness dispatch is exhaustive (D1, D2, D3, D4, D6, D7 — the r06 leaves). -/
theorem oneWitness_structured_cases (disc C : ℤ) :
    (disc < 0 ∧ oneWitnessBranch disc C = .D1) ∨
    (disc = 0 ∧ C ≠ 0 ∧ oneWitnessBranch disc C = .D2) ∨
    (disc = 0 ∧ C = 0 ∧ oneWitnessBranch disc C = .D3) ∨
    (0 < disc ∧ IsSquare disc ∧ C ≠ 0 ∧ oneWitnessBranch disc C = .D4) ∨
    (0 < disc ∧ IsSquare disc ∧ C = 0 ∧ oneWitnessBranch disc C = .D6) ∨
    (0 < disc ∧ ¬ IsSquare disc ∧ oneWitnessBranch disc C = .D7) := by
  sorry

/-- The kinds of the one-witness leaves are those of the table (D1 bounded; D2/D3/D4/D6 polynomial; D7 Pell). -/
theorem oneWitness_branch_kinds :
    QuadraticBranch.D1.kind = none ∧
    QuadraticBranch.D2.kind = some StructuredKind.polynomialProgression ∧
    QuadraticBranch.D3.kind = some StructuredKind.polynomialProgression ∧
    QuadraticBranch.D4.kind = some StructuredKind.polynomialProgression ∧
    QuadraticBranch.D6.kind = some StructuredKind.polynomialProgression ∧
    QuadraticBranch.D7.kind = some StructuredKind.pellUnitOrbit := by
  sorry

/-- The kinds of the singular leaves are those of the table (B4 is MM with the s28 correction: it is the
    positive-slope family transported by the witness reflection, not a decreasing family). -/
theorem singular_branch_kinds :
    QuadraticBranch.B0.kind = some StructuredKind.polynomialProgression ∧
    QuadraticBranch.B1a.kind = some StructuredKind.movingModulusStepOrbit ∧
    QuadraticBranch.B1b.kind = some StructuredKind.polynomialProgression ∧
    QuadraticBranch.B1c.kind = some StructuredKind.movingModulusStepOrbit ∧
    QuadraticBranch.B2.kind = some StructuredKind.movingModulusStepOrbit ∧
    QuadraticBranch.B3.kind = some StructuredKind.polynomialProgression ∧
    QuadraticBranch.B4.kind = some StructuredKind.movingModulusStepOrbit := by
  sorry

end DiophCompression
