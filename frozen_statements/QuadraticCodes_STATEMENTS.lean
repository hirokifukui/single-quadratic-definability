/-
  frozen_statements/QuadraticCodes_STATEMENTS.lean — APAL Structural Theory Gate 3, 必須A
  (frozen s26, 2026-09-01). Standard finite quadratic codes with a primitive-recursive evaluation, the
  polynomial of a code (degree ≤ 2, surjective onto quadratics), compatibility with the list coding of
  UnaryDiagonal.lean (codeOfNat / natOfCode), the code-uniform Grunewald–Segal hypothesis on standard codes,
  its equivalence with UniformQuadraticSolvabilityDecidableZZ, and the per-equation consequence.
-/
import DiophCompression.UnaryDiagonal

namespace DiophCompression

open MvPolynomial MPUP

/-! ### The code type -/

/-- A term of a quadratic code: coefficient × (up to two variable codes; `none` = absent factor).
    Constant = `(c, none, none)`, linear = `(c, some i, none)`, quadratic = `(c, some i, some j)`.
    Duplicate terms add; a term `(c, none, some j)` is the same polynomial as `(c, some j, none)`. -/
abbrev QuadraticTerm : Type := ℤ × (Option ℕ × Option ℕ)

/-- A quadratic code: witness arity `r` and a finite list of terms. `Primcodable` by construction. -/
abbrev QuadraticCode : Type := ℕ × List QuadraticTerm

/-- Witness arity of a code (a projection, hence primitive recursive). -/
def QuadraticCode.witnessArity (c : QuadraticCode) : ℕ := c.1

/-- Terms of a code. -/
def QuadraticCode.terms (c : QuadraticCode) : List QuadraticTerm := c.2

/-! ### Computable evaluation -/

/-- Variable code `i` in the environment `w` (parameters then unknowns); out of range reads as `1`. -/
def varLookup (w : List ℤ) (i : ℕ) : ℤ := (w[i]?).getD 1

/-- Optional variable factor: `none` reads as `1`. -/
def optLookup (w : List ℤ) (o : Option ℕ) : ℤ := (o.map (varLookup w)).getD 1

/-- Value of a term in an environment. -/
def QuadraticTerm.evalW (w : List ℤ) (t : QuadraticTerm) : ℤ := t.1 * optLookup w t.2.1 * optLookup w t.2.2

/-- Value of a code in an environment. -/
def QuadraticCode.evalW (c : QuadraticCode) (w : List ℤ) : ℤ := (c.2.map (QuadraticTerm.evalW w)).sum

/-- Evaluation at parameters `a : ℤᵏ` and an unknown list `u` (environment `ofFn a ++ u`). -/
def QuadraticCode.evalZZ (k : ℕ) (c : QuadraticCode) (a : Fin k → ℤ) (u : List ℤ) : ℤ :=
  c.evalW (List.ofFn a ++ u)

/-- Solvability in ℤ: some unknown list of the declared witness arity is a root. -/
def QuadraticCode.solvableZZ (k : ℕ) (c : QuadraticCode) (a : Fin k → ℤ) : Prop :=
  ∃ u : List ℤ, u.length = c.1 ∧ c.evalZZ k a u = 0

theorem varLookup_of_length_le (w : List ℤ) (i : ℕ) (h : w.length ≤ i) : varLookup w i = 1 := by
  sorry

theorem optLookup_none (w : List ℤ) : optLookup w none = 1 := by
  sorry

theorem quadraticCode_witnessArity_primrec : Primrec QuadraticCode.witnessArity := by
  sorry

theorem primrec₂_varLookup : Primrec₂ varLookup := by
  sorry

theorem primrec₂_optLookup : Primrec₂ optLookup := by
  sorry

theorem primrec₂_quadraticTerm_evalW : Primrec₂ QuadraticTerm.evalW := by
  sorry

theorem quadraticCode_evalW_eq_foldl (c : QuadraticCode) (w : List ℤ) :
    c.evalW w = c.2.foldl (fun s t => s + QuadraticTerm.evalW w t) 0 := by
  sorry

theorem primrec₂_quadraticCode_evalW : Primrec₂ QuadraticCode.evalW := by
  sorry

/-- 必須A: evaluation of a code at (parameters, unknown list) is primitive recursive, uniformly in the code. -/
theorem quadraticCode_eval_primrec (k : ℕ) :
    Primrec fun p : QuadraticCode × (Fin k → ℤ) × List ℤ => QuadraticCode.evalZZ k p.1 p.2.1 p.2.2 := by
  sorry

/-! ### The polynomial of a code -/

/-- Optional variable factor as a polynomial: `none ↦ 1`, `some i ↦ varPoly k r i`. -/
noncomputable def optVarPoly (k r : ℕ) (o : Option ℕ) : Poly k r := o.elim 1 (varPoly k r)

/-- Polynomial of a term. -/
noncomputable def QuadraticTerm.toPoly (k r : ℕ) (t : QuadraticTerm) : Poly k r :=
  C t.1 * optVarPoly k r t.2.1 * optVarPoly k r t.2.2

/-- Polynomial of a code (in `Poly k c.1`). -/
noncomputable def QuadraticCode.toPoly (k : ℕ) (c : QuadraticCode) : Poly k c.1 :=
  (c.2.map (QuadraticTerm.toPoly k c.1)).sum

theorem optVarPoly_totalDegree_le_one (k r : ℕ) (o : Option ℕ) : (optVarPoly k r o).totalDegree ≤ 1 := by
  sorry

theorem quadraticTerm_toPoly_totalDegree_le_two (k r : ℕ) (t : QuadraticTerm) :
    (QuadraticTerm.toPoly k r t).totalDegree ≤ 2 := by
  sorry

/-- 必須A: the polynomial of a code has total degree ≤ 2. -/
theorem quadraticCode_toPoly_totalDegree_le_two (k : ℕ) (c : QuadraticCode) :
    (QuadraticCode.toPoly k c).totalDegree ≤ 2 := by
  sorry

theorem evalAtZZ_varPoly (k r : ℕ) (a : Fin k → ℤ) (u : Fin r → ℤ) (i : ℕ) :
    evalAtZZ (varPoly k r i) a u = varLookup (List.ofFn a ++ List.ofFn u) i := by
  sorry

theorem evalAtZZ_optVarPoly (k r : ℕ) (a : Fin k → ℤ) (u : Fin r → ℤ) (o : Option ℕ) :
    evalAtZZ (optVarPoly k r o) a u = optLookup (List.ofFn a ++ List.ofFn u) o := by
  sorry

theorem evalAtZZ_quadraticTerm_toPoly (k r : ℕ) (a : Fin k → ℤ) (u : Fin r → ℤ) (t : QuadraticTerm) :
    evalAtZZ (QuadraticTerm.toPoly k r t) a u = QuadraticTerm.evalW (List.ofFn a ++ List.ofFn u) t := by
  sorry

/-- 必須A: the polynomial of a code evaluates as the computable evaluation. -/
theorem quadraticCode_toPoly_eval (k : ℕ) (c : QuadraticCode) (a : Fin k → ℤ) (u : Fin c.1 → ℤ) :
    evalAtZZ (QuadraticCode.toPoly k c) a u = QuadraticCode.evalZZ k c a (List.ofFn u) := by
  sorry

/-- Solvability of a code = solvability of its polynomial. -/
theorem quadraticCode_solvable_iff (k : ℕ) (c : QuadraticCode) (a : Fin k → ℤ) :
    QuadraticCode.solvableZZ k c a ↔ ∃ u : Fin c.1 → ℤ, evalAtZZ (QuadraticCode.toPoly k c) a u = 0 := by
  sorry

/-! ### Surjectivity and compatibility with the list coding of UnaryDiagonal.lean -/

/-- A list-code entry `(variable codes, coefficient)` as a term (the first two variable codes). -/
def termOfListEntry (p : List ℕ × ℤ) : QuadraticTerm := (p.2, (p.1[0]?, p.1[1]?))

/-- Terms of a list code. -/
def termsOfList (L : List (List ℕ × ℤ)) : List QuadraticTerm := L.map termOfListEntry

theorem termOfListEntry_toPoly (k r : ℕ) (p : List ℕ × ℤ) :
    QuadraticTerm.toPoly k r (termOfListEntry p) = C p.2 * monPoly k r p.1 := by
  sorry

theorem termsOfList_toPoly (k r : ℕ) (L : List (List ℕ × ℤ)) :
    QuadraticCode.toPoly k (r, termsOfList L) = interpPoly k r L := by
  sorry

/-- 必須A: every polynomial of total degree ≤ 2 is the polynomial of a code. -/
theorem quadraticCode_surjective (k r : ℕ) (P : Poly k r) (hP : P.totalDegree ≤ 2) :
    ∃ c : QuadraticCode, (⟨c.1, QuadraticCode.toPoly k c⟩ : Σ r : ℕ, Poly k r) = ⟨r, P⟩ := by
  sorry

/-- The list coding of UnaryDiagonal.lean read as a `QuadraticCode` (undecodable code ↦ `1 = 0`). -/
def codeOfNat (e : ℕ) : QuadraticCode :=
  (Encodable.decode e : Option (ℕ × List (List ℕ × ℤ))).elim (0, [(1, (none, none))])
    (fun p => (p.1, termsOfList p.2))

theorem primrec_termsOfList : Primrec termsOfList := by
  sorry

theorem primrec_codeOfNat : Primrec codeOfNat := by
  sorry

/-- Compatibility: the noncomputable decoder is the polynomial of the computable code. -/
theorem decodePolyZZ_eq_codeOfNat (k e : ℕ) :
    decodePolyZZ k e = ⟨(codeOfNat e).1, QuadraticCode.toPoly k (codeOfNat e)⟩ := by
  sorry

/-- A term as a list-code entry. -/
def listEntryOfTerm (t : QuadraticTerm) : List ℕ × ℤ := (t.2.1.toList ++ t.2.2.toList, t.1)

/-- A `QuadraticCode` as a natural-number code of UnaryDiagonal.lean. -/
def natOfCode (c : QuadraticCode) : ℕ := Encodable.encode (c.1, c.2.map listEntryOfTerm)

theorem primrec_option_toList : Primrec (Option.toList : Option ℕ → List ℕ) := by
  sorry

theorem primrec_natOfCode : Primrec natOfCode := by
  sorry

theorem listEntryOfTerm_interp (k r : ℕ) (t : QuadraticTerm) :
    C (listEntryOfTerm t).2 * monPoly k r (listEntryOfTerm t).1 = QuadraticTerm.toPoly k r t := by
  sorry

/-- Compatibility (converse): the decoder recovers the polynomial of a code through `natOfCode`. -/
theorem decodePolyZZ_natOfCode (k : ℕ) (c : QuadraticCode) :
    decodePolyZZ k (natOfCode c) = ⟨c.1, QuadraticCode.toPoly k c⟩ := by
  sorry

/-! ### The code-uniform Grunewald–Segal hypothesis on codes -/

/-- External hypothesis (Grunewald–Segal, on the STANDARD codes): for every parameter arity `k`, solvability
    in ℤ of the coded quadratic equation at parameters `a` is a decidable predicate of `(code, a)`. This is
    exactly the input/output contract of a uniform decision procedure for integer quadratic equations
    (Grunewald–Segal 1981) — the coefficient table and the witness arity are explicit finite data. -/
def UniformQuadraticSolvabilityOnCodes : Prop :=
  ∀ k : ℕ, ComputablePred fun p : QuadraticCode × (Fin k → ℤ) => QuadraticCode.solvableZZ k p.1 p.2

theorem computablePred_comp_computable {α β : Type} [Primcodable α] [Primcodable β] {p : β → Prop}
    (hp : ComputablePred p) {f : α → β} (hf : Computable f) : ComputablePred fun a => p (f a) := by
  sorry

/-- The code-uniform hypothesis on standard codes implies the list-code one of UnaryDiagonal.lean. -/
theorem uniformGS_of_uniformOnCodes (h : UniformQuadraticSolvabilityOnCodes) :
    UniformQuadraticSolvabilityDecidableZZ := by
  sorry

/-- The list-code hypothesis implies the standard-code one. -/
theorem uniformOnCodes_of_uniformGS (h : UniformQuadraticSolvabilityDecidableZZ) :
    UniformQuadraticSolvabilityOnCodes := by
  sorry

/-- 必須A: the two code-uniform hypotheses are equivalent. -/
theorem uniformCodeGS_iff : UniformQuadraticSolvabilityOnCodes ↔ UniformQuadraticSolvabilityDecidableZZ := by
  sorry

/-- 必須A: the code-uniform hypothesis (standard codes) implies the per-equation Grunewald–Segal hypothesis. -/
theorem uniformCodeGS_implies_perEquationGS (h : UniformQuadraticSolvabilityOnCodes) :
    QuadraticSolvabilityDecidableZZ := by
  sorry

end DiophCompression
