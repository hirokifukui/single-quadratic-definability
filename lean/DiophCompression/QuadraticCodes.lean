/-
  DiophCompression/QuadraticCodes.lean — APAL Structural Theory Gate 3, 必須A (Grunewald–Segal code bridge)
  (session 26, 2026-09-01, claude.ai direct). Statements frozen in frozen_statements/QuadraticCodes_STATEMENTS.lean.

  The paper's STANDARD code for a quadratic equation is an explicit finite datum
    QuadraticCode = (witness arity r, list of terms), term = (coefficient, ≤ 2 variable codes),
  with a COMPUTABLE (primitive recursive) evaluation `evalZZ` on an explicit environment list
  (parameters ++ unknowns; an out-of-range variable code reads as 1, an absent factor as 1 — the invalid-code
  behaviour is fixed here, not left to the decoder). The noncomputable `decodePolyZZ` of UnaryDiagonal.lean is
  kept as a COMPATIBILITY layer: codeOfNat / natOfCode transport between the two codings and the two
  code-uniform hypotheses are proved equivalent (uniformCodeGS_iff). The per-equation Grunewald–Segal
  hypothesis follows from the code-uniform one (uniformCodeGS_implies_perEquationGS). No sorry; std-3 expected.
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
  simp [varLookup, List.getElem?_eq_none h]

theorem optLookup_none (w : List ℤ) : optLookup w none = 1 := by
  simp [optLookup]

theorem quadraticCode_witnessArity_primrec : Primrec QuadraticCode.witnessArity := Primrec.fst

theorem primrec₂_varLookup : Primrec₂ varLookup := by
  unfold varLookup
  exact Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd) (Primrec.const 1)

theorem primrec₂_optLookup : Primrec₂ optLookup := by
  unfold optLookup
  exact Primrec.option_getD.comp
    (Primrec.option_map Primrec.snd (primrec₂_varLookup.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
    (Primrec.const 1)

theorem primrec₂_quadraticTerm_evalW : Primrec₂ QuadraticTerm.evalW := by
  unfold QuadraticTerm.evalW
  refine primrec₂_int_mul.comp (primrec₂_int_mul.comp ?_ ?_) ?_
  · exact Primrec.fst.comp Primrec.snd
  · exact primrec₂_optLookup.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  · exact primrec₂_optLookup.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem quadraticCode_evalW_eq_foldl (c : QuadraticCode) (w : List ℤ) :
    c.evalW w = c.2.foldl (fun s t => s + QuadraticTerm.evalW w t) 0 := by
  unfold QuadraticCode.evalW
  rw [List.sum_eq_foldl, List.foldl_map]

theorem primrec₂_quadraticCode_evalW : Primrec₂ QuadraticCode.evalW := by
  have h : Primrec fun p : QuadraticCode × List ℤ =>
      List.foldl (fun s t => s + QuadraticTerm.evalW p.2 t) 0 p.1.2 := by
    have hstep : Primrec₂ fun (p : QuadraticCode × List ℤ) (sb : ℤ × QuadraticTerm) =>
        sb.1 + QuadraticTerm.evalW p.2 sb.2 :=
      primrec₂_int_add.comp (Primrec.fst.comp Primrec.snd)
        (primrec₂_quadraticTerm_evalW.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
    exact Primrec.list_foldl (f := fun p : QuadraticCode × List ℤ => p.1.2) (g := fun _ => (0 : ℤ))
      (Primrec.snd.comp Primrec.fst) (Primrec.const (0 : ℤ)) hstep
  exact h.of_eq fun p => (quadraticCode_evalW_eq_foldl p.1 p.2).symm

/-- 必須A: evaluation of a code at (parameters, unknown list) is primitive recursive, uniformly in the code. -/
theorem quadraticCode_eval_primrec (k : ℕ) :
    Primrec fun p : QuadraticCode × (Fin k → ℤ) × List ℤ => QuadraticCode.evalZZ k p.1 p.2.1 p.2.2 := by
  unfold QuadraticCode.evalZZ
  have hofn : Primrec fun p : QuadraticCode × (Fin k → ℤ) × List ℤ => List.ofFn p.2.1 :=
    (Primrec.list_ofFn (f := fun (i : Fin k) (p : QuadraticCode × (Fin k → ℤ) × List ℤ) => p.2.1 i)
      fun i => Primrec.fin_app.comp (Primrec.fst.comp Primrec.snd) (Primrec.const i)).of_eq fun p => rfl
  have happ : Primrec fun p : QuadraticCode × (Fin k → ℤ) × List ℤ => List.ofFn p.2.1 ++ p.2.2 :=
    Primrec.list_append.comp hofn (Primrec.snd.comp Primrec.snd)
  exact primrec₂_quadraticCode_evalW.comp Primrec.fst happ

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
  rcases o with _ | i
  · simp [optVarPoly]
  · simpa [optVarPoly] using varPoly_totalDegree_le_one k r i

theorem quadraticTerm_toPoly_totalDegree_le_two (k r : ℕ) (t : QuadraticTerm) :
    (QuadraticTerm.toPoly k r t).totalDegree ≤ 2 := by
  unfold QuadraticTerm.toPoly
  refine (totalDegree_mul _ _).trans ?_
  have h1 := optVarPoly_totalDegree_le_one k r t.2.2
  have h2 : (C t.1 * optVarPoly k r t.2.1).totalDegree ≤ 1 := by
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C]
    simpa using optVarPoly_totalDegree_le_one k r t.2.1
  omega

/-- 必須A: the polynomial of a code has total degree ≤ 2. -/
theorem quadraticCode_toPoly_totalDegree_le_two (k : ℕ) (c : QuadraticCode) :
    (QuadraticCode.toPoly k c).totalDegree ≤ 2 := by
  obtain ⟨r, T⟩ := c
  unfold QuadraticCode.toPoly
  induction T with
  | nil => simp
  | cons t T ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (totalDegree_add _ _).trans (max_le (quadraticTerm_toPoly_totalDegree_le_two k r t) ih)

theorem evalAtZZ_varPoly (k r : ℕ) (a : Fin k → ℤ) (u : Fin r → ℤ) (i : ℕ) :
    evalAtZZ (varPoly k r i) a u = varLookup (List.ofFn a ++ List.ofFn u) i := by
  unfold varPoly varOfCode varLookup
  split_ifs with h h'
  · rw [List.getElem?_append_left (by simpa using h), List.getElem?_ofFn, dif_pos h]
    simp [evalAtZZ]
  · rw [List.getElem?_append_right (by simpa using h), List.getElem?_ofFn]
    simp only [List.length_ofFn]
    rw [dif_pos h']
    simp [evalAtZZ]
  · rw [List.getElem?_append_right (by simpa using h), List.getElem?_ofFn]
    simp only [List.length_ofFn]
    rw [dif_neg h']
    simp [evalAtZZ]

theorem evalAtZZ_optVarPoly (k r : ℕ) (a : Fin k → ℤ) (u : Fin r → ℤ) (o : Option ℕ) :
    evalAtZZ (optVarPoly k r o) a u = optLookup (List.ofFn a ++ List.ofFn u) o := by
  rcases o with _ | i
  · simp [optVarPoly, optLookup, evalAtZZ]
  · simp only [optVarPoly, Option.elim_some, optLookup, Option.map_some, Option.getD_some]
    exact evalAtZZ_varPoly k r a u i

theorem evalAtZZ_quadraticTerm_toPoly (k r : ℕ) (a : Fin k → ℤ) (u : Fin r → ℤ) (t : QuadraticTerm) :
    evalAtZZ (QuadraticTerm.toPoly k r t) a u = QuadraticTerm.evalW (List.ofFn a ++ List.ofFn u) t := by
  unfold QuadraticTerm.toPoly QuadraticTerm.evalW
  simp only [evalAtZZ, map_mul, eval_C]
  rw [← evalAtZZ, ← evalAtZZ, evalAtZZ_optVarPoly, evalAtZZ_optVarPoly]

/-- 必須A: the polynomial of a code evaluates as the computable evaluation. -/
theorem quadraticCode_toPoly_eval (k : ℕ) (c : QuadraticCode) (a : Fin k → ℤ) (u : Fin c.1 → ℤ) :
    evalAtZZ (QuadraticCode.toPoly k c) a u = QuadraticCode.evalZZ k c a (List.ofFn u) := by
  unfold QuadraticCode.toPoly QuadraticCode.evalZZ QuadraticCode.evalW
  simp only [evalAtZZ, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp]
  rw [← evalAtZZ, evalAtZZ_quadraticTerm_toPoly]

/-- Solvability of a code = solvability of its polynomial. -/
theorem quadraticCode_solvable_iff (k : ℕ) (c : QuadraticCode) (a : Fin k → ℤ) :
    QuadraticCode.solvableZZ k c a ↔ ∃ u : Fin c.1 → ℤ, evalAtZZ (QuadraticCode.toPoly k c) a u = 0 := by
  obtain ⟨r, T⟩ := c
  constructor
  · rintro ⟨u, hlen, hu⟩
    subst hlen
    refine ⟨fun i => u[i.1], ?_⟩
    rw [quadraticCode_toPoly_eval]
    simpa [List.ofFn_getElem] using hu
  · rintro ⟨u, hu⟩
    exact ⟨List.ofFn u, List.length_ofFn, by rw [← quadraticCode_toPoly_eval]; exact hu⟩

/-! ### Surjectivity and compatibility with the list coding of UnaryDiagonal.lean -/

/-- A list-code entry `(variable codes, coefficient)` as a term (the first two variable codes). -/
def termOfListEntry (p : List ℕ × ℤ) : QuadraticTerm := (p.2, (p.1[0]?, p.1[1]?))

/-- Terms of a list code. -/
def termsOfList (L : List (List ℕ × ℤ)) : List QuadraticTerm := L.map termOfListEntry

theorem termOfListEntry_toPoly (k r : ℕ) (p : List ℕ × ℤ) :
    QuadraticTerm.toPoly k r (termOfListEntry p) = C p.2 * monPoly k r p.1 := by
  obtain ⟨vs, c⟩ := p
  rcases vs with _ | ⟨x, _ | ⟨y, rest⟩⟩ <;> simp [termOfListEntry, QuadraticTerm.toPoly, optVarPoly, monPoly, mul_assoc]

theorem termsOfList_toPoly (k r : ℕ) (L : List (List ℕ × ℤ)) :
    QuadraticCode.toPoly k (r, termsOfList L) = interpPoly k r L := by
  unfold QuadraticCode.toPoly termsOfList interpPoly
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  exact termOfListEntry_toPoly k r p

/-- 必須A: every polynomial of total degree ≤ 2 is the polynomial of a code. -/
theorem quadraticCode_surjective (k r : ℕ) (P : Poly k r) (hP : P.totalDegree ≤ 2) :
    ∃ c : QuadraticCode, (⟨c.1, QuadraticCode.toPoly k c⟩ : Σ r : ℕ, Poly k r) = ⟨r, P⟩ := by
  obtain ⟨L, hL⟩ := interpPoly_surjective k r P hP
  exact ⟨(r, termsOfList L), by rw [termsOfList_toPoly, hL]⟩

/-- The list coding of UnaryDiagonal.lean read as a `QuadraticCode` (undecodable code ↦ `1 = 0`). -/
def codeOfNat (e : ℕ) : QuadraticCode :=
  (Encodable.decode e : Option (ℕ × List (List ℕ × ℤ))).elim (0, [(1, (none, none))])
    (fun p => (p.1, termsOfList p.2))

theorem primrec_termsOfList : Primrec termsOfList := by
  unfold termsOfList termOfListEntry
  refine Primrec.list_map Primrec.id ?_
  exact Primrec.pair (Primrec.snd.comp Primrec.snd)
    (Primrec.pair (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
      (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)))

theorem primrec_codeOfNat : Primrec codeOfNat := by
  have h : Primrec fun e : ℕ => Option.casesOn (motive := fun _ => QuadraticCode)
      (Encodable.decode e : Option (ℕ × List (List ℕ × ℤ)))
      ((0, [(1, (none, none))]) : QuadraticCode) (fun p => (p.1, termsOfList p.2)) := by
    refine Primrec.option_casesOn Primrec.decode (Primrec.const _) ?_
    exact Primrec.pair (Primrec.fst.comp Primrec.snd) (primrec_termsOfList.comp (Primrec.snd.comp Primrec.snd))
  refine h.of_eq fun e => ?_
  unfold codeOfNat
  rcases (Encodable.decode e : Option (ℕ × List (List ℕ × ℤ))) with _ | p <;> rfl

/-- Compatibility: the noncomputable decoder is the polynomial of the computable code. -/
theorem decodePolyZZ_eq_codeOfNat (k e : ℕ) :
    decodePolyZZ k e = ⟨(codeOfNat e).1, QuadraticCode.toPoly k (codeOfNat e)⟩ := by
  unfold decodePolyZZ codeOfNat
  rcases (Encodable.decode e : Option (ℕ × List (List ℕ × ℤ))) with _ | ⟨r, L⟩
  · simp only [QuadraticCode.toPoly, QuadraticTerm.toPoly, optVarPoly, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Option.elim_none, mul_one, C_1]
    exact congrArg (Sigma.mk 0) (add_zero (1 : Poly k 0)).symm
  · simp only [Option.elim_some]
    rw [termsOfList_toPoly]

/-- A term as a list-code entry. -/
def listEntryOfTerm (t : QuadraticTerm) : List ℕ × ℤ := (t.2.1.toList ++ t.2.2.toList, t.1)

/-- A `QuadraticCode` as a natural-number code of UnaryDiagonal.lean. -/
def natOfCode (c : QuadraticCode) : ℕ := Encodable.encode (c.1, c.2.map listEntryOfTerm)

theorem primrec_option_toList : Primrec (Option.toList : Option ℕ → List ℕ) := by
  have h : Primrec fun o : Option ℕ => Option.casesOn (motive := fun _ => List ℕ) o ([] : List ℕ) (fun x => [x]) :=
    Primrec.option_casesOn Primrec.id (Primrec.const []) (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  exact h.of_eq fun o => by rcases o with _ | x <;> rfl

theorem primrec_natOfCode : Primrec natOfCode := by
  unfold natOfCode listEntryOfTerm
  refine Primrec.encode.comp (Primrec.pair Primrec.fst ?_)
  refine Primrec.list_map Primrec.snd ?_
  exact Primrec.pair (Primrec.list_append.comp (primrec_option_toList.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    (primrec_option_toList.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))) (Primrec.fst.comp Primrec.snd)

theorem listEntryOfTerm_interp (k r : ℕ) (t : QuadraticTerm) :
    C (listEntryOfTerm t).2 * monPoly k r (listEntryOfTerm t).1 = QuadraticTerm.toPoly k r t := by
  obtain ⟨c, o₁, o₂⟩ := t
  rcases o₁ with _ | i <;> rcases o₂ with _ | j <;>
    simp [listEntryOfTerm, QuadraticTerm.toPoly, optVarPoly, monPoly, mul_assoc]

/-- Compatibility (converse): the decoder recovers the polynomial of a code through `natOfCode`. -/
theorem decodePolyZZ_natOfCode (k : ℕ) (c : QuadraticCode) :
    decodePolyZZ k (natOfCode c) = ⟨c.1, QuadraticCode.toPoly k c⟩ := by
  obtain ⟨r, T⟩ := c
  unfold decodePolyZZ natOfCode
  rw [Encodable.encodek]
  simp only
  congr 1
  unfold interpPoly QuadraticCode.toPoly
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  exact listEntryOfTerm_interp k r t

/-! ### The code-uniform Grunewald–Segal hypothesis on codes -/

/-- External hypothesis (Grunewald–Segal, on the STANDARD codes): for every parameter arity `k`, solvability
    in ℤ of the coded quadratic equation at parameters `a` is a decidable predicate of `(code, a)`. This is
    exactly the input/output contract of a uniform decision procedure for integer quadratic equations
    (Grunewald–Segal 1981) — the coefficient table and the witness arity are explicit finite data. -/
def UniformQuadraticSolvabilityOnCodes : Prop :=
  ∀ k : ℕ, ComputablePred fun p : QuadraticCode × (Fin k → ℤ) => QuadraticCode.solvableZZ k p.1 p.2

theorem computablePred_comp_computable {α β : Type} [Primcodable α] [Primcodable β] {p : β → Prop}
    (hp : ComputablePred p) {f : α → β} (hf : Computable f) : ComputablePred fun a => p (f a) := by
  obtain ⟨g, hg, hpg⟩ := ComputablePred.computable_iff.1 hp
  refine ComputablePred.computable_iff.2 ⟨fun a => g (f a), hg.comp hf, ?_⟩
  funext a
  exact congrFun hpg (f a)

/-- The code-uniform hypothesis on standard codes implies the list-code one of UnaryDiagonal.lean. -/
theorem uniformGS_of_uniformOnCodes (h : UniformQuadraticSolvabilityOnCodes) :
    UniformQuadraticSolvabilityDecidableZZ := by
  intro k
  have hc : ComputablePred fun p : ℕ × (Fin k → ℤ) => QuadraticCode.solvableZZ k (codeOfNat p.1) p.2 :=
    computablePred_comp_computable (h k)
      (f := fun p : ℕ × (Fin k → ℤ) => (codeOfNat p.1, p.2))
      ((primrec_codeOfNat.comp Primrec.fst).pair Primrec.snd).to_comp
  refine hc.of_eq fun p => ?_
  rw [quadraticCode_solvable_iff, decodePolyZZ_eq_codeOfNat k p.1]

/-- The list-code hypothesis implies the standard-code one. -/
theorem uniformOnCodes_of_uniformGS (h : UniformQuadraticSolvabilityDecidableZZ) :
    UniformQuadraticSolvabilityOnCodes := by
  intro k
  have hc : ComputablePred fun p : QuadraticCode × (Fin k → ℤ) =>
      ∃ u : Fin (decodePolyZZ k (natOfCode p.1)).1 → ℤ, evalAtZZ (decodePolyZZ k (natOfCode p.1)).2 p.2 u = 0 :=
    computablePred_comp_computable (h k)
      (f := fun p : QuadraticCode × (Fin k → ℤ) => (natOfCode p.1, p.2))
      ((primrec_natOfCode.comp Primrec.fst).pair Primrec.snd).to_comp
  refine hc.of_eq fun p => ?_
  rw [quadraticCode_solvable_iff, decodePolyZZ_natOfCode k p.1]

/-- 必須A: the two code-uniform hypotheses are equivalent. -/
theorem uniformCodeGS_iff : UniformQuadraticSolvabilityOnCodes ↔ UniformQuadraticSolvabilityDecidableZZ :=
  ⟨uniformGS_of_uniformOnCodes, uniformOnCodes_of_uniformGS⟩

/-- 必須A: the code-uniform hypothesis (standard codes) implies the per-equation Grunewald–Segal hypothesis. -/
theorem uniformCodeGS_implies_perEquationGS (h : UniformQuadraticSolvabilityOnCodes) :
    QuadraticSolvabilityDecidableZZ :=
  quadraticSolvabilityDecidable_of_uniform (uniformGS_of_uniformOnCodes h)

end DiophCompression

#print axioms DiophCompression.quadraticCode_eval_primrec
#print axioms DiophCompression.quadraticCode_toPoly_totalDegree_le_two
#print axioms DiophCompression.quadraticCode_toPoly_eval
#print axioms DiophCompression.quadraticCode_surjective
#print axioms DiophCompression.decodePolyZZ_eq_codeOfNat
#print axioms DiophCompression.decodePolyZZ_natOfCode
#print axioms DiophCompression.uniformCodeGS_iff
#print axioms DiophCompression.uniformCodeGS_implies_perEquationGS
