/-
  frozen_statements/UnaryDiagonal_STATEMENTS.lean — APAL Structural Theory Gate 2, 必須B part 2
  (frozen s25, 2026-09-01). Coefficient-vector coding of degree-≤2 integer polynomials (GPT E11),
  the CODE-UNIFORM Grunewald–Segal hypothesis (a new, separately disclosed Prop; implies the per-P one),
  the diagonal relation D_k ⊆ ℤ^{k+1} (recursive under uniform GS, never SE_2 — unconditionally), and the
  relation phase diagram at every positive arity: SE_2(k) ⊊ REC(k) ⊊ RE(k) = PP_2(k) = SE_4(k), k ≥ 1.
-/
import DiophCompression.HaltingTransport

namespace DiophCompression

open MvPolynomial MPUP

/-- Variable of a code: `n < k` reads as parameter `n`, `k ≤ n < k + r` as unknown `n - k`, else invalid. -/
def varOfCode (k r : ℕ) (n : ℕ) : Option (Fin k ⊕ Fin r) :=
  if h : n < k then some (Sum.inl ⟨n, h⟩)
  else if h' : n - k < r then some (Sum.inr ⟨n - k, h'⟩) else none

/-- Code of a variable. -/
def codeOfVar (k r : ℕ) (v : Fin k ⊕ Fin r) : ℕ := Sum.elim (fun i => i.val) (fun t => k + t.val) v

/-- The polynomial of a variable code: `X v`, or `1` for an invalid code. -/
noncomputable def varPoly (k r : ℕ) (n : ℕ) : Poly k r :=
  match varOfCode k r n with
  | none => 1
  | some v => X v

/-- Monomial of a list of variable codes, truncated to length ≤ 2. -/
noncomputable def monPoly (k r : ℕ) (vs : List ℕ) : Poly k r := ((vs.take 2).map (varPoly k r)).prod

/-- The polynomial of a code list: `Σ c · monomial`. -/
noncomputable def interpPoly (k r : ℕ) (L : List (List ℕ × ℤ)) : Poly k r :=
  (L.map fun t => C t.2 * monPoly k r t.1).sum

/-- Decoding of a natural-number code as a pair (witness arity `r`, polynomial in `Poly k r`) of total
    degree ≤ 2: the code is a list of (variable-code list, coefficient) pairs; every list of variable codes
    is truncated to length ≤ 2, invalid variable codes read as `1`, an undecodable code reads as `⟨0, 1⟩`. -/
noncomputable def decodePolyZZ (k : ℕ) (e : ℕ) : Σ r : ℕ, Poly k r :=
  match (Encodable.decode e : Option (ℕ × List (List ℕ × ℤ))) with
  | none => ⟨0, 1⟩
  | some (r, L) => ⟨r, interpPoly k r L⟩

/-- Every decoded polynomial has total degree ≤ 2 (so the uniform hypothesis below speaks only of
    quadratic equations). -/
theorem decodePolyZZ_totalDegree_le_two (k e : ℕ) : (decodePolyZZ k e).2.totalDegree ≤ 2 := by
  sorry

/-- Every degree-≤2 polynomial has a code. -/
theorem decodePolyZZ_surjective (k r : ℕ) (P : Poly k r) (hP : P.totalDegree ≤ 2) :
    ∃ e : ℕ, decodePolyZZ k e = ⟨r, P⟩ := by
  sorry

/-- External hypothesis (Grunewald–Segal, code-uniform form): for every parameter arity `k`, solvability
    in ℤ of the quadratic equation with code `e` at parameters `a` is a decidable predicate of `(e, a)`. -/
def UniformQuadraticSolvabilityDecidableZZ : Prop :=
  ∀ k : ℕ, ComputablePred fun p : ℕ × (Fin k → ℤ) =>
    ∃ u : Fin (decodePolyZZ k p.1).1 → ℤ, evalAtZZ (decodePolyZZ k p.1).2 p.2 u = 0

/-- The uniform hypothesis implies the per-equation one. -/
theorem quadraticSolvabilityDecidable_of_uniform (hU : UniformQuadraticSolvabilityDecidableZZ) :
    QuadraticSolvabilityDecidableZZ := by
  sorry

/-- The diagonal relation on ℤ^{k+1}: `v ∈ D` iff the quadratic equation coded by `v 0` has no integer
    solution at parameters `v`. -/
def diagonalSetZZ (k : ℕ) : Set (Fin (k + 1) → ℤ) :=
  {v | ¬ ∃ u : Fin (decodePolyZZ (k + 1) (Encodable.encode (v 0))).1 → ℤ,
      evalAtZZ (decodePolyZZ (k + 1) (Encodable.encode (v 0))).2 v u = 0}

/-- Conditional on uniform GS: the diagonal relation is recursive. -/
theorem diagonalSetZZ_computablePred (hU : UniformQuadraticSolvabilityDecidableZZ) (k : ℕ) :
    ComputablePred fun v => v ∈ diagonalSetZZ k := by
  sorry

/-- Unconditional: the diagonal relation is not SE_2-definable. -/
theorem diagonalSetZZ_not_singleQuadratic (k : ℕ) : ¬ WithinSingleEquationZZ 2 (diagonalSetZZ k) := by
  sorry

/-- Conditional on uniform GS: SE_2(k) ⊊ REC(k) at every positive arity. -/
theorem singleQuadratic_strict_recursive_all_positive_arity (hU : UniformQuadraticSolvabilityDecidableZZ)
    (k : ℕ) : SingleEqFragmentZZ 2 (k + 1) ⊂ RecFragmentZZ (k + 1) := by
  sorry

/-- Conditional on uniform GS: SE_2(1) ⊊ REC(1). -/
theorem unary_singleQuadratic_strict_recursive (hU : UniformQuadraticSolvabilityDecidableZZ) :
    SingleEqFragmentZZ 2 1 ⊂ RecFragmentZZ 1 := by
  sorry

/-- The relation phase diagram at every positive arity (uniform GS + DPRM):
    SE_2(k) ⊊ REC(k) ⊊ RE(k) = PP_2(k) = SE_4(k). -/
theorem relation_phase_diagram_all_positive_arity (hU : UniformQuadraticSolvabilityDecidableZZ)
    (hD : DPRM_ZZ) {k : ℕ} (hk : 0 < k) :
    SingleEqFragmentZZ 2 k ⊂ RecFragmentZZ k ∧
      RecFragmentZZ k ⊂ REFragmentZZ k ∧
      REFragmentZZ k = PPFragmentZZ 2 k ∧
      PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k := by
  sorry

end DiophCompression
