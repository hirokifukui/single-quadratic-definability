/-
  DiophCompression/UnaryDiagonal.lean — APAL Structural Theory Gate 2, kernel item 必須B part 2
  (session 25, 2026-09-01, claude.ai direct, 0 CC).
  Coefficient-vector coding of degree-≤2 integer polynomials, the code-uniform Grunewald–Segal hypothesis
  (new Prop, implies the per-equation one), the diagonal relation (recursive under uniform GS, never SE_2),
  SE_2(k) ⊊ REC(k) for every k ≥ 1, and the full relation phase diagram at every positive arity.
  Statements frozen in frozen_statements/UnaryDiagonal_STATEMENTS.lean.
-/
import DiophCompression.HaltingTransport

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Variable codes -/

/-- Variable of a code: `n < k` reads as parameter `n`, `k ≤ n < k + r` as unknown `n - k`, else invalid. -/
def varOfCode (k r : ℕ) (n : ℕ) : Option (Fin k ⊕ Fin r) :=
  if h : n < k then some (Sum.inl ⟨n, h⟩)
  else if h' : n - k < r then some (Sum.inr ⟨n - k, h'⟩) else none

/-- Code of a variable. -/
def codeOfVar (k r : ℕ) (v : Fin k ⊕ Fin r) : ℕ := Sum.elim (fun i => i.val) (fun t => k + t.val) v

theorem varOfCode_codeOfVar (k r : ℕ) (v : Fin k ⊕ Fin r) : varOfCode k r (codeOfVar k r v) = some v := by
  rcases v with i | t
  · simp [varOfCode, codeOfVar, i.isLt]
  · simp [varOfCode, codeOfVar, t.isLt]

/-- The polynomial of a variable code: `X v`, or `1` for an invalid code. -/
noncomputable def varPoly (k r : ℕ) (n : ℕ) : Poly k r :=
  match varOfCode k r n with
  | none => 1
  | some v => X v

theorem varPoly_totalDegree_le_one (k r n : ℕ) : (varPoly k r n).totalDegree ≤ 1 := by
  unfold varPoly
  rcases varOfCode k r n with _ | v
  · simp
  · exact (totalDegree_X v).le

theorem varPoly_codeOfVar (k r : ℕ) (v : Fin k ⊕ Fin r) : varPoly k r (codeOfVar k r v) = X v := by
  unfold varPoly
  rw [varOfCode_codeOfVar]

/-! ### Monomials and polynomials from codes -/

/-- Monomial of a list of variable codes, truncated to length ≤ 2. -/
noncomputable def monPoly (k r : ℕ) (vs : List ℕ) : Poly k r := ((vs.take 2).map (varPoly k r)).prod

theorem list_prod_totalDegree_le (k r : ℕ) (L : List (Poly k r)) (h : ∀ q ∈ L, q.totalDegree ≤ 1) :
    L.prod.totalDegree ≤ L.length := by
  induction L with
  | nil => simp
  | cons q L ih =>
    simp only [List.prod_cons, List.length_cons]
    refine (totalDegree_mul _ _).trans ?_
    have h1 := h q (List.mem_cons_self ..)
    have h2 := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    omega

theorem monPoly_totalDegree_le_two (k r : ℕ) (vs : List ℕ) : (monPoly k r vs).totalDegree ≤ 2 := by
  refine (list_prod_totalDegree_le k r _ ?_).trans ?_
  · intro q hq
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hq
    exact varPoly_totalDegree_le_one k r n
  · rw [List.length_map]
    exact List.length_take_le 2 vs

/-- The polynomial of a code list: `Σ c · monomial`. -/
noncomputable def interpPoly (k r : ℕ) (L : List (List ℕ × ℤ)) : Poly k r :=
  (L.map fun t => C t.2 * monPoly k r t.1).sum

theorem interpPoly_totalDegree_le_two (k r : ℕ) (L : List (List ℕ × ℤ)) :
    (interpPoly k r L).totalDegree ≤ 2 := by
  unfold interpPoly
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (totalDegree_add _ _).trans (max_le ?_ ih)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C]
    simpa using monPoly_totalDegree_le_two k r t.1

/-- Every monomial of degree ≤ 2 is a `monPoly` (variables listed with multiplicity). -/
theorem prod_map_X_toMultiset (k r : ℕ) (m : (Fin k ⊕ Fin r) →₀ ℕ) :
    (m.toMultiset.map (X : Fin k ⊕ Fin r → Poly k r)).prod = monomial m (1 : ℤ) := by
  induction m using Finsupp.induction_linear with
  | zero => simp [monomial_zero']
  | add f g hf hg =>
    rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.prod_add, hf, hg, monomial_mul, mul_one]
  | single a n =>
    rw [Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.map_singleton, Multiset.prod_nsmul,
      Multiset.prod_singleton, X_pow_eq_monomial]

theorem exists_monPoly_eq_monomial (k r : ℕ) (m : (Fin k ⊕ Fin r) →₀ ℕ) :
    ∃ vs : List ℕ, (m.sum fun _ e => e) ≤ 2 → monPoly k r vs = monomial m 1 := by
  refine ⟨(m.toMultiset.map (codeOfVar k r)).toList, fun hm => ?_⟩
  have hlen : ((m.toMultiset.map (codeOfVar k r)).toList).length ≤ 2 := by
    rw [Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
    exact hm
  unfold monPoly
  rw [List.take_of_length_le hlen, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList,
    Multiset.map_map]
  have hcomp : varPoly k r ∘ codeOfVar k r = (X : Fin k ⊕ Fin r → Poly k r) := by
    funext v
    exact varPoly_codeOfVar k r v
  rw [hcomp]
  exact prod_map_X_toMultiset k r m

theorem interpPoly_surjective (k r : ℕ) (P : Poly k r) (hP : P.totalDegree ≤ 2) :
    ∃ L : List (List ℕ × ℤ), interpPoly k r L = P := by
  classical
  choose vs hvs using exists_monPoly_eq_monomial k r
  refine ⟨P.support.toList.map fun m => (vs m, coeff m P), ?_⟩
  unfold interpPoly
  rw [List.map_map, Finset.sum_map_toList]
  conv_rhs => rw [← support_sum_monomial_coeff P]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Function.comp]
  rw [hvs m ((le_totalDegree hm).trans hP), C_mul_monomial, mul_one]

/-! ### The code → polynomial map -/

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
  unfold decodePolyZZ
  rcases (Encodable.decode e : Option (ℕ × List (List ℕ × ℤ))) with _ | ⟨r, L⟩
  · simp
  · exact interpPoly_totalDegree_le_two k r L

/-- Every degree-≤2 polynomial has a code. -/
theorem decodePolyZZ_surjective (k r : ℕ) (P : Poly k r) (hP : P.totalDegree ≤ 2) :
    ∃ e : ℕ, decodePolyZZ k e = ⟨r, P⟩ := by
  obtain ⟨L, hL⟩ := interpPoly_surjective k r P hP
  refine ⟨Encodable.encode (r, L), ?_⟩
  unfold decodePolyZZ
  rw [Encodable.encodek]
  exact congrArg (Sigma.mk r) hL

/-! ### The code-uniform Grunewald–Segal hypothesis -/

/-- External hypothesis (Grunewald–Segal, code-uniform form): for every parameter arity `k`, solvability
    in ℤ of the quadratic equation with code `e` at parameters `a` is a decidable predicate of `(e, a)`. -/
def UniformQuadraticSolvabilityDecidableZZ : Prop :=
  ∀ k : ℕ, ComputablePred fun p : ℕ × (Fin k → ℤ) =>
    ∃ u : Fin (decodePolyZZ k p.1).1 → ℤ, evalAtZZ (decodePolyZZ k p.1).2 p.2 u = 0

theorem computablePred_sol_of_uniform (hU : UniformQuadraticSolvabilityDecidableZZ) (k e : ℕ) :
    ComputablePred fun a : Fin k → ℤ =>
      ∃ u : Fin (decodePolyZZ k e).1 → ℤ, evalAtZZ (decodePolyZZ k e).2 a u = 0 := by
  obtain ⟨g, hg, hp⟩ := ComputablePred.computable_iff.1 (hU k)
  refine ComputablePred.computable_iff.2 ⟨fun a => g (e, a), hg.comp ((Computable.const e).pair Computable.id), ?_⟩
  funext a
  exact congrFun hp (e, a)

/-- The uniform hypothesis implies the per-equation one. -/
theorem quadraticSolvabilityDecidable_of_uniform (hU : UniformQuadraticSolvabilityDecidableZZ) :
    QuadraticSolvabilityDecidableZZ := by
  intro k r P hP
  obtain ⟨e, he⟩ := decodePolyZZ_surjective k r P hP
  have h := computablePred_sol_of_uniform hU k e
  rw [he] at h
  exact h

/-! ### The diagonal relation -/

/-- The diagonal relation on ℤ^{k+1}: `v ∈ D` iff the quadratic equation coded by `v 0` has no integer
    solution at parameters `v`. -/
def diagonalSetZZ (k : ℕ) : Set (Fin (k + 1) → ℤ) :=
  {v | ¬ ∃ u : Fin (decodePolyZZ (k + 1) (Encodable.encode (v 0))).1 → ℤ,
      evalAtZZ (decodePolyZZ (k + 1) (Encodable.encode (v 0))).2 v u = 0}

/-- Conditional on uniform GS: the diagonal relation is recursive. -/
theorem diagonalSetZZ_computablePred (hU : UniformQuadraticSolvabilityDecidableZZ) (k : ℕ) :
    ComputablePred fun v => v ∈ diagonalSetZZ k := by
  obtain ⟨g, hg, hp⟩ := ComputablePred.computable_iff.1 (hU (k + 1))
  have hpair : Computable fun v : Fin (k + 1) → ℤ => (Encodable.encode (v 0), v) :=
    (Primrec.encode.comp (Primrec.fin_app.comp Primrec.id (Primrec.const 0))).to_comp.pair Computable.id
  have h1 : ComputablePred fun v : Fin (k + 1) → ℤ =>
      ∃ u : Fin (decodePolyZZ (k + 1) (Encodable.encode (v 0))).1 → ℤ,
        evalAtZZ (decodePolyZZ (k + 1) (Encodable.encode (v 0))).2 v u = 0 :=
    ComputablePred.computable_iff.2 ⟨_, hg.comp hpair, funext fun v => congrFun hp (Encodable.encode (v 0), v)⟩
  exact h1.not

/-- Unconditional: the diagonal relation is not SE_2-definable. -/
theorem diagonalSetZZ_not_singleQuadratic (k : ℕ) : ¬ WithinSingleEquationZZ 2 (diagonalSetZZ k) := by
  rintro ⟨r, P, hP, hrep⟩
  obtain ⟨e, he⟩ := decodePolyZZ_surjective (k + 1) r P hP
  set v : Fin (k + 1) → ℤ := fun _ => Denumerable.ofNat ℤ e with hv
  have henc : Encodable.encode (v 0) = e := Denumerable.encode_ofNat e
  have key : ∀ s : Σ r : ℕ, Poly (k + 1) r, s = ⟨r, P⟩ →
      ((∃ u : Fin s.1 → ℤ, evalAtZZ s.2 v u = 0) ↔ ∃ u : Fin r → ℤ, evalAtZZ P v u = 0) := by
    rintro s rfl
    exact Iff.rfl
  have h1 : v ∈ diagonalSetZZ k ↔ ¬ ∃ u : Fin r → ℤ, evalAtZZ P v u = 0 := by
    unfold diagonalSetZZ
    simp only [Set.mem_setOf_eq]
    rw [henc]
    exact not_congr (key _ he)
  have h2 := hrep v
  by_cases hs : ∃ u : Fin r → ℤ, evalAtZZ P v u = 0
  · exact h1.1 (h2.2 hs) hs
  · exact hs (h2.1 (h1.2 hs))

/-! ### Strictness and the phase diagram -/

/-- Conditional on uniform GS: SE_2(k) ⊊ REC(k) at every positive arity. -/
theorem singleQuadratic_strict_recursive_all_positive_arity (hU : UniformQuadraticSolvabilityDecidableZZ)
    (k : ℕ) : SingleEqFragmentZZ 2 (k + 1) ⊂ RecFragmentZZ (k + 1) := by
  rw [Set.ssubset_def]
  refine ⟨singleEqFragmentZZ_two_subset_recFragmentZZ (quadraticSolvabilityDecidable_of_uniform hU) _,
    fun hsub => ?_⟩
  have hmem : diagonalSetZZ k ∈ RecFragmentZZ (k + 1) := diagonalSetZZ_computablePred hU k
  exact diagonalSetZZ_not_singleQuadratic k (hsub hmem)

/-- Conditional on uniform GS: SE_2(1) ⊊ REC(1). -/
theorem unary_singleQuadratic_strict_recursive (hU : UniformQuadraticSolvabilityDecidableZZ) :
    SingleEqFragmentZZ 2 1 ⊂ RecFragmentZZ 1 :=
  singleQuadratic_strict_recursive_all_positive_arity hU 0

/-- The relation phase diagram at every positive arity (uniform GS + DPRM):
    SE_2(k) ⊊ REC(k) ⊊ RE(k) = PP_2(k) = SE_4(k). -/
theorem relation_phase_diagram_all_positive_arity (hU : UniformQuadraticSolvabilityDecidableZZ)
    (hD : DPRM_ZZ) {k : ℕ} (hk : 0 < k) :
    SingleEqFragmentZZ 2 k ⊂ RecFragmentZZ k ∧
      RecFragmentZZ k ⊂ REFragmentZZ k ∧
      REFragmentZZ k = PPFragmentZZ 2 k ∧
      PPFragmentZZ 2 k = SingleEqFragmentZZ 4 k := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  exact ⟨singleQuadratic_strict_recursive_all_positive_arity hU k',
    recursive_strictly_contained_re k', (ppQuadratic_eq_re_of_DPRM hD _).symm,
    (singleEqFragmentZZ_four_eq_ppFragmentZZ_two _).symm⟩

#print axioms DiophCompression.decodePolyZZ_totalDegree_le_two
#print axioms DiophCompression.decodePolyZZ_surjective
#print axioms DiophCompression.quadraticSolvabilityDecidable_of_uniform
#print axioms DiophCompression.diagonalSetZZ_computablePred
#print axioms DiophCompression.diagonalSetZZ_not_singleQuadratic
#print axioms DiophCompression.singleQuadratic_strict_recursive_all_positive_arity
#print axioms DiophCompression.unary_singleQuadratic_strict_recursive
#print axioms DiophCompression.relation_phase_diagram_all_positive_arity

end DiophCompression
