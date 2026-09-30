**Author.** Hiroki Fukui (Research Institute of Criminal Psychiatry / Sex Offender Medical Center, Tokyo, Japan; Department of Neuropsychiatry, Kyoto University, Kyoto, Japan).

**Funding.** This research did not receive any specific grant from funding agencies in the public, commercial, or not-for-profit sectors. **Competing interests.** The author declares no known competing financial interests or personal relationships that could have appeared to influence the work reported in this paper.

**Keywords.** Diophantine definability; existential fragments; quadratic equations; finite fibres; definable functions; computability.

**MSC 2020.** Primary 03D25; Secondary 11D09, 11U05, 03B35, 11Y50, 68V15.

**Abstract.** Let SE₂ be the class of relations on ℤᵏ definable by a *single* polynomial equation of total degree at most two, with unrestricted integer unknowns.

Under a published input on ternary lattice cosets, f : ℤⁿ → ℤᵐ with two or more outputs is SE₂-definable exactly when f(a + Mt) = f(a) + Bt for a modulus M and an integer matrix B; a scalar function, exactly when it has this form, agrees with a rational polynomial of degree at most two, or is half the even one of two integer affine forms of opposite parity. The converses and the case without unknowns need no such input.

Finite fibres lie in a box of quadratic height and have polynomially bounded cardinality, with one constant depending on the equation alone; definable total functions therefore grow at most quadratically; they are computable; they are not closed under composition. SE₂-definable injections ℤⁿ → ℤᵐ satisfy n ≤ m, and this is sharp.

Unconditionally, with one constant C for all parameter points, each scalar fibre is bounded by C(1+‖a‖∞)² or carries a certificate pinning an infinite output subset of one of three forms: polynomial progressions, Pell-unit orbits, moving-modulus step orbits.

Two published results enter as named hypotheses: Grunewald–Segal decidability of quadratic solvability (code-uniform) and DPRM over ℕ. They give SE₂ ⊊ REC ⊊ RE = PP₂ = SE₄ at every positive arity. Sections 2–9 are formalized in Lean 4, as is Section 10 except Lemma 10.8, with the ternary input as an explicit hypothesis.

---

## Introduction

**The problem.** Fix a single polynomial equation P(a, u) = 0 with integer coefficients, of total degree at most two in the parameters a ∈ ℤᵏ and the unknowns u ∈ ℤʳ together, and ask which relations on ℤᵏ it can define by existential projection: a ∈ A if and only if some integer vector u satisfies P(a, u) = 0. The class of such relations, over all r and all P of total degree at most two, is the single-quadratic existential fragment SE₂(k). Nothing restricts the number of unknowns, so the fragment is not small: it contains every non-semilinear set that a single quadratic can carve out, and its fibres already include Pell-type infinite orbits. The question studied here is how much this one degree bound constrains the fragment, and where the fragment sits between the classes it is squeezed between.

**The boundary it lies on.** Two classical results frame the question. Solvability of a single quadratic equation in integers is decidable (Grunewald–Segal [GS04]), so a single quadratic atom cannot encode an undecidable relation. On the other side, every recursively enumerable relation is Diophantine (Davis–Putnam–Robinson–Matiyasevich [DPR61, Mat70]), and Skolem's degree reduction [Sko38] turns any polynomial equation into a system of quadratics, or into a single quartic. So the passage from *one* quadratic equation to a primitive-positive system of quadratics — equivalently, to a single equation of degree four — crosses from a decidable class to the whole of the recursively enumerable relations. The fragment SE₂ sits on that boundary, and this paper is about what happens there: although the fragment already supports non-semilinear behaviour and Pell-type infinite orbits, its finite fibres and total functions satisfy uniform polynomial restrictions, and total degree and formula shape jointly control fibre structure, functional growth, closure under composition, and computability.

**Main result: the functions one quadratic equation defines.** A total function f : ℤⁿ → ℤᵐ is SE₂-definable when its graph is. Say that f has a *common slope* if there are M ≥ 1 and an integer m × n matrix B with f(a + Mt) = f(a) + Bt for all a, t ∈ ℤⁿ: one rational slope B/M on every residue class modulo M. Assume TCER, an eventual representation property of positive definite ternary lattice cosets that follows from published work of Kane and Kim (Lemma 10.8). Then a function with two or more outputs is SE₂-definable exactly when it has a common slope (Proposition 10.9). A function f : ℤⁿ → ℤ is SE₂-definable exactly when it has a common slope, or agrees on ℤⁿ with a polynomial with rational coefficients of total degree at most two, or there are integer vectors p, q and integers c, c', with p - q having even coordinates, p having an odd coordinate and c - c' odd, such that 2f(a) = p · a + c when p · a + c is even and 2f(a) = q · a + c' otherwise (Proposition 10.14). The three families overlap, and none of them can be dropped. The converse constructions use no analytic input, and neither does the case without unknowns, where exactly the last two families occur (Proposition 10.16). The classification is proved in Section 10. The sharp bound n ≤ m for SE₂-definable injections (Theorem 4.1) keeps its own proof, which uses no analytic input.

**Finite fibres.** The first group of results says that a single quadratic cannot spread a finite fibre far. For every P of total degree at most two there is one constant C, depending on P alone, such that whenever the fibre over a parameter point a is finite, every element of it has sup-norm at most C·N², where N bounds ‖a‖_∞ (Theorem 2.1), and the fibre has at most (2CN² + 1)ᵐ elements (Theorem 2.2) — the same constant serving both bounds. The uniformity in a is the point: the bound is not a search bound for the equation in front of us but a single constant valid at every parameter point, which is what the rest of the paper rests on.

**Definable functions.** A total function f : ℤⁿ → ℤᵐ is SE₂-definable when its graph is. The finite-fibre bound forces such functions to grow at most quadratically (Theorem 3.2); they are computable (Theorem 3.3); and they are not closed under composition, since x ↦ x² is definable while x ↦ x⁴ is not (Theorem 3.4). An SE₂-definable injection ℤⁿ → ℤᵐ must satisfy n ≤ m (Theorem 4.1), and conversely one exists whenever n ≤ m (Theorem 4.3), so no single quadratic defines the graph of an injection ℤⁿ → ℤ for n ≥ 2 and the one-sorted coding arity is exactly one; and an integer polynomial has SE₂-definable graph exactly when its total degree is at most two (Theorem 5.1). The growth bound and the non-closure follow from the same constant C; that constant alone gives only n ≤ 2m for injections (Remark 4.5), and the sharp bound n ≤ m comes from the structural alternative of Theorem 4.2 — a box count on the linear-growth side and a collision f(ρ + Mv) = f(ρ − Mv) on the coset side.

**Normal forms.** Beyond growth, the equation fixes the shape of a definable function. Theorem 4.2 gives every SE₂-definable total function linear growth or a weak vector coset normal form. The full form --- one modulus and, on every residue class, a vector quadratic polynomial --- holds unconditionally except when the quadratic part in the unknowns is semidefinite of polar rank at least three, and everywhere under one analytic input, TCER, the eventual representation of large integers by an individual positive definite ternary lattice coset (\cref{proposition:10.6,proposition:10.7}). TCER is a consequence of published work on theta series of lattice cosets (Lemma 10.8) and enters the formal development as an explicit hypothesis. With at least two outputs the branch proofs give the common slope of the main result. Consequently a ↦ (a², 0) is not SE₂-definable under TCER although a ↦ a² is (Proposition 10.10), while a full form alone does not yield a common slope (Proposition 10.11). Appending a zero output keeps a function SE₂-definable exactly when it has a common slope (Proposition 10.15).

**Infinite fibres: finite or structured.** The second group describes the infinite fibres positively. Theorem 8.5 asserts, unconditionally and with one constant C for all parameter points, that every scalar fibre of every equation of total degree at most two is either bounded by C(1 + ‖a‖_∞)² or carries a structured certificate: arithmetic data of one of three kinds — a polynomial progression, a Pell-unit orbit, or a moving-modulus step orbit — that generates an infinite subset of the fibre and is represented in the formalization by a typed realization whose fields witness an infinite arithmetic output subset. The certificate pins an infinite output subset, not the whole fibre, and the three kinds are a sufficient language rather than a classification. The engine behind both groups of results is an arithmetic projection dichotomy for homogeneous quadratic forms (\cref{theorem:9.2,theorem:9.3}): for a fixed form, the set of natural numbers c admitting an integer witness of an affine perturbation is either infinite or bounded by a constant depending on the form alone.

**The computability phase diagram.** Combining the structural results with the two classical inputs places the fragment exactly. Under code-uniform decidability of quadratic solvability and DPRM over ℕ,

  SE₂(k) ⊊ REC(k) ⊊ RE(k) = PP₂(k) = SE₄(k) for every k ≥ 1,

and, for total functions, Fun(SE₂) ⊊ TotComp = Fun(PP₂) = Fun(SE₄) at every positive input and output arity (\cref{theorem:6.8,theorem:7.1}). At arity zero all five classes coincide, which is why every strictness statement carries an arity hypothesis. Two of the arrows are proved without either input: REC ⊊ RE (Theorem 6.1) and Fun(SE₂) ⊊ TotComp (Theorem 3.5); the inclusion SE₂ ⊆ REC uses the quadratic-solvability principle, and the equalities with PP₂ and SE₄ use DPRM. The strictness SE₂ ⊊ REC at arity one is the delicate arrow: it needs the uniform, code-level form of decidability, and is obtained by an effective diagonalization over a coded family (Theorem 6.5, Corollary 6.6).

**What is new and what is used.** We separate the contributions by kind, so that a reader can see at once what this paper claims and what it takes from the literature.

- *Core mathematical novelty candidates.* The uniform finite-fibre height and cardinality bounds with a single constant (\cref{theorem:2.1,theorem:2.2}); quadratic growth of SE₂-definable functions (Theorem 3.2) and their non-closure under composition as a structural consequence (Theorem 3.4); the sharp injective dimension theorem n ≤ m with its converse (\cref{theorem:4.1,theorem:4.3}) and the structural alternative behind it (Theorem 4.2); the graph classification graph(p) ∈ SE₂ ⟺ deg p ≤ 2 (Theorem 5.1); the unconditional finite-or-structured theorem (Theorem 8.5); and the arithmetic projection dichotomy in bounded and data-carrying form for every number of unknowns (\cref{theorem:9.2,theorem:9.3}). We call them candidates because our literature search (Section 11) found no statement containing them, not because novelty has been externally adjudicated.
- *Definable functions.* Under TCER, the exact characterization of the SE₂-definable total functions: a common slope for two or more outputs (Proposition 10.9), three families for one output (Proposition 10.14), with converse constructions that need no analytic input; the case without unknowns, unconditionally (Proposition 10.16); the padding criterion (Proposition 10.15) and presentations with unique unknowns (Proposition 10.17); and the reduction of the full vector coset normal form to the nonzero semidefinite case (Proposition 10.6), within which polar rank at most two is settled without further input, with the full form under TCER (Proposition 10.7). The components are known or elementary: the one-hot quadratic penalty behind the converse, the rigidity of square-valued quadratic forms (Lemma 10.4) and the two-coset lemma (Lemma 10.13); what is added is the characterization of the functions, compared with Presburger-definable functions in Section 11. TCER is taken from published work (Lemma 10.8).
- *Standard logical consequences and new synthesis.* The computability of SE₂-definable total functions from a total single-valued c.e. graph (Theorem 3.3) and the exactness of Fun(SE₂) ⊊ TotComp by arity (Theorem 3.5); the effective diagonalization over a coded family and its arity-one consequence (\cref{theorem:6.5,corollary:6.6}), a standard argument made effective here by the code bridge; Skolem's degree reduction PP₂ = SE₄ = Dioph (Theorem 6.2), the transport of DPRM from ℕ to ℤ (Theorem 6.7), the code bridge from our finite quadratic codes to the coefficient-table input of [GS04] (Theorem 6.4), and the exact relation and function phase diagrams (\cref{theorem:6.8,theorem:7.1}). These are known arrows or standard arguments assembled into one exact picture; the arrows are not claimed as new, the exactness of the picture is.
- *Classical inputs.* Decidability of integer quadratic solvability in its code-uniform form (Definition 1.5, after [GS04]) and DPRM over ℕ (Definition 1.6), the theorem of [DPR61, Mat70]. Both are published results; they enter as explicit named hypotheses of the theorems that use them, and neither is an axiom of the formalization.
- *Formalization contributions.* The typed certificate language with per-kind soundness (\cref{definition:8.2,theorem:8.3}), the quadratic-code and DPRM transport layers, and the Lean development itself: Sections 2–10 and Appendix C are Lean 4 declarations checked against mathlib, Section 10 with TCER as an explicit hypothesis and apart from Lemma 10.8; every statement in the statement-fidelity registry is frozen and diffed against the development, every root's axiom footprint is within the standard three, and the artifact ships the checks that recompute these facts (Section 12).

**Proof strategy.** Everything on the finite side flows from one decomposition and one dichotomy. A polynomial of total degree at most two in (a, u) is H(c, u) + Σ ℓᵢ(a)·xᵢ + q(a), with H the homogeneous quadratic component in the output-and-witness variables and only the affine part depending on the parameter (Section 2). The arithmetic projection dichotomy (Section 9, proved in full in Appendix F) says that for a fixed H the set of c admitting a witness for any affine perturbation is either infinite or bounded by K·((1 + Σ|ℓ_i|)² + |q|) — a constant K depending on H alone, times a quadratic height in the affine data (ℓ, q) (Definition 9.1); the constant K is not effective, and Section 12 and the trust document say so. Applied to the fibre equation this gives Theorem 2.1 at once, and the growth and non-closure consequences for functions follow by reading the graph of f as a fibre. The sharp injective bound n ≤ m of Theorem 4.1 does not follow from the fibre bound alone: it needs the structural alternative of Theorem 4.2, a box count on the linear-growth side and a collision f(ρ + Mv) = f(ρ − Mv) on the coset side. The infinite side is the same dichotomy in data-carrying form: where the projection is infinite, the proof produces the certificate rather than merely asserting infinitude, and the three kinds capture three recurring arithmetic mechanisms emitted across the proof branches (Remark 8.8). The computability side is diagonalization over an explicitly coded family, made effective by the code bridge.

**Organization.** Section 1 fixes the fragments SE₂, REC, RE, PP₂, SE₄ and the two external inputs. Sections 2–5 prove the finite-fibre bounds and their consequences for functions, injections and polynomial graphs. Sections 6 and 7 assemble the relation and function phase diagrams. Section 8 introduces structured certificates and proves the finite-or-structured theorem; Section 9 states the arithmetic projection dichotomy that drives it. Section 10 proves the normal forms and the classification of definable functions. Section 11 places the results against the literature, and Section 12 describes the formalization and what it does and does not certify. Appendix A collects open problems; Appendices B–D collect capacity refinements, the multi-parameter universal-pair question that motivated the fragment, and technical lemmas; Appendix E is the statement map from paper labels to Lean names; Appendix F is the complete proof of the projection dichotomy.

## 1. Fragments: SE₂, REC, RE, PP₂, SE₄

**Setting.** Parameters and unknowns are integers. For k, r ∈ ℕ write Poly k r := MvPolynomial (Fin k ⊕ Fin r) ℤ and, for P ∈ Poly k r, a ∈ ℤᵏ, u ∈ ℤʳ, evalAtZZ P a u := P(a, u). A polynomial *represents* A ⊆ ℤᵏ when a ∈ A ⟺ ∃ u ∈ ℤʳ, P(a,u) = 0 (`RepresentsZZ`).

**Definition 1.1** (`OneSortedFragments.lean`). For d, k ∈ ℕ:

- WithinSingleEquationZZ d A :⟺ ∃ r, ∃ P ∈ Poly k r, totalDegree P ≤ d ∧ P represents A; SE_d(k) := {A | WithinSingleEquationZZ d A}.
- WithinPPZZ d A :⟺ ∃ r m, ∃ S : Fin m → Poly k r, (∀ i, totalDegree (S i) ≤ d) ∧ (a ∈ A ⟺ ∃ u, ∀ i, S i (a,u) = 0); PP_d(k) := {A | WithinPPZZ d A}.
- REC(k) := {A | ComputablePred (· ∈ A)}, RE(k) := {A | REPred (· ∈ A)} (mathlib `Mathlib.Computability`), through the `Primcodable (Fin k → ℤ)` instance.
- Dioph(k) := {A | ∃ r P, P represents A} (no degree bound).

The number of unknowns r is existentially quantified and never bounded: the fragment is cut out by the *degree* alone. This is the opposite convention to the existential-rank literature, which bounds the number of unknowns and leaves the degree free; the two conventions are orthogonal in intent. We prove no comparison between the two hierarchies in either direction, and none is claimed.

**Proposition 1.2** (unconditional lattice; `FragmentLattice.lean`, `singleEqFragmentZZ_subset_ppFragmentZZ`, `singleEqFragmentZZ_subset_diophFragmentZZ`, `fragment_lattice_ZZ`). For every k and every d: SE_d(k) ⊆ PP_d(k) ⊆ Dioph(k) (the two generic inclusions; `fragment_lattice_ZZ` is the d = 2 chain); SE₄(k) = PP₂(k) = Dioph(k) (`singleEqFragmentZZ_four_eq_ppFragmentZZ_two`, `singleEqFragmentZZ_four_eq_diophFragmentZZ`).

*Proof.* A finite system S₁ = … = S_m = 0 over ℤ has the same solutions as the single equation ΣS_i² = 0, of degree at most 2d; with d = 2 this lands in SE₄. Conversely, Skolem's reduction replaces every monomial of degree ≥ 3 by a fresh unknown together with a quadratic defining equation, so any Diophantine set is PP₂; iterating the reduction terminates because each step strictly decreases the multiset of monomial degrees. ∎

**Proposition 1.3** (`ComputabilityFragments.lean`). SE_d(k) ⊆ RE(k) and PP_d(k) ⊆ RE(k) for every d, unconditionally (`singleEquation_relation_re`, `ppRelation_re`; the degree-four and degree-two cases are `singleQuartic_relation_re` and `ppQuadratic_relation_re`): witness search by `Nat.rfind` over a primitive-recursive solution checker (`primrec₂_solCheck`). REC(k) ⊆ RE(k) (`recFragmentZZ_subset_reFragmentZZ`).

*Proof.* For SE_d, let A be represented by P ∈ Poly k r. The predicate (a, u) ↦ (P(a,u) = 0) is primitive recursive: evaluating a fixed integer polynomial is a composition of additions and multiplications, and equality on ℤ is decidable. Since ℤʳ is `Primcodable`, the unbounded search `Nat.rfind` over the codes of witnesses halts on a exactly when some u is a root, so membership is r.e. For PP_d the checker tests the finitely many equations of the system instead of one, which is again primitive recursive, and the same search applies. REC(k) ⊆ RE(k) is the standard fact that a decidable predicate is r.e. ∎

**Proposition 1.4** (Arity zero; `ArityZeroFragments.lean`, `relation_phase_diagram_arity_zero`). ℤ⁰ is a singleton, so every relation is ∅ or univ; all five classes coincide and equal the full power set (`relation_phase_diagram_arity_zero`, unconditional). All strictness statements below are therefore stated for positive arity. This is not a triviality to be waved away: it is the reason every exactness statement in Sections 6 and 7 carries an arity hypothesis, and a phase diagram asserted "for all arities" would be false as stated.

*Proof.* ℤ⁰ has exactly one element, so 𝒫(ℤ⁰) = {∅, univ}; univ is represented by the equation 0 = 0 and ∅ by 1 = 0, both of total degree at most two and with no witnesses, and both sets are decidable and r.e. So the five classes all equal the full power set, and no strictness statement can hold at arity zero. ∎

This paper has two load-bearing external inputs, together with one auxiliary proposition derived from them. Skolem's degree reduction is *not* an external input: it is proved here (Theorem 6.2). The named propositions are the following. Each is a `def … : Prop` in the formalization and appears as an explicit hypothesis wherever it is used; none is an axiom, so no result silently depends on any of them.

**Definition 1.5** (Grunewald–Segal, code-uniform form; `QuadraticCodes.lean`). A *quadratic code* is a pair c = (r, T) with r ∈ ℕ the witness arity and T a finite list of terms (coefficient, at most two variable codes); it is an explicit finite datum, and the type of codes is `Primcodable`. The evaluation of a code at parameters a and an unknown list u reads variable code i as the i-th entry of the environment list ofFn a ++ u, out-of-range codes as 1, absent factors as 1 (`QuadraticCode.evalZZ`). The code c is *solvable at a* if some u of length r is a root (`QuadraticCode.solvableZZ`). We set

  UniformQuadraticSolvabilityOnCodes :⟺ ∀ k, ComputablePred (fun (c, a) ⇒ c solvable at a).

The Grunewald–Segal procedure yields this hypothesis after an effective translation from our finite quadratic code to the coefficient-table representation it takes as input; what Definition 1.5 records is that coding-equivalent consequence, not their statement. The shape is the same on both sides — a coefficient table and a witness arity in, a yes/no answer out, uniformly in the table — but we do not assert that the two inputs are the same object. The citation needs care. The 1981 note [GS81] is, in its authors' own description, a sketch of an effective procedure for an arbitrary quadratic equation with rational coefficients; the algorithm is presented in full in [GS04], and it is there that the input is stated to be an equation *in arbitrarily many unknowns*, which is the generality our fragment requires. We therefore cite [GS04] as the source of Definition 1.5 and [GS81] as its announcement. Two things should be said precisely about this hypothesis. First, we do not claim that our coding is theirs: Theorem 6.4 supplies the compiler that turns an instance in our form into a parameter-free coefficient table, and Theorem 6.4(f) shows that this compiler is primitive recursive, so the *translation* of inputs is effective. Second, the hypothesis is uniformity of the decision procedure in the table. We isolate this code-uniform quadratic-solvability principle as an explicit external hypothesis. The published abstract of [GS04] describes an algorithm that takes an arbitrary quadratic equation as its input, which supports the required generality; we have not audited the body of [GS04] against Definition 1.5, and every result below that depends on the definition remains explicitly conditional on the principle as stated there. Theorem 6.4(f) does not establish uniformity and is not asked to; it establishes that the translation between our instance form and that input is effective. We therefore state Definition 1.5 as the classical input in its uniform form, and we do not claim to have derived uniformity from per-equation decidability.

Three conventions must be matched before the two statements can be compared at all, and we record how each is handled. *Coefficients.* [GS04] admits rational coefficients; a quadratic code carries integer ones. Multiplying an equation through by a common denominator changes neither its solution set nor its total degree, so the instances we compile are a subclass of theirs and no clearing step is needed in the direction we use. *Unknowns.* Ours range over ℤ. The headline statement of [GS04] concerns solutions in positive integers, so the convention must be addressed rather than assumed away, and it is addressed by [GS04] itself: the algorithm there is stated for integral solutions constrained to a region bounded by an arbitrary finite collection of rational affine hyperplanes, and the empty collection gives unrestricted integral solutions. The ℤ form is thus part of what is claimed, not something we reconstruct. [GS81] states the integer case directly, but describes itself as a sketch, which is why we cite [GS04] as the source. Independently of both, the substitution u = u⁺ − u⁻ with u⁺, u⁻ ≥ 1 carries integer solutions to positive ones and back, doubling the number of unknowns and leaving the degree at two; the number of unknowns is unrestricted in our fragment, so nothing we assert would fail under the other convention either. *Arity.* The witness arity is part of the code, so within each fixed parameter arity k the decider of Definition 1.5 is uniform in the code and hence in the witness arity. The ∀ k of Definition 1.5 quantifies over the parameter arity outside \textrm{ComputablePred}: it asserts, for each fixed k, one decider uniform in the finite quadratic code and the parameter tuple, and it does not assert a single algorithm uniform in k. The development also formalizes the global form — one decider on the sigma-coded instance type of codes paired with parameter lists (`GlobalQuadraticSolvabilityDecidable`) — and proves that it implies Definition 1.5 (`globalGS_implies_uniformGS`); the hypothesis used in this paper is therefore the weaker, fixed-arity form, and every result conditional on it holds a fortiori under the global principle.

The clause-by-clause crosswalk from [GS04] to Definition 1.5 is `literature/GS_CROSSWALK.md` in the artifact, with the level of evidence recorded row by row. One point from it belongs here. [GS04] states a decision procedure, not a bound: it lists a finite solution set and reports infinitude otherwise, and its auxiliary result on the density at infinity of the translates of a rational point is qualitative. That reading is corroborated from outside: [Die03], appearing a year earlier, records that for s = 3 and s = 4 no polynomial bounds were then known. So the non-effectivity in Remark 2.3 is not a bound we have declined to look up; it reflects the state of the line we are citing.

**Definition 1.6** (DPRM over ℕ; `DPRMTransport.lean`). WithinDiophNN A :⟺ ∃ s, ∃ P ∈ Poly k s, ∀ a ∈ ℕᵏ, a ∈ A ⟺ ∃ y ∈ ℕˢ, P(a,y) = 0 (integer coefficients, natural unknowns); DPRM_NN :⟺ ∀ k A, REPred (· ∈ A) → WithinDiophNN A. This is the theorem of [DPR61, Mat70] in its standard form.

**Definition 1.7** (auxiliary, derived). QuadraticSolvabilityDecidableZZ (per-equation decidability) and DPRM_ZZ (every r.e. relation on ℤᵏ is Dioph) are *consequences* of \cref{definition:1.5,definition:1.6} (\cref{theorem:6.4,theorem:6.7}); they are kept as intermediate hypotheses so that each result can name the weakest input it actually uses.

## 2. Finite-fibre height and cardinality

Write fiberVecZZ P a := {b ∈ ℤᵐ | ∃ u, P(a ++ b, u) = 0} for P ∈ Poly (n+m) r, and fiberZZ P a for the scalar case m = 1.

**Theorem 2.1** (uniform finite-fibre height; `FiniteFiberGrowth.lean`, `singleQuadratic_finiteFiber_height_vector`). Let P ∈ Poly (n+m) r with totalDegree P ≤ 2. There is C ∈ ℕ such that for all N ≥ 1 and all a ∈ ℤⁿ with ‖a‖_∞ ≤ N: if fiberVecZZ P a is finite, then every b in it satisfies ‖b‖_∞ ≤ C·N².

**Theorem 2.2** (finite-fibre cardinality; `FiniteFiberCardinality.lean`, `singleQuadratic_finiteFiber_cardinality_vector`). With the same P, there is C ∈ ℕ such that simultaneously FiberHeightBoundVecZZ P C and FiberCardBoundVecZZ P C hold, the latter meaning: for N ≥ 1 and ‖a‖_∞ ≤ N, a finite fibre has at most (2CN² + 1)ᵐ elements. The constant is the same C (the cardinality bound is the box count of the height bound: `fiberCardBoundVec_of_fiberHeightBoundVec`).

*Proof of Theorem 2.1.* We first treat the scalar case m = 1 (`singleQuadratic_finiteFiber_height_scalar`) and then reduce the vector case to it.

Fix P ∈ Poly (n+1) r of total degree at most two and a parameter point a ∈ ℤⁿ. Relabel the variables so that the output coordinate c and the r unknowns u form one block of r+1 variables and the parameters form the other (`relabelG`, `eval_relabelG_ZZ`); the relabelled polynomial has total degree at most two, since renaming variables cannot raise the degree. Splitting it into homogeneous components in the block (c, u) and specialising the parameters at a gives

P(a, c, u) = H(c,u) + Σ_i ℓ_i(a)·x_i + q(a),

where H is the homogeneous quadratic component in the r+1 variables x = (c, u) (possibly the zero polynomial), each ℓᵢ is a polynomial of degree at most one in a, and q has degree at most two in a (`normal_form_general_quadratic`). The point of the decomposition is that H does not depend on a: as the parameter point moves, only the affine part of the fibre equation moves, and it moves polynomially.

Now apply the arithmetic projection dichotomy of Section 9 (Theorem 9.2) to the homogeneous form H. It supplies a constant K, depending on H alone, such that for every affine datum (ℓ, q) the set of natural numbers c admitting an integer witness u with H(c,u) + ℓ·(c,u) + q = 0 is either infinite or bounded above by

fboundG K ℓ q = K·((1 + Σ_i|ℓ_i|)² + |q|).

Applying this to H, and to its reflection in the output coordinate (`flipZero H`, still homogeneous of degree two), covers the negative half of the fibre as well; the two constants are combined into one. If the fibre is finite, the infinite horn of the dichotomy is impossible on both halves, so every c in the fibre satisfies |c| ≤ fboundG (K₁+K₂) ℓ(a) q(a).

It remains to bound that expression in terms of N. Each ℓᵢ has degree at most one and q degree at most two in a, so on the box ‖a‖_∞ ≤ N their values are bounded by SL·N and SQ·N² for constants SL, SQ depending only on the coefficient sizes of P (`eval_abs_le_int`), whence fboundG (K₁+K₂) ℓ(a) q(a) ≤ C·N² with C := (K₁+K₂)·((1+SL)² + SQ) (`fboundG_box_le`). This proves the scalar case, and the constant depends only on P.

For the vector case, fix a coordinate j and consider the polynomial obtained by keeping the j-th output coordinate as the output and moving the remaining m−1 output coordinates into the block of unknowns (`coordPoly`). This does not change the total degree, and a point b of the vector fibre yields, for each j, a point b_j of the scalar fibre of coordPoly j (`mem_fiberZZ_coordPoly`). A finite vector fibre has finite scalar projections, so the scalar bound applies to each coordinate with a constant C_j; taking C to be the maximum over the finitely many j gives the statement. ∎

*Proof of Theorem 2.2.* Given the height bound, a finite fibre is contained in the box of side 2CN²+1 centred at the origin in ℤᵐ, which has (2CN²+1)ᵐ lattice points (`ncard_le_of_abs_le_vec`). No new constant is needed. ∎

**Remark 2.3** (on effectivity). The constant C is not claimed to be effective in Theorem 2.1, and the proof above shows precisely where effectivity would have to come from. The parameter-dependent part is completely explicit: SL and SQ are read off the coefficients of P, and the passage from fboundG to C·N² is elementary. The one non-explicit ingredient is K, the constant supplied by the projection dichotomy for the homogeneous form H. The paper proves that K exists; it does not prove an algorithm that computes K, or C, from the coefficients of P, and no such algorithm is claimed. We therefore state \cref{theorem:2.1,theorem:2.2,theorem:3.2,theorem:4.1} with a non-effective constant, and we do not use effectivity anywhere. Nothing in Sections 6 and 7 depends on it, and it is worth separating four things that are easy to run together. The finite-fibre theorem gives a non-effective structural bound. The computability of SE₂-definable *total functions* (Theorem 7.1) uses neither that bound nor any external input: totality plus a Diophantine graph makes a dovetailed search terminate. The recursiveness of SE₂ *relations* (Section 6) uses Definition 1.5, since positive search settles membership but not its complement. Uniformity in the code is not a convenience there: a decision procedure supplied one equation at a time would give each fixed relation as recursive, but the diagonalization of Theorem 6.5, which is what separates SE₂ from REC at arity one, quantifies over a coded family and needs the decision to be uniform in the code. The certificates of Section 8 assert the existence of a structured output subset, with witnesses selected non-effectively. A non-effective bound terminates no search, and we nowhere ask it to.

**Remark 2.4** (worst case, not sharp). The exponent 2 is attained (b − a² = 0) but the bound is not sharp in general: for x·y = a with a ≠ 0 the finite fibre lies in [−N, N], and for b² = a it lies in [−√N, √N]. The theorem is a uniform worst-case bound; the sharp exponent as a function of the shape of P is not studied here.

## 3. Definable total functions

**Definition 3.1** (`FiniteFiberGrowth.lean`, `ComputableFunctions.lean`). For f : ℤⁿ → ℤᵐ, graphVecZZ f := {v ∈ ℤⁿ⁺ᵐ | (v_{n+j})_j = f((v_i)_i)}. f is SE₂-definable (SingleQuadraticDefinableFunctionZZ) if graphVecZZ f ∈ SE₂(n+m); PP₂-definable, SE₄-definable likewise; TotalComputableFunctionZZ f :⟺ Computable f.

**Theorem 3.2** (quadratic growth; `singleQuadratic_function_quadratic_growth`). If f is SE₂-definable there is C ∈ ℕ with |f(a)_j| ≤ C·N² for all N ≥ 1, ‖a‖_∞ ≤ N, all j.

*Proof.* The fibre of graphVecZZ f over a is the singleton {f(a)} (`fiberVecZZ_eq_singleton_of_represents`), hence finite; apply Theorem 2.1. ∎

**Theorem 3.3** (`singleQuadratic_total_function_computable`, `ppQuadratic_total_function_computable`). SE₂- and PP₂-definable total functions are computable (witness search on the graph, then read off the unique output).

*Proof.* Let f : ℤⁿ → ℤᵐ be total with graphVecZZ f ∈ SE₂(n+m), represented by P with witness arity r: (a, b) ∈ graph ⟺ ∃u ∈ ℤʳ, P(a, b, u) = 0. Given a, search over the codes of pairs (b, u) ∈ ℤᵐ × ℤʳ, which is `Primcodable`, testing the primitive recursive predicate P(a,b,u) = 0. Totality of f guarantees that some pair satisfies it, so the search terminates; and the graph is the graph of a function, so the b returned is f(a) regardless of which pair is found first. Hence f is computable. The PP₂ case is identical with the system in place of the single equation. Two things are not used and should be named: no height bound and no classical input. Termination comes from totality, and correctness from functionality of the graph. ∎

**Theorem 3.4** (composition; `ppQuadratic_functions_closed_under_composition`, `singleQuadratic_functions_not_closed_under_composition`). PP₂-definable functions are closed under composition (the intermediate vector is carried as fresh witnesses, `compSys`). SE₂-definable functions are not: x ↦ x² is SE₂-definable but x ↦ x⁴ is not, since quartic growth contradicts Theorem 3.2. The ℤ → ℤ instance is `UnarySE2ZZ`.

*Proof.* *Closure for PP₂.* Let f : ℤⁿ → ℤᵐ and g : ℤᵐ → ℤᵖ have PP₂-definable graphs, by systems S_f in witnesses u and S_g in witnesses v. Then

(a, c) ∈ graph(g ∘ f) ⟺ ∃ b ∈ ℤᵐ, ∃u, ∃v : S_f(a, b, u) = 0 ∧ S_g(b, c, v) = 0,

and the right-hand side is a single system: no equation is altered, the intermediate vector b is carried as fresh existential witnesses alongside u and v, and every equation still has total degree at most two. So graph(g ∘ f) ∈ PP₂(n+p). The step that a system permits and a single equation does not is exactly this conjunction: combining two quadratics into one equation by summing their squares would produce total degree four.

*Failure for SE₂.* The map x ↦ x² is SE₂-definable: its graph is cut out by b − a² = 0, one equation of total degree two with no witnesses. If Fun(SE₂) were closed under composition, x ↦ x⁴ would be SE₂-definable, and Theorem 3.2 would give a constant C with |a⁴| ≤ C(1+|a|)² for every a — false for |a| large. So closure fails, and it fails at arity one (`UnarySE2ZZ`). ∎

This is the first place where the difference between one equation and a system becomes a theorem rather than a convention. Closure under composition is exactly the ability to hide an intermediate value; a system can hide it in a fresh unknown, whereas a single equation of bounded degree cannot, because the degree budget that would pay for the substitution is already spent.

**Theorem 3.5** (exactness by arity; `FunctionPhaseByArity.lean`). For n, m ≥ 1, Fun_{n,m}(SE₂) ⊊ TotComp_{n,m} with witness a ↦ (a₀³, 0, …, 0) (`cubeFirstZZ`, `singleQuadratic_functions_strict_of_pos_arity`); for n = 0 or m = 0 every function is both SE₂-definable and computable (`singleQuadratic_functions_eq_at_zero_input`, `_output`). All unconditional.

*Proof.* Let n, m ≥ 1. The map a ↦ (a₀³, 0, …, 0) is total and computable. Were it SE₂-definable, Theorem 3.2 would supply C with |a₀³| ≤ C(1+‖a‖_∞)² for all a, which fails as a₀ → ∞. With the inclusion Fun_{n,m}(SE₂) ⊆ TotComp_{n,m} of Theorem 3.3, this gives strictness. For n = 0: ℤ⁰ is a singleton, so a function ℤ⁰ → ℤᵐ is one constant vector b*, and its graph {b*} is cut out by the single equation Σ_j (b_j − b*_j)² = 0 of total degree two with no witnesses; every such function is also computable, so the two classes coincide. For m = 0: there is exactly one function ℤⁿ → ℤ⁰, its graph is everything, cut out by 0 = 0, and it is computable; again the classes coincide. ∎

## 4. Injective dimension theorem

**Theorem 4.1** (`singleQuadratic_injective_dimension_sharp`). If f : ℤⁿ → ℤᵐ is SE₂-definable and injective then n ≤ m.

*Proof.* Write the defining equation, after renaming the variables, as Q(z) + ℓ_a(z) + q(a) = 0, where z carries the output and the unknowns, Q is an integer quadratic form in z alone, ℓ_a is linear in z with coefficients affine in a, and q is quadratic in a. Over ℚ the form Q admits five behaviours, exhaustive but not pairwise exclusive (`branch_exhaustive`), and each forces one of the two structural alternatives of Theorem 4.2: either f has *linear* growth, ‖f(a)‖_∞ ≤ C(1 + ‖a‖_∞), or f agrees with a vector of rational polynomials of degree at most two on one full lattice coset ρ + Mℤⁿ. In the first case the box ‖a‖_∞ ≤ N has (2N+1)ⁿ points whose images lie in a box of side 2C(1+N)+1, so injectivity gives (2N+1)ⁿ ≤ (2C(1+N)+1)ᵐ for every N, and comparing growth in N forces n ≤ m. In the second case counting does not suffice: the images lie in a box of side quadratic in N, and the count alone yields only n ≤ 2m (Remark 4.5). Suppose instead n > m, and write the restriction to the coset as f(ρ + Mt) = (p₁(t), …, p_m(t)) with p_j = c_j + L_j + H_j, where L_j is linear and H_j is homogeneous quadratic over ℚ. The linear map L = (L₁, …, L_m) : ℚⁿ → ℚᵐ has a nonzero kernel because m < n; clearing denominators gives v ∈ ℤⁿ \setminus {0} with L(v) = 0. Since H_j(-v) = H_j(v), p_j(v) - p_j(-v) = 2L_j(v) = 0 for every j, so f(ρ + Mv) = f(ρ - Mv) while ρ + Mv ≠ ρ - Mv because M > 0 and v ≠ 0, contradicting injectivity. Hence n ≤ m. No hypothesis on the discriminant, on a common centre of the quadratic parts, or on the number of unknowns is used (`exists_collision_vector`, `not_injective_of_weakVectorCosetNF`). ∎

**Theorem 4.2** (the structural alternative, `summit_of_defines`). If a single quadratic equation defines a total function f : ℤⁿ → ℤᵐ, then f has linear growth or f has a weak vector coset normal form. There is no hypothesis on the number of unknowns, no nondegeneracy hypothesis, and no hypothesis on the form.

*Proof.* By the exhaustive rational case split on Q (`branch_exhaustive`): Q ≡ 0 gives the coset normal form; the semidefinite, negative-semidefinite and quotient-anisotropic cases give linear growth. The isotropic case splits once more: when some solution lies off the centre family it gives the coset normal form, and when every solution lies in the radical it returns linear growth through the same affine consumer as the other branches (`summit_of_isotropicBranch`). The five cases and their witnesses are the content of the companion proof note (`PROOF_NOTE_DIMENSION.md`, deposited with the artifact), one section per case. ∎

**Theorem 4.3** (sharpness, `singleQuadratic_sharp_iff`). An injective SE₂-definable function ℤⁿ → ℤᵐ exists if and only if n ≤ m. The existence direction is witnessed by zero-padding and uses no unknowns.

*Proof.* Necessity is Theorem 4.1. For sufficiency, zero-padding a ↦ (a₁, …, a_n, 0, …, 0) is injective, and its graph is defined by a single quadratic equation with no unknowns (`exists_graph_injective_pad`). ∎

**Corollary 4.4** (`not_atomGraphZZ_two`, `atomGraphZZ_capacity_eq_one`). No single quadratic equation defines the graph of an injection ℤⁿ → ℤ for n ≥ 2, and a degree-one equation does so for n = 1. Hence the one-sorted coding arity is exactly one: ca(SE₂) = 1.

*Proof.* Theorem 4.1 with m = 1 gives n ≤ 1 for every finite number of unknowns; `atomGraphZZ_degree_one_one` is the lower bound. ∎

**Remark 4.5** (the previous bound). The box count of Theorem 3.2 alone yields only n ≤ 2m --- images of a box of side N lie in a box of side quadratic in N. That inequality (`singleQuadratic_injective_dimension_bound`) remains true and is now a corollary of Theorem 4.1; it is recorded because it is what a growth bound alone can give, and the improvement to n ≤ m is exactly the content of the structural alternative.

**Remark 4.6** (what is due to whom at n = 2, m = 1, no unknowns). When the defined function is itself a polynomial, the case n = 2, m = 1 with no unknowns is Lew and Rosenberg [LR78a], Thm. 5.3(2): no quadratic storing function exists on ℤ². Their statement is about polynomials, and their three-line proof uses only integer-valuedness. The restriction of the same question to the lattice points of an affine convex cone, under a nonzero-discriminant hypothesis, is Gjaldb\ae k [Gj21], Theorem 2. Neither reaches the present statement, because a function with SE₂-definable graph need not be a polynomial: the equation 4b² - (4a₁+2)b + (a₁² + a₁) = 0 is total and output-unique over ℤ and defines a ↦ ⌈a₁/2⌉, which is not a polynomial of any degree (`parity_exists_unique`; the formalised part is `parity_not_quadratic`, which rules out rational polynomials of degree at most two). Nor do they admit unknowns. In the indefinite case the non-squareness of the Pell discriminant is not quoted but proved here from quotient-anisotropy, by exhibiting the isotropic non-radical vector that a square discriminant would force (`not_isSquare_pellDiscr`); square-value questions of this kind go back to Davenport, Lewis and Schinzel [DLS64], cited as background and not used in the formalisation.

## 5. Polynomial graph classification

**Theorem 5.1** (`MultivariatePolynomialGraphs.lean`, `polynomial_graph_singleQuadratic_iff`). For every n and every p ∈ ℤ[x₁,…,x_n]: graph(p) ∈ SE₂(n+1) ⟺ totalDegree p ≤ 2. Here totalDegree is mathlib's, so the zero polynomial has degree 0 and falls under the left-hand side; no separate convention is adopted for it.

*Proof.* (⇐) The graph is cut out by the single equation y − p = 0, of total degree at most two. (⇒) Suppose deg p = d ≥ 3. Write p = p_d + (lower), with p_d the top homogeneous part, which is nonzero. Since ℤ is infinite, p_d does not vanish identically, so there is v ∈ ℤⁿ with p_d(v) ≠ 0 (`exists_eval_ne_zero`). Restrict p to the line t ↦ tv: the resulting univariate polynomial has degree exactly d and leading coefficient p_d(v) (`linePoly_natDegree`, `exists_line_natDegree_eq_totalDegree`), so |p(tv)| grows like |t|^d. On the other hand a ↦ p(a) would be an SE₂-definable total function, hence of quadratic growth by Theorem 3.2, so |p(tv)| ≤ C(1 + ‖tv‖_∞)² = C(1 + |t|·‖v‖_∞)² for all t; for |t| ≥ 1 this is at most C(1 + ‖v‖_∞)² t², so |p(tv)| = O(t²) — a contradiction for large t since d ≥ 3. ∎

No substitution or coordinate-change lemma is needed: the growth theorem is already vector-valued and holds at every arity.

## 6. Relation phase diagram

**Theorem 6.1** (unconditional strictness REC ⊊ RE; `HaltingTransport.lean`, `recursive_strictly_contained_re`). For every k ≥ 1, REC(k) ⊊ RE(k).

*Proof.* Transport mathlib's halting problem (`ComputablePred.halting_problem`, `halting_problem_re`) to ℤᵏ by reading coordinate 0 as a code (`haltingRelZZ`). ∎

**Theorem 6.2** (Skolem [Sko38], unconditional; Proposition 1.2). PP₂(k) = SE₄(k) = Dioph(k) for every k.

*Proof of Theorem 6.2.* This is the second clause of Proposition 1.2, restated at the point where the phase diagram consumes it; nothing is added here. The two inclusions are the Lean theorems named there (`singleEqFragmentZZ_four_eq_ppFragmentZZ_two`, `singleEqFragmentZZ_four_eq_diophFragmentZZ`), and the argument is the sum-of-squares collapse in one direction and Skolem's degree reduction in the other. It is stated separately because Section 6 needs it as an arrow of the diagram and because a reader tracing which arrows consume a hypothesis should find this one carrying none. ∎

**Theorem 6.3** (per-equation decidability ⇒ SE₂ ⊆ REC; `singleEqFragmentZZ_two_subset_recFragmentZZ`). Assume QuadraticSolvabilityDecidableZZ. Then SE₂(k) ⊆ REC(k) for all k; for k ≥ 2 the inclusion is strict, witnessed by the graph of x ↦ x³ (`cubic_graph_not_withinSingleEquationZZ`, `powerGraphZZ_computablePred`; `apal_structural_core_of_perEquationGS`).

*Proof.* *Inclusion.* Let A ∈ SE₂(k) be represented by P of total degree at most two with witness arity r, so that a ∈ A ⟺ P(a, ·) has an integer root. QuadraticSolvabilityDecidableZZ says precisely that this predicate of a is decidable for the fixed P, so A ∈ REC(k).

*Strictness at k = 2.* The graph {(a, b) ∈ ℤ² : b = a³} is decidable — compute a³ and compare. It is not SE₂-definable: it is the graph of a total function, and Theorem 3.2 bounds SE₂-definable total functions by C(1+|a|)², which a³ exceeds for large a.

*Strictness at k > 2.* Take A_k := {(a₁, …, a_k) ∈ ℤᵏ : a₂ = a₁³}, which is decidable. If A_k were SE₂-definable by P(a₁, …, a_k, u), then substituting the constants a₃ = ⋯ = a_k = 0 gives P′(a₁, a₂, u) := P(a₁, a₂, 0, …, 0, u), whose total degree is at most that of P — substituting constants for variables cannot raise total degree — and which represents {(a₁, a₂) : a₂ = a₁³}. That contradicts the case k = 2. So A_k ∈ REC(k) \ SE₂(k) for every k ≥ 2. ∎

**Theorem 6.4** (code bridge; `QuadraticCodes.lean`, `GSInputCompiler.lean`, `GSCompilerComputable.lean`). (a) Evaluation of a code at (parameters, unknown list) is primitive recursive uniformly in the code (`quadraticCode_eval_primrec`). (b) The polynomial of a code has total degree at most two (`quadraticCode_toPoly_totalDegree_le_two`) and evaluates as the computable evaluation (`quadraticCode_toPoly_eval`). (c) Every polynomial of total degree at most two is the polynomial of a code (`quadraticCode_surjective`). (d) UniformQuadraticSolvabilityOnCodes ⇒ QuadraticSolvabilityDecidableZZ (`uniformCodeGS_implies_perEquationGS`). (e) The flat form, in which a code is carried as a single natural number rather than as a pair, is equivalent (`uniformCodeGS_iff`, via `codeOfNat`/`natOfCode`). (f) The *input compiler* that folds a parameter list into the coefficient table, producing a parameter-free equation with the same integer solutions, is primitive recursive (`globalGS_input_compiler_computable`, `globalInstance_eval_iff`); consequently the reduction from our instance form to the parameter-free coefficient-table form of the literature is effective, not merely extensional.

*Proof.* Throughout, a code is a pair c = (r, T): a witness arity r ∈ ℕ and a finite list T of terms, each term a coefficient α ∈ ℤ together with at most two variable codes. Evaluation at parameters a ∈ ℤᵏ and unknowns u ∈ ℤʳ reads a variable code i as the i-th entry of the environment `ofFn a ++ u`, an out-of-range code as 1 and an absent factor as 1, and sums the terms.

*(a).* Fix the environment map e(a, u) := `ofFn a ++ u`. The value of a single term (α, i?, j?) is α · e(a,u)[i] · e(a,u)[j] with the two conventions above, and the value of the code is the fold of those values over T. Every ingredient is primitive recursive: list indexing with a default and list append are primitive recursive; integer addition and multiplication are; `Option.elim` against the constant 1 is; and primitive recursive functions are closed under composition, pairing and `List.foldr`. The code c occurs as an *argument* of the composite, not as a parameter of the construction, so the resulting map (c, a, u) ↦ evalZZ c a u is primitive recursive uniformly in c, which is the content of the clause. That the type of codes is `Primcodable` is what makes "uniformly in c" a statement about a single function rather than a family.

*(b).* Define toPoly c as the sum over T of the monomials α·X_i·X_j, an absent or out-of-range factor contributing the constant 1. Each summand is a monomial in at most two variables, hence of total degree at most two, and the total degree of a sum is at most the maximum of the total degrees; so totalDegree (toPoly c) ≤ 2. Agreement with the computable evaluation is an induction on T: polynomial evaluation is additive over the sum, and on a single term both sides compute α · (value of the first factor) · (value of the second factor) under the same two conventions. The empty list gives 0 on both sides.

*(c).* Let P be a polynomial in k + r variables with totalDegree P ≤ 2. Its monomial expansion is finite and unique, and each monomial of degree at most two is 1, X_i, or X_i X_j with i ≤ j. Map the expansion term by term: a constant monomial α becomes the term (α, none, none); α X_i becomes (α, some i, none); α X_i X_j becomes (α, some i, some j). Let T_P be the resulting list and c_P := (r, T_P). By (b), toPoly c_P is the sum of exactly those monomials, i.e. P. The map is total because the support of P is finite, and it needs no choice: the monomial expansion of a polynomial is unique. Surjectivity is what lets a *coded* family range over all degree-two equations, which is the hypothesis (i) of the diagonalization Theorem 6.5 uses.

*(d).* Assume UniformQuadraticSolvabilityOnCodes and let P of total degree at most two with witness arity r be given. By (c) pick a code c_P with toPoly c_P = P; by (b), for every a the equation P(a, ·) = 0 has an integer solution u ∈ ℤʳ if and only if c_P is solvable at a. The hypothesis says that (c, a) ↦ (c solvable at a) is a computable predicate; the map a ↦ (c_P, a) is computable (a constant paired with the identity), and computable predicates are closed under composition with computable maps, so a ↦ (P solvable at a) is computable. That is QuadraticSolvabilityDecidableZZ. Only this direction is claimed. The converse fails to be available for the use we make of it: deciding one equation at a time gives each fixed relation as recursive but does not give a single decider uniform in the code, and the diagonalization behind Corollary 6.6 quantifies over the coded family. That is why Definition 1.5 is stated in the uniform form and Theorem 6.3 in the per-equation form, and why the two are kept apart everywhere in Sections 6 and 7.

*(e).* `natOfCode` and `codeOfNat` are the `Primcodable` encoding and decoding of the code type; they are mutually inverse and both primitive recursive by construction of the instance. A computable predicate transports along a computable bijection in both directions, so uniform decidability stated on codes and uniform decidability stated on their numeric encodings are equivalent hypotheses. The clause is bookkeeping, not mathematics; it is recorded because the two forms both occur in the literature and it should be visible that nothing depends on the choice.

*(f).* The equations of [GS04] carry no parameters: the input is a coefficient table. Our instances carry a parameter vector a, so a bridge is required, and the clause asserts that the bridge is effective rather than merely extensional. Define the compiler on terms. A term (α, i?, j?) of a code with k parameters is rewritten by evaluating every factor whose variable code lies in the parameter block, namely in the range i < k: if both factors are parameters the term becomes the constant (α·a_i·a_j, none, none); if exactly one is, it becomes (α·a_i, some j, none) with the unknown index shifted down by k; if neither is, only the shift is applied. Applying this term by term is a `List.map` whose step function is a case split on two `Option` fields together with lookups into `ofFn a`, so the compiler is primitive recursive, and again uniformly in (c, a) because both are arguments. Two properties are immediate from (b) and the definition of evaluation: the compiled code still has at most two variable codes per term, hence total degree at most two; and for every u, evaluating the compiled code at the empty parameter list and u gives the same integer as evaluating c at (a, u), so the two equations have literally the same solution set in u (`globalInstance_eval_iff`). Hence the reduction from our instance form to the parameter-free coefficient-table form is a primitive recursive map of inputs, which is what "effective, not merely extensional" means here. ∎

**Theorem 6.5** (effective fragment diagonalization; `EffectiveDiagonal.lean`, `coded_family_ssubset_rec`). Let C be a Primcodable type, interp : C → 𝒫(ℤᵏ⁺¹), and F ⊆ 𝒫(ℤᵏ⁺¹) with (i) F coded: every A ∈ F equals interp e for some e; (ii) membership v ∈ interp e uniformly decidable in (e, v); (iii) F ⊆ REC(k+1). Then F ⊊ REC(k+1).

*Proof.* The diagonal D := {v | the code decoded from v₀, if any, does not accept v} is recursive by (ii) (`effDiagonal_computablePred`) and not in F by self-application: if D = interp e, evaluate at the constant vector whose entries encode e (`effDiagonal_not_mem`). ∎

**Corollary 6.6** (`singleQuadratic_strict_recursive_of_codes`). Assume UniformQuadraticSolvabilityOnCodes. Then SE₂(k) ⊊ REC(k) for every k ≥ 1, in particular at arity one, where the x³ witness is unavailable.

*Proof.* Instantiate Theorem 6.5 with C the type of quadratic codes and interp c = {v | c solvable at v}: (i) is Theorem 6.4(c), (ii) is the hypothesis, (iii) is Theorem 6.3 via Theorem 6.4(d). ∎

The separation of Theorem 6.5 from its instance is deliberate. The diagonal argument uses nothing about quadratic equations except that they form an explicitly coded family whose membership relation is uniformly decidable; stated that way, the lemma applies verbatim to any fragment for which a decision procedure uniform in the code is available.

**Theorem 6.7** (DPRM transport; `DPRMTransport.lean`, `DPRM_ZZ_of_DPRM_NN`). DPRM_NN ⇒ DPRM_ZZ.

*Proof.* For A ⊆ ℤᵏ r.e., the preimage A' ⊆ ℕ²ᵏ under b ↦ (b_i − b_{k+i})_i is r.e. (`rePred_diffPreimage`; the difference map is primitive recursive). DPRM_NN gives P with A' = {b | ∃ y ∈ ℕˢ, P(b,y) = 0}. Then a ∈ A iff there are integers p, q ∈ ℤᵏ, y ∈ ℤˢ and w ∈ ℤ^((2k+s)×4) with a = p − q, P(p,q,y) = 0, and each coordinate of (p,q,y) equal to the sum of the four squares of the corresponding w's (Lagrange, mathlib `Nat.sum_four_squares`); the single equation is the sum of squares of these conditions (`transportPoly`, `transportPoly_eval_eq_zero_iff`). The witness arity is 5(2k+s) (`transportWitnessArity_eq`), and the final representing polynomial — after the renaming that indexes the witnesses by a `Fin` type — has total degree at most max(2·deg P, 4) (`transportedRepresentation_totalDegree_le`, `DPRM_ZZ_resource_bound_final`). ∎

**Theorem 6.8** (relation phase diagram; `relation_phase_diagram_all_positive_arity_of_classical`). Assume UniformQuadraticSolvabilityOnCodes and DPRM_NN. Then for every k ≥ 1:
  SE₂(k) ⊊ REC(k) ⊊ RE(k) = PP₂(k) = SE₄(k),
where SE₂ ⊊ REC uses the hypothesis only through Corollary 6.6 at k = 1 (through Theorem 6.3 at k ≥ 2), REC ⊊ RE is Theorem 6.1, RE = PP₂ is DPRM (Theorem 6.7 with `ppQuadratic_eq_re_of_DPRM`), and PP₂ = SE₄ is Theorem 6.2. At k = 0 all five classes coincide.

*Proof.* Every arrow is already proved. SE₂(k) ⊆ REC(k) is Theorem 6.3 via Theorem 6.4(d), and the inclusion is strict: at k = 1 by Corollary 6.6, whose diagonalization needs the uniform form of the hypothesis and Theorem 6.4(c) for the coded family; at k ≥ 2 by the x³ witness of Theorem 6.3. REC(k) ⊊ RE(k) is Theorem 6.1, unconditional. RE(k) = PP₂(k) is Theorem 6.7 under DPRM_NN, and PP₂(k) = SE₄(k) is Theorem 6.2, unconditional. The collapse at k = 0 is Proposition 1.4. ∎

**Layering.** The formalization exports the diagram in dependency layers (`apal_structural_core_unconditional`, `_of_uniformGS`, `_of_perEquationGS`, `_of_DPRM`, `_of_DPRM_NN`), so that a reader can see exactly which arrow uses which classical input, and the unconditional part of the diagram can be read off without accepting any of them.

## 7. Function phase diagram

**Theorem 7.1** (`function_phase_diagram_by_arity_of_DPRM_NN`). Assume DPRM_NN. For all n, m: TotComp_{n,m} = Fun_{n,m}(PP₂) = Fun_{n,m}(SE₄) (`ppQuadratic_functions_eq_totalComputable_of_DPRM`, `ppQuadratic_functions_eq_singleQuartic`); Fun_{n,m}(SE₂) ⊆ TotComp_{n,m} always, strictly for n, m ≥ 1 and with equality for n = 0 or m = 0 (Theorem 3.5); Fun(PP₂) is closed under composition and Fun(SE₂) is not (Theorem 3.4). The only conditional arrow is TotComp ⊆ Fun(PP₂).

*Proof.* TotComp = Fun(PP₂) = Fun(SE₄) is the DPRM transport of Theorem 6.7 read at the level of graphs. Fun(SE₂) ⊆ TotComp is Theorem 3.3, which uses no classical input; strictness for n, m ≥ 1 and equality for n = 0 or m = 0 are Theorem 3.5; the failure of closure under composition is Theorem 3.4. The only arrow that consumes a hypothesis is therefore TotComp ⊆ Fun(PP₂). ∎

## 8. Structured infinite fibres

Sections 2–7 constrain the fibres that are *finite*. This section describes the infinite ones. The result is not merely that an unbounded fibre exists, but that it contains an infinite subset generated by arithmetic data of one of three forms produced by the proof, and that the data can be exhibited. The certificate describes a subset, never a parametrisation of the whole fibre. The three forms are those the argument emits; they are not claimed to be canonical, and a fibre may carry certificates of more than one form.

For P ∈ Poly (n+1) r and a ∈ ℤⁿ let fiberZZ P a := {c | ∃ u, P(a, c, u) = 0} be the scalar fibre over a.

**Definition 8.1** (generic certificate; `InfiniteFiberCertificate.lean`). An *infinite-subset certificate* for (P, a) consists of an infinite index type, an injective output map from it into ℤ, and a witness map, together with proofs that each output lies in the fibre with the given witness. It certifies that the fibre is infinite by exhibiting it as containing the image of an injection.

The word *constructive* is deliberately avoided here, and the following four statements are kept apart throughout the paper.

| statement | status |
|---|---|
| the output family has the stated arithmetic form (progression, orbit, step orbit) | proved, with the data displayed |
| every output of the family lies in the fibre, i.e. a witness exists for it | proved |
| a witness map exists, assigning to each output one realising witness | proved, but the assignment is made extensionally (`Classical.choice`) from the membership proofs |
| the witness map is computable, or a certificate can be extracted algorithmically from P | not proved, and not claimed |
The certificate presents the infinite output subset by explicit arithmetic data. Witnesses realising individual outputs exist and are selected extensionally; no theorem here asserts an effective witness-generating algorithm.

**Definition 8.2** (the three kinds; `StructuredCertificates.lean`). A *structured certificate* `StructuredCertificate P a` is one of three realizations, each of which carries arithmetic data that *pin* the output map rather than merely asserting that some injection exists.

1. *Polynomial progression.* A polynomial q ∈ ℤ[t] with 1 ≤ deg q ≤ 2, a threshold t₀, witnesses w_t, and proofs that P(a, q(t), w_t) = 0 for every t ≥ t₀ and that q is injective on that tail. The fibre contains an arithmetic or quadratic progression outright.
2. *Pell-unit orbit.* A positive nonsquare D, a unit (x₀, y₀) of x² − Dy² = 1 with y₀ ≠ 0, a base point (X₀, Y₀) of norm N₀ := X₀² − DY₀², and the orbit generated by the unit as an explicit recurrence,

  X_{k+1} = x₀X_k + D y₀ Y_k, Y_{k+1} = y₀X_k + x₀Y_k,
  together with an affine projection with denominator, denom·output_k = p_c + p_x X_k + p_y Y_k with denom ≠ 0, witnesses, and injectivity of the output. The norm is preserved along the orbit as a theorem of the data (`PellUnitOrbitRealization.orbit_norm`), not as an extra hypothesis.
3. *Moving-modulus step orbit.* Integers b > 0, μ, and a positive *modulus factor* F, a sign ε ∈ {±1}, a sequence c_k with moduli t_k := b·c_k + μ > 0, and primes p_k with

  F·b·t_k < p_k, p_k ≡ 1 (mod F·b·t_k), t_{k+1} = t_k · p_k,
  with witnesses for the outputs ε·c_k. Strict monotonicity of c_k is a consequence of the recurrence and does not have to be assumed (`MovingModulusStepOrbitRealization.c_strictMono`).

The three kinds are a sufficient certificate language, not a classification: no claim is made that they are canonical, exhaustive of the fibre, or mutually exclusive, and a fibre may carry certificates of more than one kind (Example 8.6 exhibits two). The third kind deserves a word. The relevant family is an iterated moving-modulus orbit rather than a fixed prime progression: at each step the congruence that the next prime must satisfy is taken modulo a quantity that itself grows with the current output, so the object is an orbit under a step map whose modulus moves. Dirichlet's theorem is what makes each individual step possible — there is always a prime in the relevant progression — but the family is generated by iterating the step from a base point, not by ranging over the primes of one progression. Writing the certificate as data with the recurrence \texttt{t_{k+1} = t_k·p_k} in it makes the distinction unmissable.

**Theorem 8.3** (soundness; `fiber_infinite_of_structuredCertificate`, `StructuredCertificate.toSubset`). Every structured certificate yields a generic certificate and hence proves the fibre infinite; a certified fibre exceeds every bound (`fiber_unbounded_of_certificate`); certificates pull back along integral changes of witness coordinates (`certificate_pullback`), which is what allows a certificate produced in transformed coordinates to be reported in the original ones.

*Proof.* Three assertions, each by the data.

*Every structured certificate yields a generic one.* A generic certificate asks for an infinite index type, an injective output map into ℤ, a witness map, and proofs that each output lies in the fibre with its witness. Each kind of Definition 8.2 supplies exactly these. For a polynomial progression the index type is the tail {t : t ≥ t₀}, which is infinite; the output map is q, injective on that tail by hypothesis; the witnesses are the w_t, and P(a, q(t), w_t) = 0 is part of the data. For a Pell-unit orbit the index type is ℕ; the output map is determined by denom·output_k = p_c + p_x X_k + p_y Y_k with denom ≠ 0, and its injectivity is part of the data; the witnesses are again given. For a moving-modulus step orbit the index type is ℕ and the outputs are ε·c_k, whose injectivity is not assumed but follows from the recurrence: t_{k+1} = t_k·p_k with p_k > F·b·t_k ≥ 1 forces t_k, and hence c_k = (t_k − μ)/b, to increase strictly (`MovingModulusStepOrbitRealization.c_strictMono`). In all three cases forgetting the arithmetic data and keeping the index type, the output map and the witnesses is a generic certificate.

*A certified fibre is infinite, and exceeds every bound.* The output map of a generic certificate is an injection of an infinite type into the fibre, so the fibre contains an infinite set of integers. An infinite set of integers is unbounded in absolute value: a bound B confines it to the finite set [−B, B]. Hence no B bounds the fibre.

*Pull-back along integral changes of witness coordinates.* Let T be an integral matrix with integral inverse and let P′(a, c, u) := P(a, c, Tu). Then u is a witness for P′ at output c precisely when Tu is one for P, and the correspondence u ↦ Tu is a bijection of ℤʳ. Given a certificate for P′, replace each witness w by Tw and keep the index type, the output map and the arithmetic data unchanged; every membership proof transports along the identity P′(a, c, w) = P(a, c, Tw). Injectivity of the output map is untouched because outputs are not changed. This is what allows a certificate produced in transformed coordinates — the coordinates in which the projection dichotomy works — to be reported in the original ones. ∎

**Definition 8.4** (the summit target; `SummitTarget.lean`). For P of total degree at most two,
  UniformQuadraticFiberStructureZZ P :⟺ ∃ C ∈ ℕ, ∀ a ∈ ℤⁿ,
  ( ∀ c ∈ fiberZZ P a, |c| ≤ C·(1 + ‖a‖_∞)² ) ∨ Nonempty (StructuredCertificate P a).

The order of the quantifiers is the content of the definition: C is chosen after P and *before* a, so one constant serves every parameter point. The weak form ∀ a ∃ C_a, in which the bound may be chosen after seeing the parameter, is strictly weaker and is not what is proved here. The two horns cannot both hold at a given a, since a certificate exhibits an unbounded output family inside the fibre while the first horn bounds every element of it (`uniform_bound_certificate_exclusive`). The weaker per-point form, in which the bound B may depend on a, is `QuadraticFiberBoundedOrStructured`.

The distinction matters and is not cosmetic. On a *finite* fibre the per-point form is satisfied by taking B to be the fibre's own maximum, whatever that maximum happens to be (`weak_target_trivial_on_finite_fibre`), so a theorem stated in the weak form would carry no information about how the bound depends on the parameters. The uniform form asserts the quadratic dependence, which is exactly the content of Section 2.

**Theorem 8.5** (structured summit, unconditional; `SummitClosure.lean`, `uniformQuadraticFiberStructureZZ_of_quadratic`, `singleQuadratic_fiber_bounded_or_structurallyInfinite`). For every P ∈ Poly (n+1) r with totalDegree P ≤ 2, UniformQuadraticFiberStructureZZ P holds. Consequently every scalar fibre of every equation of total degree at most two is bounded by C(1+‖a‖_∞)² with C depending only on P, or carries a structured certificate of one of the three kinds of Definition 8.2.

*Proof.* The proof has four steps, each of which is a separate theorem in the formalization.

*(i) The uniform constant is free.* For quadratic P the strong target is equivalent to the certificate supply on the infinite side alone: UniformQuadraticFiberStructureZZ P ⟺ (∀ a, fiberZZ P a infinite → the fibre carries a structured certificate) (`uniformQuadraticFiberStructureZZ_iff_infiniteFiberStructured`). One direction is immediate; for the other, take the constant C supplied by Theorem 2.1 in the sup-norm form, and split on whether the fibre is finite. If it is, Theorem 2.1 gives the bound with that C; if it is not, the hypothesis supplies the certificate. So nothing is lost by demanding uniformity, and the whole remaining obligation is the infinite side.

*(ii) Reduction to the nonnegative halves.* An infinite subset of ℤ is infinite on the nonnegative or on the nonpositive side (`infinite_integer_set_pos_or_neg`). Reflecting the output coordinate maps one side to the other, and the reflection acts on certificates kind-preservingly: the polynomial q is replaced by its reflection, the affine projection of a Pell orbit by its negative, and the moving-modulus sign field ε flips (`OutputNegation.lean`, `structuredCertificate_of_flipZero`). It therefore suffices to certify a half-fibre that is infinite, with the sign carried as a parameter ε satisfying ε² = 1.

*(iii) Homogenisation: a half-fibre is the fibre of a homogeneous form.* This is the same decomposition used in the proof of Theorem 2.1, now used to transport structure rather than a bound. Relabelling and splitting into homogeneous components writes the specialised equation as H(x) + ℓ(a)·x + q(a) with H homogeneous of degree two in x = (c, u), and the ε = −1 case is handled by the reflected form (`flipZero H`, `fiberVal_flip`). One obtains H, an integer vector L and an integer Q with

fiberSetG H L Q = {m ∈ ℕ | ε·m ∈ fiberZZ P a}

(`exists_fiberSetG_eq_fiberNatSigned`). The left-hand side is exactly the object about which Section 9 speaks.

*(iv) The dichotomy in data-carrying form, and the conversion.* Theorem 9.3 below is the projection dichotomy strengthened so that the infinite horn produces not the proposition "this set is infinite" but a *structured family* inside it — a progression, a quadratic progression, a Pell orbit with its recurrence, or a moving-modulus orbit with its primes (`StructuredFamily`, `quadraticProjectionDichotomyZ_all_data`). Transporting such a family along the set equality of step (iii) and converting it into a certificate is then mechanical: choice supplies the witnesses from the membership proofs, the sign ε travels into the polynomial coefficients, into the affine projection, or into the sign field according to the kind, and the derived side conditions of the Pell kind (D > 0, D not a square, y₀ ≠ 0) follow from the unit equation together with x₀ ≥ 2 (`structuredCertificate_of_family`). If instead the bounded horn holds, the half-fibre is finite, contradicting the assumption of step (ii). ∎

**Examples 8.6** (one instance of each kind, and an overlap). Take n = 0, so that the fibre is a single set of integers.

1. *Polynomial progression.* The equation c − u² = 0 has fibre {t² : t ∈ ℕ}, a degree-two progression with output map c_t = t². This is also the example that refutes any attempt to describe every one-unknown fibre by unit orbits alone.
2. *Pell-unit orbit.* The equation c² − 2u² − 1 = 0 has as its fibre the set of x-coordinates of x² − 2y² = 1. That fibre *contains* the orbit of the unit 3 + 2√2 under the recurrence of Definition 8.2(2), taken from the base point (X₀, Y₀) = (1, 0), with output projection the identity (denom = 1): the outputs are 1, 3, 17, 99, …. The fibre is strictly larger than this orbit — it also contains −1, −3, −17, … — which is the general situation: a certificate exhibits a structured infinite subset of the fibre, not a parametrisation of all of it.
3. *Moving-modulus step orbit.* For the singular branch with positive slope the construction of Section 9 returns the recurrence b·c_{k+1} + μ = (b·c_k + μ)·p_k with the primes p_k chosen stagewise above the branch's modulus factor; the outputs grow strictly and are pinned by that recurrence rather than by a closed form. An instance of the data, with r = 3 unknowns, is the equation
  u² + v² + (c + 1)·w = 0,
  taking b = 1, μ = 1, ε = 1 and modulus factor F = 2, so that t_k = c_k + 1. Start from c₀ = 0, t₀ = 1. The step requires a prime p_k with p_k > F·b·t_k = 2t_k and p_k ≡ 1 (mod 2t_k), which Dirichlet's theorem supplies at every stage; the first two choices are p₀ = 3, giving t₁ = 3 and c₁ = 2, and p₁ = 7, giving t₂ = 21 and c₂ = 20. Each output c_k is realised by the witness (u, v, w) = (0, 0, 0). This instantiates the constructor of Definition 8.2(3) exactly. It should be read as an exhibition of the data shape and not as evidence that the shape is forced: the fibre of this equation is all of ℤ, so the same fibre also carries a certificate of kind (1).

*Overlap.* The three kinds are not mutually exclusive, and two fibres above carry certificates of two kinds each.

The fibre {t²} of (1) also carries a certificate of kind (2). Write (3 + 2√2)ᵏ = x_k + y_k√2, so that x_k² − 2y_k² = 1. Take for the orbit the *square* of that unit, (x₀, y₀) = (17, 12), which satisfies 17² − 2·12² = 1, and the base point (X₀, Y₀) = (1, 0). The orbit of Definition 8.2(2) is then X_k + Y_k√2 = (17 + 12√2)ᵏ = (3 + 2√2)²ᵏ, so that

  X_k = x_k² + 2y_k² = 2x_k² − 1,
using x_k² − 2y_k² = 1. Hence 2·x_k² = X_k + 1, which is an affine projection with denominator in the sense of Definition 8.2(2):

  denom = 2, p_c = 1, p_x = 1, p_y = 0, output_k = x_k².
The outputs are 1, 9, 289, … , each realised in the fibre of c − u² = 0 by the witness u = x_k, and they are strictly increasing, hence injective. So the same fibre carries both a polynomial progression and a Pell-unit orbit. (Writing the projection against the *unsquared* orbit would not do: c = x_k² is quadratic in the orbit coordinate, and Definition 8.2(2) admits only affine projections. Passing to the squared unit is what makes the projection affine.)

The fibre of the equation in (3) is all of ℤ, and it carries both the moving-modulus certificate displayed there and the polynomial progression q(t) = t of kind (1).

A certificate is a witness of structure, not a canonical invariant of the fibre.

**Remark 8.7** (the shapes a fibre can have, and where each lands in Theorem 8.5). All five occur, and each is exhibited in the formalization (`SummitInstances.lean`).

| fibre | example (n = 0) | horn of Theorem 8.5 |
|---|---|---|
| empty | 1 = 0 | bounded, vacuously |
| finite, nonempty | c² − 4 = 0, fibre {−2, 2} | bounded |
| the output zero alone | c = 0 | bounded |
| infinite on the nonpositive side only | c + u² = 0, fibre {−t²} | certificate, after the ε = −1 transport |
| infinite on both sides | 0 = 0, fibre ℤ | certificate |
The fourth row is why the proof works with signed halves: the nonnegative half of that fibre is {0}, so a construction looking only at nonnegative outputs would wrongly report a bounded fibre. The two halves meet exactly in the output zero (`halves_inter`), so the fibre is infinite if and only if some half is, and the sign ε is carried through the construction rather than handled by a separate argument.

**Remark 8.8** (which kind comes from where). The kind of certificate is determined by the branch of the proof of Theorem 9.3 that produces it. Exhaustiveness is established by the typed case analysis inside the production theorem itself (`quadraticProjectionDichotomyZ_all_data`, `TopDichotomyData`); `BranchExhaustion.lean` is a generated documentation layer that mirrors that analysis as a finite table and does not independently establish it. The correspondence is many-to-one in both directions, and it is worth stating it as the table has it rather than in a slogan. In the full-rank layer the direction families give Pell-unit orbits, the α = 0 leaves give polynomial progressions, and the semidefinite leaf is bounded. In the singular block the positive-slope leaves give moving-modulus step orbits and the remaining leaves give polynomial progressions. In the one-witness layer — reached both by the r ≤ 1 dispatch and by the uncoupled rank-one leaf, which pass through Theorem V.4 — the leaves give polynomial progressions except the Δ > 0 non-square case, which gives a Pell-unit orbit, and the definite case, which is bounded. So no layer emits only one kind and no kind comes from only one layer; in particular Pell-unit orbits arise in the one-witness layer as well as in the full-rank one, which is what Corollary V.5 records. No branch is left without a kind, and no kind is produced by a branch that cannot support its data.

## 9. The arithmetic projection theorem

**Definition 9.1** (`SemanticQuadraticGeneral/Defs.lean`). For a form H in r+1 variables write fiberSetG H ℓ q := {c ∈ ℕ | ∃ u ∈ ℤʳ, H(c,u) + ℓ·(c,u) + q = 0} and fboundG K ℓ q := K·((1 + Σ|ℓ_i|)² + |q|). Then DichotomyG H :⟺ ∃ K, for every affine datum (ℓ, q), fiberSetG H ℓ q is infinite or bounded by fboundG K ℓ q. QuadraticProjectionDichotomyZ r :⟺ every homogeneous quadratic H in r+1 variables satisfies DichotomyG H.

**Theorem 9.2** (`quadraticProjectionDichotomyZ_all`, unconditional). For every r, QuadraticProjectionDichotomyZ r.

*Proof.* This is what Appendix F proves, in full and without appeal to the formalization: Part I settles the full-rank case for r ≥ 2, Part II the singular case with its dispatch and the size transport back to the original affine data, Part V the small-arity and two-variable leaves the dispatch calls, and Part IV assembles them. ∎

**Theorem 9.3** (data-carrying form; `SemanticQuadraticGeneral/TopDichotomyData.lean`, `quadraticProjectionDichotomyZ_all_data`, `quadraticProjectionDichotomyZ_structured`, unconditional). The same statement with "infinite" replaced by "carries a structured family": ∃ K, for every (ℓ, q), either there is a `StructuredFamily (fiberSetG H ℓ q)`, or every element is bounded by fboundG K ℓ q. Theorem 9.2 follows by forgetting the family (`dichotomyG_of_dichotomyGData`).

*Proof.* The complete proof of \cref{theorem:9.2,theorem:9.3} is Appendix F of this paper, where it is given as twenty-five numbered lemmas with their proofs; the formal development verifies the same argument, and Section 12 records the correspondence. What follows in this section is a road map of that proof, so that a reader can see the shape of the argument before reading it in full. \cref{theorem:2.1,theorem:8.5} both rest on this one theorem, and a reader is entitled to know what kind of argument carries that weight.

*Normal form.* The quadratic form H is presented by its Gram data, and one first brings it into a shape in which the radical is visible. The reduction uses a unimodular *congruence* U^T G U — not a Smith-normal-form left–right equivalence, which would destroy the quadratic form — obtained from the saturation of the integer kernel of G together with a complement of the torsion-free quotient (`RadicalDecomposition.lean`, `Unimodular3.lean`). This splits the problem into a full-rank part and a singular part, and the affine data transform correctly under the congruence, which is what makes the bound fboundG survive the change of coordinates.

*Full-rank case.* The fibre equation is a nondegenerate quadratic condition, and the dichotomy is proved at each fibre point rather than for the fibre as a whole. The top-level split is on the sign of α(2αc₀+β): non-positive forces c₀ ≤ |β| and the point is bounded; positive, together with a signed non-square direction, produces an infinite orbit (Part I §§3–5). The case α = 0 is separate (§6), and the direction is produced by a sign trichotomy of the adjugate form, with the semidefinite alternative α·W̃ ≥ 0 everywhere treated on its own (§§7–8). The classical isotropic–anisotropic distinction enters inside that last step rather than at the top: an isotropic form yields a line of solutions and a polynomial progression (Lemma V.3); an anisotropic one brings in the unit group of a real quadratic order (Lemma V.2), and a suitable initial solution of the shifted norm equation generates an infinite orbit under a unit preserving the congruence conditions the branch requires. (Nothing below needs the stronger classical statement that all solutions fall into finitely many such orbits; one infinite orbit suffices.) Iterating the unit produces the Pell-unit orbit of Definition 8.2(2), with the recurrence read off from multiplication by x₀ + y₀√D; the affine projection with denominator appears because the output coordinate is recovered from the orbit point only after clearing a fixed denominator (`FullRankAssemblyData.lean`).

*Singular case.* The form degenerates along its radical, and the reduction does **not** proceed by an induction on the number of unknowns. Part II dispatches on the rank k₀ of the nondegenerate quotient: k₀ = 0 to Lemma 4, k₀ = 1 to Lemma 6, k₀ ≥ 2 to Lemma 5 (`QuotientRankZero.lean`, `QuotientRankOne.lean`). Underneath the dispatch sit the radical affine coefficients (`RadicalAffine.lean`), a nonzero-minor periodicity argument, a proportional compression, and the size transport back to the original affine data. The rank-zero leaf is the largest single case: all three of its infinite branches turn out to be progressions (an identity family, a periodic family, and a square progression).

*The moving-modulus branch.* One branch of the singular case resists both treatments: the fibre condition becomes a divisibility b·c + μ ∣ (a quadratic expression in the remaining unknowns), and the divisor moves with c. The step lemma shows that from a fibre point with positive modulus t = b·c + μ one can always find a prime p, congruent to 1 modulo F·b·t and larger than it, and a new fibre point whose modulus is exactly t·p (`moving_modulus_prime_step_data`). The congruence is what allows the quadratic residue condition to be transported to the new modulus; the size condition is what makes the sequence strictly increasing. Iterating from any base point with positive modulus gives the moving-modulus step orbit, with the modulus factor F pinned to 2|det G₀| in the singular-block branch — G₀ being the nondegenerate quotient block of Lemma 2, not the original Gram matrix, whose determinant is zero in that branch — and to 8·max(1,|D'|)·|2k| in the rank-one coupled branch. Dirichlet's theorem on primes in arithmetic progressions (mathlib `Nat.infinite_setOf_prime_and_eq_mod`) supplies the prime at each step, and only there.

*Bounded branches.* Where no family is produced, the branch yields an explicit bound of the shape fboundG K ℓ q, and the constants are combined by taking the maximum over the finitely many branches. The branch table, with the kind emitted by each branch, ships with the formalization. ∎

## 10. Definable functions: normal forms and classification

This section classifies the SE₂-definable total functions. Say that f : ℤⁿ → ℤᵐ has a *common slope* if there are M ≥ 1 and an integer m × n matrix B with f(a + Mt) = f(a) + Bt for all a, t ∈ ℤⁿ. Under the analytic input TCER stated before Proposition 10.7, a function with two or more outputs is SE₂-definable exactly when it has a common slope (Proposition 10.9); with one output, exactly when it has a common slope, agrees with a rational polynomial of total degree at most two, or is of the parity-affine kind (Proposition 10.14); and a ↦ (f(a), 0) is SE₂-definable exactly when f has a common slope (Proposition 10.15). Every map to ℤ⁰ has a common slope. The converse directions use no analytic input, and neither does the case without unknowns (Proposition 10.16). Under TCER every SE₂-definable function has a presentation whose unknowns are unique (Proposition 10.17), and a ↦ ⌊a/3⌋ needs exactly one unknown (Proposition 10.18). The section treats the normal forms first (Proposition 10.1 to Lemma 10.8), then several outputs (Proposition 10.9 to Proposition 10.12), one output (Lemma 10.13 to Proposition 10.15) and the unknowns (Proposition 10.16 to Proposition 10.18).

**The weak vector coset normal form.** By Theorem 4.2, every single quadratic equation that defines a total function f yields linear growth or a weak vector coset normal form. Whether the second alternative is always available --- every such f has a weak vector coset normal form --- was left open in the first version of this work. The artifact now reduces it, together with its full-residue strengthening, to the semidefinite branch (Proposition 10.1, Proposition 10.6), settles that branch in low rank (Proposition 10.2), and settles the whole question conditionally on one explicit analytic input on ternary lattice cosets (Proposition 10.7). Nothing in Sections 1–9 uses the results of this section. Write the equation as Q(z) + ℓ_a(z) + q(a) = 0 with z the outputs and the r unknowns, and let d be the rank of the polar form of Q over ℚ.

**Proposition 10.1** (`generalWeakNF_iff_definiteWeakNF`, `rankExcess_compiler`, `definite_reduction`; standard axioms). Every total function defined by a single quadratic equation over ℤ has a weak vector coset normal form if and only if this holds for the equations with at least one output whose form Q is positive definite.

*Proof.* Every branch of Q other than the positive semidefinite one is either closed or carried to it by a change of sign (`generalWeakNF_iff_semidefiniteWeakNF`). For a nonzero positive semidefinite Q with m ≥ 1 outputs one has m ≤ d ≤ m + r, and an integer change of the unknown coordinates alone, read off a Smith normal form of the saturated lattice of radical unknown vectors, removes m + r - d unknowns without changing the inputs, the outputs or the graph. What remains has integer coefficients, total degree at most two, and a positive definite form of rank d (`rankExcess_compiler`, `definite_reduction`). ∎

The number d - m counts the unknowns of the compiled equation, not the least number with which the graph can be defined: (b - a)² + (u₁ + u₂)² = 0 has d = 2 and compiles to one unknown, while b - a = 0 defines the same graph with none (`sameGraph_three_witnessCounts`).

**Proposition 10.2** (`lowRankSemidefiniteWeakNF_holds`, `definiteWeakNF_oneOut_oneWit_holds`; standard axioms). Let f : ℤⁿ → ℤᵐ, m ≥ 1, be defined by a single quadratic equation over ℤ whose form Q is nonzero, semidefinite of either sign, and of polar rank at most two. Then f has a weak vector coset normal form. In particular this holds for one output, one unknown and a positive definite form, for every n.

*Proof.* After a change of sign and the compilation in the proof of Proposition 10.1, the form is positive definite in d ≤ 2 output-and-unknown coordinates. If d = 1 there is one output and no unknown, and the full vector coset normal form is known (`fullVectorCosetNF_of_defines`). Let d = 2. Completing the square gives Q(z - c(a)) = R(a) with c rational affine and R rational of degree at most two, and Q(w) = α\big((w₁ + βw₂)² + Δw₂²\big) with α, Δ > 0 (`binary_compiler_gen`). If R vanishes at every integer input, every solution is the centre and f is affine. Otherwise fix an integer input a₀ with R(a₀) ≠ 0 and an integer solution z₀ there; the off-centre vector z₀ - c(a₀) gives a representation R(a₀)/α = r₀² + Δ s₀². Write R(a₀ + x)/α = r₀² + Δs₀² + 2ℓ(x) + H(x) with ℓ linear and H a quadratic form. Totality makes this a rational value of X² + ΔY² at every integer x, so Lemma 10.5 gives rational affine r, s with R(a₀ + x)/α = r(x)² + Δ s(x)² identically and (r(0), s(0)) = (r₀, s₀). The resulting affine family of solutions passes through z₀ exactly; a common denominator M of its coefficients makes it integral on a₀ + Mℤⁿ, and output-uniqueness identifies its output coordinates with f there (`weakVectorCosetNF_of_binary`). No class-number argument and no uniqueness of the unknowns is used. ∎

The three lemmas used in the proof of Proposition 10.2 follow.

**Lemma 10.3** (`direction_discriminant_square`; standard axioms). Let Δ > 0, A ≠ 0, B, C be rational. If At² + Bt + C is a value of X² + ΔY² with rational X, Y for every integer t, then B² - 4AC = -Δh² for some rational h. Consequently, if c + 2ℓ(x) + H(x), with ℓ a rational linear form and H a rational quadratic form on ℚⁿ, is such a value at every x ∈ ℤⁿ, then \big(cH(v) - ℓ(v)²\big)/Δ is the square of a rational number for every v ∈ ℤⁿ.

*Proof.* Replacing Δ by an integer in its square class and multiplying the polynomial by a square, we may assume that Δ, A, B, C are integers; neither step changes the hypothesis or the conclusion. Put δ = B² - 4AC. If δ = 0 the conclusion holds with h = 0. Suppose δ ≠ 0 and δ ≠ -Δh² for every rational h. Then -Δ and -Δδ are not rational squares, so each is a quadratic non-residue on some unit residue class modulo a common period (`nonResidueClass_holds`); by the multiplicativity of the Jacobi symbol one of the two classes or their product carries (-Δ/\cdot) = -1 and (δ/\cdot) = +1 (`characterSeparation_holds`), and Dirichlet's theorem gives arbitrarily large primes p in that class (`separating_prime_of_residueWitness`). Take such a p with p ∤ 2AΔδ. As δ is a nonzero square modulo p, the polynomial P(t) = At² + Bt + C has a root t₀ modulo p with P'(t₀) ≢ 0, and P(t₀ + p) ≡ P(t₀) + pP'(t₀) \pmod{p²}; so p divides one of P(t₀), P(t₀ + p) exactly once. On the other hand a rational value X² + ΔY² has even p-adic valuation: after removing the common power of p from X and Y, a relation p ∣ X² + ΔY² with X, Y not both divisible by p would make -Δ a square modulo p. This contradiction proves the first statement. For the second, restrict to the line t ↦ tv: the value is c + 2ℓ(v)t + H(v)t². If H(v) ≠ 0, the first statement gives 4ℓ(v)² - 4cH(v) = -Δh², that is \big(cH(v) - ℓ(v)²\big)/Δ = (h/2)². If H(v) = 0, the same valuation argument applied to the linear polynomial c + 2ℓ(v)t shows ℓ(v) = 0 (`not_total_of_linear`), and the quantity is 0. ∎

The one-variable statement is `rat_discriminant_of_total'`; it is proved in the artifact but lies outside the frozen statement registry, so Lemma 10.3 is registered under its direction-wise form.

**Lemma 10.4** (`square_values_rigidity`; standard axioms). Let T be a rational quadratic form on ℚⁿ such that T(v) is the square of a rational number for every v ∈ ℤⁿ. Then T = h² for a rational linear form h.

*Proof.* Let N ≥ 1 clear the denominators of T and put A = N²T. The values of A on ℤⁿ are integers and rational squares, hence squares of integers. If A vanishes on ℤⁿ it vanishes on ℚⁿ by homogeneity, and h = 0. Otherwise fix w ∈ ℤⁿ with A(w) = a², a > 0, and let B_A(x, y) = A(x + y) - A(x) - A(y). For v ∈ ℤⁿ the polynomial p(t) = A(tw + v) = a²t² + B_A(w, v)t + A(v) is the square of an integer at every integer t. Let y_t ≥ 0 be its square root. For large t, y_t - at = \big(B_A(w, v)t + A(v)\big)/(y_t + at) tends to B_A(w, v)/(2a); an integer sequence with a limit is eventually constant, so p(t) = (at + e)² for some integer e and infinitely many t, hence identically. Comparing coefficients, A(v) = \big(B_A(w, v)/(2a)\big)². Thus h(x) = B_A(w, x)/(2aN) satisfies T = h² on ℤⁿ, and on ℚⁿ by homogeneity. ∎

The formal proof reaches Lemma 10.4 through the affine version `c21_affine_square`. It is the case of quadratic forms of a theorem of Kojima [Koj15] (see also [Sch00], Theorem 52): an integer polynomial that is a square at every integer point is the square of a polynomial. It is also related to Hilbert-type irreducibility over ℤ [BDKN22]. The argument above is self-contained.

**Lemma 10.5** (`norm_section`; standard axioms). Let Δ > 0 and let r₀, s₀ be rational with c = r₀² + Δs₀² > 0. If c + 2ℓ(x) + H(x) is a value of X² + ΔY² at every x ∈ ℤⁿ, there are rational affine functions r, s on ℚⁿ with (r(0), s(0)) = (r₀, s₀) and c + 2ℓ(x) + H(x) = r(x)² + Δ s(x)² for every x ∈ ℚⁿ.

*Proof.* By Lemma 10.3 and Lemma 10.4, (cH - ℓ²)/Δ = k² for a rational linear form k. Put u = c + ℓ. Then u² + Δk² = c(c + 2ℓ + H). Solve r₀r + Δs₀s = u, r₀s - s₀r = k, whose determinant is c ≠ 0: r = (r₀u - Δs₀k)/c and s = (s₀u + r₀k)/c are rational affine. Brahmagupta's identity (r₀² + Δs₀²)(r² + Δs²) = (r₀r + Δs₀s)² + Δ(r₀s - s₀r)² gives c(r² + Δs²) = u² + Δk² = c(c + 2ℓ + H). At x = 0, u = c and k = 0, so (r(0), s(0)) = (r₀, s₀). ∎

**The full-residue form.** A *full* vector coset normal form of f is one modulus M ≥ 1 together with, on every residue class modulo M, a vector quadratic polynomial that agrees with f on that class (`FullVectorCosetNF`). Write polar(x, y) = Q(x + y) - Q(x) - Q(y).

**Proposition 10.6** (`generalFullNF_iff_semidefiniteFullNF`, `isotropicBranchFullNF_holds`; standard axioms). Every total function defined by a single quadratic equation over ℤ has a full vector coset normal form if and only if this holds for the equations with at least one output whose form Q is nonzero and semidefinite of either sign.

*Proof.* Use the case split of Theorem 4.2 (`branch_exhaustive`). If Q ≡ 0, the scalar relation behind the weak form already carries the full-residue form of the case without unknowns (`linearBranchFullNF_holds`). In the quotient-anisotropic indefinite case every off-centre vector of a solution lies in the radical, and f is globally affine (`anisotropicIndefiniteFullNF_holds`). Let Q have a non-radical isotropic vector. If d ≥ 3, the Eichler transformations x ↦ x + polar(x, e)v - \big(polar(x, v) + Q(v)\,polar(x, e)\big)e, with e isotropic and polar(e, v) = 0, preserve Q. Through an integer solution they return to the integer lattice at two parameters ±M, and output uniqueness at these two points forces every output coordinate to vanish on the polar complement of two isotropic vectors that are not polar-orthogonal to each other. This is impossible, so every off-centre vector is radical and f is again globally affine (`isotropicBranchFullNF_of_three_le_polarRank`). If d ≤ 2, then Q = XY in rational coordinates modulo the radical. If the residual R were not constant, a quadratic section of the solution set along an input line and the scaling (X, Y) ↦ (λX, Y/λ) would give two integer solutions at one input with different outputs. The factor λ ∉ {0, 1} must be congruent to 1 modulo the denominators of the section and divide its values on a progression; it is λ = F(k₀)/F(k₁) for k₀ = k₁ + K F(k₁) s, since F(k₀) = F(k₁)\,μ(s) with μ(s) ≡ 1 \pmod{K} (`exists_scaling_divisor`). So R is constant, and a constant residual gives the full form with a common slope (`isotropicBranchFullNF_of_polarRank_le_two`). ∎

Neither case can be merged into the other: b(2u + 1) = 0 is output-unique of polar rank two with an off-radical integer solution, and (4b + 1)(4u + 1) = 1 has constant residual 1, not 0 (`rank_hypothesis_needed`, `residual_zero_not_forced`).

For the semidefinite branch in polar rank at least three we use one analytic input. Call TCER the following statement (`TernaryCosetEventualRepresentation`): for every positive definite integral ternary form y ↦ y^(\top)Sy and every coset ρ + dℤ³ there are finitely many primes and finitely many positive integers e such that, for every bound on the valuations at those primes, every sufficiently large integer that is primitively represented by the coset modulo every prime power, has the bounded valuations, and is not e times a rational square for any of the e, is represented by the coset.

**Proposition 10.7** (`sealedFullNF_of_TCER`, `generalFullNF_of_TCER`). Assume TCER. Then every total function defined by a single quadratic equation over ℤ, with any finite number of unknowns, has a full vector coset normal form, and in particular a weak vector coset normal form.

*Proof.* By Proposition 10.6 it suffices to treat a nonzero semidefinite form. Polar rank at most two is settled without TCER (rank one by the no-unknown case, rank two by `rankTwoSemidefiniteFullNF_holds`). In polar rank at least three a ternary slice of the equation is fixed first, two of its cosets with different output residues are chosen, and a progression of targets is built that is primitively represented at every prime power, has prescribed valuations at the bad primes and avoids the exceptional square classes; TCER applied to both cosets gives two solutions at one input with different outputs unless the residual is constant (`ccr_of_TCER`, `semidefiniteFullNF_allRanks_of_TCER`). The formal statement is on the original class `SingleQuadraticDefinableFunctionZZ`. ∎

In ordinary mathematics TCER is supplied by an eventual-representation consequence of the splitting of the theta series of a ternary lattice coset, stated for an individual coset on p. 5 of the published version of [KK26]. We record it in the form used here.

**Lemma 10.8** (Kane--Kim consequence in the TCER convention). Let S be a positive definite integral symmetric 3 × 3 matrix with ternary form Q_S, d ≥ 1 and ρ ∈ ℤ³. There are finitely many primes and finitely many positive integers e such that, for every bound b on the valuations at those primes, there is N₀ ≥ 1 with the following property: every integer N ≥ N₀ that is primitively represented by ρ + dℤ³ modulo every prime power, satisfies v_p(N) ≤ b(p) at those primes and is not e times a rational square for any of the e, equals Q_S(ρ + dx) for some x ∈ ℤ³. In particular TCER holds.

*Proof.* If a prime divides d and every coordinate of ρ, no integer is primitively represented by the coset modulo that prime, and the primitive statement TCER is empty for this coset. Otherwise d and the coordinates of ρ are coprime, and the coset is the lattice coset dL + ρ of conductor d in the sense of [KK26], for the integral lattice L = ℤ³ with bilinear form x^(\top)Sy. Its theta series splits as E + U + f. The coefficient of E at N is a product of local densities by Shimura's Siegel--Weil formula for lattice cosets, and it is at least c_{ε}N^(1/2 - ε) when N is locally represented by the coset and has bounded divisibility at finitely many bad primes; U is supported on finitely many square classes tℤ²; and the coefficient of f is O(N^(3/7 + ε)) by Duke's bound. With ε = 1/56 the representation number of N outside the classes tℤ² is at least cN^(27/56) - CN^(25/56) = N^(25/56)(cN^(1/28) - C), which is positive once N > (2C/c)²⁸; here c > 0 and C depend only on the coset and the bound b, and no effective value is claimed. Take the bad primes of [KK26] and let the e be the t. A solution modulo every power of p gives a p-adic solution by compactness of ℤ_p³, so primitive representability modulo every prime power implies local representability; excluding every class eℚ² excludes at least the classes tℤ²; and N₀ may be taken ≥ 1. The order of quantifiers --- coset, then bad primes and exceptional classes, then the valuation bound, then the threshold --- is the order in [KK26]. ∎

In Lemma 10.8, N is primitively represented by ρ + dℤ³ modulo p^e if Q_S(ρ + dx) - N is divisible by p^e for some x ∈ ℤ³ such that p does not divide every coordinate of ρ + dx; the vector may depend on p and e. This is the local hypothesis `LocalPrimRep` of TCER, and the primitivity concerns the represented vector ρ + dx, not x. The first step of the proof uses it: for S = I₃, d = 2 and ρ = 0 the integer 4 = Q_S(2, 0, 0) is represented by the coset modulo every prime power, but not primitively modulo 2, since every point of 2ℤ³ has all coordinates even; so under an ordinary local hypothesis this coset would not be vacuous. We do not state or use the version with ordinary local representability.

The numbering of Lemma 10.8 is ours: [KK26] states the consequence in its introduction, proves the splitting and the finiteness of the exceptional square classes, and takes the lower bound for E from Shimura's formula and the bound for f from Duke. The only analytic input not formalized in the artifact is TCER itself. The Lean development verifies the implication from its explicitly stated form to Proposition 10.7; the hypothesis is an argument of the theorem, not an axiom, and the standard-axiom footprint of the conditional theorem does not certify it. Formalizing that input, or replacing it in this application by an argument that avoids the analytic theory, is a separate task.

**Several outputs.** With two or more outputs the branch proofs give more than a full form: one integer slope on all residue classes. Say that f : ℤⁿ → ℤᵐ has a *common slope* if there are M ≥ 1 and an integer m × n matrix B with f(a + Mt) = f(a) + Bt for all a, t ∈ ℤⁿ (`CommonSlopeIntNF`).

**Proposition 10.9** (`singleQuadratic_iff_commonSlope_of_TCER`). Assume TCER and let m ≥ 2. A function f : ℤⁿ → ℤᵐ is defined by a single quadratic equation over ℤ, with any finite number of unknowns, if and only if it has a common slope.

*Proof.* Only the forward direction uses TCER (`sealedCommonSlopeNF_of_TCER`). With m ≥ 2 the form Q is nonzero, since a relation with Q ≡ 0 is output-unique only when m ≤ 1, and its polar rank d is at least m. In the isotropic branch with d ≥ 3 no input with an affine centre has an integer solution: if the off-centre vector x of a solution is radical, a shift by an integral multiple Ne₀ of a non-radical isotropic vector keeps Q(x), gives a solution at the same input and makes the off-centre vector non-radical, and the Eichler argument of Proposition 10.6 applies; so this branch contains no function (`isotropic_three_le_polarRank_not_defines`). With d ≤ 2 the residual is constant (Proposition 10.6) and the constant-residual transport gives a common slope. In the quotient-anisotropic indefinite case f is globally affine, and its rational coefficients are the integers f(0) and f(e_i) - f(0) (`intAffine_of_ratAffine`). In the semidefinite case the positive definite reduction and TCER give a constant residual, hence a common slope, before any full form is extracted.

The backward direction holds for every m without TCER (`singleQuadratic_of_commonSlope`). Put β_{ρ} = f(ρ) for ρ ∈ {0, \dots, M - 1}ⁿ and δ_{ρ} = Mβ_{ρ} - Bρ. With unknowns u ∈ ℤⁿ and e ∈ ℤ^{Mⁿ} the equation
  \Big(\sum_{ρ} e_{ρ} - 1\Big)² + \sum_{ρ} e_{ρ}(e_{ρ} - 1) + \Big\lVert a - Mu - \sum_{ρ} e_{ρ}ρ\Big\rVert² + \Big\lVert Mb - Ba - \sum_{ρ} e_{ρ}δ_{ρ}\Big\rVert² = 0
has total degree two, and every summand is non-negative on the integers. A solution therefore has e equal to a unit vector at some ρ, a = Mu + ρ and Mb = M(β_{ρ} + Bu), so b = f(ρ + Mu) = f(a); conversely Euclidean division of a by M gives a solution with b = f(a), and its witnesses are unique (`slopeEncoder_graph_iff`, `slopeEncoder_witness_unique`). The equation uses n + Mⁿ unknowns besides the outputs; no minimality is claimed, and one-hot quadratic penalties are a known device. ∎

The map a ↦ a² is defined by b - a² = 0 (`sqFn_singleQuadratic`), and (a + M)² - a² = 2Ma + M² depends on a, so a ↦ (a², 0) has no common slope (`sqPadFn_not_commonSlope`).

**Proposition 10.10** (`sqPadFn_not_singleQuadratic_of_TCER`). Assume TCER. The map ℤ → ℤ², a ↦ (a², 0), is not defined by a single quadratic equation over ℤ.

*Proof.* By Proposition 10.9 with m = 2 and the remark above. ∎

So adding a constant output coordinate need not preserve definability by one quadratic equation; the zero-padding in Theorem 4.3 pads linearly and is a different operation. The forward direction of Proposition 10.9 needs the branch proofs, because a full form does not give a common slope, already for one output.

**Proposition 10.11** (`not_commonSlope_of_fullVectorCosetNF`). It is not the case that every function defined by a single quadratic equation over ℤ that has a full vector coset normal form has a common slope.

*Proof.* The equation (2b - a)(2b + 3a - 1) = 0 defines f(2t) = t, f(2t + 1) = -3t - 1, which is affine on both classes modulo 2 (`parityFn_singleQuadratic`, `parityFn_fullVectorCosetNF`). A common slope with modulus M would give f(2M) - f(0) = f(1 + 2M) - f(1), that is M = -3M (`parityFn_not_commonSlope`). ∎

A common slope is a finite certificate. Its image is \bigcup_{ρ}\big(f(ρ) + Bℤⁿ\big) over ρ ∈ {0, \dots, M - 1}ⁿ (`commonSlope_range`).

**Proposition 10.12** (`commonSlope_injective_iff`). Let f : ℤⁿ → ℤᵐ satisfy f(a + Mt) = f(a) + Bt for all a, t, with M ≥ 1 and B an integer matrix. Then f is injective if and only if t ↦ Bt is injective on ℤⁿ and f(ρ) - f(σ) ∉ Bℤⁿ for distinct ρ, σ ∈ {0, \dots, M - 1}ⁿ.

*Proof.* Write every input as ρ + Mu with 0 ≤ ρ_i < M; the decomposition is unique. A collision f(ρ + Mu) = f(σ + Mv) reads f(ρ) - f(σ) = B(v - u). If ρ = σ it is a kernel element of B; otherwise it is an overlap of two residue images. Conversely a kernel element t ≠ 0 gives f(Mt) = f(0), and f(ρ) - f(σ) = Bt gives f(ρ) = f(σ + Mt) with ρ ≠ σ + Mt. ∎

For such f, injectivity forces n ≤ m through Theorem 4.1, which needs no hypothesis (`commonSlope_injective_dim`).

**One output.** With one output the forms Q ≡ 0 and polar rank one survive, and after the witnesses are removed a single equation αy² + (β · x + d)y + T(x) = 0 with integer coefficients and T quadratic remains (`scalar_commonSlope_or_rn_of_TCER`). The witnesses disappear for different reasons in the two cases. If Q ≡ 0 the equation is linear in the output and the unknowns; at an input where an unknown had a nonzero coefficient, either the output has coefficient zero and is not determined, or a kernel vector with nonzero output coordinate gives a second output, so output uniqueness makes the coefficient of every unknown vanish at every integer input, hence identically (`rn_of_sol_linear`); the completed-square centre of the other branches is not used. If the polar rank is one, every vector whose output coordinate is zero lies in the radical of the polar form (`witnessDir_inRadicalQ`), and the unknowns are eliminated from the equation (`noWitnessData_defines`). If α ≠ 0 its discriminant is the square of 2αf(x) + β · x + d at every integer x, hence of an integer affine form, so y is a solution exactly when 2αy is one of two integer affine values u(x), v(x) (`rn_two_roots`). The sets where 2α divides u or v are empty or cosets of subgroups of ℤⁿ, and together they cover ℤⁿ.

**Lemma 10.13** (`addSubgroup_two_coset_cover`). Let H and K be subgroups of an additive commutative group G and b ∈ G. If every element of G lies in exactly one of H and b + K, then H = K, b ∉ H, every element lies in H or in b + H, and g + g ∈ H for every g ∈ G.

*Proof.* First b ∉ H, since b = b + 0 lies in b + K. If k ∈ K were not in H, then k ∈ b + K, so -b ∈ K and 0 ∈ H would also lie in b + K. If h ∈ H were not in K, then h + b ∉ b + K, so h + b ∈ H and b ∈ H. Hence H = K. If g ∈ H then g + g ∈ H. If g ∈ b + H and g + g ∉ H, then g + g ∈ b + H and g = (g + g) - g ∈ H, which is impossible. No finiteness or density is used. ∎

**Proposition 10.14** (`scalar_singleQuadratic_iff_of_TCER`). Assume TCER. A function f : ℤⁿ → ℤ is defined by a single quadratic equation over ℤ, with any finite number of unknowns, if and only if one of the following holds: f has a common slope; f agrees on ℤⁿ with a polynomial with rational coefficients of total degree at most two; or there are integer vectors p, q and integers c, c', with p - q having even coordinates, p having an odd coordinate and c - c' odd, such that 2f(a) = p · a + c when p · a + c is even and 2f(a) = q · a + c' otherwise.

*Proof.* The reverse direction holds without TCER (`singleQuadratic_of_scalarFamilies`). A common slope is compiled as in Proposition 10.9. For a rational polynomial q with common denominator N the equation Nb - Nq(a) = 0 has no unknowns. In the third case (p - q) · a + (c - c') is odd for every a, so exactly one of p · a + c and q · a + c' is even, and (2b - p · a - c)(2b - q · a - c') = 0 holds exactly at b = f(a); again there are no unknowns.

Only the forward direction uses TCER (`sealed_scalarFamilies_of_TCER`). If Q ≢ 0 and the polar rank is at least two, the branch arguments in the proof of Proposition 10.9 use only m > 0 and give a common slope (`commonSlope_of_TCER_of_two_le_polarRank`). Otherwise the equation reduces to αy² + (β · x + d)y + T(x) = 0. If α = 0, f is a rational polynomial of degree at most two. If α ≠ 0, then at each integer x the equation has the integer root y = f(x), so Δ(x) = (β · x + d)² - 4αT(x) = (2αf(x) + β · x + d)² is a square at every integer point. A quadratic polynomial that is a square at every integer point is the square of an affine function L with rational coefficients (`c21_affine_square`); since L(x) = ±(2αf(x) + β · x + d) is an integer for every integer x, the constant s = L(0) and the coefficients ℓ_i = L(e_i) - L(0) are integers. Put u(x) = -(β · x + d) + (ℓ · x + s) and v(x) = -(β · x + d) - (ℓ · x + s). Then 4α(αy² + (β · x + d)y + T(x)) = (2αy - u(x))(2αy - v(x)), so for all integers x and y the equation holds if and only if 2αy = u(x) or 2αy = v(x) (`rn_two_roots`). Let I_u and I_v be the sets where 2α divides u or v; on I_u the quotient is a solution, so 2αf = u there, and likewise on I_v, and I_u ∪ I_v = ℤⁿ. If I_u and I_v meet at x₀, both divisibilities hold on x₀ + 2αℤⁿ, so u = v there, hence everywhere (`affine_eq_of_eq_on_coset`), and f is affine; the same holds if one of the sets is empty. Otherwise I_u and I_v are disjoint cosets of {h : 2α ∣ U · h} and {h : 2α ∣ V · h}, where U and V are the linear parts of u and v. By Lemma 10.13 these subgroups coincide and contain 2ℤⁿ, so α divides the coordinates of U, V and the constants; writing u = α(p · x + c) and v = α(q · x + c'), the two sets are where p · x + c, respectively q · x + c', is even. Exactly one of them holds at 0 and at each unit vector, which gives the parity conditions, and a proper non-empty set forces an odd coordinate of p (`rn_classify`). ∎

The three families overlap: an affine function belongs to the first two. The rational coefficients are needed, as a ↦ a(a - 1)/2 shows, and the function of Proposition 10.11 is of the third kind with p = 1, c = 0, q = -3, c' = 1 (`parityFn_parityAffine`). The denominator two refers to the normalized case in the proof: two distinct roots whose integrality sets are both non-empty and disjoint. Other displayed denominators occur, since multiplying an equation by a non-zero integer does not change its graph: (6b - 3a)(6b + 9a - 3) = 9(2b - a)(2b + 3a - 1). A repeated root also defines a function: (2b - 2a)² = 0 holds exactly at b = a. The following are negative controls for the parity and coverage conditions of the third family, not impossibility results for other presentations: (2b - a)(2b - a - 2) = 0 has two solutions at a = 0, and (3b - a)(3b - a + 1) = 0 has none at a = 2 (`sameParity_not_function`, `modThree_not_total`). For every number of outputs other than one, definability under TCER is exactly the common slope (`singleQuadratic_iff_commonSlope_of_TCER_of_ne_one`).

**Proposition 10.15** (`singleQuadratic_padZero_iff_of_TCER`). Assume TCER. For every f : ℤⁿ → ℤᵐ, the map a ↦ (f(a), 0) ∈ ℤᵐ × ℤ is defined by a single quadratic equation over ℤ if and only if f has a common slope.

*Proof.* A common slope of (f, 0) restricts to f, and a common slope of f extends by a zero row (`commonSlope_padZero_iff`). For m ≥ 1 apply Proposition 10.9 with m + 1 ≥ 2 outputs; for m = 0 both sides hold. No definability of f itself is assumed. ∎

Proposition 10.10 is the case f(a) = a² (`sqPadFn_not_singleQuadratic_of_padding`). Common slopes compose: if f has modulus M and matrix B and g has N and C, then g ∘ f has MN and CB (`commonSlope_comp`); this is not a statement about composition of definable functions in general. In the equation of Proposition 10.9 the part of degree two in the output b and the unknowns u, e is a sum of squares that vanishes only at zero, so every function with a common slope has a presentation whose quadratic part in the output and the unknowns is positive definite and whose witnesses are unique (`commonSlope_posDef_presentation`); nothing is claimed about other presentations.

**Unknowns.** Without unknowns the scalar classification needs no analytic input.

**Proposition 10.16** (`zeroWitness_iff`). A function f : ℤⁿ → ℤ is defined by a single quadratic equation over ℤ without unknowns if and only if f agrees on ℤⁿ with a polynomial with rational coefficients of total degree at most two, or f is of the third kind in Proposition 10.14.

*Proof.* The reverse direction is the construction in the proof of Proposition 10.14, which uses no unknowns. Conversely, without unknowns the output is the only coordinate of the quadratic part, so its polar rank is at most one, and the argument of Proposition 10.14 in the cases Q ≡ 0 and polar rank one gives the two alternatives (`scalar_rn_of_polarRank_le_one`, `rn_classify`). Neither case uses TCER. ∎

A common slope need not be definable without unknowns: Proposition 10.18 gives an example.

**Proposition 10.17** (`singleQuadratic_iff_uniqueWitness_of_TCER`). Assume TCER. A function f : ℤⁿ → ℤᵐ is defined by a single quadratic equation over ℤ if and only if it is defined by a single quadratic equation over ℤ whose solutions in the unknowns coincide whenever the inputs and outputs do. In particular each input then has exactly one solution in the output and the unknowns together.

*Proof.* The reverse direction is immediate. For the forward direction, with m ≠ 1 the function has a common slope by Proposition 10.9, the case m = 0 being trivial; with m = 1 it has a common slope or is of one of the other two kinds of Proposition 10.14. In the equation of the proof of Proposition 10.9 the degree-two part in the output and the unknowns is a sum of squares that vanishes only at zero, and a solution determines e, as the unit vector at the residue ρ of a modulo M, and then u (`commonSlope_posDef_presentation`, `uniqueWitness_of_commonSlope`). The other two kinds are defined without unknowns (Proposition 10.16). Each input has a solution by totality, its output is unique, and then so are the unknowns (`existsUnique_of_uniqueWitness`). Only the forward direction uses TCER. ∎

This concerns one presentation of each function, not every presentation.

**Proposition 10.18** (`floorThird_min_witnesses`). The map ℤ → ℤ, a ↦ ⌊a/3⌋, is defined by a single quadratic equation over ℤ with one unknown, and by no single quadratic equation over ℤ without unknowns.

*Proof.* The equation (3b - a + 1)² + u² - 1 = 0 has one unknown u. If (3b - a + 1)² + u² = 1 then |3b - a + 1| ≤ 1, so a - 2 ≤ 3b ≤ a and b = ⌊a/3⌋; conversely, for a = 3q + r with 0 ≤ r < 3 take b = q and u = 1 if r = 1, u = 0 otherwise (`floorThird_oneWitness`). At a = 1, b = 0 both u = 1 and u = -1 are solutions, so the unknown is not unique in this presentation (`floorThirdPoly_two_witnesses`). Without unknowns, Proposition 10.16 would make a ↦ ⌊a/3⌋ a rational polynomial of degree at most two or of the third kind of Proposition 10.14. The first is impossible: such a polynomial would vanish at 0, 1 and 2 and take the value 1 at 3. In the second, the coefficient p is odd, since n = 1; so one of x = 0 and x = 1 has px + c even, and then so has x + 6, which gives 6p = 2(⌊(x + 6)/3⌋ - ⌊x/3⌋) = 4, impossible in integers (`floorThird_not_zeroWitness`). No TCER is used. ∎

The count refers to this one format, a single equation of total degree at most two with integer unknowns; we do not study the least number of unknowns in general. The map a ↦ ⌊a/3⌋ has a common slope, with M = 3 and B = 1, and belongs to neither of the other two families; a ↦ a² has no common slope (`sqFn_not_commonSlope`) and grows faster than any function of the third kind, which is affine on each of two cosets, so it belongs only to the second; and the function of Proposition 10.11 has no common slope and takes the values 0, -1, 1, -4 at 0, 1, 2, 3, which no polynomial of degree at most two does. So none of the three families of Proposition 10.14 can be dropped.
## 11. Relation to the literature

We separate what is used from what is proved.

**Classical inputs, used and not claimed.** Two are external: the decidability of integer quadratic solvability [GS04], and DPRM [DPR61, Mat70]. Section 10 uses a third, the eventual representation theorem for ternary lattice cosets of Kane and Kim [KK26], through Lemma 10.8. Skolem's degree reduction, and with it PP₂ = SE₄ = Dioph, is proved here rather than assumed (Theorem 6.2); REC ⊊ RE and the equality TotComp = Fun(PP₂) under DPRM are derived in Section 6. Section 6 states each of these as a named hypothesis or proves it from mathlib's computability library. Dirichlet's theorem on primes in arithmetic progressions and Lagrange's four-square theorem are used from mathlib.

**Contributions.** (1) The uniform finite-fibre quadratic height bound (Theorem 2.1); (2) the finite-fibre cardinality bound with the same constant (Theorem 2.2); (3) quadratic growth of SE₂-definable total functions (Theorem 3.2); (4) the sharp injective dimension theorem n ≤ m, its converse, and the structural alternative that yields it (Theorem 4.1, Theorem 4.2, Theorem 4.3), with ca(SE₂) = 1 as a corollary; (5) the classification graph(p) ∈ SE₂ ⟺ deg p ≤ 2 (Theorem 5.1); (6) non-closure of Fun(SE₂) under composition, and exactness of Fun(SE₂) ⊊ TotComp by arity (Theorem 3.4, Theorem 3.5); (7) the typed certificate language with per-kind soundness (Definition 8.2, Theorem 8.3); (8) the unconditional structured summit (Theorem 8.5); (9) the arithmetic projection dichotomy in both its bounded and its data-carrying form, for every number of unknowns (Theorem 9.2, Theorem 9.3); (10) the effective diagonalization lemma for coded families (Theorem 6.5) and its consequence at arity one (Corollary 6.6); (11) the classification of SE₂-definable total functions under TCER (\cref{proposition:10.9,proposition:10.14}), with converse constructions and the case without unknowns that need no analytic input (Proposition 10.16).

The correct summary of the paper is this: the structural theorems identify the internal finite-fibre and functional constraints on the single-quadratic fragment, and combining them with classical decidability, DPRM and degree reduction places the fragment exactly in the computability hierarchy. The phase-diagram arrows themselves are not claimed as new; what is new is the pair of constraints that make the diagram exact, and the positive description of the infinite fibres.

**Comparison with adjacent programmes.** The existential-rank literature (Daans–Dittmann–Fehm [DDF] and related work) bounds the *number* of existential variables while leaving the degree free, for the domains and the classes of definable sets considered there; the present fragment bounds the *degree* while leaving the number of unknowns free. The degree–unknowns trade-offs for universal equations (Jones [Jon82]: every r.e. set by one equation of fixed degree in a fixed number of unknowns, degree and unknowns traded against each other) are the classical form of that tension; the finite-fold programme (Matiyasevich [Mat10]) asks that each parameter point have finitely many *witnesses*, a bound on the witness side, whereas our finite fibres are on the *output* side with the witnesses unrestricted. We prove no refinement in either direction between these hierarchies and ours, and the objects studied differ: fibre growth, function growth and graph classification do not appear there. Theorem 5.1 is not derived from the degree-free arity collapse of [DDF, Lemmas 8.19–8.20], and that collapse is not derived here from Theorem 5.1; whether either implies the other is a question this paper does not settle. The closest published statement to our Section 8 is in [GS04]. Besides deciding solvability, the algorithm there decides, for a single given equation and a region cut out by finitely many rational affine hyperplanes, whether the solution set is finite, lists it when it is, and reports infinitude when it is not. Two differences should be stated plainly. First, that is an algorithmic statement about one instance: it answers a question about the equation in front of it, and it does not by itself yield a constant valid at every parameter point, which is what Theorem 2.1 asserts and what the whole of Sections 3–5 rests on. Second, it reports infinitude rather than describing it, whereas Theorem 8.5 exhibits the infinite fibre as generated by data of one of three named kinds. We do not claim that our results could not be derived from theirs with further work; we claim that the statements are different, and that the uniformity in the parameters and the structural description of the infinite case are what this paper adds.

**Presburger-definable functions.** Presburger cell decomposition describes the definable functions on ℤⁿ by finitely many linear formulas on cells cut out by linear inequalities and congruences (Cluckers [Clu03], Definitions 1–2 and Theorem 1). Section 10 concerns a different restriction: the graph of a total function must be the projection of the zero set of one polynomial of total degree at most two. With two or more outputs the classified functions are Presburger-definable and form a proper subclass: their linear parts coincide on all residue classes, and a ↦ (|a|, 0) is Presburger-definable without a common slope. With one output the common-slope and parity-affine families are Presburger-definable, while a function with a genuinely quadratic part, such as a ↦ a², is not; so the scalar class is not contained in the Presburger-definable functions. The contrast with Presburger arithmetic does not come from an inability of one quadratic equation to express inequalities: four squares define the relation a ≥ 0. It comes from asking for the graph of a total function, with a unique output at every input. The one-hot quadratic penalty behind the converse constructions is a standard device of quadratic unconstrained optimization; the characterization of the functions is what Section 10 adds.

**The nearest neighbour on the infinite side.** Grechuk and Agbanwa [GA26] fix a non-degenerate quadratic form F and a univariate integer polynomial P and develop a method for showing that P(x) is represented by F for infinitely many integers x. The method covers certain cubic and quartic P, and certain P of the form R(Q(x)) with deg R = 3 and deg Q = 2; the headline application is that x⁶ − 4 is a sum of two squares infinitely often, hence that y² + x³y + z² + 1 = 0 has infinitely many integer solutions. Their main results are formalized in Lean. This is the nearest neighbour to Theorem 8.5 in the current literature and deserves to be placed precisely. It is a 2026 arXiv preprint, and we cite it as such: nothing below treats it as a published theorem. Their question concerns one pair (F, P) at a time and is answered by establishing infinitude; ours fixes a single equation of total degree at most two and asserts, with one constant valid at every parameter point, that each scalar fibre is either bounded or carries arithmetic data generating an infinite output subset. Neither statement contains the other: they obtain infinitude for families we do not treat, and we obtain uniformity in the parameter together with a description of the infinite case, which they do not claim. Their own reading of the boundary agrees with ours: they observe that when deg P ≤ 2 the resulting equation is in principle covered by the Grunewald–Segal algorithm, which is the same placement of [GS04] we make in Definition 1.5 and in the comparison above. We do not use their method and make no priority claim against it. That both developments are Lean-formalized is a coincidence of practice, not a mathematical relation. Set against each other at the level of statements:

|  | Grechuk–Agbanwa [GA26] | this paper |
|---|---|---|
| object | one fixed non-degenerate quadratic form F and one univariate P, of certain degrees 3 and 4 and certain composites R∘Q | one equation of total degree ≤ 2, with parameters |
| question | is P(x) represented by F for infinitely many integers x? | for every parameter point, is the scalar fibre bounded, and if not, by what data is it generated? |
| quantifier over parameters | none: the pair (F, P) is fixed | one constant C chosen after the equation and before the parameter |
| conclusion in the infinite case | infinitude is established | an arithmetic certificate of one of three named kinds is exhibited |
| logical application | not the aim | finite-fibre relations, definable functions, the computability placement of SE₂ |
| Lean scope | the main results | the whole structure theory, Sections 2–9 |
| status | arXiv preprint, July 2026 | — |
Neither row of conclusions implies the other: they treat representation problems we do not, and we obtain parameter-uniformity together with a description of the infinite case, which they do not claim.

The theory of integral binary quadratic forms and their unit orbits (Lagrange reduction, Nagell [Nag]) is an *input* to Section 9 and to Section 10 rather than a competitor: what is done here with it is the uniformity in the affine data, which is what the projection dichotomy adds. The quartic collapse SE₄ = Dioph is classical and is quoted as such.

**Search bounds.** The nearest quantitative neighbours of Theorem 2.1 are the search bounds for Diophantine equations, a line beginning with Cassels [Cas55] — an isotropic integral quadratic form in n variables has a nonzero integral zero of size at most a power of its largest coefficient — and continued by many authors, including Masser [Mas98] for the rational case; Fukshansky [Fuk13] surveys the direction. The closest single statement is Dietmann [Die03], as printed in §6 of the survey [Fuk13] (with the s = 2 case due to Kornhauser): for an inhomogeneous integral quadratic Q in s ≥ 3 variables with nonsingular quadratic part and coefficient height at most H, there is a polynomial bound Λ_s(H) such that if Q has an integer zero at all, it has one of size at most Λ_s(H). Dietmann's theorem, as stated in Fukshansky's peer-reviewed survey, gives a small zero under existence assumptions and a coefficient-height bound; the original Dietmann article was not independently audited here, and it is not a load-bearing input of this paper. Three differences should be stated. First, that literature bounds the SMALLEST solution, whereas Theorem 2.1 bounds EVERY element of a fibre that is finite; neither quantifier implies the other, since a finite fibre may have a small least element and a large greatest one. Second, their bound is a function of the coefficient height of the one equation at hand, whereas ours fixes the equation with a parameter block and asserts a single constant valid at every parameter point, with an exponent that does not grow with the number of unknowns. Third, Dietmann assumes s ≥ 3 and a nonsingular quadratic part, whereas Theorem 2.1 assumes only total degree at most two — the singular and low-arity cases, which are exactly where Section 9 does its work, are inside our statement. We do not claim independence from this line, and it is a fair question whether a uniform-in-parameters bound can be extracted from those methods; we claim that the statements differ in the three ways above.

## 12. Formalization

**What the kernel certifies.** Apart from the literature-to-TCER adapter in Lemma 10.8, every result stated above is a Lean 4 declaration, with the external inputs retained as the explicit hypotheses specified below; the declarations are in the accompanying artifact, archived at ⟨DOI⟩. For declarations cited in the paper-claim registry, `scripts/PaperClaimTypeReport.lean` records elaborated types and axiom footprints; `scripts/FinalAxiomReport.lean` is a separate report over its own listed roots. Every recorded footprint is contained in the standard set `[propext, Classical.choice, Quot.sound]`; contained, not equal, since the roots do not all use all three. The forbidden tokens `sorryAx`, `native_decide`, `ofReduceBool`, `trustCompiler` do not occur anywhere in the development. The toolchain is `leanprover/lean4:v4.31.0-rc1` with the mathlib revision pinned in the lakefile; the Lean tree distributed with the paper is copied from a clean-room build whose source manifest is required to match hash for hash, and the artifact ships the build script and the manifests. The counts — roots, their division among subsets of the standard set, and the external-input-free roots — are in `release/TRUST_BOUNDARY_APAL.md` of the artifact, where a tool recomputes them from the certificates and fails the build if the document and the development disagree.

**External inputs are hypotheses.** The two classical inputs (\cref{definition:1.5,definition:1.6}) and the analytic input TCER of Section 10 are `def … : Prop`, and a result uses one only by taking it as an argument. TCER is not formalized: Lemma 10.8 derives it from [KK26] in ordinary mathematics. `#print axioms` reports transitive *axiom* dependencies and is blind to hypotheses, so a conditional and an unconditional theorem can print the same footprint; which results are unconditional is therefore read from a second report, `scripts/HypothesisBinderLedger.lean`, which inspects the hypothesis binders of each root's type and reports the roots that carry no external-input binder, explicit, implicit, instance or wrapped, with seven planted-hypothesis controls. A few load-bearing declarations — notably the conversion of a structured family into a certificate in Section 8 — are definitions producing data rather than theorems and so are not roots of the report; their footprints are inherited by every theorem that uses them, and those theorems are reported. The layers are:

| layer | results | input used |
|---|---|---|
| unconditional | \cref{theorem:2.1,theorem:2.2,theorem:3.2,theorem:3.3,theorem:3.4,theorem:4.1,theorem:5.1,theorem:6.1,theorem:6.2}, \crefrange{theorem:8.3}{theorem:8.5}, \cref{theorem:9.2,theorem:9.3} | none beyond mathlib |
| conditional on Definition 1.5 | SE₂ ⊆ REC and its strictness at positive arity (Theorem 6.3 and Corollary 6.6) | code-uniform quadratic solvability |
| conditional on Definition 1.6 | RE = PP₂ = SE₄ and the function phase diagram of Section 7 | DPRM over ℕ |
| conditional on Definition 1.5 and Definition 1.6 | the complete relation phase diagram (Theorem 6.8) | quadratic solvability and DPRM over ℕ |
| unconditional, Section 10 | \cref{proposition:10.1,proposition:10.2,lemma:10.3,lemma:10.4,lemma:10.5,proposition:10.6,proposition:10.11,proposition:10.12,lemma:10.13,proposition:10.16,proposition:10.18}; the reverse directions of \cref{proposition:10.9,proposition:10.14,proposition:10.17} | none beyond mathlib |
| conditional on TCER | \cref{proposition:10.7,proposition:10.10,proposition:10.15}; the forward directions of \cref{proposition:10.9,proposition:10.14,proposition:10.17} | TCER (Lemma 10.8) |
Fun(SE₂) ⊆ TotComp belongs to the first row and not the second: it follows from totality together with a Diophantine graph, and uses neither classical input nor the height bound.

**Statement fidelity.** A formal proof certifies that a formal statement follows from the axioms; it does not certify that the statement says what the prose says. Three mechanisms guard that gap, and none of them establishes the correspondence by itself. The principal formal statements are registered in a frozen-statement layer: each registered declaration is frozen in a separate file and diffed against the production tree as declaration text with runs of whitespace normalised (`scripts/statement_diff.py`, with a negative control that plants a mutation and a missing declaration and requires both to be caught); definition bodies are covered separately by an elaborated-value hash certificate. The artifact's reconciliation report identifies the exported roots outside that registry. Second, every numbered theorem, proposition and corollary of this paper that names a Lean declaration has a row in a paper-claim registry (`submission/native/PAPER_CLAIMS.tsv`) recording the Lean roots it cites, the quantifier pattern, the degree bound, the witness domain and the external hypotheses, together with a hash of the paper statement and the SHA-256 of each cited root's elaborated Lean type (`scripts/PaperClaimTypeReport.lean`). The registry detects unreviewed changes to registered paper statements and to Lean root types: editing a statement, substituting an unrelated root, or changing a root's type fails the build, and the artifact ships planted negative controls, all of which must be caught. The semantic correspondence between a mathematical statement and a Lean type is recorded one row per cited root (`PAPER_CLAIMS_REVIEW.tsv`) as a model-assisted, author-approved correspondence registry: each row was read by a language model against the fully elaborated Lean type and its disposition was approved by the author; it is not established by text hashing alone, and the correspondence remains an author-approved mapping supported by the type and axiom reports, not a machine-certified one. Third, additional validation includes the concrete coefficient examples formalized in `SemanticQuadraticTwoWitness/Fidelity2W.lean` and `SemanticQuadraticSingular/Fidelity3W.lean`, and the validation record of Appendix C (`certificates/APPENDIX_C_STATEMENT_FIDELITY.log`), which reports a comparison of the monomial-count tables with an independent Python enumeration. These checks are supplementary and do not establish semantic correspondence between the paper and the Lean types; that correspondence remains subject to author review, recorded in the artifact (`release/AUTHOR_SIGNOFF_SHEET.md`).

**Names cited here.** Every declaration named in this paper exists in the development. The principal results and their roots are: the finite-or-structured theorem for single-quadratic fibres (Theorem 8.5, `uniformQuadraticFiberStructureZZ_of_quadratic`; its per-fibre corollary `singleQuadratic_fiber_bounded_or_structurallyInfinite` is the weaker ∀a∃B form of Definition 8.4 and is not the theorem); the arithmetic projection dichotomy, bounded or infinite (Theorem 9.2, `quadraticProjectionDichotomyZ_all`) and its data-carrying form (Theorem 9.3, `quadraticProjectionDichotomyZ_all_data`); the finite-fibre height bound (Theorem 2.1, `singleQuadratic_finiteFiber_height_vector`); definable-function growth (Theorem 3.2, `singleQuadratic_function_quadratic_growth`); the polynomial-graph classification (Theorem 5.1, `polynomial_graph_singleQuadratic_iff`); SE₂ ⊆ REC under the Grunewald–Segal principle (Theorem 6.3, `singleEqFragmentZZ_two_subset_recFragmentZZ`); the relation phase diagram at every positive arity under the two literature hypotheses (Theorem 6.8, `relation_phase_diagram_all_positive_arity_of_classical`); and the function phase diagram under DPRM_NN (Theorem 7.1, `function_phase_diagram_by_arity_of_DPRM_NN`); the exact roots of every numbered result are the rows of the paper-claim registry, and the full root map is in the artifact. The multi-parameter universal-pair question of Appendix C is an application of the same development and is not a headline result. Some names are cited as signposts into the sources and are covered by neither the frozen set nor the axiom report under those names; no numbered result of this paper rests on such a name. The census of cited names, and the reconciliation of the axiom report with the frozen set, are in the trust document, recomputed at every build.

Lean is an additional verification of the proofs given in this paper, not a substitute for them: every numbered result is proved in the text or in the appendices.

## Methods

The mathematics was produced in the order: computation, formalization, prose. Candidate statements were explored in a computer algebra system. Selected load-bearing statements were fixed by the author and frozen in separate files at designated milestones, before the corresponding production proofs or subsequent refactorings were accepted; the frozen layer is diffed against the production tree at every build. Computer-algebra and finite-instance checks — positive, negative and near-miss instances against an independent reimplementation — were used as adversarial validation of algebraic identities and translations. They do not certify that a formal statement models the intended problem: semantic correspondence between the intended mathematical problem, the paper statement and the Lean type remained subject to author review, and two earlier misformalizations of that kind were caught by review, not by the kernel. Tactic-level proof search in Lean was delegated to a large language model acting as a coding agent, in single-threaded sessions with no nested delegation; the author independently executed the clean build, the theorem audit and the axiom-footprint reports on the final source tree, model-generated proof terms were accepted only after kernel checking and reconciliation with the human-readable proof, and no agent self-report was accepted as evidence. A second model, from a different vendor, served as an adversarial reader of statements and drafts; its objections were recorded with dispositions, and those that were correct led to corrections incorporated here. Randomised and exhaustive numerical checks were used to look for counterexamples and to corroborate new lemmas before they were written down; they are evidence of the absence of certain errors and are never treated as proof.

## Data and artifact availability

The Lean sources, the frozen statement files, the axiom and ledger reports, the branch table, and the clean-room build script are archived at ⟨DOI⟩ and mirrored at ⟨REPO⟩, together with the hashes of every artifact referenced in Section 12. No data other than these artifacts underlies the results.

Every numeric claim of Section 12 and both locators above are substituted into this document at build time from the artefacts themselves; the build refuses to produce a final PDF while any of them is unfilled.

## Appendix A. Open problems

**The one-sorted coding arity, settled.** In the first version of this work the value of ca(SE₂) was left open at n = 2. It is now determined: Corollary 4.4 gives ca(SE₂) = 1. No single quadratic equation with any finite number of integer unknowns defines the graph of an injection ℤ² → ℤ. The mixed-semantics analogue, with inputs and output in ℕ and unknowns in ℤ, is a different question with a different answer --- it equals 2, witnessed by the Cantor pairing (Appendix B) --- and the two must not be identified. That they genuinely differ is itself a theorem (`natInput_intInput_separation_at_two`): `AtomGraphZ 2 2` and ¬\,`AtomGraphZZ 2 2` hold simultaneously. In particular Theorem 4.1 itself does not survive replacing ℤ by ℕ, and neither does the symmetric-point collision on a full lattice coset that proves it; it is the theorem and that collision that fail, not every individual step.

**A one-witness normal form.** For a single quadratic equation with exactly one unknown one expects a finite-union normal form of its fibres, a different object from the normal forms of total functions in Section 10: a finite exceptional set, finitely many polynomial progressions of degree at most two, and finitely many affine projections of unit orbits with the exponent restricted to a congruence class. Establishing it requires the finiteness of the number of unit-orbit classes for x² − Dy² = N in orbit-decomposition form. We state the expectation and do not prove it here; a draft formalization is in the development notes accompanying the artifact, where it is marked as conditional and unproved, and nothing in Sections 1–9 uses it.

**Effectivity.** The constant K of Theorem 9.2, and hence the constants of \cref{theorem:2.1,theorem:2.2,theorem:3.2}, are not effective. Theorem 4.1 carries no constant: its coset branch is a collision argument, not a count. Everything else in those proofs is explicit, so an effective version of Theorem 9.2 would make all of them effective with constants that can be read off mechanically. We do not claim that the small-solution bounds cited in Section 11 yield such a version: those bound solutions of a single equation, whereas what is needed is a bound uniform over all affine perturbations of a fixed quadratic part.

**Beyond Section 10.** Three questions are not addressed here. A Lean proof of TCER itself would remove the one analytic hypothesis of Section 10; the artifact states it as a hypothesis and Lemma 10.8 derives it from published work. The least number of unknowns with which a given SE₂-definable function can be defined is not determined in general; Proposition 10.18 settles one example. And the classification of Section 10 concerns graphs of total functions: a single quadratic equation defines more general relations, including the relation a ≥ 0 through four squares, and those are not classified.
## Appendix B. Capacity refinements and the arity-two witness

The capacity core (`APALLogicCore.lean`, `apal_logic_core`) bounds the arity at which single quadratic equations can define the graph of an injection into ℤ. What is proved is a pair of bounds, not an equality:

AtomGraphZZ 2 n → n ≤ 2   (the upper bound), and   AtomGraphZZ 1 1   (the lower bound, already at degree one).

The upper bound is now sharpened to AtomGraphZZ 2 n → n ≤ 1 (`atomGraphZZ_le_one`, a case of Theorem 4.1 at m = 1), so the two bounds meet and ca(SE₂) = 1 (`atomGraphZZ_capacity_eq_one`). The purpose of this appendix is therefore no longer to record a gap but to keep the two semantics apart, which remains necessary.

Two semantics must be kept apart, since they carry the same informal description and different theorems.

|  | inputs | output | unknowns | predicate | arity-two witness |
|---|---|---|---|---|---|
| one-sorted | ℤⁿ | ℤ | ℤʳ | `AtomGraphZZ` | **none exists** (Corollary 4.4) |
| mixed | ℕⁿ | ℕ | ℤʳ | `GraphAchievableZ` | **proved**: `graphCapacityZ r 2 = 2` for every r |
In the mixed setting the arity-two witness exists and the capacity is exactly two for every number of integer unknowns (`quadraticWitnessInertiaZ`): integer unknowns buy no input arity at degree two. That theorem does not transfer to the one-sorted setting, and we do not use it there. Over ℤ the arity-two witness does not exist at all, by Corollary 4.4; the bound n ≤ m of Theorem 4.1 is attained at every pair n ≤ m, but by the zero-padding of Theorem 4.3, not by any compression.

The appendix also records: PP₂ graphs of injections at every arity, so the failure at n ≥ 2 is a property of the *single-equation* fragment and not of degree two; the chain SE₂(k) ⊊ PP₂(k) ⊆ SE₄(k) for k ≥ 4; and the internal arity collapse of PP₂ through the integer tuple code.

Finally, on effectivity of the constants in Sections 2–4: as explained in Remark 2.3 the only non-explicit ingredient is the constant K of the projection dichotomy. The search-bound literature cited in Section 11 is explicit throughout, and is the natural place to look for the technique if an effective K is ever wanted. Everything else — the coefficient sums SL and SQ, the box counts, the arity bookkeeping — is explicit in the formalization, so an effective version of Theorem 9.2 would immediately make \cref{theorem:2.1,theorem:2.2,theorem:3.2,theorem:4.1} effective, with constants that can be read off mechanically.

## Appendix C. The multi-parameter universal-pair question

Bayer, David, Haßler, Matiyasevich and Schleicher [BDHMS25, §6.2] ask whether there is a pair of constants (ν, δ) such that every Diophantine subset of ℕᵖ is definable by a single equation with ν unknowns and degree at most δ, uniformly in p. The answer is negative, and the obstruction is a count. It is not a count of coefficient vectors: those range over ℤ and there are infinitely many of them. What is counted is the set of *specialisations* of one fixed polynomial as its parameters run over a finite box, and the count has the same shape as the one that proves Theorem 4.1 — a box of inputs against a box of images.

**Theorem C.1** (`coder_counting_bound_weighted`, `multiUniversalN_bound_weighted`, `multiUniversalZ_bound_weighted`, `wtCount_closed_form`; standard axioms). Let ν, δ : ℕ → ℕ and suppose that for every p, every Diophantine subset of ℕ^p is defined by a single equation in ν(p) unknowns of total degree at most δ(p), with unknowns ranging over ℕ or over ℤ. Then for every p ≥ 1,
  p − 1 ≤ wtCount δ(p) (ν(p) + 1) = C(δ(p) + ν(p) + 1, ν(p) + 2),
  where wtCount d k := Σ_{|m| ≤ d, m in k variables} (d − |m|).

*Proof.* Fix n and set p = n + 1.

*(1) The coder, and what universality is applied to.* Define e : ℕⁿ → ℕ by iterating Cantor's pairing bijection ⟨·,·⟩ : ℕ² → ℕ: e of the empty tuple is 0, and e(a₁, …, a_{k+1}) = ⟨e(a₁, …, a_k), a_{k+1}⟩ (`code`). Section 2 defines no coder; earlier versions of this appendix cited one there, and that reference was wrong rather than merely terse. e is injective, because ⟨·,·⟩ is and injectivity at arity k lifts to arity k + 1 in both components (`code_injective`). Its graph {(a, c) ∈ ℕⁿ⁺¹ : c = e(a)} is a Diophantine subset of ℕᵖ for p = n + 1, the pairing relation being cut out by a polynomial equation and the iteration being a finite conjunction of such (`diophN_graph_code`). The hypothesis of the theorem quantifies over every Diophantine subset of ℕᵖ, so it applies to this graph in particular. The hypothesis at p supplies an integer polynomial C in the p parameters (a, c) and r ≤ ν(p) unknowns u, of total degree d ≤ δ(p), such that (a, c) lies in the graph if and only if C(a, c, u) = 0 has a solution u in the admissible range. It is the *graph* that is represented, not a subset of ℕⁿ; this is where the extra parameter c comes from, and it is why the fibre below has 1 + r variables rather than r.

*(2) Specialisation.* For a ∈ ℕⁿ let Φ(a) := C(a, ·, ·) ∈ ℤ[c, u₁, …, u_r], the polynomial in 1 + r variables obtained by substituting the numbers a for the first n parameters. Its total degree is at most d.

*(3) Φ is injective.* Suppose Φ(a) = Φ(a′). Because e is total and single-valued, (a, e(a)) lies in the graph, so there is an admissible u with C(a, e(a), u) = 0, that is, Φ(a) vanishes at (e(a), u). Then Φ(a′) vanishes there too, so (a′, e(a)) lies in the graph, so e(a′) = e(a). Injectivity of e now gives a′ = a. Totality and single-valuedness are what produce the witness; injectivity is used only at this last step, to turn equal outputs into equal inputs.

*(4) Coefficient growth over a box, graded by monomial degree.* Write Φ(a) = Σ_{|m| ≤ d} f_m(a) · zᵐ, where z = (c, u) and m runs over the monomials of degree at most d in the 1 + r fibre variables. Each f_m is a polynomial in a with integer coefficients, and since C has total degree d and zᵐ already carries |m| of it, f_m has degree at most d − |m|. Let K := Σ_β |coeff_β(C)| be the ℓ¹ size of the fixed polynomial C, a finite number determined by C alone. For a in the box [0, N]ⁿ with N ≥ 1 this gives

  |f_m(a)| ≤ K · N^(d − |m|)
(`aux_coeff_bound_weighted`). The exponent drops with |m|: a monomial that has already spent |m| on the fibre variables can receive contributions only from those terms of C whose parameter part has degree at most d − |m|.

*(5) The count.* By (4) the coefficient at m takes at most 2K·N^(d−|m|) + 1 integer values, and since N ≥ 1 this is at most (2K + 1)·N^(d−|m|). Multiplying over the M := C(d + r + 1, r + 1) monomials, the number of distinct specialisations is at most (2K + 1)^M · N^W, where W := Σ_{|m| ≤ d} (d − |m|) = wtCount d (r + 1). By (3) the (N + 1)ⁿ points of the box give pairwise distinct specialisations, so

(N + 1)ⁿ ≤ (2K + 1)^M · N^W

(`aux_counting_weighted`). Suppose n ≥ W + 1 and take N := (2K + 1)^M + 1. Then (2K + 1)^M · N^W < N · N^W = N^(W+1) ≤ Nⁿ < (N + 1)ⁿ, contradicting the display. Two edges of the count deserve a sentence, since a reader checking it will look for them. *Vanishing coefficients.* If some f_m is identically zero the display still holds: the range counted at m is the integer interval of radius K·N^(d−|m|), which contains 0, so a coefficient that takes one value is counted among the at most 2K·N^(d−|m|) + 1 that it may take. Nothing in (4) or (5) assumes f_m ≠ 0. *Degree zero.* If d = 0 then C is a constant, W = wtCount 0 (r + 1) = C(r + 1, r + 2) = 0, and the bound reads n ≤ 0: a constant equation represents no coder of positive arity, which is the right conclusion and is delivered by the same inequality rather than by a separate case. Hence n ≤ W = wtCount d (r + 1), and since wtCount is monotone in both arguments (`wtCount_mono`) and d ≤ δ(p), r ≤ ν(p), we get n ≤ wtCount δ(p) (ν(p) + 1), which is the assertion at p = n + 1.

*Closed form.* For k ≥ 1, which is the case here since k = r + 1, the number of monomials of degree exactly j in k variables is C(j + k − 1, k − 1), so W = Σ_{j=0}^d (d − j)·C(j + k − 1, k − 1). Writing d − j as the number of i with j ≤ i ≤ d − 1 and exchanging the order of summation, W = Σ_{i=0}^(d−1) Σ_{j=0}ⁱ C(j + k − 1, k − 1) = Σ_{i=0}^(d−1) C(i + k, k) = C(d + k, k + 1), by the hockey-stick identity applied twice. The Lean statement `wtCount_closed_form` is proved for every k, including k = 0, where the displayed count of monomials does not apply and W = d = C(d, 1) directly. ∎

In particular no *constant* pair (ν, δ) can work: the right-hand side of Theorem C.1 is then one fixed number while the left-hand side is unbounded. This is the negative answer to the question, and it is what `not_MPUP_N` and `not_MPUP_Z` state.

**Remark C.2** (the weighted and the crude bound). The unweighted form of the obstruction (`coder_counting_bound`) bounds every coefficient by K·N^d, uniformly in the monomial, and so pays d for each of the M monomials, giving the cruder n ≤ d·M. Step (4) pays only d − |m|, which turns a product of equal factors into a sum of unequal ones. That the weighted bound refines the crude one and is not a competing claim is a theorem: `wtCount_le_crude` proves wtCount d k ≤ d · monoCount d k. The bound as stated, in terms of wtCount, and both closed forms are verified in the formal artifact: `wtCount_closed_form` proves wtCount d k = C(d + k, k + 1) and `monoCount_closed_form` proves the companion identity monoCount d k = C(d + k, k). The comparison with Theorem 4.1 is that both are box counts, and the difference is which box: there the images of a parameter box are confined by the growth theorem, here the specialisations of a fixed polynomial over a parameter box are confined by the size of its own coefficients.

## Appendix D. Technical arithmetic lemmas

The following are used throughout and are proved in the formalization.

*Growth on boxes.* For an integer polynomial p of total degree d and ‖a‖_∞ ≤ N with N ≥ 1, |p(a)| ≤ S·N^d where S is the sum of the absolute values of the coefficients (`eval_abs_le_int`). This is what turns "degree at most two in the parameters" into "at most SQ·N²".

*Top homogeneous part and lines.* The top homogeneous part of a nonzero polynomial is nonzero and does not vanish identically over an infinite integral domain (`topHomogeneous_ne_zero`, `exists_eval_ne_zero`); restricting to a line through the origin in a direction where it does not vanish gives a univariate polynomial of the same degree (`linePoly_natDegree`, `exists_line_natDegree_eq_totalDegree`). This is the engine of Theorem 5.1.

*Box counting.* The number of integer points of ℤᵐ in a box of half-side B is (2B+1)ᵐ, and a set with a coordinatewise bound has at most that cardinality (`ncard_le_of_abs_le_vec`).

*Primitive recursion over ℤ.* mathlib's computability library is developed over ℕ; the integer operations are obtained through the sign-magnitude encoding, and addition, multiplication, powers and polynomial evaluation at an integer coordinate vector are primitive recursive (`IntPrimrec.lean`: `primrec₂_int_add`, `primrec₂_int_mul`, `primrec_int_pow`, `primrec_eval_of_coords`). These are what make the code-level statements of Section 6 meaningful.

*Four squares and the sum-of-squares trick.* Every natural number is a sum of four squares (mathlib), which converts an ℕ-valued unknown into four ℤ-valued ones (`exists_fourSquares`); a finite system over ℤ has the same solutions as the single equation given by the sum of the squares of its members (`transportPoly_eval_eq_zero_iff`). Together these are the whole of Theorem 6.7 apart from bookkeeping.

*Homogeneous decomposition of a quadratic.* Any polynomial of total degree at most two in a two-block variable set splits, after specialising one block, as a homogeneous quadratic in the other block plus an affine part whose coefficients are polynomials of degree at most one and two in the specialised block (`normal_form_general_quadratic`). This single lemma is what connects Sections 2 and 8 to Section 9.

## Appendix E. Statement map

Appendix E is machine-generated at build time from this manuscript, from the frozen statement files and from the paper-claim manifest `submission/native/PAPER_CLAIMS.tsv`. The table printed here carries one row per statement of that manifest — the main theorems of Sections 2–9 and Appendix C, and the results of Section 10 that cite a declaration — giving the number, the Lean name it cites, and the frozen file in which that name's signature of record is held; a dash means the statement is derived and cites no declaration of its own. The map over *every* numbered statement of Sections 1–10 and Appendices A–C, definitions, remarks and examples included, is `release/STATEMENT_MAP_FULL.md` in the artifact. Appendix F carries its own proofs and is not indexed in either. Neither table is maintained by hand: both come from a single run of the same generator, the build fails if the printed table is empty or if a statement of the manifest has no row, and it fails if the shipped full map is not what that run produced.

The map below is generated by `manuscript/gen_appendix_e_numbered.py` and inlined at build time; it is not maintained by hand. 47 statements (those of the paper-claim manifest), of which 41 cite at least one Lean name. A dash means the statement is derived and cites no declaration of its own.

| # | statement | Lean name(s) | frozen file |
|---|---|---|---|
| 1.2 | Proposition | `singleEqFragmentZZ_subset_ppFragmentZZ`, `singleEqFragmentZZ_subset_diophFragmentZZ`, `fragment_lattice_ZZ` | FragmentLattice_STATEMENTS.lean, OneSortedFragments_STATEMENTS.lean |
| 1.3 | Proposition | — | — |
| 1.4 | Proposition | `relation_phase_diagram_arity_zero` | ArityZeroFragments_STATEMENTS.lean |
| 2.1 | Theorem | `singleQuadratic_finiteFiber_height_vector` | FiniteFiberGrowth_STATEMENTS.lean |
| 2.2 | Theorem | `singleQuadratic_finiteFiber_cardinality_vector` | FiniteFiberCardinality_STATEMENTS.lean |
| 3.2 | Theorem | `singleQuadratic_function_quadratic_growth` | FiniteFiberGrowth_STATEMENTS.lean |
| 3.3 | Theorem | `singleQuadratic_total_function_computable`, `ppQuadratic_total_function_computable` | ComputableFunctions_STATEMENTS.lean |
| 3.4 | Theorem | `ppQuadratic_functions_closed_under_composition`, `singleQuadratic_functions_not_closed_under_composition` | ComputableFunctions_STATEMENTS.lean, PolynomialGraphs_STATEMENTS.lean |
| 3.5 | Theorem | — | — |
| 4.1 | Theorem | `singleQuadratic_injective_dimension_sharp` | ResearchUpgrade_STATEMENTS.lean |
| 4.2 | Theorem | `summit_of_defines` | ResearchUpgrade_STATEMENTS.lean |
| 4.3 | Theorem | `singleQuadratic_sharp_iff` | ResearchUpgrade_STATEMENTS.lean |
| 4.4 | Corollary | `not_atomGraphZZ_two`, `atomGraphZZ_capacity_eq_one` | ResearchUpgrade_STATEMENTS.lean |
| 4.5 | Remark | — | — |
| 5.1 | Theorem | `polynomial_graph_singleQuadratic_iff` | MultivariatePolynomialGraphs_STATEMENTS.lean |
| 6.1 | Theorem | `recursive_strictly_contained_re` | HaltingTransport_STATEMENTS.lean |
| 6.2 | Theorem | — | — |
| 6.3 | Theorem | `singleEqFragmentZZ_two_subset_recFragmentZZ` | ComputabilityFragments_STATEMENTS.lean |
| 6.4 | Theorem | — | — |
| 6.5 | Theorem | `coded_family_ssubset_rec` | EffectiveDiagonal_STATEMENTS.lean |
| 6.6 | Corollary | `singleQuadratic_strict_recursive_of_codes` | EffectiveDiagonal_STATEMENTS.lean |
| 6.7 | Theorem | `DPRM_ZZ_of_DPRM_NN` | DPRMTransport_STATEMENTS.lean |
| 6.8 | Theorem | `relation_phase_diagram_all_positive_arity_of_classical` | RelationPhaseAllPositiveArityClassical_STATEMENTS.lean |
| 7.1 | Theorem | `function_phase_diagram_by_arity_of_DPRM_NN` | FunctionPhaseByArityNN_STATEMENTS.lean |
| 8.3 | Theorem | `fiber_infinite_of_structuredCertificate`, `StructuredCertificate.toSubset` | StructuredCertificates_STATEMENTS.lean |
| 8.4 | Definition | — | — |
| 8.5 | Theorem | `uniformQuadraticFiberStructureZZ_of_quadratic`, `singleQuadratic_fiber_bounded_or_structurallyInfinite` | SummitClosure_STATEMENTS.lean |
| 9.2 | Theorem | `quadraticProjectionDichotomyZ_all` | not in frozen_statements |
| 9.3 | Theorem | `quadraticProjectionDichotomyZ_all_data`, `quadraticProjectionDichotomyZ_structured` | SummitClosure_STATEMENTS.lean, TopDichotomyData_STATEMENTS.lean |
| 10.1 | Proposition | `generalWeakNF_iff_definiteWeakNF`, `rankExcess_compiler`, `definite_reduction` | ResearchUpgrade_STATEMENTS.lean |
| 10.2 | Proposition | `lowRankSemidefiniteWeakNF_holds`, `definiteWeakNF_oneOut_oneWit_holds` | ResearchUpgrade_STATEMENTS.lean |
| 10.3 | Lemma | `direction_discriminant_square` | ResearchUpgrade_STATEMENTS.lean |
| 10.4 | Lemma | `square_values_rigidity` | ResearchUpgrade_STATEMENTS.lean |
| 10.5 | Lemma | `norm_section` | ResearchUpgrade_STATEMENTS.lean |
| 10.6 | Proposition | `generalFullNF_iff_semidefiniteFullNF`, `isotropicBranchFullNF_holds` | ResearchUpgrade_STATEMENTS.lean |
| 10.7 | Proposition | `sealedFullNF_of_TCER`, `generalFullNF_of_TCER` | ResearchUpgrade_STATEMENTS.lean |
| 10.9 | Proposition | `singleQuadratic_iff_commonSlope_of_TCER` | ResearchUpgrade_STATEMENTS.lean |
| 10.10 | Proposition | `sqPadFn_not_singleQuadratic_of_TCER` | ResearchUpgrade_STATEMENTS.lean |
| 10.11 | Proposition | `not_commonSlope_of_fullVectorCosetNF` | ResearchUpgrade_STATEMENTS.lean |
| 10.12 | Proposition | `commonSlope_injective_iff` | ResearchUpgrade_STATEMENTS.lean |
| 10.13 | Lemma | `addSubgroup_two_coset_cover` | ResearchUpgrade_STATEMENTS.lean |
| 10.14 | Proposition | `scalar_singleQuadratic_iff_of_TCER` | ResearchUpgrade_STATEMENTS.lean |
| 10.15 | Proposition | `singleQuadratic_padZero_iff_of_TCER` | ResearchUpgrade_STATEMENTS.lean |
| 10.16 | Proposition | `zeroWitness_iff` | ResearchUpgrade_STATEMENTS.lean |
| 10.17 | Proposition | `singleQuadratic_iff_uniqueWitness_of_TCER` | ResearchUpgrade_STATEMENTS.lean |
| 10.18 | Proposition | `floorThird_min_witnesses` | ResearchUpgrade_STATEMENTS.lean |
| C.1 | Theorem | `coder_counting_bound_weighted`, `multiUniversalN_bound_weighted`, `multiUniversalZ_bound_weighted`, `wtCount_closed_form` | WeightedBound_STATEMENTS.lean |

Names cited by the paper but absent from `frozen_statements/`: 1.


## Appendix F. The arithmetic projection theorem: complete proof

This appendix proves Theorems 9.2 and 9.3 in full. Parts I and II give the full-rank and the singular case of the projection argument; Part III proves the properties of the Pell-unit orbit that the full-rank argument uses; Part IV assembles the pieces, transports between the two halves of the fibre, and derives the summit; Part V proves the five auxiliary results the earlier parts cite (Lemmas V.1, V.2, V.3, V.6 and Theorem V.4). The paper depends on no text outside itself. The formal development verifies the same argument; it is corroboration, and no step below ends with a citation to a Lean declaration in place of a proof.

### F.0 Coverage of the twenty-five required lemmas

The proof below is organised so that each of the twenty-five lemmas the argument requires is proved in a named part and section (Parts I–IV). The lemma-by-lemma coverage table, listing where each is proved, ships with the artifact as `release/APPENDIX_F_COVERAGE.md`; the proof is complete without it. The Pell-orbit lemmas of Part III are proved here for the first time.

### Part I. The full-rank case: a complete per-point proof

#### 0. Data and statement

Fix r ≥ 2. A fiber datum is (A, B, C, ℓ) with A ∈ ℤ, B ∈ ℤʳ, C ∈ M_r(ℤ), and affine part ℓ = (l, m, q), l ∈ ℤ, m ∈ ℤʳ, q ∈ ℤ. The fiber polynomial and projection set are

F(c, u) = A c² + c·(B·u) + uᵀCu + l c + m·u + q,   S = S(l,m,q) = { c ∈ ℕ : ∃ u ∈ ℤʳ, F(c,u) = 0 }.

Write G = C + Cᵀ (symmetric, even diagonal), N = det G, and assume N ≠ 0 (the full-rank hypothesis). Write adj(G) for the adjugate, W̃(Y) = Yᵀ·adj(G)·Y for the adjugate form, and

Y(c,u) = G u + c B + m        (the completed vector),   α = 2NA − Bᵀ·adj(G)·B,   β = β(l,m) = 2Nl − 2·Bᵀ·adj(G)·m,   γ = γ(m,q) = 2Nq − mᵀ·adj(G)·m.

α depends only on (A,B,C); β is linear in (l,m); γ is linear in q and quadratic in m. The bound shape is fbound = K·((1+|ℓ|₁)²+|q|) with |ℓ|₁ = |l| + Σ_i|m_i| and K = K(A,B,C) independent of (l,m,q).

**Theorem** (full-rank projection dichotomy). If det G ≠ 0 there is K₁ = K₁(A,B,C) such that for every (l,m,q): S(l,m,q) is infinite, or every c ∈ S(l,m,q) satisfies c ≤ K₁·((1+|ℓ|₁)²+|q|).

*Proof of the full-rank projection dichotomy.* The proof shape is a per-point alternative:

every c₀ ∈ S either satisfies a direct bound c₀ ≤ |β|-type,   or generates, through one of its own witnesses u₀, an infinite   family of fiber elements.

If S is not infinite, the second alternative is impossible at every point, so every point satisfies the direct bound. No global line restriction of the fiber occurs anywhere in the argument, and no boundedness statement is ever transported from a subfamily to S.

#### 1. The completion identity

For every (c,u) ∈ ℤ × ℤʳ,

2N·F(c,u) = W̃(Y(c,u)) + α c² + β c + γ.                        (1.1)

Both sides are integer polynomials in (c,u); the identity is checked by expanding, using G·adj(G) = N·I and the symmetry of adj(G). The factor 2N is a nonzero scalar multiplier, not a unit of ℤ: it is never divided by. The one cancellation used downstream is of the form 2N·x = 0 ⇒ x = 0 with N ≠ 0, which holds because ℤ is an integral domain. In particular F(c,u) = 0 ⟺ W̃(Y) + αc² + βc + γ = 0.

#### 2. The scaled line through a fiber point

Let (c₀, u₀) ∈ ℤ × ℤʳ and let w ∈ ℤʳ be any direction. The scaled line through (c₀, u₀) in direction w is the two-parameter integer family

c(t) = c₀ + N t,   u(t,s) = u₀ + s·adj(G)·w − t·adj(G)·B,          (t,s) ∈ ℤ².      (2.1)

Every point of the family lies in ℤ × ℤʳ because adj(G) is an integer matrix; this is the integrality mechanism N·ℤʳ ⊆ G·ℤʳ in action, since G·(adj(G)·d) = N·d for every d ∈ ℤʳ.

*Lattice transport.* Along (2.1) the completed vector moves in the single direction w:

Y(c(t), u(t,s)) = Y₀ + (N s)·w,   where Y₀ = Y(c₀,u₀).           (2.2)

The c-dependence of Y cancels against the −t·adj(G)·B term: G·(t·adj(G)·B) = Nt·B absorbs the increment (Nt)·B of the cB summand.

*Line value.* Substituting (2.2) into (1.1) and expanding the square,

2N·F(c(t), u(t,s)) = 2N·F(c₀,u₀)       + N·[ Nα·t² + N·W̃(w)·s² + Z₀·t + 2B₀·s ],                    (2.3)

where Z₀ = 2α c₀ + β and B₀ = Y₀ᵀ·adj(G)·w. The bracket is a binary integer quadratic in (t,s) with no ts-term, no constant term, t²-coefficient Nα and s²-coefficient N·W̃(w). If (c₀,u₀) is a fiber solution, F(c₀,u₀) = 0, so the zeros of F on the line are exactly the integer zeros of the bracket, and (t,s) = (0,0) is one of them.

#### 3. The bounded alternative at a point: α(2αc₀+β) ≤ 0 forces c₀ ≤ |β|

Let α ≠ 0 and let c₀ ∈ S, c₀ ≥ 0, with α·(2α c₀ + β) ≤ 0. Then 2α²c₀ ≤ −αβ ≤ |α|·|β|. Since |α| ≥ 1 and c₀ ≥ 0, |α|·c₀ ≤ α²·c₀, hence |α|·2c₀ ≤ 2α²c₀ ≤ |α|·|β|; cancelling |α| > 0 gives 2c₀ ≤ |β| and in particular

c₀ ≤ |β|.                                                        (3.1)

This step uses nothing about witnesses: it is a sign computation on the linear polynomial 2αc₀ + β. The passage from |β| to fbound is the size estimate |β| ≤ kβ·(1+|ℓ|₁) with the explicit constant kβ = 2|N| + 2·Σ_ij|B_i·adj(G)_ij|, together with (1+|ℓ|₁) ≤ (1+|ℓ|₁)² + |q|.

#### 4. The infinite alternative at a point: α(2αc₀+β) > 0 with a signed non-square direction

Call w ∈ ℤʳ a *signed non-square direction* for α when

α·W̃(w) < 0  and  −α·W̃(w) is not a square in ℤ.                  (4.1)

**Proposition**. Let α ≠ 0, let w satisfy (4.1), and let c₀ ∈ S with witness u₀ and α·Z₀ > 0, where Z₀ = 2αc₀ + β. Then S is infinite.

*Proof.* Consider the scaled line (2.1) through (c₀,u₀) in direction w, and the binary quadratic of (2.3):

Q(t,s) = Nα·t² + N·W̃(w)·s² + Z₀·t + 2B₀·s.

Write ε = sign(N) ∈ {±1}, so that N·ε = |N| ≥ 1. The following six facts drive the Pell mechanism.

(i) *Discriminant positivity.* disc(Q) with respect to its quadratic part (Nα, 0, N·W̃(w)) equals 0² − 4·Nα·N·W̃(w) = (2N)²·(−α·W̃(w)) > 0 by (4.1).

(ii) *Discriminant non-squareness.* A square times a non-square is a non-square: (2N)² ≠ 0 and −α·W̃(w) non-square give disc(Q) non-square.

(iii) *Initial point.* Q(0,0) = 0: the auxiliary one-witness fiber set of the form (Nα, 0, N·W̃(w)) with affine data (ε·Z₀, 2B₀, 0) contains t = 0.

(iv) *Orientation.* The Pell entry condition at the initial point is the positivity of X₀ = 2·disc(Q)·0 + (2·0·2B₀ − 4·N·W̃(w)·ε·Z₀) = −4·|N|·W̃(w)·Z₀. From α·W̃(w) < 0 and α·Z₀ > 0, the product α²·W̃(w)·Z₀ is negative, and α² > 0 forces W̃(w)·Z₀ < 0; hence X₀ > 0.

(v) *Infinite orbit.* By (i)–(iv), the Pell automorph of the binary form (Nα, 0, N·W̃(w)) — powered from a nontrivial positive solution of p² − disc·q² = 1, which exists because disc(Q) is positive and non-square — moves the initial point to solutions with strictly increasing t-height: the auxiliary fiber set contains infinitely many t ∈ ℕ. This is the one-witness Pell theorem of the two-variable layer, applied verbatim to the auxiliary form.

(vi) *Transport back, distinctness, nonnegativity, residue.* Each auxiliary solution t = z′ ∈ ℕ (with its s) yields, through t := ε·z′ in (2.1) and the identity (2.3) with 2N cancelled, a genuine fiber solution: the sign adjustment ε in the affine coefficient of (iii) and in t := ε·z′ cancel through ε² = 1, landing at

c = c₀ + N·(ε·z′) = c₀ + |N|·z′ ∈ ℕ.

The map z′ ↦ c₀ + |N|·z′ is injective (|N| ≥ 1), its outputs are nonnegative, and they all lie in the residue class c₀ mod |N|. The image of an infinite set under an injective map is infinite, so S is infinite. ∎

#### 5. The per-point dichotomy for α ≠ 0 with a direction

**Proposition**. Let α ≠ 0 and let w be a signed non-square direction for α. Then the dichotomy holds with K = kβ (as in §3): for every (l,m,q), S is infinite or every c ∈ S satisfies c ≤ kβ·((1+|ℓ|₁)²+|q|).

*Proof.* Fix (l,m,q). If S is infinite there is nothing to prove. Suppose S is not infinite, and let c ∈ S be arbitrary with witness u. Exactly one of the following holds:

- α·(2αc+β) ≤ 0. Then c ≤ |β| by §3, and |β| folds into the bound shape.
- α·(2αc+β) > 0. Then §4 applies at (c, u) — the scaled line through this
very point — and S is infinite, contradicting the case assumption.
Hence every point of S satisfies the direct bound. ∎

The quantifier structure is the load-bearing part: the bound is proved for each element of S individually, from data at that element. At no point is a subfamily's boundedness transferred outward.

#### 6. The case α = 0

Here the identity (1.1) reads 2N·F = W̃(Y) + βc + γ. Three sub-cases.

*(6a) β = 0: shift periodicity.* Take the scaled line (2.1) with direction w = 0 through any solution (c₀,u₀): by (2.3) with α = 0, β = 0, W̃(0) = 0, the bracket vanishes for every (t,s), so every c₀ + Nt with t ∈ ℤ and c₀ + Nt ≥ 0 is again a fiber element. Membership of c in S therefore depends only on c mod |N|: c ∈ S ⟺ c + |N| ∈ S (shift by t = ±ε). A subset of ℕ that is invariant in both directions under shift by |N| ≥ 1 is empty or contains a full residue class; empty makes the bound vacuous, a full residue class is infinite.

*(6b) β ≠ 0 with a progression direction: β·W̃(w) < 0.* If S is empty the bound is vacuous. Otherwise fix a solution (c₀,u₀) and set B₀ = Y₀ᵀ·adj(G)·w. For every target k ∈ ℕ choose an auxiliary integer

τ = k + |2N·B₀| + c₀ + 1 ≥ 1,

and set the line parameters of (2.1) to t := z and s := β·τ, where z = −2B₀·τ − N·W̃(w)·β·τ². With α = 0 the bracket of (2.3) — here Z₀ = β — evaluates at (z, β·τ) to β·(N·W̃(w)·β·τ² + z + 2B₀·τ) = 0 by the choice of z, so c₀ + N·z carries a fiber solution, and

c₀ + N·z = c₀ − (2N·B₀)·τ + N²·(−W̃(w)·β)·τ².

The leading coefficient N²·(−W̃(w)β) is ≥ 1, so the quadratic term dominates: c₀ + N·z ≥ c₀ − |2N·B₀|·τ + τ² ≥ k by the choice of τ. Fiber elements exceed every k, so S is unbounded, hence infinite.

*(6c) β ≠ 0 with β·W̃ ≥ 0 everywhere.* For c ∈ S with witness u, the identity gives W̃(Y) + βc + γ = 0, so β²c = −βγ − β·W̃(Y) ≤ −βγ ≤ |β|·|γ|. Since |β| ≥ 1 and c ≥ 0, cancelling as in §3 gives

c ≤ |γ| ≤ kγ·((1+Σ_i|m_i|)²+|q|) ≤ kγ·((1+|ℓ|₁)²+|q|),

with the explicit constant kγ = 2|N| + Σ_ij|adj(G)_ij|. Again the bound is per-point.

The dichotomy for α = 0 holds with K = kγ, once for every β ≠ 0 one of the two hypotheses of (6b)/(6c) is available; §8 supplies this from the sign pattern of W̃.

#### 7. The semidefinite alternative for α ≠ 0: α·W̃ ≥ 0 everywhere

If α·W̃(Y) ≥ 0 for every Y — W̃ semidefinite with the same orientation as α — the bound is direct and no direction is needed. For c ∈ S with witness u, (1.1) gives α·(αc² + βc + γ) = −α·W̃(Y) ≤ 0, hence α²c² ≤ |α||β|c + |α||γ|, and cancelling |α| ≥ 1 as before, c² ≤ |β|c + |γ|. If c > |β| + |γ| then c² > (|β|+|γ|)·c ≥ |β|c + |γ| (using c ≥ 1), a contradiction; so

c ≤ |β| + |γ| ≤ (kβ + kγ)·((1+|ℓ|₁)²+|q|).

The dichotomy holds with K = kβ + kγ, and the infinite branch is never invoked. This is the semidefinite edge case; it is also per-point.

#### 8. Producing the direction: the sign trichotomy of the adjugate form

The propositions of §§5–7 cover every (A,B,C) with N ≠ 0 once the following sign analysis of W̃ is in place. Throughout, r ≥ 2 supplies two coordinate indices i ≠ j.

*(8a) Anisotropy under semidefiniteness.* If ε ≠ 0 and ε·W̃ ≥ 0 everywhere, then W̃(w) = 0 forces w = 0. Reason: for every v, testing ε·W̃ ≥ 0 on the line w-direction plus v and letting the w-coefficient grow shows the pairing wᵀ·adj(G)·v vanishes; taking v over the standard basis gives adj(G)·w = 0, and then N·w = G·adj(G)·w = 0 with N ≠ 0 forces w = 0.

*(8b) Attaining the sign.* Under (8a)'s hypotheses, some coordinate vector has ε·W̃ > 0: a standard basis vector with ε·W̃ = 0 would be zero by (8a).

*(8c) Indefinite case.* If W̃(v) > 0 and W̃(w) < 0 for some v, w, restrict W̃ to the plane x·v + y·w: the restricted values form a binary quadratic a x² + b xy + c y² with a > 0 > c, hence discriminant b² − 4ac > 0. If that discriminant is a square, the form splits into two integer linear factors and a walk along one factor line produces, for every h > 0 and σ = ±1, a point x with σ·W̃(x) > 0 and h·|W̃(x)| non-square; if it is not a square, the form is anisotropic and Lemma V.2 below (the points (k−b, 2a), k ∈ {0,1,D,D+1}) produces the same conclusion; the square case is Lemma V.3 below (explicit isotropic-line point). In either case: for every h > 0 and σ = ±1 there is x with σ·W̃(x) > 0 and h·|W̃(x)| non-square. Taking σ = −sign(α) and h = |α| yields a signed non-square direction for α. For a progression direction no square condition is needed: for any β ≠ 0, whichever of v, w has W̃-value of sign opposite to β already satisfies β·W̃ < 0.

*(8d) Semidefinite opposite to α.* If α ≠ 0 and α·W̃ ≤ 0 everywhere, restrict −α·W̃ to the coordinate plane (i,j): its values there form the binary quadratic p x² + e xy + q y² with p, q > 0 (positivity at nonzero points holds by (8a) with ε = −α) and e even (e is twice an adjugate pairing scaled by −α), and e² < 4pq. The inequality is strict for the same reason p, q > 0 are: if e² ≥ 4pq the binary form p x² + e xy + q y² would take the value 0 or a negative value at a nonzero integer point of the plane — at (−e, 2p) it takes p(4pq − e²), which is ≤ 0 — and (8a) forbids that. A positive definite integer binary form with even cross term represents a positive non-square value (Lemma V.1 below: at one of (1,0), (0,1), (1,p)); at the representing point x·eᵢ + y·eⱼ one has −α·W̃ equal to that value, so α·W̃ < 0 with −α·W̃ non-square — a signed non-square direction for α.

*(8e) Assembly grid.* Combining the trichotomy of α with the sign pattern of W̃:

| sign pattern of W̃ | α < 0 | α = 0 | α > 0 |
|---|---|---|---|
| both signs attained | direction by (8c) → §5 | β = 0: → (6a); β ≠ 0: progression by (8c) → (6b) | direction by (8c) → §5 |
| W̃ ≤ 0 everywhere | root bound → §7 | β = 0: → (6a); β < 0: (6c); β > 0: direction by (8b) → (6b) | direction by (8d) → §5 |
| W̃ ≥ 0 everywhere | direction by (8d) → §5 | β = 0: → (6a); β > 0: (6c); β < 0: direction by (8b) → (6b) | root bound → §7 |
Every cell terminates in §5, §6, or §7, each of which delivers the dichotomy with K ∈ {kβ, kγ, kβ+kγ}. Taking K₁ = kβ + kγ dominates all cells, and K₁ is determined by (A,B,C) alone. This proves the Theorem. ∎

#### 9. The constant

In this full-rank layer the constants are the explicit integer expressions

kβ = 2|det G| + 2·Σ_ij |B_i·adj(G)_ij|,   kγ = 2|det G| + Σ_ij |adj(G)_ij|,

evaluated from (B, C); they do not depend on (l, m, q), which is the uniformity the capacity counting uses. No claim is made here about effectivity of constants in the singular layer (Lemmas 2–5 of the companion document), where the normal form involves a choice of basis; the capacity argument needs only existence of one finite constant per (A,B,C).

#### 10. Line-by-line Lean correspondence

The lemmas of Parts I--V are each anchored to a named declaration of `DiophCompression/SemanticQuadraticMatrix/` (and `Directions.lean`, `PellStep.lean` in the sibling directory `DiophCompression/SemanticQuadraticTwoWitness/`); the table listing every lemma with its anchor and file:lines is `release/APPENDIX_F_LEAN_ANCHORS.md` of the artifact, beside the full statement map `release/STATEMENT_MAP_FULL.md` and the proof companion. The anchors that carry the theorem are those of the table in §9 above.

### Part II. The singular case: complete proofs of the component lemmas

#### 0. Setup and notation

Fix r ≥ 0. A fiber datum is a tuple (A, B, C, ℓ) with A ∈ ℤ, B ∈ ℤʳ, C ∈ M_r(ℤ), and an affine part ℓ = (l, m, q), l ∈ ℤ, m ∈ ℤʳ, q ∈ ℤ. The fiber polynomial is

F(c, u) = A c² + c·(B·u) + uᵀCu + l c + m·u + q,

and the projection set is S = { c ∈ ℕ : ∃ u ∈ ℤʳ, F(c,u) = 0 }. Write G = C + Cᵀ for the Gram matrix and |ℓ|₁ = |l| + Σ_i|m_i| for the ℓ¹-size of the affine data. The bound shape throughout is

fbound = K · ((1 + |ℓ|₁)² + |q|),

with K depending only on (A, B, C) — never on (l, m, q). The dichotomy to be proved: **S is infinite, or S ⊆ [0, fbound]**.

Two conventions used silently below. First, 2·uᵀCu = uᵀGu, so all quadratic-value arguments may replace C by its symmetrization at the cost of the nonzero scalar multiplier 2 — not a unit of ℤ — which never divides anything in these proofs: it multiplies, and it cancels only through torsion-freeness of ℤ (2x = 2y ⟹ x = y). Second, "periodic in c" always means: membership of c depends only on c mod P for a fixed positive integer P; a nonempty periodic subset of ℕ contains a full residue class and is infinite.

#### 1. Lemma 1 — full-rank adjugate reduction (det G ≠ 0)

**Statement.** If det G ≠ 0 there is K₁ = K₁(A,B,C) such that for all (l,m,q): S is infinite or S ⊆ [0, K₁·((1+|ℓ|₁)²+|q|)].

*Proof.* The argument is per fibre point and is given in full as Part I of this appendix; the numbering there is self-contained and nothing below depends on any text outside this paper. The structure:

The completion identity 2N·F(c,u) = W̃(Y) + αc² + βc + γ — with Y = Gu + cB + m the completed vector, W̃(Y) = Yᵀ·adj(G)·Y the adjugate form, α = 2NA − Bᵀ·adj(G)·B, β = 2Nl − 2Bᵀ·adj(G)·m, γ = 2Nq − mᵀ·adj(G)·m — converts the fiber condition without division. For α ≠ 0 with a signed non-square direction w (α·W̃(w) < 0 and −α·W̃(w) non-square), take an arbitrary c₀ ∈ S with witness u₀. Either α(2αc₀+β) ≤ 0, and a sign computation on 2αc₀+β forces c₀ ≤ |β| directly; or α(2αc₀+β) > 0, and the scaled line c = c₀ + Nt, u = u₀ + s·adj(G)·w − t·adj(G)·B through this very point — an integer family along which Y moves by (Ns)·w only — carries a Pell orbit: the line value is a binary quadratic in (t,s) with discriminant (2N)²·(−α·W̃(w)), positive and non-square, whose automorph moves the initial solution (t,s) = (0,0) to infinitely many solutions, landing fiber elements at c₀ + |N|·z′ for infinitely many distinct z′ ∈ ℕ. If S is not infinite the second alternative is impossible at every point, so every point of S obeys c₀ ≤ |β| — the bound is proved pointwise, never transported from a subfamily. The direction w is produced from the sign trichotomy of W̃: indefinite W̃ restricts to a plane binary form of positive discriminant (split or anisotropic walk); W̃ semidefinite opposite to α restricts to a positive definite plane form with even cross term representing a suitable non-square; W̃ semidefinite aligned with α needs no direction — the identity forces c² ≤ |β|c + |γ|, hence c ≤ |β| + |γ| (root bound). For α = 0: β = 0 gives shift periodicity mod |N| (empty or infinite); β ≠ 0 with a progression direction (β·W̃(w) < 0) gives quadratic-growth unboundedness along the line; β ≠ 0 with β·W̃ ≥ 0 everywhere forces c ≤ |γ| pointwise. The constants kβ = 2|N| + 2Σ_ij|B_i·adj(G)_ij| and kγ = 2|N| + Σ_ij|adj(G)_ij| depend only on (B,C); K₁ = kβ + kγ dominates every branch. ∎

#### 2. Lemma 2 — integral radical decomposition (det G = 0)

**Statement.** If det G = 0 (G symmetric, the case G = 0 included), there is U ∈ GL_r(ℤ) with UᵀGU = diag(G₀, 0), det G₀ ≠ 0, where the zero block has size s = dim ker. Moreover F ∘ U has the shape required by Lemmas 3A/3B: the last s variables (the radical variables) appear only linearly.

*Proof.* Let K = ker(G : ℚʳ → ℚʳ) ∩ ℤʳ, a submodule of ℤʳ.

(i) *K is saturated*: if k·x ∈ K with k ≠ 0, then G(kx) = 0, so k·(Gx) = 0 in ℤʳ, and since ℤʳ is torsion-free, Gx = 0, i.e. x ∈ K.

(ii) *The quotient is free*: ℤʳ/K is finitely generated; it is torsion-free precisely by (i) (a torsion element x + K with k·x ∈ K forces x ∈ K); a finitely generated torsion-free module over the PID ℤ is free.

(iii) *The sequence splits*: 0 → K → ℤʳ → ℤʳ/K → 0 with free quotient splits; choose a basis w₁,…,w_s of K and lifts v₁,…,v_{r−s} of a basis of the quotient. The matrix U with columns (v₁,…,v_{r−s}, w₁,…,w_s) lies in GL_r(ℤ): its columns generate ℤʳ (every x decomposes as lift-part plus K-part) and are ℤ-linearly independent.

(iv) *Block shape*: for the last s columns, G·w_j = 0, so UᵀGU has zero in the last s columns; by symmetry of G, also in the last s rows. The leading (r−s)×(r−s) block G₀ represents the form induced on ℤʳ/K, which is nondegenerate: a vector v with G₀-pairing zero against the whole quotient lifts to x ∉ K with Gx pairing to zero against ℤʳ, hence Gx = 0 by nondegeneracy of the standard pairing, hence x ∈ K — contradiction.

(v) *Effect on F*: write u = U·(v, w). The quadratic value satisfies 2·uᵀCu = uᵀGu = (v,w)ᵀ·UᵀGU·(v,w) = vᵀG₀v: the radical variables w drop out of the quadratic part entirely. This holds although UᵀCU itself may keep nonzero entries in the radical block — the value only sees the symmetric part, and the factor 2 cancels because ℤ is torsion-free (2x = 2y ⟹ x = y). The terms c·(B·u) and m·u are linear in u, hence remain linear in (v,w); collecting, each radical variable wᵢ carries the affine-in-c coefficient a_i(c) = b_i c + m_i′ with (bᵢ) determined by (B, U) and (mᵢ′) linear in m. The transformation is a congruence Uᵀ(·)U with a single U ∈ GL_r(ℤ) — not a Smith normal form, which is a two-sided equivalence P(·)Q and does not preserve quadratic values. ∎

All five steps read verbatim when G = 0: the kernel is all of ℤʳ, the quotient is the zero module (free on the empty basis), U consists of kernel columns only, the leading block G₀ is the empty 0×0 matrix whose determinant is the empty product 1 ≠ 0, the nondegeneracy step (iv) is vacuous, and in (v) the quadratic part vanishes identically, so every variable carries an affine-in-c coefficient. The kernel statement `singular_symmetric_congruent_block` carries no G ≠ 0 hypothesis; the dispatch sends every det G = 0 datum, G = 0 included, through this lemma.

Four further remarks close the edge cases and the scope. (a) *Radical dimension zero cannot occur here*: over ℤ, det G = 0 forces a nonzero rational kernel and hence a nonzero saturated integral kernel, so s ≥ 1 whenever this lemma is invoked; s = 0 is exactly the det G ≠ 0 case of Lemma 1. (b) *Existence-only by design*: an algorithmic variant is available in principle — the saturated kernel and a complement can be produced by Hermite-normal-form computations — but no such claim is used or made anywhere in this paper. (c) *Independence of the completion*: any two completions U, U′ differ by a block-triangular unimodular change T respecting the kernel, so the normal forms are congruent over ℤ with det G₀′ = det(T₁)²·det G₀ = det G₀, and the projection set — the only object consumed downstream — is unchanged under any U ∈ GL_r(ℤ), since u ↦ U·u is a bijection of ℤʳ. (d) *Low-dimensional controls*: concrete small instances are formalized in the fidelity layer (`SemanticQuadraticSingular/Fidelity3W.lean`, nine coefficient tuples for r = 3 checked in the kernel); no CAS enumeration is claimed here beyond what Section 12 records.

#### 3. Lemma 3A — nonzero-minor periodicity

**Statement.** In the Lemma 2 normal form, suppose two radical coefficient pairs have a nonzero minor: b_im_j′ − b_jm_i′ ≠ 0 for some i, j. Then S is empty or infinite.

*Proof.* By Bézout, for fixed c the radical variables solve Σ_i (b_ic+m_i′)w_i = t exactly when g(c) ∣ t, where g(c) = gcd(b₁c+m₁′, …, b_sc+m_s′) ≥ 0. Hence, writing F₀(c, v) for the non-radical part of the normal form (the v-variables being the nondegenerate-block variables),

c ∈ S  ⟺  ∃ v ∈ ℤ^(k₀) : g(c) ∣ F₀(c, v).                    (3.1)

The identity  b_j(b_ic + m_i′) − b_i(b_jc + m_j′) = b_jm_i′ − b_im_j′ =: Δ_ij shows g(c) ∣ Δ_ij for every c. Fix i, j with Δ := Δ_ij ≠ 0 and set P = Δ². Claim: membership (3.1) is periodic with period P.

Let c′ ≡ c (mod P).

(i) *g is unchanged*: every common divisor e of the values (bₖc+mₖ′)ₖ divides g(c), hence divides Δ, hence divides P; then e ∣ b_kc+m_k′ and e ∣ P ∣ (c′−c)·b_k give e ∣ b_kc′+m_k′ — so common divisors at c are common divisors at c′, and symmetrically. The two gcds have the same divisor sets, so g(c′) = g(c) =: g.

(ii) *The residues are unchanged*: g ∣ Δ ∣ P and c′ ≡ c (mod P) give, for any v, F₀(c′, v) ≡ F₀(c, v) (mod g) (polynomial evaluation respects the congruence, coefficients integral). Hence g ∣ F₀(c, v) ⟺ g ∣ F₀(c′, v) for the SAME v, and the existential (3.1) transfers in both directions.

So S is a periodic subset of ℕ with period P; a nonempty periodic subset of ℕ contains a full residue class and is infinite. ∎

*Consequence for capacity*: the graph of a function has singleton fibers — totality and single-valuedness are what make them singletons, not injectivity — so its datum can never fall in this branch; the branch removes itself from the counting argument rather than contributing a bound. Injectivity is used only in the counting step, where it makes the outputs associated with distinct inputs distinct.

#### 4. Lemma 3B — proportional compression

**Statement.** If all pair minors vanish, there is a single pair (b′, μ′) ∈ ℤ² such that for every c and every target t ∈ ℤ:

(∃ w ∈ ℤˢ : Σᵢ (bᵢc+mᵢ′)wᵢ = t)  ⟺  (∃ w ∈ ℤ : (b′c+μ′)·w = t).

*Proof.* Vanishing minors mean the vectors (b_i, m_i′) ∈ ℤ² are pairwise proportional. Discard identically-zero pairs (their variables contribute nothing to either side). If all pairs are zero, take (b′, μ′) = (0,0); both sides then say t = 0. Otherwise let (b₀, μ₀) be a primitive vector (content 1) with every (b_i, m_i′) = λ_i(b₀, μ₀), λ_i ∈ ℤ not all zero (integrality of the λᵢ: Lemma V.6 below, gcd(b₀,μ₀) = 1 and Gauss's lemma), and set g = gcd(λ₁,…,λ_s) > 0 and (b′, μ′) = g·(b₀, μ₀).

(⇒) Σ_i λ_i(b₀c+μ₀)w_i = t gives (b₀c+μ₀)·(Σλ_iw_i) = t. As w ranges over ℤˢ, Σλᵢwᵢ ranges over exactly gℤ: it always lies in gℤ because g divides every λᵢ, and every element of gℤ occurs, by Bézout. So the left side is solvable iff t ∈ (b₀c+μ₀)·gℤ = (b′c+μ′)ℤ… with the sign convention b′c+μ′ = g(b₀c+μ₀); that is precisely solvability of (b′c+μ′)w = t.

(⇐) is the same equality read backwards: t ∈ (b′c+μ′)ℤ = (b₀c+μ₀)·gℤ, and gℤ = {Σλᵢwᵢ}, producing an explicit w ∈ ℤˢ.

Both directions are Bézout; the equivalence is exact, not one-sided, so any number s of radical variables is replaced by exactly one coupled variable without changing the projection set. ∎

#### 5. Lemma 4 — quotient-rank-zero leaf (moving linear modulus)

**Statement.** For the normal form with k₀ = 0, i.e. the fiber condition ∃w : Q(c) + (bc+μ)w = 0 with Q(c) = Ac² + lc + q: there is K₄ = |A| + |b| + |b|² + 2 such that S is infinite or S ⊆ [0, K₄·((1+|l|+|μ|)²+|q|)].

*Proof.* Solvability in w is the divisibility (bc+μ) ∣ Q(c) (with the convention that modulus 0 divides only 0). The remainder identity — an algebraic identity in ℤ[A,l,q,b,μ,c], verified by expansion:

R := Aμ² − blμ + b²q      = b²·Q(c) − (bc+μ)·(A(bc+μ) + (bl − 2Aμ)).                (5.1)

Hence (bc+μ) ∣ Q(c) ⟹ (bc+μ) ∣ b²Q(c) ⟹ (bc+μ) ∣ R. Four branches:

**(b ≠ 0, R ≠ 0) — bounded.** Every c ∈ S satisfies |bc+μ| ≤ |R| (a nonzero multiple is at least as large in absolute value as the divisor), so |c| ≤ (|R|+|μ|)/|b| ≤ |R|+|μ|. Since |R| ≤ |A|μ² + |b||l||μ| + b²|q| ≤ (|A|+|b|+b²)·((|l|+|μ|)² + |q|), the bound K₄·((1+|l|+|μ|)²+|q|) holds with K₄ = |A|+|b|+|b|²+2 (the +2 absorbs the |μ| addend and the shift from (|l|+|μ|)² to (1+|l|+|μ|)²).

**(b ≠ 0, R = 0) — congruence sub-split.** Expanding the cofactor in (5.1): L(c) := A(bc+μ) + (bl − 2Aμ) = Abc + bl − Aμ, and R = 0 gives the identity b²·Q(c) = (bc+μ)·L(c). For any c with t := bc+μ ≠ 0, multiply the target divisibility by b²:  t ∣ Q(c) ⟺ t·b² ∣ b²·Q(c) = t·L(c) ⟺ b² ∣ L(c). The moving-modulus condition is therefore EQUIVALENT to the fixed linear congruence

A·b·c + b·l − A·μ ≡ 0 (mod b²).                              (5.2)

- If (5.2) has a solution c₀ ∈ ℤ, its solution set contains the arithmetic
progression c ≡ c₀ (mod b²); shifting c₀ by a multiple of b² into ℕ, every   member c of the progression with bc+μ ≠ 0 (all but at most one) lies in S   — infinite.
- If (5.2) has no solution, then no c with bc+μ ≠ 0 lies in S; the only
possible member is the single c with bc+μ = 0 (it exists only when   b ∣ μ, and then t = 0 requires Q(c) = 0 as well), and that c satisfies   |c| = |μ|/|b| ≤ |μ| — bounded, inside the K₄ bound.
(Kernel: this is precisely the case split `∃ c₀, b² ∣ (A·b·c₀ + b·l − A·μ)` inside `quotient_rank_zero_dichotomy`; the infinite arm is discharged by the explicit injection t ↦ c₁ + b²·t into the fiber.)

**(b = 0, μ ≠ 0) — fixed modulus.** The condition is μ ∣ Q(c); Q(c) mod μ depends only on c mod μ, so membership is periodic with period |μ|; empty or infinite.

**(b = 0, μ = 0) — no coupled variable.** The condition is Q(c) = 0. If A = l = 0 and q = 0, every c solves — infinite. If A = l = 0, q ≠ 0, S is empty. Otherwise Q is a nonzero polynomial of degree ≤ 2 with at most two integer roots; both roots satisfy |c| ≤ |l| + |q| + 1 when A = 0 (root −q/l), and |c| ≤ (|l|+|q|+1) when A ≠ 0 by the elementary root bound |c| ≤ 1 + max(|l|,|q|)/|A| ≤ 1 + |l| + |q| — inside the K₄ bound. ∎

The modulus in the two b ≠ 0 branches moves with c; the mechanism is division of the moving modulus into the FIXED remainder R, not a fixed- modulus periodicity. That distinction is what the four-branch structure records, and conflating the two is the error the branch table exists to prevent.

#### 6. Lemma 5 — moving-modulus prime progression (k₀ ≥ 2)

**Statement.** Consider the normal form F₀(c, v) + (bc+μ)w = 0 with F₀ carrying a nondegenerate Gram block G₀ of rank k₀ ≥ 2, and no restriction on the sign of b. Then S is infinite, or every c ∈ S satisfies a bound of the branch shape.

*Proof of Lemma 5.* 
**Reduction to b ≥ 0.** The unimodular substitution w ↦ −w is a bijection of ℤ and carries the condition F₀(c, v) + (bc+μ)w = 0 to F₀(c, v) + (−bc−μ)w = 0, so the datum (b, μ) and the datum (−b, −μ) have the *same* projection set S. We may therefore assume b ≥ 0 throughout. (This is the same normalisation used inside Lemma 6; it is stated here and in the dispatch because Lemma 3B is free to return either sign.)

**The case b = 0.** Lemma 3B may return b′ = 0 — it does so whenever every radical pair is of the form (0, mᵢ′), and it returns (b′, μ′) = (0,0) when all of them vanish — so this case must be treated, and it is not covered by the prime-progression argument below, which needs a modulus that moves with c.

*(b = 0, μ ≠ 0) — fixed modulus.* The condition is ∃v, w : F₀(c,v) + μw = 0, that is ∃v : μ ∣ F₀(c,v). All coefficients of F₀ are integers, so for c ≡ c′ (mod |μ|) and any v we have F₀(c,v) ≡ F₀(c′,v) (mod μ); hence membership of c in S depends only on the residue of c modulo |μ|. S is therefore a union of residue classes intersected with ℕ: empty, or infinite. This is the same argument as the corresponding branch of Lemma 4 and uses nothing about k₀.

*(b = 0, μ = 0) — no coupled variable.* The condition is ∃v, w : F₀(c,v) = 0, in which w is free and contributes nothing, so S = {c ∈ ℕ : ∃ v ∈ ℤ^(k₀), F₀(c,v) = 0}. That is exactly a full-rank fibre datum in the k₀ variables v: the v-quadratic part of F₀ has Gram G₀ with det G₀ ≠ 0, and the hypothesis k₀ ≥ 2 supplies precisely the two coordinate indices that Part I requires. Lemma 1 applies verbatim, in dimension k₀, and returns its own verdict and constant. There is no regress: Lemma 1 is a terminal leaf and is invoked here directly, not through Lemma 2 or 3B.

**The case b > 0.** Assume a solution (c₀, v₀, w₀) with t₀ = bc₀+μ > 0. (If every solution has bc+μ ≤ 0 then bc ≤ −μ ≤ |μ| for c ∈ S, and b ≥ 1 gives c ≤ |μ|, inside the uniform bound.)

*Choice of prime.* Let D = 2·|det G₀|·b·t₀ > 0. By Dirichlet's theorem on primes in arithmetic progressions there are infinitely many primes p ≡ 1 (mod D); choose one with p > max(D, |det G₀|, t₀, 2). Then: p is odd; p ∤ det G₀ (p > |det G₀| and p prime); b ∣ p−1; t₀ ∣ p−1; gcd(t₀, p) = 1.

*The step.* Write p−1 = b·j (integer since b ∣ p−1) and c₁ = c₀ + t₀·j. Then b c₁ + μ = t₀ + b t₀ j = t₀(1 + (p−1)) = t₀·p, and c₁ > c₀ since t₀, j > 0.

*Persistence mod t₀.* c₁ ≡ c₀ (mod t₀) because t₀ ∣ t₀j. Take v ≡ v₀ (mod t₀). Then F₀(c₁, v) ≡ F₀(c₀, v₀) (mod t₀) (all coefficients integral, congruence respected by polynomial evaluation), and F₀(c₀, v₀) = −t₀·w₀ ≡ 0 (mod t₀). So F₀(c₁, v) ≡ 0 (mod t₀) along this congruence class of v.

*Solvability mod p.* The quadratic part of F₀ in v has Gram G₀ with p ∤ det G₀ and rank k₀ ≥ 2. We use the following classical fact, proved here rather than cited, since Appendix F takes no step by citation.

  **Fact (universality over F_p).** Let p be an odd prime and let Q be a quadratic form in k ≥ 2 variables over F_p whose Gram matrix G satisfies p ∤ det G. Then Q represents every element of F_p.

*Proof.* Since p is odd, 2 is a unit, so the polarisation B(x,y) = ½(Q(x+y) − Q(x) − Q(y)) is a symmetric bilinear form with Gram G, and Gram–Schmidt against B diagonalises Q: in a suitable basis Q = a₁x₁² + ⋯ + a_kx_k², and det G ≠ 0 forces every a_i ≠ 0. Setting x₃ = ⋯ = x_k = 0 leaves the binary form a₁x² + a₂y² with a₁, a₂ ≠ 0, so it suffices to represent an arbitrary t by that form. The squares of F_p are (p−1)/2 nonzero values together with 0, so |{x² : x ∈ F_p}| = (p+1)/2; multiplication by the unit a₁ is a bijection, hence |A| = |{a₁x² : x ∈ F_p}| = (p+1)/2, and likewise |B| = |{t − a₂y² : y ∈ F_p}| = (p+1)/2. Now |A| + |B| = p + 1 > p = |F_p|, so A and B cannot be disjoint. Any common value gives a₁x² = t − a₂y², that is Q(x, y) = t. ∎

The hypothesis p ∤ det G is not decorative: over F₇ the degenerate form Q(x,y) = x² represents only 4 of the 7 residues. The formal proof in the development follows a polarisation route that avoids diagonalising (`FiniteFieldQuadraticGeneral.lean`); it corroborates the argument above and does not replace it.

After completing the square in the linear terms mod p (unit 2 invertible), F₀(c₁, v) ≡ 0 (mod p) has a solution v ≡ v_p.

*Gluing.* gcd(t₀, p) = 1, so CRT produces v₁ ∈ ℤ^(k₀) with v₁ ≡ v (mod t₀) and v₁ ≡ v_p (mod p). Then F₀(c₁, v₁) ≡ 0 mod t₀ and mod p, hence mod t₀p, i.e. t₀p ∣ F₀(c₁, v₁). Set w₁ = −F₀(c₁, v₁)/(t₀p) ∈ ℤ; then F₀(c₁, v₁) + (bc₁+μ)w₁ = F₀(c₁, v₁) + t₀p·w₁ = 0, a solution at c₁ with t₁ = bc₁+μ = t₀p > 0.

*Iteration.* The new solution satisfies the same hypothesis (t₁ > 0), so the step repeats with strictly increasing c. S is infinite.

*The complementary branch.* Stated with the case split above: if every solution has bc+μ ≤ 0, then for c ∈ S we have bc ≤ −μ ≤ |μ|, and b ≥ 1 gives c ≤ |μ| ≤ (1+|l|+|μ|)² — within fbound. Together with the two b = 0 branches and the sign reduction, the four cases b < 0, b = 0 with μ = 0, b = 0 with μ ≠ 0, and b > 0 exhaust the data Lemma 3B can present. ∎

#### 7. Lemma 6 — rank-one coupled dichotomy (k₀ = 1)

**Statement.** For the normal form with k₀ = 1: fiber condition ∃ u, w ∈ ℤ : Q(c,u) + (bc+μ)·w = 0, with Q(c,u) = A c² + B₁ c u + k u² + l c + m₁ u + q and k ≠ 0 (the single nondegenerate variable; det G₀ = 2k). There is K₆ = K₆(A, B₁, k, b) such that for all (l, m₁, μ, q): S is infinite or every c ∈ S satisfies c ≤ K₆·((1+|l|+|m₁|+|μ|)²+|q|).

*Proof.* Solvability in w is the divisibility (bc+μ) ∣ Q(c,u) for some u (the modulus 0 divides only 0). The unimodular change w ↦ −w replaces (b, μ) by (−b, −μ) without changing the projection set, so b ≥ 0 may be assumed; three cases.

*(b = 0, μ = 0) — uncoupled.* The condition is ∃u : Q(c,u) = 0, exactly the one-witness two-variable dichotomy of the base layer (proved in full as Theorem V.4 below, with the transfer stated as Corollary V.5), whose constant transfers unchanged (its infinite branch already contains the Pell classes of that layer — which is where a Pell mechanism enters the rank-one component, and why no separate Pell argument appears below).

*(b = 0, μ ≠ 0) — fixed modulus.* The condition is ∃u : μ ∣ Q(c,u). For c′ ≡ c (mod |μ|) the difference

Q(c′,u) − Q(c,u) = (c′−c)·(A(c′+c) + B₁u + l)

is divisible by μ, so the condition transfers in both directions with the same u: membership is periodic mod |μ| — empty or infinite.

*(b > 0) — coupled: the rank-one prime step.* If every fiber element has bc+μ ≤ 0, then c ≤ bc ≤ −μ ≤ |μ| (b ≥ 1, c ≥ 0): bounded, inside the K₆ shape. Otherwise some fiber element (c₀, u₀) has t₀ = bc₀+μ > 0 with t₀ ∣ Q(c₀,u₀), and the following step produces a fiber element at strictly larger c; iterating makes S unbounded, hence infinite.

*The discriminant invariant.* Write disc_u Q(c) = (B₁c+m₁)² − 4k(Ac²+lc+q) for the u-discriminant of Q at c, and set

D′ = (b·m₁ − B₁·μ)² − 4k·(Aμ² − blμ + b²q).

The identity b²·disc_u Q(c) − D′ = (bc+μ)·(integer cofactor), checked by expansion, gives b²·disc_u Q(c) ≡ D′ (mod bc+μ) for every c. (The second summand of D′ is −4k times the Lemma-4 remainder R.)

*Choice of prime.* By Dirichlet's theorem choose a prime

p ≡ 1 (mod 8·max(1,|D′|)·b·|2k|·t₀),   p > t₀.

Then p is odd, p ∤ 2k, b ∣ p−1, t₀ ∣ p−1, gcd(t₀, p) = 1, and D′ is a square mod p: for D′ ≠ 0 decompose D′ = sign(D′)·2^e·m with m odd; the Legendre symbols at 2 and −1 equal 1 because p ≡ 1 (mod 8), and (m/p) = (p/m) = (1/m) = 1 by quadratic reciprocity (p ≡ 1 mod 4) together with p ≡ 1 (mod m); multiplicativity gives (D′/p) = 1. For D′ = 0 the root below is a double root. No square/non-square case split on D′ is needed: the residue argument is uniform for every D′ ≠ 0, perfect squares included (a square is a residue modulo every prime).

*The step.* Set c₁ = c₀ + t₀·(p−1)/b, an integer since b ∣ p−1. Then bc₁ + μ = t₀ + t₀(p−1) = t₀·p and c₁ > c₀.

*Root mod p.* b²·disc_u Q(c₁) ≡ D′ (mod t₀p), so disc_u Q(c₁) is a square mod p. Here b is invertible mod p: p ≡ 1 (mod b), so p ∣ b would give p ≤ b and simultaneously p = 1 + (a positive multiple of b) > b — a contradiction. With p ∤ 2k, completing the square in u shows Q(c₁, ·) has a root u_p mod p.

*Persistence mod t₀.* c₁ ≡ c₀ (mod t₀), so with u ≡ u₀ (mod t₀): Q(c₁,u) ≡ Q(c₀,u₀) ≡ 0 (mod t₀).

*Gluing.* gcd(t₀,p) = 1: CRT produces u₁ with u₁ ≡ u₀ (mod t₀) and u₁ ≡ u_p (mod p), so t₀p = bc₁+μ divides Q(c₁,u₁) — a fiber element at c₁ with the new modulus t₀p > 0, and the hypothesis of the step holds again. ∎

*General r.* The k₀ = 1 leaf of the dispatch presents the fiber polynomial with a 1×1 nondegenerate block: expanding the one-index sums identifies it with the scalar polynomial above under k = C₁₁ (with 2C₁₁ = det G₀ ≠ 0), b = the compressed slope, μ = the compressed offset; the constant transfers unchanged. This is the translation layer `QuotientRankOne.lean`; the analytic content is the scalar core of the two-witness layer.

#### 8. Assembly and the capacity corollary

*Proof of the assembly and the capacity corollary.* **Dispatch.** The witness count r is unrestricted here (Part II fixes r ≥ 0), while Lemma 1 is stated and proved in Part I for r ≥ 2 — its direction step needs two coordinate indices i ≠ j. The small cases are therefore routed separately, and the routing is exhaustive as follows.

*r ≤ 1.* Theorem V.4 applies directly and settles both. For r = 1 the fibre datum (A, B, C, ℓ) is precisely the coefficient data (A, B, C, l, m, q) of Theorem V.4, with B ∈ ℤ¹ the coefficient of cu and C ∈ ℤ^(1×1) that of u²; the theorem gives S infinite or c ≤ K·((1+|l|+|m|)² + |q|), and |ℓ|₁ = |l|+|m|, so that bound is of the branch shape below with K_branch = K(A,B,C). No assumption on det G is needed: the cases C = 0 and C ≠ 0 are both inside Theorem V.4. For r = 0 the fibre condition carries no unknown, and taking B = C = m = 0 in Theorem V.4 leaves exactly the condition Ac² + lc + q = 0 on c, with the same conclusion.

*r ≥ 2.* Given (A,B,C): if det G ≠ 0, Lemma 1. If det G = 0, Lemma 2 produces the normal form; if a radical pair minor is nonzero, Lemma 3A (empty-or-infinite); otherwise Lemma 3B compresses to one coupled variable, its output sign is normalised to b ≥ 0 by w ↦ −w (Lemma 5, reduction step; the same substitution is used inside Lemma 6), and the quotient rank k₀ of G₀ dispatches to Lemma 4 (k₀=0), Lemma 6 (k₀=1), or Lemma 5 (k₀≥2). Each of those three lemmas treats b = 0 as well as b > 0, which matters because Lemma 3B returns b′ = 0 whenever the radical pairs are all of the form (0, mᵢ′). **Size transport.** The branch lemmas bound c in the data of the NORMAL FORM, after the congruence u = U(v,w) of Lemma 2 and the compression of Lemma 3B, whereas the dichotomy of Definition 9.1 is stated in the ORIGINAL affine data (ℓ, q). The step between them is short but it is exactly the parameter uniformity this paper claims, so it is carried out here rather than asserted.

Write κ(U) := max_i Σ_j |U_ij| for the largest ℓ¹ row sum of U; κ(U) ≥ 1 because U is integral and invertible, and κ(U) depends only on U, hence only on G, hence only on C — never on (l, m, q). Three estimates:

(i)   Substituting u = U(v,w) leaves A, l and q untouched and replaces m by         Uᵀm, so |Uᵀm|₁ ≤ κ(U)·|m|₁ (coordinate j of Uᵀm pairs m with column j of U,         and summing over j groups the terms by row: Σ_j|Σ_i U_ijm_i| ≤ Σ_i|m_i|·Σ_j|U_ij|         ≤ κ(U)|m|₁). Hence |ℓ_norm|₁ = |l| + |Uᵀm|₁ ≤ κ(U)·|ℓ|₁.   (ii)  Lemma 3B outputs (b′, μ′) = g·(b₀, μ₀) with (b_i, m_i′) = λ_i(b₀, μ₀) and         g = gcd(λ₁,…,λ_s). Since g divides each λᵢ and the λᵢ are not all zero,         g ≤ max_i|λ_i|, so |μ′| = g|μ₀| ≤ max_i|λ_iμ₀| = max_i|m_i′| ≤ |Uᵀm|₁ (and         |μ′| = 0 trivially when μ₀ = 0). The leading linear coefficient m₁ of         the non-radical block is likewise a coordinate of Uᵀm.   (iii) |b′| = g|b₀| = gcd_i(b_i), and the bᵢ are determined by (B, U) alone.         So the compressed slope, which is the only normal-form quantity a branch         constant depends on, is fixed by (A, B, C) and not by the affine data —         which is what lets K_branch be chosen before the parameter point.

Consequently every normal-form quantity a branch bound uses satisfies |l| + |μ′| ≤ |ℓ_norm|₁ ≤ κ(U)|ℓ|₁, while q is unchanged, so

K_branch·((1+|l|+|μ′|)² + |q|) ≤ K_branch·κ(U)²·((1+|ℓ|₁)² + |q|),

and the branch bound has the fbound shape in the original data with the constant K_branch·κ(U)². Every terminal verdict is "infinite" or "c ≤ K_branch·((1+|ℓ|₁)²+|q|)"; K_H = κ(U)² times the max over the finitely many branch constants. Each branch supplies one finite constant determined by (A,B,C), which is all the capacity counting uses; no computability claim is made for the constants of the singular branches, where the normal form involves a choice of basis. (Lean: `DichotomySG`, `dichotomyM_of_dichotomySG_zero`, `singular_projection_dichotomy_all_r`, `quadraticProjectionDichotomyZ_all`.)

**Capacity corollary (G_ℤ(r,2) = 2 for all r).** Upper bound: let P(a₁,…,a_n, c, u) represent the graph of an injective e : ℕⁿ → ℕ with total degree ≤ 2 and r ℤ-witnesses. For parameters a ∈ [0,N]ⁿ, substitute: the resulting fiber datum has fixed (A,B,C) (the (c,u)-quadratic part of P, independent of a) and affine data with |ℓ|₁ ≤ κ_P·(1+N), |q| ≤ κ_P·(1+N)² (coefficients of P are fixed; substituted parameters have size ≤ N; degree ≤ 2 caps parameter-monomials at quadratic). Totality and single-valuedness make every fiber a singleton, excluding the infinite branch, so every output e(a) ≤ K_H·((1+κ_P(1+N))² + κ_P(1+N)²) ≤ κ'·N² for N large. The (N+1)ⁿ inputs map injectively into [0, κ'N²]: (N+1)ⁿ ≤ κ'N² + 1 for all large N forces n ≤ 2. Lower bound: the quadratic pairing polynomial (a₁,a₂) ↦ code with no witnesses represents an injective graph at degree 2, so n = 2 is achieved, for every r by witness padding. Hence G_ℤ(r,2) = 2. The same substitution argument with r = 0 in both directions gives the arity-spectrum inertia GraphAchievableZ(n,r,2) ⟺ GraphAchievableZ(n,0,2). ∎

#### 9. Lean anchor table

| § | claim | Lean anchor (each with the standard axiom footprint) |
|---|---|---|
| 1 | full-rank dichotomy | `full_rank_dichotomy_all`, `full_rank_projection_dichotomy_of_direction_property` (FullRankGeneric.lean); leaves: Class_D*.lean, Directions.lean, PellStep.lean, PellPow.lean; complete per-point text: FULL_RANK_PROOF_V2.md (accompanying artifact) |
| 2 | saturation/splitting/block | `integer_kernel_is_saturated`, `saturated_submodule_has_complement`, `singular_symmetric_congruent_block`, `nondegenerate_quotient_block` (RadicalDecomposition.lean) |
| 3A | minor periodicity | `affine_family_nonzero_minor_periodic` (RadicalAffine.lean) |
| 3B | compression | `affine_family_zero_minors_proportional`, `primitive_affine_direction`, `radical_family_reduces_to_one_coupled_variable` (RadicalAffine.lean) |
| 4 | remainder identity + dichotomy | `linear_modulus_divides_quadratic_remainder`, `quotient_rank_zero_bounded_or_infinite`, `quotient_rank_zero_dichotomy` (QuotientRankZero.lean) |
| 5 | prime progression | `moving_remainder_identity_general`, `moving_remainder_root_mod_prime_general`, `moving_modulus_prime_step_general`, `quotient_rank_ge_two_moving_dichotomy` (MovingModulusGeneral.lean) |
| 7 (Lemma 6) | rank-one coupled dichotomy | `quotient_rank_one_normal_form`, `quotient_rank_one_coupled_dichotomy`, `quotient_rank_one_dichotomy` (QuotientRankOne.lean); scalar core: `dichotomy2_rank_one_normal`, `rank_one_uncoupled`, `rank_one_coupled_pos` (SemanticQuadraticTwoWitness/RankOne.lean), `rank_one_coupled_prime_step`, `dPrime_identity`, `square_mod_prime_of_one_mod_eight_abs` (SemanticQuadraticTwoWitness/RankOneCoupled.lean) |
| 8 | assembly + capacity | `quadraticProjectionDichotomyZ_all`, `quadraticWitnessInertiaZ`, `graphAchievableZ_degree_two_iff` (SingularAssembly.lean); `graphCapacityZ_two_of_projectionDichotomy` (ProjectionDichotomy.lean) |
External inputs at natural-language level, listed in full: Dirichlet's theorem on primes in arithmetic progressions (§6; in the kernel via mathlib); quadratic reciprocity and the values of the Legendre symbol at −1 and 2, used in the rank-one coupled leaf (§7); solvability of Pell's equation for a positive nonsquare discriminant, used in Theorem V.4's Pell case and again in Part III (in the kernel via mathlib `Pell.exists_of_not_isSquare`); and the classical two-variable quadratic dichotomy leaf constants (§1), which are kernel-verified here and depend on nothing outside this development. Universality of a nondegenerate quadratic form of rank ≥ 2 over F_p is not on this list: it is proved in §6 above, where a reader expecting to find it among the inputs will find it as a theorem.

### Part III. Pell-unit orbits: recurrence, norm, congruence, growth

The full-rank argument of Part I produces a unit of a real quadratic order and iterates it to obtain the orbit. This Part proves the properties of that iteration which Part I uses (`StructuredFamilyCore.pell`, `FullRankAssemblyData.lean`).

Throughout, D is a positive nonsquare integer and (P, Q) ∈ ℤ² satisfies

(III.1)  P² − D·Q² = 1,   P ≥ 2,   Q ≥ 1.

Such a pair exists for every positive nonsquare D, since Pell's equation is then solvable; Part I produces one from the discriminant data of the form. It need not be, and is not claimed to be, the fundamental unit — any nontrivial positive solution serves. Given a starting point (X₀, Y₀) ∈ ℤ² define

(III.2)  X_{k+1} = X_k·P + D·Y_k·Q,   Y_{k+1} = X_k·Q + Y_k·P.

This is multiplication by the unit P + Q√D in ℤ[√D], written out in coordinates: if ξ_k = X_k + Y_k√D then ξ_{k+1} = ξ_k·(P + Q√D).

#### Lemma III.1 (norm preservation along the orbit)

For every k, X_k² − D·Y_k² = X₀² − D·Y₀².

*Proof.* It suffices to prove the one-step identity, and then induct. Expanding (III.2),

X_{k+1}² − D·Y_{k+1}²     = (X_k P + D Y_k Q)² − D·(X_k Q + Y_k P)²     = X_k²P² + 2D·X_k Y_k P Q + D²Y_k²Q² − D·X_k²Q² − 2D·X_k Y_k P Q − D·Y_k²P²     = X_k²P² + D²Y_k²Q² − D·X_k²Q² − D·Y_k²P²     = X_k²(P² − D Q²) − D·Y_k²(P² − D Q²)     = (X_k² − D·Y_k²)·(P² − D·Q²).

By (III.1) the second factor is 1, so the norm is unchanged. The cross terms cancel exactly, which is the only point at which (III.1) is used; no positivity is needed here. ∎

#### Lemma III.2 (congruence preservation)

Let m ≥ 1 and suppose P ≡ 1 and Q ≡ 0 (mod m). Then X_k ≡ X₀ and Y_k ≡ Y₀ (mod m) for every k.

*Proof.* One step: X_{k+1} = X_k·P + D·Y_k·Q ≡ X_k·1 + D·Y_k·0 = X_k, and Y_{k+1} = X_k·Q + Y_k·P ≡ X_k·0 + Y_k·1 = Y_k (mod m). Induct. ∎

The hypothesis of Lemma III.2 is not restrictive, and the reason is a finiteness argument rather than a cyclicity one.

**Lemma III.2′.** Let m ≥ 1 and let (P, Q) satisfy P² − D·Q² = 1. Then there is d with 1 ≤ d ≤ m² such that the coordinates (P_d, Q_d) of (P + Q√D)^d satisfy P_d ≡ 1 and Q_d ≡ 0 (mod m).

*Proof.* Let G be the set of pairs (x, y) ∈ (ℤ/m)² with x² − D·y² = 1, under the composition (x, y)·(x′, y′) = (x x′ + D y y′, x y′ + y x′) inherited from multiplication in ℤ[√D]. That G is closed under this composition is the multiplicativity of the norm, written out: for all x, y, x′, y′,

(x x′ + D y y′)² − D·(x y′ + y x′)² = (x² − D y²)·(x′² − D y′²),

an identity of polynomials in ℤ[x, y, x′, y′, D] — the same computation as in Lemma III.1, with (P, Q) replaced by (x′, y′) — so a product of two elements of norm 1 again has norm 1. Composition is associative, (1, 0) is neutral, and (x, −y) inverts (x, y) since (x + y√D)(x − y√D) = x² − D y² = 1; so G is a group. It is a subset of (ℤ/m)², hence |G| ≤ m². The reduction of (P, Q) lies in G, so its order d divides |G| and in particular d ≤ m². Then (P, Q)^d reduces to (1, 0), which is the assertion. ∎

No cyclicity of G is claimed or needed: the argument uses only that G is a finite group and that the order of an element divides the order of the group. Part I selects a power of the unit (P, Q) that meets the congruence required by the branch — Lemma III.2′ says such a power exists, with an explicit bound on the exponent — and Lemma III.2 is what makes that selection stable along the whole orbit once it has been made.

#### Lemma III.3 (strict growth)

Suppose X₀ ≥ 1 and Y₀ ≥ 0. Then for every k: X_k ≥ 1, Y_k ≥ 0, and X_{k+1} ≥ 2·X_k. In particular X_k ≥ 2ᵏ·X₀, so (X_k) is strictly increasing and unbounded.

*Proof.* Induction on k. The base case is the hypothesis. Assume X_k ≥ 1 and Y_k ≥ 0. Since D ≥ 2 and Q ≥ 1 we have D·Y_k·Q ≥ 0, so

X_{k+1} = X_k·P + D·Y_k·Q ≥ X_k·P ≥ 2·X_k ≥ 2 ≥ 1,

using P ≥ 2. Likewise X_k·Q ≥ 0 and Y_k·P ≥ 0 give Y_{k+1} ≥ 0. The chain X_k ≥ 2ᵏ·X₀ follows, and 2ᵏ·X₀ → ∞. ∎

#### Lemma III.4 (the output projection is strictly increasing)

Let denom, px, pc ∈ ℤ with denom ≠ 0 and px ≠ 0, and suppose c_k ∈ ℕ satisfies denom·c_k = px·X_k + pc for every k, with (X_k) as in Lemma III.3. Then (c_k) is strictly increasing — from k = 0, not merely from some index on — and the set {c_k : k ≥ 0} is infinite.

*Proof.* From denom·c_k = px·X_k + pc,

denom·(c_{k+1} − c_k) = px·(X_{k+1} − X_k),

and Lemma III.3 gives X_{k+1} − X_k ≥ X_k ≥ 1, so the right-hand side is nonzero for *every* k, not merely from some index on. Hence

|c_{k+1} − c_k| = (|px|/|denom|)·(X_{k+1} − X_k) ≥ |px|·X_k/|denom| > 0,

and the sign of c_{k+1} − c_k is the sign of px/denom — of the quotient, not of px alone — which is the same for every k. So (c_k) is strictly monotone from the start. A strictly monotone integer sequence is injective, so its range is infinite. It is moreover increasing: a strictly decreasing sequence in ℕ cannot be infinite, and c_k ∈ ℕ by hypothesis. No sign condition on px, denom or pc needs to be assumed; the hypothesis that the c_k are natural numbers forces the direction. ∎

#### Remark III.5 (what is and is not effective here)

Lemmas III.1–III.4 are entirely effective: given (D, P, Q, X₀, Y₀, denom, px, pc) every term of the orbit and of the output sequence is computable, and by Lemma III.4 the output sequence is strictly increasing from the first index, so no threshold has to be computed. This effectivity is local to the Pell branch. It does not make the certificate of Section 8 effective, because the *witnesses* u realising c_k ∈ fibre are selected from membership proofs rather than constructed, and because the constant K of Theorem 9.2 — which decides which branch applies — is not effective. The orbit is explicit; the choice of orbit is not.

### Part IV. Assembly

#### IV.1 From a branch to a data-carrying family

Parts I and II each terminate, in the unbounded alternative, not in the bare proposition "this set is infinite" but in explicit arithmetic data: a first-degree or second-degree progression (Part II §3, §4, §5), a unit orbit with its recurrence (Part I §4 together with Part III), or a step orbit with its primes (Part II §6). Collecting the alternatives gives, for each branch, a family of one of three forms together with the data that pin its output map: a coefficient triple in the progression case, the tuple (D, P, Q, X₀, Y₀, denom, px, pc) in the Pell case, and (b, μ, modulusFactor) with the prime sequence in the moving-modulus case. In every case the output map is a function c : ℕ → ℕ presented by an equation — c_t = αt² + βt + γ, or denom·c_k = px·X_k + pc, or the recurrence b·c_{k+1} + μ = (b·c_k + μ)·p_k — and is strictly monotone, hence injective.

Two things should be said about what this does and does not give. First, the three forms are those the case analysis emits. Nothing here proves that they are mutually exclusive, and a single fibre may admit families of more than one form; the classification is of the proof's output, not of the fibre. Second, the passage from a family to a certificate for the original polynomial P selects, for each output value c_t, a witness u_t with P(a, c_t, u_t) = 0. The existence of such a u_t is part of the membership statement c_t ∈ fibre; the selection is not constructive. What is proved is that an infinite, arithmetically structured set of outputs exists and that each of its elements is realised — not that the realising witnesses can be computed.

#### IV.2 Output-negation transport

Parts I–III work with a fibre of natural numbers. The fibre of P at a is a set of integers with two halves, and the halves meet exactly in the output zero, so a set of integers is infinite if and only if at least one half is. Write ε ∈ {+1, −1} for the selector and

fibreNatSigned(P, a, ε) = { m ∈ ℕ : ε·m ∈ fibre(P, a) }.

Homogenising P and specialising the parameters at a presents each signed half as a set fiberSetG(H, ℓ, q) for a homogeneous quadratic H — this is where the degree hypothesis on P is consumed, and the affine data (ℓ, q) become integers once a is fixed. The sign ε is carried through the construction rather than handled by a second argument: it travels into the polynomial coefficients in the progression case, into the affine projection in the Pell case, and into the sign field in the moving-modulus case. Consequently no separate degree bound for a negated output polynomial is required, and the kind of the family is preserved by the transport.

If the half selected by ε is infinite, Parts I–III supply a family inside it, and the transport above turns that family into a certificate for P at a. If both halves are finite the fibre is finite, which is the other horn.

#### IV.3 The summit

*Proof of Theorems 9.2 and 9.3.* Let P have total degree at most two. Apply the dichotomy of Parts I–II to the homogeneous part H of P. It supplies a constant K depending on H alone — not on the affine data, and hence not on the parameter point a, since a enters only through (ℓ, q). Fix a. Either every element of each signed half is bounded by fboundG(K, ℓ, q), in which case, since ‖ℓ‖ and |q| are bounded by an explicit polynomial of degree at most two in ‖a‖∞ read off the coefficients of P, every element of the fibre satisfies |c| ≤ C·(1 + ‖a‖∞)² for a constant C determined by K and by the coefficients of P; or some half is unbounded, hence infinite, and IV.1–IV.2 produce a certificate.

This is the required quantifier order: C is chosen after P and before a. One constant per equation serves every parameter point. The two horns are mutually exclusive at a given point, since a certificate exhibits an unbounded output family inside the fibre and the bounded horn bounds every element of it.

Theorem 9.2 follows by forgetting the family, and Theorem 9.3 is the statement just proved. ∎

### Part V. Transplanted lemmas: directions, the one-witness dichotomy, and integer proportionality

Parts I and II above invoke five auxiliary results. They are proved here in full: nothing in Appendix F depends on any text outside this manuscript. The numbering V.1–V.6 is in bijection with the labels used in Parts I and II, and each result carries the name of the Lean theorem that certifies it. Note that Appendix C of this paper is a different appendix on a different subject; the labels below are the only ones Parts I and II refer to.

Throughout §V.1, Q(x,y) = a x² + b xy + c y² with a, b, c ∈ ℤ and D = b² − 4ac.

#### V.0 Two elementary facts about squares

**Fact V.0.1** (`not_isSquare_of_between`). If n ≥ 0 and n² < X < (n+1)² for an integer n, then X is not a square.

*Proof.* If X = s² then X = |s|², and n² < |s|² < (n+1)² with n ≥ 0 and |s| ≥ 0 gives n < |s| < n+1, which no integer satisfies. ∎

**Fact V.0.2** (`not_isSquare_sq_mul`, `not_isSquare_mul_of_coprime`, `not_both_squares`). (i) If r ≠ 0 and r²X is a square, then X is a square. (ii) If X > 0 is not a square and gcd(X, Y) = 1, then XY is not a square. (iii) If XY is not a square and H ≠ 0, then H·X and H·Y are not both squares.

*Proof.* (i) If r²X = s² then r² ∣ s², hence r ∣ s; write s = rt and cancel r² ≠ 0 to get X = t². (ii) If XY = s² with gcd(X,Y) = 1 then X is a unit times a square, so X = ±t²; X > 0 forces X = t², contradicting that X is not a square. (iii) If HX = r₁² and HY = r₂² then H²·XY = (r₁r₂)², and (i) with r = H ≠ 0 makes XY a square. ∎

#### V.1 Signed non-square directions: the definite case

\setcounter{Part}{0}

**Lemma V.1** (definite direction; `definite_nonsquare_direction`). Let p, q > 0, let h be even, and let h² < 4pq. Then at least one point (x,y) ∈ {(1,0), (0,1), (1,p)} satisfies both Q(x,y) = p x² + h xy + q y² > 0 and Q(x,y) is not a square.

*Proof.* If p is not a square, take (1,0): Q(1,0) = p > 0 and p is not a square. If p is a square but q is not, take (0,1): Q(0,1) = q > 0 and q is not a square.

Otherwise p = r² and q = t² with r, t > 0; put m = rt > 0. Evaluate at (1,p):

  Q(1,p) = p + hp + qp² = p(1 + h + qp) = r²(1 + h + t²r²) = r²(m² + h + 1).
The hypothesis h² < 4pq = 4m² gives −2m < h < 2m, hence

  (m−1)² = m² − 2m + 1 < m² + h + 1 < m² + 2m + 1 = (m+1)².
Both inequalities are strict, so m² + h + 1 > (m−1)² ≥ 0, and in fact m² + h + 1 > 0. The only square in the closed range [(m−1)², (m+1)²] other than the two endpoints is m², and m² + h + 1 = m² would force h = −1, which is excluded because h is even. So m² + h + 1 lies strictly between two consecutive squares — either (m−1)² and m², or m² and (m+1)² — and Fact V.0.1 shows it is not a square. Finally r ≠ 0, so if r²(m² + h + 1) were a square then Fact V.0.2(i) would make m² + h + 1 a square. Hence Q(1,p) = r²(m² + h + 1) is positive and not a square. ∎

#### V.2 Signed non-square directions: the anisotropic case

**Lemma V.2** (anisotropic direction; `anisotropic_signed_nonsquare_direction`). Let D > 0 be a non-square, let h > 0 and σ ∈ {1, −1}. Then for at least one k ∈ {0, 1, D, D+1} the point (x,y) = (k − b, 2a) satisfies σ·Q(x,y) > 0 and h·|Q(x,y)| is not a square.

*Proof.* First, a ≠ 0: if a = 0 then D = b², a square. Second, D ≥ 2: D > 0 and D = 1 is a square. For every integer k,

  Q(k − b, 2a) = a(k−b)² + 2ab(k−b) + 4a²c = a(k² − b² + 4ac) = a(k² − D).  (V.1)
Since D ≡ 0 and D − 1 ≡ −1 modulo D, gcd(D, D−1) = 1; likewise D³ − 1 ≡ −1 (mod D) gives gcd(D, D³−1) = 1. As D > 0 is not a square, Fact V.0.2(ii) with X = D shows that neither D(D−1) nor D(D³−1) = D(D−1)(D²+D+1) is a square.

*Case σa < 0.* Take k ∈ {0, 1}. Since D ≥ 2 we have k² − D < 0, so by (V.1) σ·Q = (σa)(k² − D) > 0, and |Q| = |a|(D − k²), which is |a|D for k = 0 and |a|(D−1) for k = 1. Apply Fact V.0.2(iii) with H = h|a| ≠ 0, X = D and Y = D − 1: since XY = D(D−1) is not a square, at least one of h|a|D and h|a|(D−1) is not a square. Choose k accordingly.

*Case σa > 0.* Take k ∈ {D, D+1}. Then k² − D equals D² − D = D(D−1) > 0 for k = D, and (D+1)² − D = D² + D + 1 > 0 for k = D+1; so σ·Q = (σa)(k² − D) > 0 and |Q| = |a|(k² − D). Apply Fact V.0.2(iii) with H = h|a| ≠ 0, X = D(D−1) and Y = D² + D + 1: their product is D(D−1)(D²+D+1) = D(D³−1), which is not a square, so at least one of h|a|D(D−1) and h|a|(D²+D+1) is not a square. Choose k accordingly.

Since a ≠ 0, one of the two cases applies. ∎

#### V.3 Signed non-square directions: the split case

**Lemma V.3** (split direction; `split_signed_nonsquare_direction`, `split_finish`). Let D = d² with d > 0, let h > 0 and σ ∈ {1, −1}. Then there is (x,y) ∈ ℤ² with σ·Q(x,y) > 0 and h·|Q(x,y)| not a square. Explicitly, with K as below and y₀ := σKh(K²h² + 1):

- a = c = 0 (so d = |b| and b ≠ 0): K = b, (x,y) = (1, y₀);
- a = 0, c ≠ 0: K = 4cd², (x,y) = (−2c + 2c·y₀, (b+d) − (b−d)·y₀);
- a ≠ 0: K = 4ad², (x,y) = ((b+d) − (b−d)·y₀, −2a + 2a·y₀);

  and in each case Q(x,y) = K·y₀.

*Proof.* *The finisher.* For any K ≠ 0, the value K·y₀ = σK²h(K²h² + 1) satisfies σ·K·y₀ = K²h(K²h² + 1) > 0, and, writing n := K²h² ≥ 1,

  h·|K·y₀| = h·K²h(K²h² + 1) = K²h²(K²h² + 1) = n(n + 1),
which is not a square because n² < n(n+1) < (n+1)² and Fact V.0.1 applies. So it suffices to exhibit, in each case, a point with Q(x,y) = K·y₀ for some K ≠ 0 depending only on (a, b, c).

*Case a = c = 0.* Then Q(x,y) = bxy and D = b² = d², so b ≠ 0, and Q(1, y₀) = b·y₀ with K = b ≠ 0.

*Case a ≠ 0.* Put v₁ = (b+d, −2a) and v₂ = (d−b, 2a). Both are isotropic:

  Q(v₁) = a(b+d)² − 2ab(b+d) + 4a²c = a(d² − b² + 4ac) = a(d² − D) = 0,
and the same computation gives Q(v₂) = 0. For the associated symmetric pairing 2B(u,v) = 2a u₁v₁ + b(u₁v₂ + u₂v₁) + 2c u₂v₂,

  2B(v₁,v₂) = 2a(d² − b²) + 4ab² − 8a²c = 2a(d² + b² − 4ac) = 2a(d² + D) = 4ad²,
using D = b² − 4ac = d². Hence

  Q(v₁ + y₀v₂) = Q(v₁) + y₀·2B(v₁,v₂) + y₀²·Q(v₂) = 4ad²·y₀,
and v₁ + y₀v₂ = ((b+d) − (b−d)y₀, −2a + 2ay₀) is the stated point, with K = 4ad² ≠ 0 because a ≠ 0 and d > 0.

*Case a = 0, c ≠ 0.* Here Q(x,y) = bxy + cy² and D = b² = d². The vectors u = (−2c, b+d) and v = (2c, d−b) are isotropic, since Q(u) = (b+d)c(d−b) = c(d² − b²) = 0 and likewise Q(v) = 0; and 2B(u,v) = b[(−2c)(d−b) + (b+d)(2c)] + 2c(b+d)(d−b) = 4b²c = 4cd². The same expansion gives Q(u + y₀v) = 4cd²·y₀, i.e. Q(−2c + 2cy₀, (b+d) − (b−d)y₀) = K·y₀ with K = 4cd² ≠ 0. ∎

#### V.4 The one-witness fibre dichotomy

Fix A, B, C ∈ ℤ. For l, m, q ∈ ℤ put

  P(c,u) = A c² + B cu + C u² + l c + m u + q,
  
  S = S(l,m,q) = {c ∈ ℕ : ∃ u ∈ ℤ, P(c,u) = 0},
  
  Δ = B² − 4AC, w = 2Cu + Bc + m, β = 2Bm − 4Cl, γ = m² − 4Cq,
so that, expanding w² and subtracting 4C·P,

  4C·P(c,u) = w² − (Δc² + βc + γ).  (V.3)

**Theorem V.4** (one-witness fibre dichotomy; `fiber_dichotomy`, FiberDichotomy.lean; leaves Class_D1–D7). There is K = K(A,B,C) ∈ ℕ such that for every (l, m, q): either S is infinite, or every c ∈ S satisfies c ≤ K·((1 + |l| + |m|)² + |q|).

*Proof.* Here β is linear in (l, m), γ is quadratic in m and linear in q, and β² − 4Δγ is quadratic in (l, m) and linear in q; so any bound that is a polynomial of degree ≤ 1 in |β|, |γ| and |β² − 4Δγ| with coefficients depending only on A, B, C has the required shape. Each case below produces either an infinite family in S or a bound of that shape. (S = ∅ falls under the bounded branch vacuously.)

*Case Δ < 0 (definite; `dichotomy_definite`).* Then C ≠ 0, since Δ < 0 forces 4AC > B² ≥ 0. At a solution, (V.3) gives Δc² + βc + γ = w² ≥ 0, and Δ ≤ −1 gives c² ≤ Δc² + βc + γ + c² ≤ βc + γ ≤ |β|c + |γ|, whence c ≤ |β| + |γ|. Always bounded.

*Case Δ = 0, C ≠ 0 (`dichotomy_degenerate_C_ne`).* By (V.3), w² = βc + γ at every solution.

If β > 0 and (c₀,u₀) is a solution with w₀ = 2Cu₀ + Bc₀ + m, put

  c_t = c₀ + 4Ctw₀ + 4C²βt², u_t = u₀ + βt − 2Btw₀ − 2BCβt².
Then 2Cu_t + Bc_t + m = w₀ + 2Cβt, and βc_t + γ = w₀² + 4Cβtw₀ + 4C²β²t² = (w₀ + 2Cβt)²; so w_t² = βc_t + γ and, by (V.3) with C ≠ 0, P(c_t,u_t) = 0. Since 4C²β > 0 we get c_t → ∞, so S is infinite.

If β = 0 then c_τ = c₀ + 2Cτ, u_τ = u₀ − Bτ satisfy 2Cu_τ + Bc_τ + m = w₀, hence w_τ² = w₀² = γ = βc_τ + γ and P(c_τ,u_τ) = 0 for every τ ∈ ℤ. Taking τ = sign(C)·t gives c_t = c₀ + 2|C|t → ∞, so S is infinite.

If β < 0 then (−β)c ≤ γ at every solution, so c ≤ |γ|.

*Case Δ = 0, C = 0 (`dichotomy_degenerate_C_zero`).* Then B² = Δ = 0, so B = 0 and P = Ac² + lc + q + mu. If m ≠ 0 and (c₀,u₀) is a solution, put c_t = c₀ + m²t; then c_t ≡ c₀ (mod m), so Ac_t² + lc_t + q ≡ Ac₀² + lc₀ + q = −mu₀ ≡ 0 (mod m), and u_t := −(Ac_t² + lc_t + q)/m is an integer with P(c_t,u_t) = 0. Hence S is infinite. If m = 0: for A ≠ 0 a root of Ac² + lc + q = 0 satisfies c² ≤ |A|c² = |lc + q| ≤ |l|c + |q|, so c ≤ |l| + |q|; for A = 0 and l ≠ 0 the root c = −q/l satisfies c ≤ |q|; for A = l = 0 the set S is ℕ (if q = 0, infinite) or ∅.

*Case Δ = δ² > 0, C ≠ 0 (`dichotomy_square_C_ne`).* Put X = 2δ²c + β and Y = 2δw. Then X² − Y² = β² − 4δ²γ =: N′ by (V.3). If N′ ≠ 0, both X − Y and X + Y are nonzero divisors of N′, so |X − Y| ≤ |N′| and |X + Y| ≤ |N′|, hence 2|X| ≤ 2|N′| and c ≤ (|N′| + |β|)/(2δ²) ≤ |N′| + |β|. If N′ = 0 then Y = sX with s ∈ {1, −1} at every solution; take one solution (c₀,u₀) with that sign, put σ = sign(C), and set

  c_t = c₀ + 2σCδ·t = c₀ + 2|C|δ·t, u_t = u₀ + σ(sδ² − Bδ)·t.
Then w_t = w₀ + 2σCsδ²t, so Y_t = Y₀ + 4σCsδ³t = s(X₀ + 4σCδ³t) = sX_t; therefore X_t² − Y_t² = 0 = N′, which by (V.3) says P(c_t,u_t) = 0. Since 2|C|δ > 0, c_t → ∞ and S is infinite.

*Case Δ = B² > 0, C = 0 (`dichotomy_square_C_zero`).* Then B ≠ 0 and P = (Bc + m)u + (Ac² + lc + q). Put R = B²q − Blm + Am². Expanding the right side verifies the identity

  B²(Ac² + lc + q) = (Bc + m)(ABc + Bl − Am) + R  (V.4)
for all c. If every c ∈ S has Bc + m = 0 then |B|c = |m| and c ≤ |m|. Otherwise fix (c₁,u₁) ∈ S with Bc₁ + m ≠ 0; multiplying P(c₁,u₁) = 0 by B² and using (V.4) gives

  (Bc₁ + m)(B²u₁ + ABc₁ + Bl − Am) = −R.  (V.5)
If R = 0, then (V.5) and Bc₁ + m ≠ 0 force B²u₁ + ABc₁ + Bl − Am = 0, and c_t = c₁ + B²t, u_t = u₁ − ABt satisfy

  P(c_t,u_t) = P(c₁,u₁) + tB·(B²u₁ + ABc₁ + Bl − Am) = 0
for every t; since B² > 0, S is infinite. If R ≠ 0 then for every c ∈ S with Bc + m ≠ 0 the identity (V.4) gives Bc + m ∣ R, so |Bc + m| ≤ |R| and c ≤ |R| + |m| ≤ (B² + |B| + |A| + 1)·((1 + |l| + |m|)² + |q|); the c with Bc + m = 0 satisfy c ≤ |m|. (The Lean constant is K = B² + |B| + |A| + 1.)

*Case Δ > 0 a non-square (Pell; `dichotomy_pell`).* Then C ≠ 0, since C = 0 would make Δ = B² a square. Put X = 2Δc + β and Y = 2w, so that (V.3) reads

  X² − ΔY² = β² − 4Δγ =: N′.
If X ≤ 0 then 2Δc ≤ −β and c ≤ |β|: bounded. So suppose some solution has X > 0; we show S is unbounded, hence infinite.

Since Δ is a positive non-square there is a unit p² − Δq² = 1 with p, q > 0 (mathlib `Pell.exists_of_not_isSquare`). Its powers (p + q√Δ)ᵏ = p_k + q_k√Δ satisfy p_{k+1} = p p_k + Δ q q_k > p_k and q_{k+1} = p q_k + q p_k > q_k, so p_k ≥ 2 and q_k ≥ 1 for k ≥ 1, and p_k² − Δq_k² = 1. Let M = 8Δ|C|. By pigeonhole on the residues (p_k, q_k) modulo M there are 1 ≤ i < j with (p_i, q_i) ≡ (p_j, q_j); then T = j − i ≥ 1 satisfies (p_T, q_T) ≡ (1, 0) (mod M), because p_T + q_T√Δ = (p_j + q_j√Δ)(p_i − q_i√Δ) ≡ (p_j + q_j√Δ)(p_j − q_j√Δ) = p_j² − Δq_j² = 1 (mod M).

Given a solution with X > 0, put ε = sign(Y) ∈ {1, −1} (with ε = 1 if Y = 0) and

  X′ = X p_T + ΔY·(εq_T), Y′ = X·(εq_T) + Y p_T,
so that ΔY(εq_T) = Δ|Y|q_T ≥ 0. Composition of the norm form gives X′² − ΔY′² = (X² − ΔY²)(p_T² − Δq_T²) = N′; moreover X′ ≥ X p_T ≥ 2X > X, and X′ ≡ X, Y′ ≡ Y (mod M).

Now 2Δ ∣ M, so c′ := (X′ − β)/(2Δ) = c + (X′ − X)/(2Δ) is an integer with c′ > c ≥ 0; 2 ∣ M and Y is even, so w′ := Y′/2 is an integer; and

  u′ := (w′ − Bc′ − m)/(2C) = u + (Y′ − Y)/(4C) − B(X′ − X)/(4ΔC)
is an integer, because M = 8Δ|C| divides both Y′ − Y and X′ − X, so that (Y′ − Y)/2 and (X′ − X)/(2Δ) are each divisible by 4|C| and hence by 2C. Then (c′, u′) is a solution with c′ > c, and iterating produces elements of S beyond every bound. ∎

#### V.5 The uncoupled rank-one branch

**Corollary V.5** (uncoupled rank-one branch; `rank_one_uncoupled`, the m₂ = 0 sub-branch). In Part II, Lemma 6, case (b = 0, μ = 0), the condition on c is ∃u : Q(c,u) = 0 with Q a quadratic in the two variables (c, u). The projection is either infinite or bounded by K·((1+|ℓ|+|m|)² + |q|) with K = K(A, B₁, k) from Theorem V.4.

*Proof.* The condition is exactly membership in the set S of Theorem V.4 for the coefficient data of Q, and Theorem V.4 gives the dichotomy with that constant. The infinite branch already contains the Pell orbits of the Δ > 0 non-square case, which is where a Pell mechanism enters the rank-one component. ∎

#### V.6 Integer proportionality from vanishing pair minors

**Lemma V.6** (`all_pairMinors_zero_iff_rank_one_affine_family`, `primitive_affine_direction`). Let (b_i, m_i) ∈ ℤ² for i = 1, …, s satisfy b_im_j − b_jm_i = 0 for all i, j. Then there exist (b₀, m₀) ∈ ℤ² with gcd(b₀, m₀) = 1 and integers λ₁, …, λ_s such that (b_i, m_i) = λ_i·(b₀, m₀) for every i.

*Proof.* If every pair is (0,0), take (b₀, m₀) = (1, 0) and λ_i = 0 for all i.

Otherwise fix i₀ with (b_{i₀}, m_{i₀}) ≠ (0,0), put g = gcd(b_{i₀}, m_{i₀}) > 0 and write b_{i₀} = g b₀, m_{i₀} = g m₀; then gcd(b₀, m₀) = 1. The minor condition with j = i₀ reads b_i·g m₀ = g b₀·m_i, and cancelling g ≠ 0 gives

  b_i m₀ = b₀ m_i for every i.  (V.2)
*If b₀ = 0*, then gcd(0, m₀) = 1 forces |m₀| = 1, and (V.2) gives b_i m₀ = 0, hence b_i = 0 for all i. Take λ_i := m_i m₀; then λ_i m₀ = m_i m₀² = m_i (as m₀² = 1) and λ_i b₀ = 0 = b_i.

*If b₀ ≠ 0*, then (V.2) shows b₀ ∣ b_i m₀, and gcd(b₀, m₀) = 1 gives b₀ ∣ b_i by Bézout: choose x, y with x b₀ + y m₀ = 1, so that

  b_i = x b₀ b_i + y·b_i m₀ = x b₀ b_i + y·b₀ m_i = b₀(x b_i + y m_i).
Set λ_i := x b_i + y m_i ∈ ℤ, so b_i = λ_i b₀. Substituting into (V.2) gives λ_i b₀ m₀ = b₀ m_i, and cancelling b₀ ≠ 0 yields m_i = λ_i m₀. ∎

This is the integrality used in Part II, Lemma 3B: the λᵢ there are these integers, so g = gcd(λ₁, …, λ_s) is well defined and positive whenever some pair is nonzero.

## Declaration on AI-assisted tools

During the preparation of this work the author used large language models (Claude, ChatGPT and Claude Code) for drafting and editing prose, for tactic-level proof search in Lean under statements fixed by the author, and as an adversarial reader of statements and drafts. After using these tools the author reviewed and edited the content as needed; no model output was treated as a source of mathematical truth. Correctness is supported by the complete human-readable proofs and by independent checking of the formal declarations by the Lean kernel. The author reviewed the mathematical statements, proofs, citations and final manuscript, and assumes full responsibility for the content of the publication.

## References

[LR78a] J. S. Lew, A. L. Rosenberg, *Polynomial indexing of integer lattice-points. I. General concepts and quadratic polynomials*, J. Number Theory **10** (1978), 192--214. DOI 10.1016/0022-314X(78)90035-5.
[LR78b] J. S. Lew, A. L. Rosenberg, *Polynomial indexing of integer lattice-points. II. Nonexistence results for higher-degree polynomials*, J. Number Theory **10** (1978), 215--243. DOI 10.1016/0022-314X(78)90036-7.
[Gj21] K. S. Gjaldb\ae k, *Non-injectivity of nonzero discriminant polynomials and applications to packing polynomials*, arXiv:2102.03392 (2021).
[DLS64] H. Davenport, D. J. Lewis, A. Schinzel, *Polynomials of certain special types*, Acta Arith. **9** (1964), 107--116. DOI 10.4064/aa-9-1-107-116.
[DLS66] H. Davenport, D. J. Lewis, A. Schinzel, *Quadratic Diophantine equations with a parameter*, Acta Arith. **11** (1966), 353--358. DOI 10.4064/aa-11-3-353-358.
[FP23] R. Fueter, G. P\'olya, *Rationale Abz\"ahlung der Gitterpunkte*, Vierteljschr. Naturforsch. Ges. Z\"urich **58** (1923), 380--386.
[GS81] F. Grunewald, D. Segal, *How to solve a quadratic equation in integers*, Math. Proc. Cambridge Philos. Soc. **89** (1981), 1–5.
[GS04] F. Grunewald, D. Segal, *On the integer solutions of quadratic equations*, J. Reine Angew. Math. **569** (2004), 13–45.
[GA26] B. Grechuk, J. Agbanwa, *On the polynomial values represented by quadratic forms*, arXiv:2607.06627 (2026).
[DPR61] M. Davis, H. Putnam, J. Robinson, *The decision problem for exponential Diophantine equations*, Ann. of Math. **74** (1961), 425–436.
[Sko38] Th. Skolem, *Diophantische Gleichungen*, Ergebnisse der Mathematik und ihrer Grenzgebiete **5**, Springer, Berlin, 1938.
[Jon82] J. P. Jones, *Universal Diophantine equation*, J. Symbolic Logic **47** (1982), 549–571. DOI 10.2307/2273588.
[Mat10] Yu. Matiyasevich, *Towards finite-fold Diophantine representations*, J. Math. Sci. (N.Y.) (2010). DOI 10.1007/s10958-010-0179-4.
[Mat70] Yu. Matiyasevich, *Enumerable sets are Diophantine*, Dokl. Akad. Nauk SSSR **191** (1970), 279–282.
[DDF] N. Daans, P. Dittmann, A. Fehm, *Existential rank and essential dimension of Diophantine sets*, arXiv:2102.06941.
[BDHMS25] T. Bayer, M. David, A. Haßler, Yu. Matiyasevich, D. Schleicher, *Diophantine equations with a small number of unknowns and low degree*, arXiv:2506.20909 (2025).
[BDKN22] A. Bodin, P. Dèbes, J. König, S. Najib, *The Hilbert--Schinzel specialization property*, J. Reine Angew. Math. **785** (2022), 55--79. arXiv:2009.07254.
[Clu03] R. Cluckers, *Presburger sets and p-minimal fields*, J. Symbolic Logic **68** (2003), 153–162. DOI 10.2178/jsl/1045861509.
[Koj15] T. Kojima, *Note on number-theoretical properties of algebraic functions*, Tohoku Math. J. **8** (1915), 24--37.
[Sch00] A. Schinzel, *Polynomials with special regard to reducibility*, Cambridge University Press, 2000.
[Cas55] J. W. S. Cassels, *Bounds for the least solutions of homogeneous quadratic equations*, Proc. Cambridge Philos. Soc. **51** (1955), 262–264.
[Die03] R. Dietmann, *Small solutions of quadratic Diophantine equations*, Proc. London Math. Soc. (3) **86** (2003), 545–582.
[Fuk13] L. Fukshansky, *Heights and quadratic forms: on Cassels' theorem and its generalizations*, in: Diophantine methods, lattices, and arithmetic theory of quadratic forms, Contemp. Math. **587**, Amer. Math. Soc., 2013, 77–94.
[KK26] B. Kane, D. Kim, *Theta series of ternary quadratic lattice cosets*, Selecta Math. (N.S.) **32** (2026), Paper No. 5. DOI 10.1007/s00029-025-01110-0.
[Mas98] D. W. Masser, *How to solve a quadratic equation in rationals*, Bull. London Math. Soc. **30** (1998), 24–28.
[Nag] T. Nagell, *Introduction to Number Theory*, Wiley, 1951 (Pell classes).
[mathlib] The mathlib Community, *The Lean mathematical library*, CPP 2020. Modules used: `Mathlib.Computability.*`, `Mathlib.NumberTheory.SumFourSquares`, `Mathlib.NumberTheory.LSeries.PrimesInAP`, `Mathlib.NumberTheory.Zsqrtd.Basic`.
