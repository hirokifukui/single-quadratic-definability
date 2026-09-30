# CLAIM_BY_CLAIM_CROSSWALK — claim-level comparison with the literature

(2026-08-29. Ten claims, eight fields each: our claim / nearest
external theorem / their assumptions / our extra assumptions / their
conclusion / our extra conclusion / overlap / residual novelty. Literature
status tags: [V-fulltext] = verbatim audit closed;
[AUDIT-pending] = located, verbatim audit of the full text not yet done
(the cited statement was checked against the abstract and the reviewed
summary only); "none located" =
search axes A1–A8 of LITERATURE_THEORY_GATE.md returned no candidate — a
per-query record, not a completeness claim. No "first" wording anywhere in
the paper before the MathSciNet pass and author 1-pagers (both gated on
the authors).)

## C1 — quadratic projection dichotomy, uniform constant

- **Ours**: for every r and every quadratic fiber datum (A,B,C) there is
  K(A,B,C) with: for all affine data (l,m,q), the projection set S is
  infinite or S ⊆ [0, K·((1+|ℓ|₁)²+|q|)] (`quadraticProjectionDichotomyZ_all`).
- **Nearest external**: Grunewald–Segal decidability [GS04, Thm 0.1]
  [V-fulltext]; classical binary-form value-set theory (r = 1 layer,
  disclosed since r06).
- **Their assumptions**: single affine quadratic, rational coefficients,
  any number of unknowns.
- **Our extra assumptions**: none beyond integrality of the datum.
- **Their conclusion**: an algorithm deciding solvability per instance.
- **Our extra conclusion**: a quantitative dichotomy with ONE constant
  uniform over the affine data, with the parameter dependence confined to
  ((1+|ℓ|₁)²+|q|).
- **Overlap**: both live on the single-quadratic decidability boundary.
- **Residual novelty**: the uniform bound and its shape; GS04 produces no
  bounds and no uniformity statement.

## C2 — G_ℤ(r,2) = 2 for all r

- **Ours**: the semantic graph capacity of one quadratic with r ℤ-witnesses
  is exactly 2, independent of r (`quadraticWitnessInertiaZ`).
- **Nearest external**: none located (axes A1–A8; capacity notion appears
  to be ours from r04 onward).
- **Their assumptions / conclusion**: —.
- **Our extra assumptions**: injective graph representation, total degree
  counts all variables.
- **Our extra conclusion**: exact value with witness-count independence.
- **Overlap**: none identified.
- **Residual novelty**: statement and value; contingent on the gated
  MathSciNet pass for the final wording.

## C3 — achievability characterization

- **Ours**: GraphAchievableZ(n, r, 2) ⟺ n ≤ 2
  (`graphAchievableZ_degree_two_iff`).
- **Nearest external**: as C2. Fields as in C2; the iff packages the upper
  bound (C1 counting) with the explicit pairing-polynomial lower bound.
- **Residual novelty**: the two-sided exactness at every r.

## C4 — arity-spectrum inertia

- **Ours**: at degree 2 the achievable arity spectrum with r witnesses
  equals the spectrum with 0 witnesses (`quadratic_graph_arity_inertia`).
- **Nearest external**: none located; witness-elimination results in the
  literature concern universality pairs (Jones spectrum), not graph
  capacity [AUDIT-pending: Jones 1982].
- **Their assumptions**: (Jones) universality, degree ≥ 4 regime.
- **Our extra assumptions**: degree-2 graph regime.
- **Their conclusion**: universal pairs ⟨unknowns, degree⟩ trade-offs.
- **Our extra conclusion**: witnesses buy nothing at degree 2 for graphs.
- **Overlap**: the trade-off theme.
- **Residual novelty**: the inertia phenomenon itself.

## C5 — syntactic capacity S(2, r+1) = r+3

- **Ours**: exact syntactic parameter capacity at degree 2
  (`capBound_degree_two` + achievability).
- **Nearest external**: monomial-counting bounds are classical
  combinatorics; the capacity framing is ours (r04).
- **Their assumptions**: —. **Our extra assumptions**: the S-capacity
  definition. **Their conclusion**: —. **Our extra conclusion**: exact
  value r+3.
- **Overlap**: the count C(d+q, q+1) is elementary.
- **Residual novelty**: the definition and its role as the top level of the
  classification; the count itself carries no novelty claim.

## C6 — exact syntactic/semantic gap

- **Ours**: S − G = r+1 exactly at degree 2 (`quadratic_gap_exact`,
  `quadratic_syntactic_semantic_gap`).
- **Nearest external**: none located (the gap requires both C2 and C5).
- **Residual novelty**: consequence-level; novelty concentrated in C2.

## C7 — U_ℤ(r,2) = U_ℕ(r,2) = 0

- **Ours**: no single quadratic is Diophantine-universal at any arity ≥ 1,
  for any witness count; Lean conditional on
  `QuadraticSolvabilityDecidableZ/N` + `HardDiophantineSetExists`; NL
  unconditional citing [GS04]+[Mat70].
- **Nearest external**: [GS04] decidability [V-fulltext]; [Mat70] DPRM;
  antecedents [GS81], [Sie72].
- **Their assumptions**: as published.
- **Our extra assumptions**: none (NL); the two named hypotheses (Lean).
- **Their conclusion**: decidability (GS04); universality of Diophantine
  sets (Mat70).
- **Our extra conclusion**: the exact capacity value U = 0 and its
  placement in the classification.
- **Overlap**: total on inputs — U = 0 is presented as a direct corollary
  of [GS04]+[Mat70], not as new decidability mathematics.
- **Residual novelty**: the classification placement and the
  kernel-checked conditional reduction; nothing else claimed.

## C8 — the three-level classification U < G < S

- **Ours**: 0 < 2 < r+3 with both gaps exact, for every r.
- **Nearest external**: none located as a classification; components as in
  C2/C5/C7.
- **Residual novelty**: the table as a theorem; the degree-2 boundary
  (one equation) as the locus where all three notions separate.

## C9 — relations to the adjacent programs: DDF and Grechuk–Agbanwa

*C9a — DDF (Daans–Dittmann–Fehm, arXiv:2102.06941; §8 read verbatim).*
- **Ours**: capacities of ONE equation at FIXED degree 2 — how many
  parameters can be named / graph-encoded / universally served.
- **Nearest external**: DDF's existential rank and essential dimension of
  Diophantine sets — the minimal number of existential quantifiers for a
  FIXED set, with degree unconstrained.
- **Their assumptions**: arbitrary degree; the set is the fixed object.
- **Our extra assumptions**: degree ≤ 2; the equation is the fixed object,
  quantifying over parameters.
- **Their conclusion**: rank/dimension invariants of sets.
- **Our extra conclusion**: exact capacity values at the decidability
  boundary, with the U/G/S separation.
- **Overlap**: representation economy for Diophantine definitions; the
  zbMATH axis `ti:"existential rank"` returns DDF and nothing else (all
  years, re-run s14).
- **Residual novelty**: a degree-sensitive complementary invariant to
  DDF's degree-unconstrained existential rank — DDF's invariants do not see
  the degree-2 phase where U, G, S separate. No comparison theorem between
  the two invariants is proved; the word "refinement" is not used in the
  paper.

*C9b — Grechuk–Agbanwa, "On the polynomial values represented by quadratic
forms", arXiv:2607.06627 [V-fulltext: PDF on disk, read in full s13; see
QUADRATIC_DECIDABILITY_AUDIT.md row GA26].*
- **Ours**: for a FIXED quadratic shape in (c, u), the ℕ-output projection
  of EVERY affine perturbation is infinite or uniformly quadratically
  bounded (projection dichotomy), and the graph-capacity classification
  G_ℤ(r,2) = 2 that follows.
- **Nearest external**: a FIXED binary quadratic form F(y,z) representing
  infinitely many values P(x) of a one-variable polynomial; main result
  formalized in Lean.
- **Their assumptions**: one fixed form and one fixed polynomial; the
  question is infinitude of representation.
- **Their conclusion**: infinitude via a tangent / Pell-type construction.
- **Overlap**: quadratic forms, Pell-type arithmetic, Lean formalization.
- **Residual novelty**: the uniform (over affine data) projection dichotomy
  with an explicit bound shape, and the capacity classification; neither
  appears there. No capacity notion in their paper.
- **Status**: audited at full text; wording in MANUSCRIPT §7 aligned to
  this row. Related-work comparison only; no priority claim in either
  direction.

## C10 — component machinery (normal form + moving-modulus prime steps)

- **Ours**: the integral congruence radical decomposition (not SNF), the
  fixed-remainder and moving-discriminant identities, and the
  Dirichlet-driven prime steps (k₀ ≥ 2 and rank-one), as a reusable
  toolkit behind C1.
- **Nearest external**: saturation/complement arguments are standard
  module theory; Dirichlet, reciprocity, Pell are classical (all inside
  the mathlib kernel boundary, see TRUST_BOUNDARY.md).
- **Their assumptions / conclusion**: classical statements as in mathlib.
- **Our extra conclusion**: the assembly under a single uniform bound
  shape.
- **Overlap**: every individual ingredient.
- **Residual novelty**: none claimed for ingredients; the dispatch
  architecture and uniformity are part of C1's claim, not separate.
