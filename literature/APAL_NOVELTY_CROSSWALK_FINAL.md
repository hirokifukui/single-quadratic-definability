# APAL_NOVELTY_CROSSWALK_FINAL — Gate 3 (r17, 2026-08-30; s17)

Format per GPT r16 §11 Gate 3: for each comparison target — our exact theorem / nearest theorem / their hypotheses /
their conclusion / overlap / residual novelty / priority status. Built on CLAIM_BY_CLAIM_CROSSWALK.md (r16, ten claims),
LITERATURE_THEORY_GATE.md, QUADRATIC_DECIDABILITY_AUDIT.md, QUADRATIC_INERTIA_NOVELTY_GATE.md; new zbMATH queries this
session are logged in §B. Audit-status tags: [V-fulltext] verbatim audit of the primary source closed; [V-partial] the cited
statement checked verbatim, rest of the paper not; [L] located (zbMATH record), not read; "miss(Q)" = zbMATH query Q returned
nothing — never "absent from the literature".
Wording rule (unchanged): no "first" / "first-ever" / "introduces the first theory" anywhere until an external novelty inquiry
returns; the paper says "we are not aware of" only where this table has a search record.

## A. Comparison targets

### T1. BDHMS 2025 — Bayer, David, Haßler, Matiyasevich, Schleicher, arXiv:2506.20909v2 [V-fulltext §6.2 and main results; AFP entry]
- Our exact theorem: `not_MPUP_N` / `not_MPUP_Z` (std-3): no multiparameter universal pair in the literal sense of their §6.2 under total-degree counting; quantitative form `Quantitative.lean`.
- Nearest theorem: their universal pairs (ν, δ) for one-parameter Diophantine universality over ℤ (with formalization in Isabelle/AFP); §6.2 poses the multiparameter question as open.
- Their hypotheses: single-parameter universality; degree = total degree; unknowns in ℤ.
- Their conclusion: explicit universal pairs over ℤ (numerical values to be quoted from their abstract at final; not reproduced here from memory).
- Overlap: setting (total degree, universal pairs); our U-layer reuses their vocabulary.
- Residual novelty: the negative answer to their §6.2 question and its quantitative form; the S/G/U spectra as the reason.
- Priority status: our result postdates and answers theirs; no competing claim located. Author 1-pager to BDHMS pending (Dr. Fukui).

### T2. DDF — Daans, Dittmann, Fehm, "Existential rank and essential dimension of diophantine sets", arXiv:2102.06941 (v5) [V-partial: Def 1.3, §8 incl. Lemma 8.19 verbatim; rest [L]]
- Our exact theorem: capacities of one equation at fixed degree 2 (Theorems A, B); degree-filtered, over ℕ-parameters.
- Nearest theorem: existential rank rk∃(D) and essential dimension of a fixed Diophantine set — minimal number of existential quantifiers, degree unconstrained, over fields/rings; Lemma 8.19 (polynomial injection R²→R collapses arities).
- Their hypotheses: fixed set; arbitrary degree; ring R with an injective polynomial pairing.
- Their conclusion: rank/dimension invariants; arity collapse via pairing when degree is free.
- Overlap: representation economy of Diophantine definitions; the pairing-collapse theme (our G lower bound uses the same Cantor pairing).
- Residual novelty: the degree-2 phase where the collapse *fails to buy anything from witnesses* (G_ℤ(r,2)=2 for all r) — invisible to a degree-free invariant. No comparison theorem between the invariants is claimed; "refinement" is not used.
- Priority status: independent programs; DDF earlier (2021) on the degree-free side. zbMATH `ti:"existential rank"` returns only DDF (re-run s17, §B.q5).

### T3. Grunewald–Segal 1981 / 2004 [V-fulltext GS04 Thm 0.1; GS81 abstract+extract]
- Our exact theorem: Theorem C, U_ℤ(r,2) = U_ℕ(r,2) = 0, Lean conditional on `QuadraticSolvabilityDecidableZ/N` + `HardDiophantineSetExists`.
- Nearest theorem: GS04 Thm 0.1 — uniform algorithm deciding solvability of a rational quadratic in any number of unknowns over ℤ, over ℕ, and over hyperplane-restricted regions.
- Their hypotheses: one affine quadratic equation, rational coefficients.
- Their conclusion: decidability (no bounds, no uniformity over parameters).
- Overlap: total on the input side of Theorem C.
- Residual novelty: none in decidability; Theorem C is a corollary placement (with DPRM) plus the kernel-checked reduction. Also: the projection dichotomy (Theorem A) is a *quantitative* statement GS do not make (per-instance algorithm vs. one constant for all affine data).
- Priority status: classical input, cited as such.

### T4. Lagarias, arXiv:math/0611209v2 (long version of FOCS 1979) [V-fulltext, pdf md5 4fc998fa]
- Our exact theorem: the r = 1 layer (`quadraticProjectionDichotomyZ_one`, Appendix C.2) — one-witness fiber dichotomy by discriminant class.
- Nearest theorem: his definite / degenerate / indefinite trichotomy of binary quadratic Diophantine equations by D = b²−ac, with small-solution bounds for the definite and degenerate classes and the Pell/automorph description of the indefinite class.
- Their hypotheses: one binary quadratic equation in two unknowns (both unknown).
- Their conclusion: solution-size bounds / structure per class (complexity of deciding BQDE).
- Overlap: the class split and the size bounds in the r = 1 layer are his in substance.
- Residual novelty: none for the class split; ours is the uniform-in-affine-data packaging (one constant, bound shape) and the assembly into the all-r theorem. Disclosed since r06.
- Priority status: Lagarias earlier; cited.

### T5. Grechuk–Agbanwa, arXiv:2607.06627 [V-fulltext, s13]
- Our exact theorem: Theorem A (projection dichotomy, uniform over affine data) and G_ℤ(r,2) = 2.
- Nearest theorem: a fixed binary quadratic form representing infinitely many values of a one-variable polynomial (Pell/tangent construction; Lean-formalized).
- Their hypotheses: one fixed form, one fixed polynomial.
- Their conclusion: infinitude of representation.
- Overlap: quadratic forms, Pell arithmetic, Lean.
- Residual novelty: uniform dichotomy with explicit bound shape; capacity classification. No capacity notion there.
- Priority status: contemporaneous (2026); related-work comparison only, no priority conflict.

### T6. Jones 1982, "Universal diophantine equation", J. Symb. Log. (Zbl 3773581, DOI 10.2307/2273588) [L — AUDIT-pending; located s17 §B.q1]
- Our exact theorem: `quadratic_graph_arity_inertia` / G-layer.
- Nearest theorem: universal Diophantine equations and the ⟨unknowns, degree⟩ spectrum (the classical pairs ⟨58,4⟩ … ⟨9, very large degree⟩ are attributed to this paper in the BDHMS/AFP chain; the exact list must be read from the JSL text, not from memory).
- Their hypotheses: universality (every r.e. set), degree ≥ 4.
- Their conclusion: trade-off pairs along the universality spectrum.
- Overlap: the unknowns/degree trade-off theme (also Matiyasevich–Robinson 1975, Zbl 3438960).
- Residual novelty: our trade-off is on the graph layer at degree 2, where the spectrum is flat in r. **Verbatim audit of Jones 1982 still required before final wording** (the AFP/BDHMS chain cites it; obtain the JSL text).
- Priority status: classical; no conflict expected, audit outstanding.

### T7. Packing / pairing polynomials — Fueter–Pólya (Vierteljschr. Naturforsch. Ges. Zürich 68, 1923; volume confirmed r16), Lew–Rosenberg, Nathanson 2016, Morales–Lew 1996 (Zbl 881755), Morales 2016 (Zbl 6661357), Stanton 2014, Sury–Vsemirnov 2022 (Zbl 7556281), Brandt–Gjaldbæk 2025 (Zbl 8102286) [L for the post-1996 items; Fueter–Pólya bibliographic record verified]
- Our exact theorem: lower bound in `graphAchievableZ_degree_two_iff` (Cantor pairing at r = 0) and the r = 0 instance of the upper bound.
- Nearest theorems: Fueter–Pólya (the two Cantor polynomials are the only quadratic bijections ℕ²→ℕ); box counting: an injective polynomial ℕⁿ→ℕ of degree d forces n ≤ d (folklore, sources in LITERATURE_NOTE_20260826.md); packing polynomials on sectors/lattices (structure of quadratic packings).
- Their hypotheses: witness-free polynomial maps; bijectivity or injectivity.
- Their conclusion: classification/existence of quadratic packings; no quadratic injective packing of ℕⁿ, n ≥ 3, by degree counting.
- Overlap: exactly the r = 0 layer of G; the counting step of our upper bound is the same folklore.
- Residual novelty: none at r = 0 (we cite it as folklore); the content of Theorem A is r ≥ 1, where the projection dichotomy replaces box counting.
- Priority status: classical; cited.

### T8. Parametric integral quadrics / integer points on affine quadrics uniformly in parameters — Siegel 1972 (Zbl 3397605), Cassels *Rational Quadratic Forms*, Watson *Integral Quadratic Forms* [U — candidates listed since r07, not audited]; zbMATH uniformity query miss (§B.q2)
- Our exact theorem: Theorem A's uniform constant K(A,B,C) over all affine (l, m, q).
- Nearest theorem: classical size bounds for a *single* quadratic equation (Siegel-type bounds on smallest solutions; Cassels' small-solution theorems for isotropic forms).
- Their hypotheses: one equation; bounds in terms of that equation's coefficients.
- Their conclusion: existence of a small solution when any exists.
- Overlap: bound-shape intuition (quadratic in the affine data) is consistent with small-solution theory.
- Residual novelty: the dichotomy form (infinite ∨ bounded) with uniformity over the affine family and the explicit shape ((1+|ℓ|₁)²+|q|); we do not claim the sharpest constant. **A targeted read of Cassels ch. 6 (small solutions) is the remaining audit item for this row.**
- Priority status: classical; no conflict expected; audit outstanding.

### T9. Bounded-degree existential definability (general) — zbMATH `any:"existential" & "definability" & "bounded degree" & "Diophantine"` miss (§B.q3); Pasten [Pas21] (as recorded in NOVELTY_CLAIMS_FORBIDDEN)
- Our exact theorem: the capacity framework S/G/U with exact degree-2 values (Theorem B, A, C).
- Nearest theorems: DDF (T2) on quantifier count; Pasten's survey framing of Diophantine definability complexity.
- Residual novelty: degree-sensitive capacities of one equation; the exact separation U < G < S at degree 2 with both gaps exact.
- Priority status: no competing statement located under the queries logged; the claim in the paper is phrased "we are not aware of a degree-filtered capacity notion for a single equation".

## B. zbMATH queries run this session (s17, 2026-08-30) — per-query record
- q1 `au:Jones & ti:"universal Diophantine" & py:1980-1985` → 1 hit, Jones 1982 (Zbl 3773581).
- q2 `any:"quadratic" & any:"integer points" & any:"uniform" & any:"family" & any:"bounded" & any:"infinite" & py:1970-2026` → miss.
- q3 `any:"existential" & any:"definability" & any:"bounded degree" & any:"Diophantine"` → miss.
- q4 `any:"Diophantine" & any:"quadratic" & any:"witnesses" & any:"degree two"` → miss.
- q5 `ti:"existential rank" | ti:"existential definability" & any:"number of quantifiers"` → 1 hit, DDF (2025 preprint record).
- q6 `ti:"packing polynomial" | ti:"packing polynomials"` → 7 hits (T7 list).

## C. Verdict for the desk (feeds APAL_DESK_SIGNIFICANCE.md)
Safe novelty claims (each a kernel theorem): exact degree-profile/specialization capacity S(d,q) (definition + value); uniform affine-perturbation projection dichotomy with explicit shape; all-r witness inertia G_ℤ(r,2) = 2; exact syntactic–semantic gap; multiparameter universal-pair obstruction (answer to BDHMS §6.2); the degree-sensitive capacity framework.
Not claimed as new: quadratic decidability (GS), Pell methods, integral radical splitting, U = 0 as mathematics (corollary of GS+DPRM), the r = 0 pairing/box-counting layer (Fueter–Pólya/folklore), the r = 1 class split (Lagarias).
Outstanding audits before final wording: Jones 1982 (T6), Cassels small-solution chapter (T8). Neither can create a priority conflict for the all-r statements; both can sharpen the related-work sentences.

---

### T8 UPDATE (s29, 2026-09-02) — audited, and one nearer theorem added

The r07 row above named Cassels/Siegel/Watson and left "a targeted read of Cassels ch. 6" as the
outstanding audit item. That audit is now done at the level of published statements, and it turned up a
theorem NEARER than Cassels:

**Dietmann, Proc. LMS (3) 86 (2003) 545–582, "Small solutions of quadratic Diophantine equations".**
Inhomogeneous integral quadratic Q in s ≥ 3 variables, nonsingular quadratic part, coefficient height
≤ H: a polynomial Λ_s(H) such that a solvable equation has a solution of size ≤ Λ_s(H). This is closer to
Theorem A/2.1 than Cassels (which is homogeneous and about the least nonzero zero), and it was not in
this file. The surrounding line — Fukshansky's survey, Contemp. Math. 587 (2013) 77–94 — is the map of
the whole direction and should be the entry point for any future audit of this row.

Verdict unchanged in substance, now stated with the sharper neighbour: they bound the SMALLEST solution
of ONE equation in terms of ITS coefficient height, under s ≥ 3 and nonsingularity; we bound EVERY element
of a FINITE fibre, uniformly over a parameter family, with one constant and an exponent independent of
the number of unknowns, and with no nonsingularity or arity hypothesis. Neither quantifier implies the
other. Priority status: classical line, no conflict, **now cited in the manuscript** ([Cas55] [Die03]
[Fuk13] [Mas98]) rather than merely logged here.

Process note. This row existed in the ledger from r07 and did not reach the manuscript, because v3.0 was
written blank-slate from the Lean tree and the literature ledger was not diffed against it. The gate that
would have caught it: before sealing, check that every row of this file with a non-empty "Nearest
theorem" appears in the manuscript's related-work section, or is explicitly recorded as deliberately
omitted.
