# Trust boundary — APAL submission artifact

This document states the CURRENT trust facts of the release: what the kernel certifies, what it does not, the external inputs, the non-effective steps, what is open, and the counts the checks recompute. It carries no development history. A separate development-history record (`history/DEVELOPMENT_AUDIT_HISTORY.md`) documents superseded certificates and corrected defects; it is not part of the current proof claim.

Release identity, source status (`submission/CANONICAL_SOURCE`), build command (`release/build_submission_from_package.sh`) and the Zenodo/GitHub locators are stated in the seal beside this file (`correspondence/SEAL_<round>.txt`) and in `release/CITATION.cff`; they are not repeated here so that one file holds each fact.

Every figure in this file is inserted by `tools/generate_trust.py` from the shipped certificates when the package is assembled ({{generated_on}}); none is typed, and `tools/submission_figures.py --trust` and `tools/shipping_artifact_gate.py` refuse a package in which this file and the certificates disagree.

## 1. What the kernel certifies

The Lean development is built against mathlib pinned at `d46bd45325c5cdf0ecf5cee0f5ff6d6e3586eb35`,
toolchain `v4.31.0-rc1`. `scripts/FinalAxiomReport.lean` prints the axiom footprints of its own listed
roots; the counts below refer to that report, not to all declarations of the development. For the
registered paper declarations, including ResearchUpgrade, elaborated types and axiom footprints are
recorded in `certificates/PaperClaimTypeReport_current.log`:

| quantity | value |
|---|---|
| axiom_roots (roots reported) | {{axiom_roots}} |
| axiom_roots_with_axioms (roots depending on some axiom) | {{axiom_roots_with_axioms}} |
| axiom_roots_axiom_free (roots depending on no axiom) | {{axiom_roots_axiom_free}} |
| footprint_all_three (`[propext, Classical.choice, Quot.sound]`) | {{footprint_all_three}} |
| footprint_propext_only (`[propext]`) | {{footprint_propext_only}} |
| footprint_propext_quot (`[propext, Quot.sound]`) | {{footprint_propext_quot}} |
| axioms outside the standard three | 0 |
| `sorryAx`, `native_decide`, `ofReduceBool`, `trustCompiler` | 0 |
| errors | 0 |

A footprint of the three standard axioms is what an ordinary classical proof looks like in Lean; it
is not a disclosure of anything unusual. What matters is the two rows above `errors`: among the reported roots there is no custom axiom
and no compiler-trusting tactic.

## 2. What the kernel does not certify

**Statement fidelity.** A kernel proof certifies that a formal statement follows from the axioms, not
that the statement models the prose. Three mechanisms sit in that gap. (i) Every declaration selected
for the statement-fidelity registry is frozen in a separate file and compared with the production tree by
whitespace-normalized textual declaration comparison (`scripts/statement_diff.py`: {{frozen_theorems}}/{{frozen_theorems}} theorems,
{{frozen_definitions}}/{{frozen_definitions}} definitions, 0 failures, {{frozen_files}} frozen files; a frozen name that matches
more than one production declaration by its short name is resolved by the exact statement text, and the log counts such
look-ups as `DUPLICATE_NAMES` — ambiguous look-ups, not duplicate Lean declarations), with a negative control that
plants a mutation and a deletion and requires both to be caught, and a unicode control. The registry
does not contain every exported root: the root reconciliation report
(`certificates/ROOT_FROZEN_RECONCILIATION_current.md`, §7 below) lists the exported roots outside it.
(ii) Separately from the textual comparison, the bodies of the frozen definitions are hashed
(`scripts/definition_fidelity.py`, `certificates/definition_bodies_current.tsv`), so that a definition whose
text is unchanged but whose meaning has moved through an unfolded dependency is a distinct certificate
from (i). (iii) Every representing polynomial was cross-checked in a computer algebra system against an
independent reimplementation before its proof was attempted.

**Paper-claim registry (model-assisted, author-approved, with tamper detection).** Every numbered theorem,
proposition and corollary of the manuscript that names a Lean declaration has a row in
`submission/native/PAPER_CLAIMS.tsv`: the Lean roots it cites, the domain, arities, degree bound,
quantifier pattern and external hypotheses in words, a hash of the paper statement, and
the SHA-256 of each cited root's elaborated Lean type, printed by `scripts/PaperClaimTypeReport.lean`
(fully qualified name, pretty-printed type at unbounded width with whitespace collapsed, binder count,
axiom footprint; four planted type controls, a fixed-degree theorem and its generic-degree cousin must
print different types, an exact alias the same) and tabulated with the external binders of the binder
ledger in `certificates/PAPER_CLAIM_LEAN_TYPES.tsv`. Distinct declarations can share a type (aliases
and layered restatements do), so a fingerprint identifies the statement, not the name.
`tools/paper_claims_check.py` fails the build when a registered statement changes, when a cited root
is missing, substituted or changes type, when a numbered statement with a Lean name is unregistered
(FORMAL_CLAIMS_FOUND/REGISTERED/MISSING are recomputed from the TeX), or when the Layer-2 review row is
missing or stale. What this registry establishes is bounded and should be read as such: it detects
unreviewed changes to registered paper statements and to the Lean root types they cite. The semantic
correspondence between a mathematical statement and a Lean type is recorded one row per cited
root in `submission/native/PAPER_CLAIMS_REVIEW.tsv` (reviewer, date, statement hash, Lean type, type
hash, disposition), and is not established by text hashing alone. The review found, and the correspondence
discloses, two head/type divergences that hashing alone could not have seen (Propositions 1.2 and 1.3
cited fixed-degree roots for statements made for every degree). `tools/paper_claims_controls.py`
plants defects into temporary copies and requires every one to be caught (its log line `NEGATIVE_CONTROLS_CAUGHT`
gives the current count); two of them (a changed
statement outside the earlier registry, an unrelated root substituted for a registered one) passed the
earlier registry check and were reported by the external reviewer.

**Prose fidelity.** The shipping documents are also swept by
`tools/fidelity_destroyer.py`, which flags sixteen prose patterns that would claim more than the
kernel proves, each annotated with what the kernel actually supports. The current fidelity report lists
the flagged prose patterns together with their reviewed dispositions (`certificates/fidelity_destroyer_current.tsv`).
Counts of flags are not counts of mathematical errors and do not establish semantic correspondence by themselves.

**Definitions are not roots.** A few load-bearing declarations — notably the conversion of a
structured family into a certificate — are definitions producing data, and definitions are not roots
of the axiom report. Their footprint is inherited by every theorem that uses them, and those theorems
are reported, but the root count is a count of theorems and not of all declarations.

## 3. External inputs

Three, and each is a `def … : Prop` appearing as an explicit hypothesis of the theorems that use it.
None is an `axiom`, so no result depends on any of them silently. `#print axioms` shows only the standard three
axioms for these theorems, as for all others; that does not make the hypotheses unnecessary, and the hypothesis-binder
ledger (`certificates/binder_ledger_current.log`) marks the roots that carry one as CONDITIONAL.

| input | where | ordinary mathematics | used for (explicit hypothesis in Lean) |
|---|---|---|---|
| code-uniform decidability of integer quadratic solvability (Grunewald–Segal, [GS04]) — the uniformity in the code is part of the hypothesis, not an afterthought | Definition 1.5 | literature input, through the code bridge of Theorem 6.4 | SE₂ ⊆ REC and its strictness at positive arity; together with DPRM over ℕ, the complete relation phase diagram of Theorem 6.8 |
| DPRM over ℕ | Definition 1.6 | literature input, transported to ℤ by Theorem 6.7 | RE = PP₂ = SE₄ and the function phase diagram; with the Grunewald–Segal input, the complete relation phase diagram of Theorem 6.8 |
| TCER, eventual representation by a positive definite ternary lattice coset under primitive local representability, bounded bad-prime valuations, and avoidance of finitely many exceptional square classes (`TCERBridge.TernaryCosetEventualRepresentation`) | Section 10 | the published theorem of Kane and Kim [KK26], applied through Lemma 10.8; not formalized | the forward directions of the classification of definable functions (Propositions 10.9, 10.14, 10.17), the full normal form (Proposition 10.7), and Propositions 10.10 and 10.15 |

None of the three is used by the sharp dimension theorem (Theorem 4.1), by the converse constructions and the case
without unknowns in Section 10 (the reverse directions of Propositions 10.9 and 10.14, and Propositions 10.16 and
10.18), by the two-coset lemma (Lemma 10.13), or by the composition and the positive-definite presentation of common slopes.

Skolem's degree reduction is **not** an external input: it is proved here (Theorem 6.2).

The bridge to [GS04] is an **effective coding-equivalent consequence**, not an identity of statements.
Theorem 6.4 supplies the compiler from our finite quadratic codes to a parameter-free coefficient
table and 6.4(f) shows the compiler is primitive recursive; uniformity of the decision procedure in
the table is assumed, in the form in which [GS04] states its input, and is not derived from
per-equation decidability.

## 4. Non-constructive steps, named

The certificates of Section 8 assert that an infinite arithmetically structured set of outputs exists
and that each element is realised by some witness. The witnesses are selected from membership proofs
using `Classical.choice`. There is no algorithm here for producing witnesses, no parametrisation of
all solutions, and no claim that the three certificate forms are canonical, exhaustive of the fibre,
or mutually exclusive. The constant K of Theorem 9.2, and with it the constants of Theorems 2.1, 2.2,
3.2 and 4.1, is not effective.

The Pell orbit itself is effective — its recurrence, norm, congruence and growth properties are
proved constructively in Appendix F, Part III — but which branch of the dichotomy applies at a given
point is decided by the non-effective constant. The orbit is explicit; the choice of orbit is not.

## 5. What is open, and stated as open

The one-sorted coding arity at n = 2 was open in the previous version and is **no longer open**:
`atomGraphZZ_le_one` sharpens the upper bound to `AtomGraphZZ 2 n → n ≤ 1`, so with
`AtomGraphZZ 1 1` the two bounds meet and ca(SE₂) = 1 (`atomGraphZZ_capacity_eq_one`,
`not_atomGraphZZ_two`). The mixed-semantics analogue remains settled at two
(`graphCapacityZ r 2 = 2`); the two must not be identified, and that they differ is itself a
theorem (`natInput_intInput_separation_at_two`). A one-witness orbit normal form — a finite-union
description of the fibres of an equation with one unknown, a different object from the normal forms of
total functions in Section 10 — is expected but not proved and is not used anywhere in Sections 1–10; its
draft formalization lives in the development notes, marked conditional. The analytic input TCER of
Section 10 is not formalized; it is a hypothesis (Section 3 above).

## 6. Boundary of this artifact

The public core is the Lean development, the frozen statements, the certificates listed in
`certificates/`, and the manuscript. The development history — internal review rounds, homework
ledgers, provider correspondence — is not part of the submission and is archived separately.

## 7. Reconciliation of the two mechanisms, and the census of cited names

This belongs with the artifact rather than the paper: a reader auditing the trust boundary needs it, a reader of the mathematics does not.

**The two mechanisms do not cover the same set, and the numbers should be reconciled here rather than left to be noticed.** The axiom report has {{axiom_roots}} roots; the declaration diff has {{frozen_theorems}} frozen theorem statements; {{recon_both}} declarations are in both. So {{recon_frozen_not_root}} frozen theorems are not themselves roots — their footprints reach the report only through the roots that use them — and {{recon_root_not_frozen}} roots are production declarations with no frozen statement. The full three-way listing is `certificates/ROOT_FROZEN_RECONCILIATION_current.md`, written by the same generator from the shipped axiom report and frozen statements at assembly (identity: a frozen `theorem` qualified by its `namespace` stack equals the root name printed by the report). Making the two sets coincide is work still to do, not a matter of presentation.

**Names cited here.** Every declaration named in this paper exists in the development. Twenty-three are outside the frozen-statement set: eight of those — `apal_logic_core`, `coder_counting_bound`, `primrec_eval_of_coords`, `primrec_int_pow`, `primrec₂_int_add`, `primrec₂_int_mul`, `quadraticProjectionDichotomyZ_all`, `quadraticWitnessInertiaZ` — are roots of the axiom report, so their footprints are reported even though their statements are not diffed. The remaining fifteen — `GraphAchievableZ`, `code`, `code_injective`, `compSys`, `coordPoly`, `diophN_graph_code`, `eval_abs_le_int`, `eval_relabelG_ZZ`, `fboundG_box_le`, `fiberVal_flip`, `mem_fiberZZ_coordPoly`, `normal_form_general_quadratic`, `not_MPUP_N`, `not_MPUP_Z`, `relabelG` — are covered by neither mechanism under those names, and are cited as signposts into the sources. Two of them deserve a word: `not_MPUP_N` and `not_MPUP_Z` (the Appendix C application) are the convenience forms, and the same two propositions are proved by `not_MPUP_N_of_bound`, `not_MPUP_Z_of_bound`, `not_MPUP_N_of_weighted_bound` and `not_MPUP_Z_of_weighted_bound`, which are roots of the axiom report, the last two also frozen. No theorem asserted in this paper rests on a name in either list: every numbered result above is proved here or in Appendix F, and the Lean names are pointers. The inventory is recomputed by `scripts/cited_name_census.py`, which fails the build if these three numbers disagree with the development. The count is a fixed point, since this paragraph is itself part of the text being censused: naming a declaration here puts it into the corpus. The figures below are the converged ones. The bare names `sorryAx`, `native_decide`, `ofReduceBool` and `trustCompiler` are Lean tokens, not declarations of ours.

## 8. The counts

The manuscript states that every axiom footprint is contained in the standard set and that no
forbidden token occurs. The numbers are here, and `tools/submission_figures.py --trust` recomputes them from the certificates and fails
the build if this document and the development disagree.

```
FIGURES (recomputed by tools/submission_figures.py; do not edit by hand)
axiom_roots={{axiom_roots}}
axiom_roots_with_axioms={{axiom_roots_with_axioms}}
axiom_roots_axiom_free={{axiom_roots_axiom_free}}
footprint_all_three={{footprint_all_three}}
footprint_propext_only={{footprint_propext_only}}
footprint_propext_quot={{footprint_propext_quot}}
binder_roots={{binder_roots}}
binder_unconditional={{binder_unconditional}}
frozen_theorems={{frozen_theorems}}
frozen_definitions={{frozen_definitions}}
frozen_files={{frozen_files}}
```

Read them with the caveat the manuscript states: the root count counts theorems, not declarations,
and a definition producing data is not a root of the axiom report.

