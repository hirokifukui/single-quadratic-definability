# mpup r53 — APAL submission artifact

Version 0.31.0 (`CITATION.cff`), 2026-09-30. Title: *Structure and computability of the
single-quadratic existential fragment over the integers*. Author: Hiroki Fukui.

## Main results

SE₂ is the class of relations on ℤᵏ definable by a single polynomial equation of total degree at most two, with
unrestricted integer unknowns.

- **Classification of the definable total functions** (Section 10). A function ℤⁿ → ℤᵐ with two or more outputs is
  SE₂-definable exactly when it has a common slope, f(a + Mt) = f(a) + Bt; a scalar function, exactly when it has a
  common slope, agrees with a rational polynomial of degree at most two, or is of a parity-affine two-branch kind.
  The forward directions use the ternary-coset input TCER, derived in ordinary mathematics from Kane and Kim
  (Lemma 10.8); the converses and the case without unknowns use no such input.
- **Finite fibres** (Sections 2–3): quadratic height, polynomially bounded cardinality; definable total functions grow
  at most quadratically, are computable, and are not closed under composition.
- **Injective dimension** (Section 4): SE₂-definable injections ℤⁿ → ℤᵐ satisfy n ≤ m, and every n ≤ m is realized
  by an injection.
- **Structured infinite fibres** (Section 8): with one constant for all parameter points, each scalar fibre is bounded
  or carries a certificate for an infinite output subset (polynomial progressions, Pell-unit orbits, moving-modulus
  step orbits).
- **Computability phase diagram** (Sections 6–7): SE₂ ⊊ REC ⊊ RE = PP₂ = SE₄ at every positive arity, with the
  Grunewald–Segal decision procedure (in a code-uniform form) and DPRM over ℕ as named hypotheses.

## Trust model in one paragraph

Every numbered result is proved in the paper. Sections 2–9, and Section 10 except Lemma 10.8, are also Lean 4
declarations whose axiom footprint is a subset of `{propext, Classical.choice, Quot.sound}`; TCER and the two
classical inputs are explicit hypotheses of the theorems that use them, never axioms. `release/TRUST_BOUNDARY_APAL.md`
gives the full boundary, `release/README_BUILD_APAL.md` the build and the gates, and `papers/blueprint/BLUEPRINT.md`
the per-statement map (trust label, Lean names, frozen file, the statements each proof cites; graph in
`papers/blueprint/dep_graph.dot`). Code and certificates are MIT,
prose is CC BY 4.0 (`LICENSING.md`). The continuous-integration workflow is shipped as
`release/github_workflows/ci.yml` and runs from the repository root with `.github/workflows/` as its location.

## Start here

    bash release/build_submission_from_package.sh
    python3 tools/shipping_artifact_gate.py .

The first command rebuilds `submission/APAL_MANUSCRIPT_v32.pdf` from this archive and nothing
else, and prints `BUILD_EXIT`, `NEWLY_BUILT_PDF_SHA256`, `GENERATED_PDF_EQ_SHIPPED`, `PDF_PAGES`
and the two manifest hashes. The second re-measures the archive (page count, hashes, manifests,
version strings) and compares them with `correspondence/SEAL_r53.txt`; any disagreement is named
and exits 1. Run them in this order, from the extracted root. They are the full package's commands; in the
public core (`APAL_PUBLIC_CORE_*.zip`) start with `README_PUBLIC_CORE.md` and
`python3 tools/public_core_release.py --verify .`, because `tools/shipping_artifact_gate.py` needs files that
the core leaves to the development history.

## Source of truth

- Mathematics: `lean/` (Lean 4, mathlib `d46bd45325c5cdf0ecf5cee0f5ff6d6e3586eb35`, toolchain
  `v4.31.0-rc1`). Every declaration selected for the statement-fidelity registry is frozen in
  `frozen_statements/` and compared with the production declaration in `lean/` by
  `tools/statement_diff.py`; `certificates/ROOT_FROZEN_RECONCILIATION_current.md` lists the exported
  roots outside that registry.
- Manuscript source status (`submission/CANONICAL_SOURCE`, mirrored in the seal and here):
  `SOURCE_STATUS=FINAL`, `BUILD_SOURCE=submission/native`, `QA_REFERENCE=manuscript/MANUSCRIPT_V32.md`,
  `MARKDOWN_IS_GENERATED=1`, `QA_INTERMEDIATE=generated Markdown`,
  `HAND_MAINTAINED_MARKDOWN_QA_DEPENDENCIES=0` (the generated Markdown is a QA intermediate, not a source). The PDF is built from the
  native TeX in `submission/native/` by `papers/apal_build/build.sh` to
  `submission/APAL_MANUSCRIPT_v32.{tex,pdf}`. `manuscript/MANUSCRIPT_V32.md` is a BUILD PRODUCT:
  `tools/tex_to_md.py` generates it from the native source at assembly and again in the build, and
  the build refuses to ship if the shipped copy differs (`MARKDOWN_GENERATED_GATE`). The prose
  scanners read that generated file; no hand-maintained Markdown exists any more (the last
  hand-maintained mirror is archived in the vault, not in this package). The shipped PDF was built
  inside this archive by the assembly; the seal records what it measured.
- Paper-claim registry (a model-assisted, author-approved paper-claim registry with tamper detection):
  `submission/native/PAPER_CLAIMS.tsv` names, for every numbered theorem, proposition, corollary and
  lemma that cites a Lean declaration in its heading, the Lean roots, domain, arities, degree bound, quantifier order,
  external hypotheses, a hash of the paper statement and the SHA-256 of each root's elaborated Lean
  type (`scripts/PaperClaimTypeReport.lean` → `certificates/PAPER_CLAIM_LEAN_TYPES.tsv`).
  `tools/paper_claims_check.py` fails the build when a registered statement changes, when a cited
  root is missing, substituted or changes type, when a numbered statement with a Lean name has no
  row, or when the Layer-2 review row (`PAPER_CLAIMS_REVIEW.tsv`) is missing or stale. The registry
  detects unreviewed changes to registered paper statements and Lean root types; the semantic
  correspondence between a mathematical statement and a Lean type is recorded one row per cited
  root in `PAPER_CLAIMS_REVIEW.tsv` as a model reading against the fully elaborated Lean type whose
  disposition was approved by the author; it is not established by text hashing alone and is not a
  machine certificate.
  `tools/paper_claims_controls.py` plants sixteen defects (statement edits, quantifier swap, domain,
  degree, deleted hypothesis, root substitution, forged type hash, wrong cross-reference, and in
  Lemma 10.3 a sign change and a deleted minus sign) into temp copies and requires all sixteen to be caught; `tools/crossref_semantic_check.py` checks that the
  cross-references listed in `CROSSREF_RULES.tsv` land on the statement they name.
- Figures: nothing in `release/TRUST_BOUNDARY_APAL.md`, `release/README_BUILD_APAL.md`,
  `release/RELEASE_CHECKLIST_APAL.md`, the version line of this file or the seal is typed. All are
  generated from `certificates/`, from `release/SEAL_INPUT.env` and from the build's own measurements
  (`tools/generate_trust.py`, `tools/generate_seal.py`), and `tools/shipping_artifact_gate.py` refuses
  a package in which any of them disagrees with the certificates or the seal.
- Public split: `PARTITION_RECORD.md` (package root) lists how this package partitions into the public-core
  and development-history archives generated from the same sealed tree (union equal to this package,
  intersection empty), with the SHA-256 of both archives.

## Build prerequisites

Lean `v4.31.0-rc1` with `elan`; mathlib at the pinned revision (in `lean/`: `lake update`, then `lake exe cache get`); Python 3.11
or later, standard library only; pandoc 3.9; TeX Live 2026 with XeTeX, fontspec, unicode-math,
geometry, lineno, longtable, booktabs, array, and the font packages `stix2-otf`, `dejavu` and `cleveref`
(`tlmgr install stix2-otf dejavu cleveref` (user mode), no administrator rights needed). Details and the measured
tool versions are in `release/README_BUILD_APAL.md`.

## Trust boundary

`release/TRUST_BOUNDARY_APAL.md` states the current trust facts only; the development history
(superseded certificates, corrected defects, round-by-round review) is `history/DEVELOPMENT_AUDIT_HISTORY.md`
and is not part of the proof claim. The trust document states what the kernel certifies, what it does not (statement
fidelity, prose fidelity, external inputs), and the external mathematical hypotheses the
conditional results depend on (DPRM; the Grunewald–Segal input, stated at published-abstract
level as an explicit hypothesis; and TCER, the ternary-coset input of Section 10, which Lemma 10.8 derives
from the published work of Kane and Kim in ordinary mathematics and which is not formalized). Axiom footprints: every root of the axiom report depends on a
subset of `[propext, Classical.choice, Quot.sound]`; no non-standard axiom, no `sorryAx`,
`native_decide`, `ofReduceBool` or `trustCompiler` (`certificates/FinalAxiomReport_current.log`).

## What is and is not kernel-verified

Kernel-verified: every theorem in `lean/`, including the main results of Sections 2–9, those of
Section 10 with TCER as an explicit hypothesis (Lemma 10.8, which derives TCER from the literature, is ordinary
mathematics), and the weighted counting obstruction of Appendix C. Not kernel-verified: that a formal statement models
the prose (mitigated by the frozen-statement diff, the CAS cross-checks recorded in
`certificates/`, and the cited-name census), the external hypotheses themselves, and the
typeset manuscript.

## The gates this archive runs on itself

`papers/apal_build/build.sh` refuses to touch a shipped artifact unless every one of these passes,
and each is exercised by a planted defect rather than asserted:

- `tools/environment_preflight.py` — the engine, driver, TeX Live release and font package are
  pinned in `papers/apal_build/BUILD_ENVIRONMENT.txt`; a build from a different environment stops
  before anything is written.
- `tools/native_statement_check.py` — every numbered statement of the native TeX equals the
  generated Markdown's (a regression check on the generator; the Markdown is derived from the TeX).
- `tools/paper_claims_check.py` — every registered statement agrees with the paper-claim registry
  (`submission/native/PAPER_CLAIMS.tsv`): Lean roots exist, their type fingerprints are the registered
  ones, quantifier order, degree bound, witness domain and external hypotheses are present in order,
  the statement hash is the registered one, every numbered statement with a Lean name is registered
  (FORMAL_CLAIMS_MISSING=0) and has a current Layer-2 (model-assisted, author-approved) review row (REVIEW_STALE=0).
- `tools/paper_claims_controls.py` — NEGATIVE_CONTROLS_CAUGHT=16/16 on planted defects, including a weaker corollary root re-promoted to EXACT beside a theorem's single EXACT root (ONE_ROOT_LABELS=3/3: Theorems 6.8, 7.1 and 8.5).
- `tools/manuscript_controls.py` — MANUSCRIPT_CONTROLS_CAUGHT=14/14 on planted text defects; `--scan` finds
  no split Pell subscript, no `\cref` inside math, no "definable" pulled into math.
- `tools/release_controls.py` — RELEASE_CONTROLS_CAUGHT=13/13 planted release defects on temp copies of the
  assembled root, including a development-history certificate re-listed in the public core.
- `tools/partition_check.py` — `PARTITION_RECORD.md` matches the tree; no public-core path matches
  `release/PUBLIC_CORE_EXCLUDE.txt` (PUBLIC_CORE_HISTORY_PATHS=0).
- `tools/generate_signoff_sheet.py` — `release/AUTHOR_SIGNOFF_SHEET.md` is generated from the registry and
  its Layer-2 review at every assembly; a filled author field is carried over only while the row's paper
  claim_hash AND full Lean type sha256 are both unchanged (`tools/signoff_controls.py`: SIGNOFF_CONTROLS=6/6 —
  paper-only change, type-only change, root change, missing hashes and an unsigned row are not carried; an
  unchanged signed row is).
- `tools/public_core_release.py` — the public core (APAL_PUBLIC_CORE archive) carries its own `CORE_SEAL.txt`,
  source and submission-input manifests, `README_PUBLIC_CORE.md` and `SHA256SUMS`, and `--verify` judges it in
  an empty directory reading nothing outside the archive (CORE_SHIPPING_EXIT=0, REQUIRED_HISTORY_FILES=0);
  the parent's partition record and seal stay in it byte for byte as provenance. The checksum gate is
  fail-closed (since the previous round): an absent, empty or unparsable `SHA256SUMS`, a duplicate, absolute or parent-traversing
  entry, a missing or wrong-digest file, or an unlisted archive file each fail it; `tools/public_core_controls.py`
  plants eight such defects in temporary archives at every assembly (CORE_CHECKSUM_CONTROLS=8/8). `--verify`
  also requires the clean-room record of the shipped Lean source: `certificates/CLEANROOM_REFERENCE.txt` names
  the original build log, which must be present byte for byte and name the source manifest that `lean/`
  reproduces; `tools/public_core_controls.py --cleanroom .` runs three planted controls on that check
  (CLEANROOM_REF_CONTROLS=3/3).
- `tools/crossref_semantic_check.py` — the semantic cross-references of `CROSSREF_RULES.tsv` resolve
  to the intended kind of statement.
- `tools/typeset_gate.py` — no Markdown residue, no duplicate label, no numbered statement without
  a proof directly after it (or a declared proof group), no unbalanced environment, no malformed display table, no overfull box over 5pt, no
  unresolved reference, no undefined citation.
- `tools/longtable_widths.py` — column widths are computed from the content of each table, not
  from the width of its header cell.
- `tools/submission_figures.py`, `tools/generate_trust.py` — every figure the checklist and the
  trust boundary state is recomputed and compared.

## Locators

`papers/apal_build/locators.txt` carries the DOI and repository fields the final build stamps
into the PDF. In this release they are set: DOI https://doi.org/10.5281/zenodo.23053094 (the Zenodo
software record) and repository https://github.com/hirokifukui/single-quadratic-definability; the shipped
PDF is the `final` build, and a `final` build refuses to run while either field is unset.
