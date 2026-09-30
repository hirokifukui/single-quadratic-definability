# Release checklist — APAL submission

Every figure in this file is inserted by `tools/generate_trust.py` from the shipped certificates when the package is assembled (2026-09-30); none is typed. Every line is checked against the artifact, not against a previous checklist.

## A. Mathematics

- [ ] Axiom report run on this tree; 421 roots (417 with a footprint, 4 axiom-free); no axiom outside the standard three; no forbidden token.
- [ ] Statement diff run on this tree; 1092/1092 theorems and 298/298 definitions over 59 frozen files; FAIL 0; negative and Unicode controls both caught.
- [ ] Binder ledger run on this tree; BINDER_ROOTS=452, BINDER_UNCONDITIONAL=406, CONTROLS=7/7, NONSTD_AXIOMS=0.
      Run it whenever the axiom report changes: it reads that file's root list but keeps its own imports.
- [ ] Type fingerprints regenerated (`scripts/PaperClaimTypeReport.lean`, `scripts/paper_claim_types.py`); TYPE_CONTROLS and TYPE_MUT_CONTROLS both 4/4.
- [ ] Paper-claim registry: FORMAL_CLAIMS_MISSING=0, REVIEW_UNREVIEWED=0, REVIEW_STALE=0, PAPER_CLAIMS_EXIT=0; NEGATIVE_CONTROLS_CAUGHT=16/16; ONE_ROOT_LABELS=3/3; SIGNOFF_CONTROLS=6/6.
- [ ] `tools/cited_name_census.py` exits 0 against the trust document's census paragraph.
- [ ] `tools/lettered_label_control.py` exits 0.
- [ ] Definition-body fidelity certificate exits 0.
- [ ] The final Lean source is tied to a successful cold clean-room build (`lean/fresh_build.sh` from an empty directory) by its source manifest; the actual number of environments is stated. A second environment is optional additional validation, not evidence already obtained.
- [ ] Every claim in the manuscript that names a Lean declaration names one that exists.
- [ ] No claim in the manuscript exceeds what the named declaration proves — `fidelity_destroyer` inventory dispositioned line by line.

## B. Build and typesetting

- [ ] `release/build_submission_from_package.sh` at the extracted root; EXTERNAL_PATHS=0, HOME_DEPENDENCIES=0, SESSION_PINNED_INPUTS=0, BUILD_EXIT=0, PACKAGE_BUILD_EXIT=0, GENERATED_PDF_EQ_SHIPPED=1.
- [ ] Layout: MISSING_GLYPHS, UNRESOLVED_REFS, UNDEFINED_CITATIONS, PLACEHOLDERS, OVERFULL_GT_5PT all 0.
- [ ] A build started in a foreign TeX environment stops at preflight and leaves the tree unchanged (TREE_UNCHANGED=1, PY_CACHE_CREATED=0); the shipping gate still passes on that tree afterwards.
- [ ] `tools/shipping_artifact_gate.py .` exits 0 on the assembled root and again on the re-extracted zip.

## C. Prose

- [ ] Title one line; abstract 250 words or fewer; keywords 7 or fewer; MSC codes present.
- [ ] Theorem numbering consistent between manuscript, appendices and statement map; every cross-reference is a `\cref`, no bare digits.
- [ ] The projection theorem has a complete human proof, not a delegation to the formalization.
- [ ] No internal round, gate or session vocabulary anywhere in the shipping documents.
- [ ] No root counts in the main narrative; they belong in the formalization section.
- [ ] No filenames outside the artifact-availability and formalization sections.

## D. Claim discipline

- [ ] The one-sorted sharpness claim that IS made (an injective SE₂-definable ℤⁿ → ℤᵐ exists iff
      n ≤ m) is proved in both directions and cited to `singleQuadratic_sharp_iff`.
- [ ] No document still states the n = 2 coding arity as open; ca(SE₂) = 1 is cited to
      `atomGraphZZ_capacity_eq_one`.
- [ ] Every `attained` names its semantics (one-sorted or mixed).
- [ ] Certificate forms described as produced by the proof, never as canonical, exclusive or complete.
- [ ] `Classical.choice` use disclosed in the trust boundary.
- [ ] Computability attributed correctly: total functions from totality plus a Diophantine graph; relations from Definition 1.5.
- [ ] The Grunewald–Segal input stated in its fixed-arity form, with the global form named as the stronger principle the development also carries.
- [ ] The paper-claim registry described as model-assisted and author-approved, never as reviewed by a human unless the author sign-off fields are filled (and then as author-reviewed, model-assisted; never as independent peer review).
- [ ] `BranchExhaustion` described as a documentation layer.

## E. Artifact hygiene

- [ ] `manuscript/` contains exactly one manuscript; no superseded manuscript ships.
- [ ] `tools/parallel_prose_control.py` passes on the assembled package with no directory exempted.
- [ ] Trust boundary, build README and this checklist generated from the same certificates at assembly; README version and date equal the seal's.
- [ ] Cover letter matches the current title and the current main theorem.
- [ ] `CITATION.cff` version and date equal the seal's (root and `release/` copies identical).
- [ ] No `.bak`, `.DS_Store`, `__pycache__` or `logs/` in the package.
- [ ] `SHA256SUMS` regenerated and verified; detached checksum file shipped alongside the zip.
- [ ] Public split generated from the sealed tree and recorded in `PARTITION_RECORD.md` (package root): union equals the full package, intersection empty, nothing missing, nothing duplicated.

## F. Journal requirements

- [ ] Elsevier AI declaration before the references, short form.
- [ ] Methods-level description of AI use, with the human author's responsibility stated.
- [ ] Data and artifact availability section with a DOI.
- [ ] Line numbers in the submission PDF.
- [ ] Complete references, every citation resolved.
