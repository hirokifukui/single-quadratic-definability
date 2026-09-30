# R52 source evidence

All excerpts below come from the received R52 ZIP. Line numbers are original source-file lines. This is a review transcript, not a new kernel certificate.

## `release/README_BUILD_APAL.md` — lines 41–79

```text
41: names every declared face and every missing one, and `build.sh` runs it before pandoc.
42: 
43: Every command block below starts at the package root. Blocks that need the Lean project enter `lean/` inside a
44: subshell, `( … )`, so the working directory is back at the package root when the block ends.
45: 
46: ## Clean-room build
47: 
48:     (
49:       cd lean
50:       lake update            # fetches mathlib at the pinned revision
51:       lake exe cache get     # optional; skips compiling mathlib from source
52:       lake build             # default target: MPUP
53:       lake build DiophCompression
54:       lake build ResearchUpgrade
55:     )
56: 
57: `lake build` returning 0 is necessary and not sufficient: a file containing `sorry` also builds. The
58: gate is the axiom report. `lean/fresh_build.sh` runs the whole sequence below from an empty directory
59: and is the script that produced the clean-room record in `certificates/`. The current certificates record one
60: cold clean-room build, on agora, of the source identified by the shipped manifest. Additional independent-environment
61: builds may be recorded separately; they are not claimed for this candidate.
62: 
63: ## The gates, in the order they should be run
64: 
65: **1. Axiom report.**
66: 
67:     (cd lean && lake env lean scripts/FinalAxiomReport.lean)
68: 
69: Expected: 421 roots, of which 417 report a footprint and 4 report none; every footprint is a subset
70: of `{propext, Classical.choice, Quot.sound}` (398 all three, 14 `propext` only, 5 `propext, Quot.sound`); the tokens `sorryAx`, `native_decide`, `ofReduceBool`,
71: `trustCompiler` do not appear; no errors. The shipped record is `certificates/FinalAxiomReport_current.log`.
72: 
73: **2. Statement fidelity.**
74: 
75:     STMT_BASE=frozen_statements LEAN_BASE=lean python3 lean/scripts/statement_diff.py --quiet
76: 
77: Expected: `THEOREMS=1092/1092`, `DEFINITIONS=298/298`, `FAIL=0`,
78: `FROZEN_FILES=59`, `SDIFF_EXIT=0`. `DUPLICATE_NAMES` counts ambiguous short-name look-ups, not
79: duplicate fully qualified Lean declarations; it is not required to be zero and is read together with the resolution by
```

## `lean/lakefile.lean` — lines 1–20

```text
1: import Lake
2: open Lake DSL
3: 
4: -- Release lakefile (external checkout). Pins mathlib to the commit used for the kernel logs.
5: package «mpup-lean» where
6:   leanOptions := #[⟨`autoImplicit, false⟩]
7: 
8: require mathlib from git
9:   "https://github.com/leanprover-community/mathlib4.git" @ "d46bd45325c5cdf0ecf5cee0f5ff6d6e3586eb35"
10: 
11: @[default_target]
12: lean_lib «MPUP» where
13: 
14: lean_lib «DiophCompression» where
15: 
16: -- r40: the s48 research results. Added as a THIRD library rather than merged into
17: -- DiophCompression, so that the r37-frozen baseline stays byte-identical and the dependency
18: -- direction (ResearchUpgrade -> DiophCompression, never the reverse) is visible in the shipped
19: -- layout. No file under MPUP/ or DiophCompression/ changed in this round.
20: lean_lib «ResearchUpgrade» where
```

## `lean/fresh_build.sh` — lines 8–28

```text
8: cd "$(dirname "$0")"
9: export PATH="$HOME/.elan/bin:$PATH"; ulimit -n 8192
10: mkdir -p logs
11: sha256_file() { if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'; else shasum -a 256 "$1" | awk '{print $1}'; fi; }
12: manifest() { # canonical source manifest: sorted (LC_ALL=C) list of "sha256  path" over all .lean/.py/.sh plus build metadata
13:   { find MPUP DiophCompression ResearchUpgrade scripts -type f \( -name '*.lean' -o -name '*.py' -o -name '*.sh' \) -print0; printf '%s\0' MPUP.lean DiophCompression.lean ResearchUpgrade.lean lakefile.lean lean-toolchain; } \
14:     | LC_ALL=C sort -z | while IFS= read -r -d '' f; do printf '%s  %s\n' "$(sha256_file "$f")" "$f"; done; }
15: echo "=== FRESH-CLONE RELEASE BUILD (release lakefile, empty dir, set -euo pipefail) ==="; date; hostname; pwd
16: echo "--- lean-toolchain ---"; cat lean-toolchain
17: echo "--- lakefile.lean ---"; cat lakefile.lean
18: manifest > logs/source_manifest_start.sha256
19: echo "SOURCE_MANIFEST_FILES=$(wc -l < logs/source_manifest_start.sha256 | tr -d ' ')"
20: echo "SRC_MANIFEST_SHA256=$(sha256_file logs/source_manifest_start.sha256)"
21: echo "=== lake update (fetch mathlib at pin) ==="; lake update > logs/lake_update.log 2>&1; echo "UPDATE_EXIT=0"; tail -3 logs/lake_update.log
22: echo "=== manifest mathlib rev ==="; python3 -c "import json;m=json.load(open('lake-manifest.json'));print('MATHLIB_REV=' + str([(p.get('rev'),p.get('inputRev')) for p in m['packages'] if p['name']=='mathlib']))"
23: echo "=== lake exe cache get ==="; lake exe cache get > logs/cache_get.log 2>&1; echo "CACHE_EXIT=0"; tail -3 logs/cache_get.log
24: echo "=== plain lake build (default target) ==="; lake build > logs/lake_build_plain.log 2>&1; echo "PLAIN_BUILD_EXIT=0"; tail -3 logs/lake_build_plain.log
25: echo "=== lake build DiophCompression ==="; lake build DiophCompression > logs/lake_build_dc.log 2>&1; echo "DC_BUILD_EXIT=0"; tail -3 logs/lake_build_dc.log
26: echo "=== lake build ResearchUpgrade (r40, third library) ==="; lake build ResearchUpgrade > logs/lake_build_ru.log 2>&1; echo "RU_BUILD_EXIT=0"; tail -3 logs/lake_build_ru.log
27: echo "=== lake build DiophCompression.QuadraticWitnessInertiaCore (all-r root) ==="; lake build DiophCompression.QuadraticWitnessInertiaCore > logs/minimal_all_r_build.log 2>&1; echo "CORE_BUILD_EXIT=0"; tail -3 logs/minimal_all_r_build.log
28: echo "=== rebuild.sh ==="; ./scripts/rebuild.sh > logs/rebuild.log 2>&1; echo "REBUILD_SH_EXIT=0"; grep -E "REBUILD_EXIT" logs/rebuild.log
```

## `certificates/CLEANROOM_REFERENCE.txt` — lines 1–12

```text
1: # CLEANROOM_REFERENCE - the clean-room record of the Lean source shipped in this package (written by the assembler).
2: # The log is kept byte for byte under its original name.  A round that does not change the Lean source reuses the
3: # earlier run's log and does not re-date it.  Checked by tools/public_core_release.py --verify (evidence consistency
4: # only: the check does not run Lean).
5: original_name=certificates/fresh_build_r49.log
6: build_round=r49
7: shipped_in_round=r52
8: environment=agora
9: new_build_performed_for_round=no
10: log_sha256=9ed741407611c68f187b475d3cbc48b0f6b62a2a06a8ef83376f3cd195307ff9
11: source_manifest=certificates/source_manifest_r52.sha256
12: source_manifest_sha256=db56ee4d1708c2e348f9412c282a093b22b5302b97b992fae3b03ad6ec1c2e7b
```

## `correspondence/LETTER_GATE33.md` — lines 12–47

```text
12: 
13: ## 0. What changed
14: 
15: * **No mathematics, no Lean.**  r52 ships the byte-identical Lean source of r49–r51; the manuscript's mathematical text is
16:   that of r50 (the changes of wording and placement are listed below).  The lakefile, `lean/fresh_build.sh`, the frozen statements, the type, definition-body and axiom certificates and the r49
17:   clean-room log are unchanged.
18: * **Build README (your P1)**: your patch, applied to `release/README_BUILD_APAL.template.md` unchanged; the README is
19:   regenerated from the template by the existing generator.  The manual clean-room block now runs `lake build` (default
20:   target MPUP), `lake build DiophCompression`, `lake build ResearchUpgrade` — the three builds `lean/fresh_build.sh` runs
21:   and the r49 log records.  The existing line `lake build DiophCompression` stays, so the gate that pins it is unchanged.
22: * **One addition from our side** to your diagnosis, closed by the same patch: the old block also left unbuilt two modules
23:   that the axiom report (gate 1) imports, `MPUP.Quantitative` and `MPUP.WeightedBound`; they lie outside the import closure
24:   of `DiophCompression` and are built by the default target.  Under the pinned toolchain v4.31.0-rc1, `lake help lean`
25:   reads "Build the imports of the given file and then runs `lean` on it", and `lake help env` only sets the environment —
26:   the distinction you took from the current reference.
27: * **CI workflow (found by us, E-33-2)**: the shipped `release/github_workflows/ci.yml` built only the default target and
28:   `DiophCompression`, audited only `DiophCompression`, and piped the audit into `tee` without `pipefail`.  It now builds the
29:   three libraries, runs `scripts/audit_dc.sh` and `scripts/audit_ru.sh`, and runs every step under `shell: bash`
30:   (`-eo pipefail`).  It has not yet run on GitHub.
31: * **The author's decisions, not answers to your review**: the title page, the cover letter and `CITATION.cff` now give the
32:   author's affiliation (Research Institute of Criminal Psychiatry / Sex Offender Medical Center, Tokyo; Department of
33:   Neuropsychiatry, Kyoto University) and e-mail; code and certificates are now MIT-licensed (prose stays CC BY 4.0), as in
34:   the author's earlier published package.  Also the author's decisions, following the Guide for Authors: the funding line uses
35:   the Guide's sentence and the title page carries a declaration of competing interest; the AI declaration now stands
36:   immediately before the references.  One abstract sentence and one introduction sentence now name the two classical inputs
37:   as the published results they are (Grunewald–Segal; DPRM, citing Davis–Putnam–Robinson and Matiyasevich); their status as
38:   named hypotheses is unchanged, and no statement or proof changes.
39: * **For the repository**: the package README opens with the main results and the trust model; a generated Blueprint
40:   (`papers/blueprint/BLUEPRINT.md`, `dep_graph.dot`) gives every numbered statement its trust label, Lean names, frozen file
41:   and the statements its proof cites; the CI workflow runs from the repository root.
42: * `certificates/CLEANROOM_REFERENCE.txt` now reads `shipped_in_round=r52`; the log it names is the same r49 log, byte for byte.
43: 
44: ## 1. Your findings
45: 
46: | your item | ours | erratum | where |
47: |---|---|---|---|
```

## `correspondence/LETTER_GATE33.md` — lines 110–137

```text
110: 
111: ```
112: FRESH_EXIT=0   SOURCE_MANIFEST_FILES=323   SRC_MANIFEST_SHA256=db56ee4d1708c2e348f9412c282a093b22b5302b97b992fae3b03ad6ec1c2e7b
113: RU_BUILD_EXIT=0  AUDIT_RU_EXIT=0  AUDIT_EXIT=0  RU_FORBIDDEN=0  RU_CAPS_MISSING=0
114: RU_AXIOM_LINES=1577     RU_RECORDS=1542     RU_NONSTD3_LINES=0
115: THEOREMS=1092/1092  DEFINITIONS=298/298  FROZEN_FILES=59
116: DEFFID_CONSTANTS=1154  DEFFID_MISMATCH=0  DEFFID_MISSING=0  DEFFID_EXTRA=0
117: FINAL_AXIOM_LINES=421  FINAL_NONSTD3_LINES=0  TYPE_ROWS=452  SOURCE_FREEZE=OK
118: logs compared: 1
119: ```
120: 
121: ## 5. State of the candidate (written before the author's seal)
122: 
123: | item | state |
124: |---|---|
125: | mathematics, Lean source, manuscript | fixed (Lean unchanged since r49; manuscript unchanged since r50) |
126: | release evidence and documents | technically complete for this candidate once r52 is sealed; the core gate runs on the real core at the seal |
127: | author sign-off sheet | 74 rows; `AUTHOR_REVIEWER`, `AUTHOR_DISPOSITION`, `AUTHOR_SIGNOFF_DATE` blank in every row — the author's to fill; not filled by us or by you |
128: | locators | DOI and repository `UNSET`; the e-mail is set and printed; the package is built in `draft` mode, and the `final` build is untested on real locators |
129: | publication | nothing published, submitted or e-mailed; no DOI reserved |
130: 
131: The Gate-32 checklist shipped with r51 recorded task 7 as PARTIAL because the core is cut only at the seal.  At the r51 seal the
132: assembler ran `--verify` and `--cleanroom` on the real core (`CLEANROOM_REFERENCE=ok`, `CLEANROOM_REF_CONTROLS=3/3`,
133: `CORE_SHIPPING_EXIT=0`), and your R51 review re-ran the checks on the core you received.
134: 
135: ## 6. Question for r52
136: 
137: Apart from the author's items (the sign-off sheet, the DOI and repository locators and the `final` build), is any P0 or P1 left?
```

## `release/github_workflows/ci.yml` — lines 1–44

```text
1: name: kernel-audit
2: on:
3:   push:
4:     branches: [main]
5:   pull_request:
6: jobs:
7:   build-and-audit:
8:     runs-on: ubuntu-latest
9:     timeout-minutes: 240
10:     defaults:
11:       run:
12:         # explicit bash = bash -eo pipefail: a failing audit fails its step even through `| tee`
13:         shell: bash
14:         # the repository root is the package root; the Lean project is lean/
15:         working-directory: lean
16:     steps:
17:       - uses: actions/checkout@v4
18:       - name: Install elan
19:         run: |
20:           curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
21:             | sh -s -- -y --default-toolchain "$(cat lean-toolchain)"
22:           echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
23:       - name: mathlib cache
24:         run: |
25:           ~/.elan/bin/lake update
26:           ~/.elan/bin/lake exe cache get
27:       - name: Build (the three libraries lean/fresh_build.sh builds)
28:         run: |
29:           ~/.elan/bin/lake build
30:           ~/.elan/bin/lake build DiophCompression
31:           ~/.elan/bin/lake build ResearchUpgrade
32:           ~/.elan/bin/lake build DiophCompression.QuadraticWitnessInertiaCore
33:       - name: Kernel audit, DiophCompression (dynamic file-enumeration gate + planted controls)
34:         run: bash scripts/audit_dc.sh | tee audit_ci.log
35:       - name: Kernel audit, ResearchUpgrade (per-file kernel audit)
36:         run: bash scripts/audit_ru.sh | tee audit_ru_ci.log
37:       - name: Upload audit logs
38:         if: always()
39:         uses: actions/upload-artifact@v4
40:         with:
41:           name: audit-logs
42:           path: |
43:             lean/audit_ci.log
44:             lean/audit_ru_ci.log
```

## `papers/blueprint/BLUEPRINT.md` — lines 1–25

```text
1: # Blueprint
2: 
3: Generated by `tools/gen_blueprint.py` from `submission/native/sections/` (through `tools/proof_companion.py`),
4: `submission/native/PAPER_CLAIMS.tsv` and `release/STATEMENT_MAP_FULL.md`; not maintained by hand. Every numbered
5: statement of the paper is one node. The statement and its proof are in the paper and, entry by entry, in
6: `release/PROOF_COMPANION.md`; this file adds what a reader checking the paper needs beside them: the trust label,
7: the Lean names, the frozen statement file, and the statements each proof cites. `dep_graph.dot` draws the
8: citation edges (render with `dot -Tpdf dep_graph.dot -o dep_graph.pdf`).
9: 
10: ## Trust labels
11: 
12: | label | meaning | nodes |
13: |---|---|---|
14: | F | a Lean declaration registered for the statement (`PAPER_CLAIMS.tsv`); standard axioms only; no external hypothesis | 34 |
15: | F+H | registered Lean declaration whose statement carries named external hypotheses (listed in the node) — hypotheses, never axioms | 11 |
16: | S | Lean name(s) listed in the statement map, not a registry row | 0 |
17: | M | proved in the paper; no Lean declaration is listed | 7 |
18: | D | definition | 9 |
19: | R | remark or examples | 8 |
20: 
21: Nodes: 69. The axiom footprint of every Lean root is recorded in `certificates/FinalAxiomReport_current.log`;
22: the registry's type fingerprints in `certificates/PaperClaimTypeReport_current.log`.
23: 
24: ## Nodes
25: 
```

## `papers/blueprint/BLUEPRINT.md` — lines 69–96

```text
69: | Theorem 9.2 | F | `quadraticProjectionDichotomyZ_all` | — | not in frozen_statements | — |
70: | Theorem 9.3 | F | `quadraticProjectionDichotomyZ_all_data`, `quadraticProjectionDichotomyZ_structured` | — | SummitClosure_STATEMENTS.lean, TopDichotomyData_STATEMENTS.lean | Definition 8.2, Lemma V.2, Lemma V.3 |
71: | Proposition 10.1 | F | `generalWeakNF_iff_definiteWeakNF` | — | ResearchUpgrade_STATEMENTS.lean | — |
72: | Proposition 10.2 | F | `lowRankSemidefiniteWeakNF_holds` | — | ResearchUpgrade_STATEMENTS.lean | Lemma 10.5, Proposition 10.1 |
73: | Lemma 10.3 | F | `direction_discriminant_square` | — | ResearchUpgrade_STATEMENTS.lean | — |
74: | Lemma 10.4 | F | `square_values_rigidity` | — | ResearchUpgrade_STATEMENTS.lean | — |
75: | Lemma 10.5 | F | `norm_section` | — | ResearchUpgrade_STATEMENTS.lean | Lemma 10.3, Lemma 10.4 |
76: | Proposition 10.6 | F | `generalFullNF_iff_semidefiniteFullNF` | — | ResearchUpgrade_STATEMENTS.lean | Theorem 4.2 |
77: | Proposition 10.7 | F+H | `sealedFullNF_of_TCER` | TernaryCosetEventualRepresentation | ResearchUpgrade_STATEMENTS.lean | Proposition 10.6 |
78: | Lemma 10.8 | M | — | — | — | — |
79: | Proposition 10.9 | F+H | `singleQuadratic_iff_commonSlope_of_TCER` | TernaryCosetEventualRepresentation | ResearchUpgrade_STATEMENTS.lean | Proposition 10.6 |
80: | Proposition 10.10 | F+H | `sqPadFn_not_singleQuadratic_of_TCER` | TernaryCosetEventualRepresentation | ResearchUpgrade_STATEMENTS.lean | Proposition 10.9 |
81: | Proposition 10.11 | F | `not_commonSlope_of_fullVectorCosetNF` | — | ResearchUpgrade_STATEMENTS.lean | — |
82: | Proposition 10.12 | F | `commonSlope_injective_iff` | — | ResearchUpgrade_STATEMENTS.lean | — |
83: | Lemma 10.13 | F | `addSubgroup_two_coset_cover` | — | ResearchUpgrade_STATEMENTS.lean | — |
84: | Proposition 10.14 | F+H | `scalar_singleQuadratic_iff_of_TCER` | TernaryCosetEventualRepresentation | ResearchUpgrade_STATEMENTS.lean | Lemma 10.13, Proposition 10.9 |
85: | Proposition 10.15 | F+H | `singleQuadratic_padZero_iff_of_TCER` | TernaryCosetEventualRepresentation | ResearchUpgrade_STATEMENTS.lean | Proposition 10.9 |
86: | Proposition 10.16 | F | `zeroWitness_iff` | — | ResearchUpgrade_STATEMENTS.lean | Proposition 10.14 |
87: | Proposition 10.17 | F+H | `singleQuadratic_iff_uniqueWitness_of_TCER` | TernaryCosetEventualRepresentation | ResearchUpgrade_STATEMENTS.lean | Proposition 10.9, Proposition 10.14, Proposition 10.16 |
88: | Proposition 10.18 | F | `floorThird_min_witnesses` | — | ResearchUpgrade_STATEMENTS.lean | Proposition 10.14, Proposition 10.16 |
89: | Theorem C.1 | F | `coder_counting_bound_weighted`, `multiUniversalN_bound_weighted`, `multiUniversalZ_bound_weighted`, `wtCount_closed_form` | — | WeightedBound_STATEMENTS.lean | — |
90: | Remark C.2 | R | — | — | — | — |
91: | Lemma V.1 | M | — | — | — | — |
92: | Lemma V.2 | M | — | — | — | — |
93: | Lemma V.3 | M | — | — | — | — |
94: | Theorem V.4 | M | — | — | — | — |
95: | Corollary V.5 | M | — | — | — | Theorem V.4 |
96: | Lemma V.6 | M | — | — | — | — |
```

## `submission/native/sections/11_s12_formalization.tex` — lines 1–18

```text
1: \section{Formalization}\label{sec:12}
2: \textbf{What the kernel certifies.} Apart from the literature-to-$\mathrm{TCER}$ adapter in \cref{lemma:10.8}, every result stated above is a Lean 4 declaration, with the external inputs retained as the explicit hypotheses specified below; the declarations are in the accompanying artifact, archived at ⟨DOI⟩. The script \texttt{scripts/FinalAxiomReport.\allowbreak{}lean} prints the axiom footprint of every exported root of the development, and every footprint is contained in the standard set \texttt{[propext, Classical.\allowbreak{}choice, Quot.\allowbreak{}sound]}; contained, not equal, since the roots do not all use all three. The forbidden tokens \texttt{sorryAx}, \texttt{native\_\allowbreak{}decide}, \texttt{ofReduceBool}, \texttt{trustCompiler} do not occur anywhere in the development. The toolchain is \texttt{leanprover/lean4:v4.\allowbreak{}31.\allowbreak{}0-rc1} with the mathlib revision pinned in the lakefile; the Lean tree distributed with the paper is copied from a clean-room build whose source manifest is required to match hash for hash, and the artifact ships the build script and the manifests. The counts — roots, their division among subsets of the standard set, and the external-input-free roots — are in \texttt{release/TRUST\_\allowbreak{}BOUNDARY\_\allowbreak{}APAL.\allowbreak{}md} of the artifact, where a tool recomputes them from the certificates and fails the build if the document and the development disagree.
3: 
4: \textbf{External inputs are hypotheses.} The two classical inputs (\cref{definition:1.5,definition:1.6}) and the analytic input $\mathrm{TCER}$ of \cref{sec:10} are \texttt{def … : Prop}, and a result uses one only by taking it as an argument. $\mathrm{TCER}$ is not formalized: \cref{lemma:10.8} derives it from \cite{KK26} in ordinary mathematics. \texttt{\#print axioms} reports transitive \emph{axiom} dependencies and is blind to hypotheses, so a conditional and an unconditional theorem can print the same footprint; which results are unconditional is therefore read from a second report, \texttt{scripts/HypothesisBinderLedger.\allowbreak{}lean}, which inspects the hypothesis binders of each root's type and reports the roots that carry no external-input binder, explicit, implicit, instance or wrapped, with seven planted-hypothesis controls. A few load-bearing declarations — notably the conversion of a structured family into a certificate in \cref{sec:8} — are definitions producing data rather than theorems and so are not roots of the report; their footprints are inherited by every theorem that uses them, and those theorems are reported. The layers are:
5: 
6: \begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.279\linewidth}>{\raggedright\arraybackslash}p{0.388\linewidth}>{\raggedright\arraybackslash}p{0.232\linewidth}@{}}
7: \toprule
8: layer & results & input used \\
9: \midrule\endhead
10: unconditional & \cref{theorem:2.1,theorem:2.2,theorem:3.2,theorem:3.3,theorem:3.4,theorem:4.1,theorem:5.1,theorem:6.1,theorem:6.2}, \crefrange{theorem:8.3}{theorem:8.5}, \cref{theorem:9.2,theorem:9.3} & none beyond mathlib \\
11: conditional on \cref{definition:1.5} & SE₂ ⊆ REC and its strictness at positive arity (\cref{theorem:6.3} and \cref{corollary:6.6}) & code-uniform quadratic solvability \\
12: conditional on \cref{definition:1.6} & RE = PP₂ = SE₄ and the function phase diagram of \cref{sec:7} & DPRM over ℕ \\
13: conditional on \cref{definition:1.5} and \cref{definition:1.6} & the complete relation phase diagram (\cref{theorem:6.8}) & quadratic solvability and DPRM over ℕ \\
14: unconditional, \cref{sec:10} & \cref{proposition:10.1,proposition:10.2,lemma:10.3,lemma:10.4,lemma:10.5,proposition:10.6,proposition:10.11,proposition:10.12,lemma:10.13,proposition:10.16,proposition:10.18}; the reverse directions of \cref{proposition:10.9,proposition:10.14,proposition:10.17} & none beyond mathlib \\
15: conditional on $\mathrm{TCER}$ & \cref{proposition:10.7,proposition:10.10,proposition:10.15}; the forward directions of \cref{proposition:10.9,proposition:10.14,proposition:10.17} & TCER (\cref{lemma:10.8}) \\
16: \bottomrule
17: \end{longtable}
18: $\mathrm{Fun}(SE_{2}) ⊆ \mathrm{TotComp}$ belongs to the first row and not the second: it follows from totality together with a Diophantine graph, and uses neither classical input nor the height bound.
```

## `release/TRUST_BOUNDARY_APAL.template.md` — lines 9–29

```text
9: ## 1. What the kernel certifies
10: 
11: The Lean development is built against mathlib pinned at `d46bd45325c5cdf0ecf5cee0f5ff6d6e3586eb35`,
12: toolchain `v4.31.0-rc1`. `scripts/FinalAxiomReport.lean` prints the axiom footprint of every exported
13: root:
14: 
15: | quantity | value |
16: |---|---|
17: | axiom_roots (roots reported) | {{axiom_roots}} |
18: | axiom_roots_with_axioms (roots depending on some axiom) | {{axiom_roots_with_axioms}} |
19: | axiom_roots_axiom_free (roots depending on no axiom) | {{axiom_roots_axiom_free}} |
20: | footprint_all_three (`[propext, Classical.choice, Quot.sound]`) | {{footprint_all_three}} |
21: | footprint_propext_only (`[propext]`) | {{footprint_propext_only}} |
22: | footprint_propext_quot (`[propext, Quot.sound]`) | {{footprint_propext_quot}} |
23: | axioms outside the standard three | 0 |
24: | `sorryAx`, `native_decide`, `ofReduceBool`, `trustCompiler` | 0 |
25: | errors | 0 |
26: 
27: A footprint of the three standard axioms is what an ordinary classical proof looks like in Lean; it
28: is not a disclosure of anything unusual. What matters is the last two rows: there is no custom axiom
29: and no compiler-trusting tactic anywhere in the development.
```

## `submission/native/frontmatter.tex` — lines 1–26

```text
1: % frontmatter.tex -- title, author, abstract, keywords, declarations (N01)
2: \title{Structure and computability of the single-quadratic existential fragment over the integers}
3: \author{Hiroki Fukui\\ \small Research Institute of Criminal Psychiatry / Sex Offender Medical Center, Tokyo, Japan\\ \small Department of Neuropsychiatry, Kyoto University, Kyoto, Japan\\ \small ORCID 0009-0008-7122-522X\\ \small ⟨EMAIL⟩}
4: \date{}
5: \maketitle
6: \linenumbers
7: \begin{abstract}
8: Let SE₂ be the class of relations on ℤᵏ definable by a \emph{single} polynomial equation of total degree at most two, with unrestricted integer unknowns.
9: 
10: Under a published input on ternary lattice cosets, f : ℤⁿ → ℤᵐ with two or more outputs is SE₂-definable exactly when f(a + Mt) = f(a) + Bt for a modulus M and an integer matrix B; a scalar function, exactly when it has this form, agrees with a rational polynomial of degree at most two, or is half the even one of two integer affine forms of opposite parity. The converses and the case without unknowns need no such input.
11: 
12: Finite fibres lie in a box of quadratic height and have polynomially bounded cardinality, with one constant depending on the equation alone; definable total functions therefore grow at most quadratically; they are computable; they are not closed under composition. SE₂-definable injections ℤⁿ → ℤᵐ satisfy n ≤ m, and this is sharp.
13: 
14: Unconditionally, with one constant C for all parameter points, each scalar fibre is bounded by C(1+‖a‖∞)² or carries a certificate pinning an infinite output subset of one of three forms: polynomial progressions, Pell-unit orbits, moving-modulus step orbits.
15: 
16: Two published results enter as named hypotheses: Grunewald–Segal decidability of quadratic solvability (code-uniform) and DPRM over ℕ. They give SE₂ ⊊ REC ⊊ RE = PP₂ = SE₄ at every positive arity. Sections 2–9 are formalized in Lean 4, as is Section 10 except Lemma 10.8, with the ternary input as an explicit hypothesis.
17: 
18: \end{abstract}
19: \noindent\textbf{Keywords.} Diophantine definability; existential fragments; quadratic equations; finite fibres; definable functions; computability.
20: 
21: \noindent\textbf{MSC 2020.} Primary 03D25; Secondary 11D09, 11U05, 03B35, 11Y50, 68V15.
22: 
23: \noindent\textbf{Funding.} This research did not receive any specific grant from funding agencies in the public, commercial, or not-for-profit sectors.
24: 
25: \noindent\textbf{Declaration of competing interest.} The author declares no known competing financial interests or personal relationships that could have appeared to influence the work reported in this paper.
26: 
```

## `submission/native/sections/20b_declaration_on_ai_assisted_tools.tex` — lines 1–3

```text
1: \section*{Declaration on AI-assisted tools}
2: During the preparation of this work the author used large language models (Claude, ChatGPT and Claude Code) for drafting and editing prose, for tactic-level proof search in Lean under statements fixed by the author, and as an adversarial reader of statements and drafts. After using these tools the author reviewed and edited the content as needed; no model output was treated as a source of mathematical truth. Correctness is supported by the complete human-readable proofs and by independent checking of the formal declarations by the Lean kernel. The author reviewed the mathematical statements, proofs, citations and final manuscript, and assumes full responsibility for the content of the publication.
3: 
```

## `papers/apal_build/locators.txt` — lines 1–15

```text
1: # Artifact locators substituted into the manuscript at build time.
2: # UNSET is legal in a DRAFT build and fatal in a FINAL build. Do not invent an identifier here:
3: # a fabricated DOI in a PDF is worse than a visible statement that none has been assigned yet.
4: DOI=UNSET
5: REPO=UNSET
6: # Fixed build epoch (s35, Gate-9 build-portability homework 11 and 12).  Two rebuilds of identical
7: # bytes used to produce different PDFs, because xelatex derives the document /ID from the clock.
8: # Measured: with SOURCE_DATE_EPOCH and FORCE_SOURCE_DATE set, two builds are byte-identical; without
9: # them the /ID differs and nothing else does.  The value is the r33 build date 2026-09-05T00:00:00Z (s37: the r30 value 1757001600
10: # resolved to 2025-09-04, a year before the release -- Gate-11 N18).  The epoch is
11: # a property of the round rather than of the machine that happens to build it.
12: SOURCE_DATE_EPOCH=1788566400
13: 
14: # author e-mail printed under the title; UNSET is legal in DRAFT, fatal in FINAL (s36, N01)
15: EMAIL=fukui@somec.org
```

## `release/SEAL_WHAT_IS_OPEN.md` — lines 1–18

```text
1:   Apart from round identifiers and the round's correspondence and check logs, this round changes: the build README,
2:   whose manual clean-room block now builds the three Lean libraries that `lean/fresh_build.sh` builds (the default
3:   target MPUP, then DiophCompression and ResearchUpgrade); the shipped continuous-integration workflow, which now also
4:   builds and audits ResearchUpgrade and runs from the repository root; the package README, which now opens with the
5:   main results and the trust model; a generated Blueprint (papers/blueprint/); the licence of code and certificates,
6:   now MIT (prose remains CC BY 4.0); and, in the manuscript, the title page (the author's affiliation and e-mail, the
7:   funding sentence and a declaration of competing interest in the journal's wording), one abstract sentence and one
8:   introduction sentence that name the two classical inputs as the published results they are, and the place of the
9:   declaration on AI-assisted tools, now immediately before the references. No statement or proof of the manuscript
10:   changes, and the Lean source is unchanged from r49. Section 10 proves the normal-form and classification results;
11:   the literature-to-TCER adapter is Lemma 10.8, and related work is discussed in Section 11. TCER is an explicit
12:   hypothesis of the Lean theorems, not an axiom, and the standard-axiom footprint of a conditional theorem does not
13:   certify it. The clean-room record is the r49 run on agora, reused for the identical source (same
14:   SRC_MANIFEST_SHA256); no new clean-room execution is claimed for this round, and one environment is recorded.
15:   Open: every author field of the regenerated sign-off sheet is blank; the final locators -- preprint and software
16:   DOIs and the repository tag -- are unset, so this package is built in `draft` mode and the `final` build remains
17:   untested on real locators. The ruling is unchanged and repeated: no Zenodo draft, DOI reservation or GitHub
18:   release until every content item is fixed and the sheet is signed.
```

## Missing from FinalAxiomReport, present in PaperClaimTypeReport

```json
{
  "registry_rows": 74,
  "unique_registered_roots": 72,
  "in_FinalAxiomReport": 50,
  "missing_in_FinalAxiomReport": [
    "DiophCompression.ResearchUpgrade.NormLift.direction_discriminant_square",
    "DiophCompression.ResearchUpgrade.NormLift.norm_section",
    "DiophCompression.ResearchUpgrade.NormLift.square_values_rigidity",
    "DiophCompression.ResearchUpgrade.QuadraticGraphData.summit_of_defines",
    "DiophCompression.ResearchUpgrade.addSubgroup_two_coset_cover",
    "DiophCompression.ResearchUpgrade.atomGraphZZ_le_one",
    "DiophCompression.ResearchUpgrade.commonSlope_injective_iff",
    "DiophCompression.ResearchUpgrade.floorThird_min_witnesses",
    "DiophCompression.ResearchUpgrade.generalFullNF_iff_semidefiniteFullNF",
    "DiophCompression.ResearchUpgrade.generalWeakNF_iff_definiteWeakNF",
    "DiophCompression.ResearchUpgrade.lowRankSemidefiniteWeakNF_holds",
    "DiophCompression.ResearchUpgrade.not_commonSlope_of_fullVectorCosetNF",
    "DiophCompression.ResearchUpgrade.scalar_singleQuadratic_iff_of_TCER",
    "DiophCompression.ResearchUpgrade.sealedFullNF_of_TCER",
    "DiophCompression.ResearchUpgrade.singleQuadratic_iff_commonSlope_of_TCER",
    "DiophCompression.ResearchUpgrade.singleQuadratic_iff_uniqueWitness_of_TCER",
    "DiophCompression.ResearchUpgrade.singleQuadratic_injective_dimension_sharp",
    "DiophCompression.ResearchUpgrade.singleQuadratic_padZero_iff_of_TCER",
    "DiophCompression.ResearchUpgrade.singleQuadratic_sharp_iff",
    "DiophCompression.ResearchUpgrade.sqPadFn_not_singleQuadratic_of_TCER",
    "DiophCompression.ResearchUpgrade.zeroWitness_iff",
    "DiophCompression.UniformQuadraticFiberStructureZZ"
  ],
  "missing_in_PaperClaimTypeReport": []
}
```

`certificates/PaperClaimTypeReport_current.log:445`

```text
DiophCompression.ResearchUpgrade.sealedFullNF_of_TCER	theorem	5	DiophCompression.ResearchUpgrade.TCERBridge.TernaryCosetEventualRepresentation → ∀ (n m : ℕ) (f : (Fin n → ℤ) → Fin m → ℤ), DiophCompression.SingleQuadraticDefinableFunctionZZ f → DiophCompression.ResearchUpgrade.FullVectorCosetNF f	propext,Classical.choice,Quot.sound
```

`certificates/PaperClaimTypeReport_current.log:451`

```text
DiophCompression.ResearchUpgrade.scalar_singleQuadratic_iff_of_TCER	theorem	3	DiophCompression.ResearchUpgrade.TCERBridge.TernaryCosetEventualRepresentation → ∀ (n : ℕ) (f : (Fin n → ℤ) → Fin 1 → ℤ), DiophCompression.SingleQuadraticDefinableFunctionZZ f ↔ DiophCompression.ResearchUpgrade.CommonSlopeIntNF f ∨ DiophCompression.ResearchUpgrade.GlobalQuadratic (DiophCompression.ResearchUpgrade.scalarOut f) ∨ DiophCompression.ResearchUpgrade.ParityAffineNF (DiophCompression.ResearchUpgrade.scalarOut f)	propext,Classical.choice,Quot.sound
```

`certificates/PaperClaimTypeReport_current.log:455`

```text
DiophCompression.ResearchUpgrade.floorThird_min_witnesses	theorem	0	DiophCompression.ResearchUpgrade.SingleQuadraticWithWitnessesZZ DiophCompression.ResearchUpgrade.floorThird 1 ∧ ¬DiophCompression.ResearchUpgrade.SingleQuadraticWithWitnessesZZ DiophCompression.ResearchUpgrade.floorThird 0	propext,Classical.choice,Quot.sound
```
