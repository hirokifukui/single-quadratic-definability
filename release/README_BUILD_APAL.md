# Building and checking the artifact

Every figure in this file is inserted by `tools/generate_trust.py` from the shipped certificates when the package is assembled (2026-09-30); none is typed. `tools/shipping_artifact_gate.py` refuses a package in which this file and the certificates disagree.

**The one command.** `bash release/build_submission_from_package.sh` rebuilds the submission PDF from the extracted archive and nothing else, and prints `EXTERNAL_PATHS`, `HOME_DEPENDENCIES`, `SESSION_PINNED_INPUTS`, `BUILD_EXIT`, `NEWLY_BUILT_PDF_SHA256` and `SOURCE_MANIFEST_SHA256`. The build's inputs live at `certificates/*_current.log` inside the archive, put there beforehand by `release/stage_build_inputs.sh`, which is a separate step and not part of the build. The build runs in a scratch directory and promotes its outputs only when every preflight and gate has passed; a build that stops at preflight leaves the extracted tree byte-identical (`TREE_UNCHANGED=1`).

## Requirements

- `elan` (any recent version); the toolchain is pinned by `lean/lean-toolchain` to `v4.31.0-rc1`.
- mathlib is pinned by `lean/lakefile.lean` to git revision
  `d46bd45325c5cdf0ecf5cee0f5ff6d6e3586eb35`.
- Python 3.11 or later for the checking scripts. No third-party Python packages are required.
- Roughly 40 GB of disk for the mathlib build cache and about one hour on a recent laptop for a cold
  build; a few minutes with `lake exe cache get`.

## Build requirements

Measured on the machine that produced the shipped PDF, not recalled (`papers/apal_build/BUILD_ENVIRONMENT.txt` is the pinned record; `tools/environment_preflight.py` refuses to build on a different one):

    pandoc      3.9
    XeTeX       3.141592653-2.6-0.999998   (TeX Live 2026)
    TeX Live    2026, basic scheme
    Python      3 (standard library only; no third-party package is imported)
    Lean        v4.31.0-rc1, mathlib d46bd45

LaTeX packages used by `papers/apal_build/preamble.tex`: fontspec, unicode-math, geometry,
lineno, longtable, booktabs, array, amsthm, cleveref.

**Fonts.** The preamble asks for STIX Two Text, STIX Two Math and DejaVu Sans Mono, all named by
file so that kpathsea resolves them from the TeX tree:

    tlmgr install stix2-otf
    tlmgr install dejavu
    tlmgr install cleveref

All are in the standard repository and install without administrator rights
(`tlmgr init-usertree` once, then `tlmgr --usermode install ...`). The measurement behind this choice — the two family-name substitutions that failed on a host without the macOS faces — is recorded in `papers/apal_build/FONT_PORTABILITY_s35.md`.

    python3 tools/font_preflight.py papers/apal_build/preamble.tex

names every declared face and every missing one, and `build.sh` runs it before pandoc.

Every command block below starts at the package root. Blocks that need the Lean project enter `lean/` inside a
subshell, `( … )`, so the working directory is back at the package root when the block ends.

## Clean-room build

    (
      cd lean
      lake update            # fetches mathlib at the pinned revision
      lake exe cache get     # optional; skips compiling mathlib from source
      lake build             # default target: MPUP
      lake build DiophCompression
      lake build ResearchUpgrade
    )

`lake build` returning 0 is necessary and not sufficient: a file containing `sorry` also builds. The
gate is the axiom report. `lean/fresh_build.sh` runs the whole sequence below from an empty directory
and is the script that produced the clean-room record in `certificates/`. The current certificates record one
cold clean-room build, on agora, of the source identified by the shipped manifest. Additional independent-environment
builds may be recorded separately; they are not claimed for this candidate.

## The gates, in the order they should be run

**1. Axiom report.**

    (cd lean && lake env lean scripts/FinalAxiomReport.lean)

Expected: 421 roots, of which 417 report a footprint and 4 report none; every footprint is a subset
of `{propext, Classical.choice, Quot.sound}` (398 all three, 14 `propext` only, 5 `propext, Quot.sound`); the tokens `sorryAx`, `native_decide`, `ofReduceBool`,
`trustCompiler` do not appear; no errors. The shipped record is `certificates/FinalAxiomReport_current.log`.

**2. Statement fidelity.**

    STMT_BASE=frozen_statements LEAN_BASE=lean python3 lean/scripts/statement_diff.py --quiet

Expected: `THEOREMS=1092/1092`, `DEFINITIONS=298/298`, `FAIL=0`,
`FROZEN_FILES=59`, `SDIFF_EXIT=0`. `DUPLICATE_NAMES` counts ambiguous short-name look-ups, not
duplicate fully qualified Lean declarations; it is not required to be zero and is read together with the resolution by
exact statement text. The script compares each frozen declaration with the
production declaration of the same name as declaration text with runs of whitespace normalised; the accompanying negative control plants a mutation and a
deletion and requires both to be caught (`--negative-control`, `--unicode-control`).

**3. Hypothesis binder ledger.**

    (cd lean && lake env lean scripts/HypothesisBinderLedger.lean)

Expected: `BINDER_ROOTS=452`, `BINDER_UNCONDITIONAL=406`, `CONTROLS=7/7`, `NONSTD_AXIOMS=0`. Run it whenever the axiom report changes: it reads that file's root list but keeps its own imports.

**4. Paper-claim registry and type fingerprints.**

    (cd lean && lake env lean scripts/PaperClaimTypeReport.lean) > certificates/PaperClaimTypeReport_current.log
    python3 tools/paper_claim_types.py .
    python3 tools/paper_claims_check.py . --native submission/native
    python3 tools/paper_claims_controls.py . --native submission/native

Expected: `FORMAL_CLAIMS_MISSING=0`, `REVIEW_UNREVIEWED=0`, `REVIEW_STALE=0`, `PAPER_CLAIMS_EXIT=0`, `NEGATIVE_CONTROLS_CAUGHT=16/16`, `ONE_ROOT_LABELS=3/3`; `python3 tools/signoff_controls.py . --native submission/native` prints `SIGNOFF_CONTROLS=6/6` (the author sign-off carry-over regression set). The seven planted controls for
Propositions 10.16–10.18 and the seven hypothesis-binder controls are separate suites; their counts are not merged.

**5. Prose fidelity.**

    python3 tools/fidelity_destroyer.py . --shipping-only \
        --dispositions certificates/fidelity_destroyer_current.tsv

Expected: no hit whose disposition is not recorded. This gate is advisory: it produces an inventory
for a human to disposition, not a pass/fail verdict, because several of its patterns have legitimate
uses (a negation, or a remark that explicitly disclaims sharpness).

## Reproducing the manifest

The Lean source manifest is the listing that `lean/fresh_build.sh` hashes before it builds: every `.lean`, `.py` and
`.sh` file under `MPUP/`, `DiophCompression/`, `ResearchUpgrade/` and `scripts/`, and the five top-level files, with
paths relative to `lean/`. From the package root:

    (
      cd lean
      {
        find MPUP DiophCompression ResearchUpgrade scripts -type f \
          \( -name '*.lean' -o -name '*.py' -o -name '*.sh' \) -print0
        printf '%s\0' MPUP.lean DiophCompression.lean ResearchUpgrade.lean \
          lakefile.lean lean-toolchain
      } | LC_ALL=C sort -z | while IFS= read -r -d '' f; do
        printf '%s  %s\n' "$(shasum -a 256 "$f" | awk '{print $1}')" "$f"
      done
    ) > /tmp/lean_source_manifest.sha256
    cmp /tmp/lean_source_manifest.sha256 certificates/source_manifest_r53.sha256
    shasum -a 256 /tmp/lean_source_manifest.sha256

`cmp` prints nothing when the listing equals the shipped `certificates/source_manifest_r53.sha256`. The SHA-256
of this listing is the clean-room key `SRC_MANIFEST_SHA256`: the clean-room log records it, and the seal
(`correspondence/SEAL_*.txt`) repeats it on its "shipped tree" line; a build whose listing hashes differently is
building a different tree. `certificates/CLEANROOM_REFERENCE.txt` names the clean-room log that carries this key. The
seal's separate `SOURCE_MANIFEST_SHA256`, and `CORE_SOURCE_MANIFEST.sha256` in the public core, are distribution
manifests over a wider scope (`lean/`, `frozen_statements/`, `manuscript/`); they are not expected to equal it.

## Package integrity

In the public core (`APAL_PUBLIC_CORE_*.zip`), from its root:

    shasum -a 256 -c SHA256SUMS
    python3 tools/public_core_release.py --verify .

In the full package, from its root (`tools/shipping_artifact_gate.py` is the full package's gate; it needs files that
the public core leaves to the development history, so it is not run on the core):

    shasum -a 256 -c SHA256SUMS
    python3 tools/shipping_artifact_gate.py .
