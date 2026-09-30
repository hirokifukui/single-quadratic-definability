# Public core of the mpup r53 artifact — a self-verifying release

This archive is the PUBLIC CORE cut from the sealed full package `mpup_gpt_r53_20260930.zip` (SHA-256 `c7ffc92c9ce562697b6fd5e12edef9cd961357956f813bb76b8f1a9e0606a64a`):
the Lean development (`lean/`), the frozen statements and certificates, the shipped tools, the native
manuscript source and the built PDF, the release documents, and the current correspondence.  The
development history (earlier rounds' reviews, homework, red-team notes, superseded drafts) is in the
companion DEVELOPMENT_HISTORY archive; the two archives partition the full package without overlap.

## Verify this archive on its own (nothing else needed)

    shasum -a 256 -c SHA256SUMS            # every file of THIS archive
    python3 tools/public_core_release.py --verify .

The second command checks `CORE_SEAL.txt` against the archive: its source manifest (`lean/`,
`frozen_statements/`, `manuscript/`), its submission-input manifest, the PDF and TeX hashes and the page
count, the paper-claim registry (`tools/paper_claims_check.py`), the local `DiophCompression`/`MPUP`
imports, and the build entry (`release/README_BUILD_APAL.md`, `release/build_submission_from_package.sh`,
`lean/lakefile.lean`, `lean/lean-toolchain`, `lean/fresh_build.sh`), and the clean-room record of the Lean source
(`certificates/CLEANROOM_REFERENCE.txt` names the original build log; the log must be present byte for byte, must
name the source manifest shipped here, and that manifest must equal the one recomputed from `lean/`).  The record
is the log of the run that built this source; when a round does not change the Lean source, the earlier run's log
is kept under its original name and is not re-dated.  It reads no file outside this archive and prints
`REQUIRED_HISTORY_FILES=0`.  Expected: `CORE_SHIPPING_EXIT=0`.

Then, if you want to rebuild: `bash release/build_submission_from_package.sh` (typesetting) and, for the
kernel, `release/README_BUILD_APAL.md` (clean-room Lean build; mathlib and toolchain pinned in `lean/`).

## Provenance layer (kept byte for byte; do not run its gates here)

`PARTITION_RECORD.md`, `correspondence/SEAL_r53.txt`, `SHIPPING_MEASUREMENTS.txt`,
`SUBMISSION_INPUT_MANIFEST.sha256` and `ASSEMBLY_GATES.log`/`PACKAGE_BUILD.log` are the FULL PACKAGE's
records and are members of the partition; they are unchanged here so that core + history reproduces the
full package.  Their figures (source manifest, submission manifest, the parent's checksum entries, gate5's 363 rules)
describe the full tree, not this archive, and `tools/shipping_artifact_gate.py` / `tools/gate5_verify.py`
are development gates that require history files by design: they are meant for the full package and
fail here for that reason alone.  The release layer named in `CORE_SEAL.txt` under CORE_RELEASE_FILES is
what this archive adds; subtract it (and `SHA256SUMS`) to recover the partition payload.
