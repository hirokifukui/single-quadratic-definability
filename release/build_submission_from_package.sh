#!/usr/bin/env bash
# build_submission_from_package.sh - rebuild the submission PDF from an extracted distribution
# and nothing else (s34, Gate-8 B01).
#
# What was wrong.  Until s34 the build read four inputs from a working tree outside the archive,
# under session-labelled names.  The r29 archive contained none of them: not a stale copy, not a
# copy under another name -- absent.  A referee who unzipped it could not rebuild the file being
# refereed, while the paper said the pipeline was reproducible.  Measured on the r29 package:
#   FinalAxiomReport_s31_*.log  0 files      statement_diff_s31.log  0 files
#
# What this script guarantees.  It refuses to run if the build scripts mention a home directory,
# an absolute path, an environment override for the work tree, or a session-labelled log name; it
# then runs the gates and the build with the extracted root as the only input, and prints the two
# hashes that let a third party say they built the same bytes.
#
# Usage:  cd <extracted>  &&  bash release/build_submission_from_package.sh  [final]
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MODE="${1:-draft}"
# s35 (Gate-9 G04).  Until s35 this variable was set here and never read again: the wrapper
# accepted "final" and called the child with no BUILD_MODE, so the child took its own default
# and built a DRAFT while the operator believed a final build had passed.  An unrecognised
# mode is now an error rather than a silent draft, for the same reason.
case "$MODE" in
  draft|final) ;;
  *) printf '%s\n' "MODE_GATE=FAIL unrecognised mode: $MODE (expected draft or final)"; exit 2 ;;
esac
cd "$ROOT"
FAILED=0
say() { printf '%s\n' "$*"; }
# ---- 0. failed-build immutability (s40, Gate-14 P05).  Until s40 a build that stopped at the
# environment preflight still rewrote SHIPPING_MEASUREMENTS.txt and SUBMISSION_INPUT_MANIFEST.sha256
# at the root and left tools/__pycache__ behind, so a shipping-gate rerun on the same extracted
# tree failed (MEASUREMENTS_AGREE).  Now: no bytecode is written, both files are written to a scratch
# directory and promoted only when every gate passed, and the tree is hashed before and after so a
# failed run can prove it left the distribution byte-identical.
export PYTHONDONTWRITEBYTECODE=1
SCRATCH=$(mktemp -d "${TMPDIR:-/tmp}/pkgbuild_out.XXXXXX")
tree_hash() { find . -type f ! -path './.git/*' -print0 | LC_ALL=C sort -z | xargs -0 shasum -a 256 | shasum -a 256 | cut -d' ' -f1; }
pycache_count() { find . -type d -name __pycache__ | wc -l | tr -d ' '; }
TREE_HASH_BEFORE=$(tree_hash); PYC_BEFORE=$(pycache_count)
say "TREE_HASH_BEFORE=$TREE_HASH_BEFORE"

# ---- 1. the distribution must be self-contained
SCAN_TARGETS="papers/apal_build/build.sh manuscript/fill_counts.py manuscript/gen_appendix_e_numbered.py"
# search terms are built by concatenation: a scanner that contains its own search term arrests
# itself, which is ERRATA_s33-03 and cost a round when it happened.
T_HOME='$'"HOME"
T_WORK="MPUP""_WORK"
T_ABS="/Users""/"
T_SESSION='_s[0-9][0-9]*_.*\.log'
HOME_DEPENDENCIES=0; EXTERNAL_PATHS=0; SESSION_PINNED=0
for f in $SCAN_TARGETS; do
  [ -f "$f" ] || { say "SCAN_MISSING $f"; FAILED=1; continue; }
  # comments are excluded: the files explain the defect they no longer have
  STRIP=$(grep -v '^[[:space:]]*#' "$f")
  printf '%s' "$STRIP" | grep -qF "$T_HOME" && { HOME_DEPENDENCIES=$((HOME_DEPENDENCIES+1)); say "HOME_DEP $f"; }
  printf '%s' "$STRIP" | grep -qF "$T_WORK" && { EXTERNAL_PATHS=$((EXTERNAL_PATHS+1)); say "WORK_OVERRIDE $f"; }
  printf '%s' "$STRIP" | grep -qF "$T_ABS"  && { EXTERNAL_PATHS=$((EXTERNAL_PATHS+1)); say "ABSOLUTE_PATH $f"; }
  printf '%s' "$STRIP" | grep -qE "$T_SESSION" && { SESSION_PINNED=$((SESSION_PINNED+1)); say "SESSION_PINNED $f"; }
done
say "EXTERNAL_PATHS=$EXTERNAL_PATHS"
say "HOME_DEPENDENCIES=$HOME_DEPENDENCIES"
say "SESSION_PINNED_INPUTS=$SESSION_PINNED"
[ "$EXTERNAL_PATHS" = 0 ] && [ "$HOME_DEPENDENCIES" = 0 ] && [ "$SESSION_PINNED" = 0 ] || FAILED=1

# ---- 2. the inputs must be present IN the archive
for f in certificates/FinalAxiomReport_current.log certificates/statement_diff_current.log \
         certificates/binder_ledger_current.log; do
  [ -f "$f" ] || { say "INPUT_MISSING $f"; FAILED=1; }
done
FROZEN=$(ls frozen_statements/*_STATEMENTS.lean 2>/dev/null | wc -l | tr -d ' ')
say "FROZEN_FILES_IN_ARCHIVE=$FROZEN"
[ "$FROZEN" -gt 0 ] || FAILED=1

# ---- 3. the trust-boundary census, which needs the Lean sources shipped at lean/
if [ -d lean/DiophCompression ] && [ -f lean/scripts/FinalAxiomReport.lean ]; then
  # the census wants the frozen statements beside the sources.  Copy them in, and REMOVE THEM
  # AGAIN before anything is hashed: a verification script that leaves its own scaffolding inside
  # the tree it then measures is reporting a property of the procedure, not of the archive.  That
  # is what happened on the first run of this script, and the seal quoted the wrong number.
  CENSUS_OVERLAY=0
  if [ ! -d lean/frozen_statements ]; then cp -R frozen_statements lean/frozen_statements && CENSUS_OVERLAY=1; fi
  python3 tools/cited_name_census.py manuscript/MANUSCRIPT_V32.md --lean-root lean --says release/TRUST_BOUNDARY_APAL.md || FAILED=1
  [ "$CENSUS_OVERLAY" = 1 ] && rm -rf lean/frozen_statements
else
  say "CENSUS=NOT_RUN lean/ sources absent -- this script is for a distribution root"
  FAILED=1
fi

# ---- 3b. one prose source (s35, Gate-9 G01/G02).  The r30 archive shipped a second, older
# rendering of the manuscript that no gate compared with the source.  A referee who unzipped it
# could read either document.
python3 tools/parallel_prose_control.py . || FAILED=1

# ---- 4. the build itself, rooted here
# s36 (Gate-10 §6).  The wrapper used to print PDF_SHA256 from submission/ after ANY build, so a
# failed build displayed the hash of whatever PDF was already there as if it had just made it.
# The pre-existing file is hashed before the build under its own name; a newly built hash is
# printed only when the build exited 0.
PRE_PDF=""; [ -f submission/APAL_MANUSCRIPT_v32.pdf ] && PRE_PDF=$(shasum -a 256 submission/APAL_MANUSCRIPT_v32.pdf | cut -d' ' -f1)
say "PREEXISTING_SHIPPED_PDF_SHA256=${PRE_PDF:-NONE}"
BUILD_MODE="$MODE" bash papers/apal_build/build.sh | tee /tmp/pkgbuild.$$
BUILD_EXIT=${PIPESTATUS[0]}
say "BUILD_EXIT=$BUILD_EXIT"
OVER_ALL=$(grep -o 'P01_OVERFULL_ALL=[0-9]*' /tmp/pkgbuild.$$ | tail -1 | cut -d= -f2)
OVER_5=$(grep -o 'P01_OVERFULL_GT_5PT=[0-9]*' /tmp/pkgbuild.$$ | tail -1 | cut -d= -f2)
rm -f /tmp/pkgbuild.$$
NEW_PDF_CREATED=0; NEW_PDF=""; NEW_TEX=""
if [ "$BUILD_EXIT" = 0 ]; then
  NEW_PDF=$(shasum -a 256 papers/apal_build/APAL_MANUSCRIPT_v32.pdf | cut -d' ' -f1)
  NEW_TEX=$(shasum -a 256 papers/apal_build/APAL_MANUSCRIPT_v32.tex | cut -d' ' -f1)
  NEW_PDF_CREATED=1
  say "NEWLY_BUILT_PDF_SHA256=$NEW_PDF"
  say "NEWLY_BUILT_TEX_SHA256=$NEW_TEX"
else
  FAILED=1
fi
say "NEW_PDF_CREATED=$NEW_PDF_CREATED"

# ---- 5. the shipping path against the build output (s36, Gate-10 Z02).  build.sh copies its
# output to submission/; here that copy is compared, not assumed, and recorded.
GEN_PDF_EQ=0; GEN_TEX_EQ=0
if [ "$NEW_PDF_CREATED" = 1 ]; then
  cmp -s papers/apal_build/APAL_MANUSCRIPT_v32.pdf submission/APAL_MANUSCRIPT_v32.pdf && GEN_PDF_EQ=1
  cmp -s papers/apal_build/APAL_MANUSCRIPT_v32.tex submission/APAL_MANUSCRIPT_v32.tex && GEN_TEX_EQ=1
fi
say "GENERATED_PDF_EQ_SHIPPED=$GEN_PDF_EQ"
say "GENERATED_TEX_EQ_SHIPPED=$GEN_TEX_EQ"
[ "$GEN_PDF_EQ" = 1 ] && [ "$GEN_TEX_EQ" = 1 ] || FAILED=1
SHIP_PDF=""; SHIP_TEX=""; PDF_PAGES=""
if [ -f submission/APAL_MANUSCRIPT_v32.pdf ]; then
  SHIP_PDF=$(shasum -a 256 submission/APAL_MANUSCRIPT_v32.pdf | cut -d' ' -f1)
  SHIP_TEX=$(shasum -a 256 submission/APAL_MANUSCRIPT_v32.tex | cut -d' ' -f1)
  PDF_PAGES=$(python3 tools/shipping_artifact_gate.py --pages submission/APAL_MANUSCRIPT_v32.pdf 2>/dev/null || echo UNKNOWN)
fi
say "SHIPPED_PDF_SHA256=${SHIP_PDF:-NONE}"
say "SHIPPED_TEX_SHA256=${SHIP_TEX:-NONE}"
say "PDF_PAGES=${PDF_PAGES:-UNKNOWN}"
XDV=$(xdvipdfmx --version 2>/dev/null | head -1 | grep -o '[0-9]\{8\}' | head -1)
say "XDVIPDFMX_VERSION=${XDV:-UNKNOWN}"
# s35 (Gate-9 G06).  There used to be one manifest here, over lean/, frozen_statements/ and
# manuscript/, and the seal spoke of it as if it covered the submission build.  It does not: the
# preamble, the locators, the build scripts, the tools that generate Appendix E and the
# certificates the counters are read from all change the PDF and none of them was hashed.  Two
# people could agree on SOURCE_MANIFEST_SHA256 and build different documents.  The Lean manifest
# keeps its name and its computation, so it is comparable with every seal back to r27; the second
# one is new and says what it covers.
find lean frozen_statements manuscript -type f ! -path '*/__pycache__/*' ! -name '*.pyc' 2>/dev/null | LC_ALL=C sort > /tmp/pkgsrc.$$
SRC_SHA=$(xargs shasum -a 256 < /tmp/pkgsrc.$$ | shasum -a 256 | cut -d' ' -f1)
say "SOURCE_MANIFEST_SHA256=$SRC_SHA"
say "SOURCE_MANIFEST_SCOPE=lean,frozen_statements,manuscript"
rm -f /tmp/pkgsrc.$$

# every input the typeset PDF actually depends on, by name, in canonical order
find papers/apal_build submission tools release certificates manuscript frozen_statements \
     -type f \
     ! -name '*.aux' ! -name '*.log' ! -name '*.out' ! -name '*.pdf' \
     ! -name 'body*.md' ! -name 'appendix_e_table.md' ! -name '*.bak*' \
     ! -path '*/__pycache__/*' ! -name '*.pyc' \
     2>/dev/null | LC_ALL=C sort > /tmp/pkgsub.$$
SUBN=$(wc -l < /tmp/pkgsub.$$ | tr -d ' ')
xargs shasum -a 256 < /tmp/pkgsub.$$ > "$SCRATCH/SUBMISSION_INPUT_MANIFEST.sha256"
say "SUBMISSION_INPUT_MANIFEST_FILES=$SUBN"
SUB_SHA=$(shasum -a 256 "$SCRATCH/SUBMISSION_INPUT_MANIFEST.sha256" | cut -d' ' -f1)
say "SUBMISSION_INPUT_MANIFEST_SHA256=$SUB_SHA"
say "SUBMISSION_INPUT_MANIFEST_SCOPE=papers/apal_build,submission,tools,release,certificates,manuscript,frozen_statements (build products and backups excluded)"
[ "$SUBN" -gt 0 ] || { say "SUBMISSION_INPUT_MANIFEST=EMPTY"; FAILED=1; }
rm -f /tmp/pkgsub.$$

# ---- 6. SHIPPING_MEASUREMENTS.txt (s36, Z02/Z04).  Everything the seal quotes about the typeset
# artifact is written here, at the package root (outside every manifest scope), by the process that
# measured it.  tools/generate_seal.py reads this file; tools/shipping_artifact_gate.py re-measures
# the artifact and refuses a seal that disagrees with it.
{
  echo "BUILD_MODE=$MODE"
  echo "BUILD_EXIT=$BUILD_EXIT"
  echo "NEW_PDF_CREATED=$NEW_PDF_CREATED"
  echo "PDF_PAGES=${PDF_PAGES:-UNKNOWN}"
  echo "SHIPPED_PDF_SHA256=${SHIP_PDF:-NONE}"
  echo "SHIPPED_TEX_SHA256=${SHIP_TEX:-NONE}"
  echo "GENERATED_PDF_EQ_SHIPPED=$GEN_PDF_EQ"
  echo "GENERATED_TEX_EQ_SHIPPED=$GEN_TEX_EQ"
  echo "OVERFULL_ALL=${OVER_ALL:-UNKNOWN}"
  echo "OVERFULL_GT_5PT=${OVER_5:-UNKNOWN}"
  echo "SOURCE_MANIFEST_SHA256=$SRC_SHA"
  echo "SUBMISSION_INPUT_MANIFEST_FILES=$SUBN"
  echo "SUBMISSION_INPUT_MANIFEST_SHA256=$SUB_SHA"
  echo "XDVIPDFMX_VERSION=${XDV:-UNKNOWN}"
  echo "PACKAGE_BUILD_EXIT=$FAILED"
} > "$SCRATCH/SHIPPING_MEASUREMENTS.txt"
# ---- 7. promotion (s40, P05): outputs reach the distribution root only on a clean run.
PYC_AFTER=$(pycache_count)
say "PY_CACHE_CREATED=$(( PYC_AFTER - PYC_BEFORE ))"
if [ "$FAILED" = 0 ]; then
  cp "$SCRATCH/SUBMISSION_INPUT_MANIFEST.sha256" SUBMISSION_INPUT_MANIFEST.sha256
  cp "$SCRATCH/SHIPPING_MEASUREMENTS.txt" SHIPPING_MEASUREMENTS.txt
  say "SHIPPING_MEASUREMENTS=written"
  say "SUBMISSION_INPUT_MANIFEST=written"
else
  TREE_HASH_AFTER=$(tree_hash)
  say "TREE_HASH_AFTER=$TREE_HASH_AFTER"
  if [ "$TREE_HASH_AFTER" = "$TREE_HASH_BEFORE" ]; then say "TREE_UNCHANGED=1"; else say "TREE_UNCHANGED=0"; fi
  say "SHIPPING_MEASUREMENTS=not_written (build failed; scratch kept at $SCRATCH)"
  say "PACKAGE_BUILD_EXIT=$FAILED"
  exit "$FAILED"
fi
rm -rf "$SCRATCH"
say "PACKAGE_BUILD_EXIT=$FAILED"
exit "$FAILED"
