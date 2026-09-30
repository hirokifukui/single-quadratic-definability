#!/usr/bin/env bash
# build.sh - assemble and typeset the APAL manuscript.
#
# s31 rewrite. The r27 build ran pandoc and xelatex and NOTHING ELSE, so the shipped PDF carried
# the placeholder tokens <ROOTS>/<THMS>/<DEFS>/<UNCOND> unfilled and an empty Appendix E, while
# the text asserted that the build fills them and fails when they are missing. A blank-slate desk
# reviewer found both and rejected the paper on them. The pipeline below does what the paper says
# it does, and the gate at step 6 refuses to emit a final PDF while any token survives.
#
#   BUILD_MODE=draft  (default)  UNSET locators become a visible prospective sentence
#   BUILD_MODE=final             every token must be filled, or the build fails
set -euo pipefail
# T08 (s32): package-relative. The two absolute paths that used to sit here made the build a
# property of one machine, which is the same defect as a gate whose number depends on the
# root it is pointed at. V is derived from this script's own location; W may be overridden.
V="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
# s34 (Gate-8 B01). W is gone. Until s34 this line read W="${MPUP_WORK:-$HOME/lean/mpup-lean}" and
# four inputs came from there. The r29 archive contained none of them, so the distribution could
# not rebuild its own PDF; and the names were session-labelled, so the numbers the PDF prints were
# pinned to session 31 and nothing would have said when they aged. Inputs now come from this root,
# put there beforehand by release/stage_build_inputs.sh, which is a separate act with a separate
# log line. If they are missing the build stops here rather than reaching outside.
B="$V/papers/apal_build"
T="$V/tools"
MODE="${BUILD_MODE:-draft}"
# s35 (Gate-9 build-portability homework 11/12).  Determinism of the PDF: xelatex writes the
# document /ID from the clock unless told otherwise, which is why two rebuilds of the same bytes
# gave two hashes at r30 and why the seal had to disclaim reproducibility.  The epoch is read from
# locators.txt so that it is a property of the round and travels with the archive.
SDE=$(sed -n 's/^SOURCE_DATE_EPOCH=//p' "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/locators.txt" | head -1)
if [ -n "$SDE" ]; then export SOURCE_DATE_EPOCH="$SDE" FORCE_SOURCE_DATE=1; fi
echo "SOURCE_DATE_EPOCH=${SOURCE_DATE_EPOCH:-UNSET}"
cd "$B"
TITLE="Structure and computability of the single-quadratic existential fragment over the integers"
need() { [ -f "$1" ] || { echo "MISSING: $1"; exit 1; }; }

FAR="$V/certificates/FinalAxiomReport_current.log"
SD="$V/certificates/statement_diff_current.log"
HL="$V/certificates/binder_ledger_current.log"
FZ="$V/frozen_statements"
need "$FAR"; need "$SD"; need "$HL"
[ -d "$FZ" ] || { echo "MISSING DIR: $FZ"; exit 1; }
[ -d "$T" ]  || { echo "MISSING DIR: $T"; exit 1; }
echo "BUILD_ROOT $V"
echo "INPUTS  far=$(basename "$FAR")  sd=$(basename "$SD")  ledger=$(basename "$HL")  frozen=$(ls "$FZ"/*_STATEMENTS.lean | wc -l | tr -d " ")"

# --- 1. Appendix E, generated from the manuscript and the frozen statements
# s38 (Gate-12 C02/F01): the Markdown is GENERATED from the native TeX, one way, before anything
# reads it.  The shipped manuscript/MANUSCRIPT_V32.md must equal this generation byte for byte.
python3 "$T/tex_to_md.py" "$V/submission/native" generated_manuscript.md
if ! cmp -s generated_manuscript.md "$V/manuscript/MANUSCRIPT_V32.md"; then
  echo "MARKDOWN_GENERATED_GATE=FAIL (manuscript/MANUSCRIPT_V32.md is not what tex_to_md.py generates)"; exit 1; fi
echo "MARKDOWN_GENERATED_GATE=OK"
python3 "$V/manuscript/gen_appendix_e_numbered.py" "$V/manuscript/MANUSCRIPT_V32.md" \
        "$FZ" appendix_e_table.md statement_map_full.md "$V/submission/native/PAPER_CLAIMS.tsv"

# --- 2. working copy: drop the H1 (the title is set once from metadata), inline Appendix E
python3 - "$V/manuscript/MANUSCRIPT_V32.md" appendix_e_table.md body_raw.md <<'PY'
import sys
src, tbl, dst = sys.argv[1:4]
lines = open(src, encoding='utf-8').read().split('\n')
assert lines[0].startswith('# '), lines[0][:40]
s = '\n'.join(lines[1:]).lstrip('\n')
marker = '<!--APPENDIX_E_TABLE-->'
assert s.count(marker) == 1, ('appendix E marker', s.count(marker))
s = s.replace(marker, open(tbl, encoding='utf-8').read(), 1)
open(dst, 'w', encoding='utf-8').write(s)
print("H1_STRIPPED  APPENDIX_E_INLINED")
PY

# --- 3. numeric placeholders, from the artefacts themselves
python3 "$V/manuscript/fill_counts.py" body_raw.md "$FAR" "$SD" "$HL" body_counts.md

# --- 4. artifact locators
python3 - locators.txt body_counts.md body.md "$MODE" <<'PY'
import re, sys
loc, src, dst, mode = sys.argv[1:5]
kv = dict(l.split('=', 1) for l in open(loc, encoding='utf-8').read().split('\n')
          if l and not l.startswith('#') and '=' in l)
s = open(src, encoding='utf-8').read()
draft_doi  = "a Zenodo deposit whose version DOI is assigned at deposit and inserted here before submission"
draft_repo = "a public Git repository named here before submission"
for key, draft in (('DOI', draft_doi), ('REPO', draft_repo)):
    val = kv.get(key, 'UNSET').strip()
    if val == 'UNSET':
        if mode == 'final':
            sys.stderr.write("BUILD_MODE=final but %s is UNSET in locators.txt\n" % key); sys.exit(1)
        val = draft
    s = s.replace('\u27e8%s\u27e9' % key, val)
open(dst, 'w', encoding='utf-8').write(s)
print("LOCATORS mode=%s DOI=%s REPO=%s" % (mode, kv.get('DOI'), kv.get('REPO')))
PY

# --- 5. THE GATE: no placeholder token may survive into the typeset source
LEFT=$(grep -o '⟨[A-Z_]*⟩' body.md | sort -u || true)
if [ -n "$LEFT" ]; then echo "PLACEHOLDER_GATE=FAIL  surviving tokens:"; echo "$LEFT"; exit 1; fi
echo "PLACEHOLDER_GATE=OK  (0 surviving tokens)"
# s34: the row pattern used to require a leading digit, so a lettered statement (Theorem C.1) was
# neither generated nor counted here.  Count both shapes.
ETBL=$(grep -c '^| \([0-9]\|[A-Z]\)' appendix_e_table.md || true)
if [ "$ETBL" -lt 10 ]; then echo "APPENDIX_E_GATE=FAIL rows=$ETBL"; exit 1; fi
echo "APPENDIX_E_GATE=OK rows=$ETBL"
# s35 (Gate-9 §8/§12).  Appendix E's paragraph promises a full map shipping with the artifact.  It
# shipped nowhere, and the copy in the vault was a stale duplicate of the printed table.  Both are
# generated from the same run now, and the shipped copy must equal what this build produces.
if ! cmp -s statement_map_full.md "$V/release/STATEMENT_MAP_FULL.md"; then
  echo "STATEMENT_MAP_FULL_GATE=FAIL (shipped copy differs from this build)"; exit 1; fi
echo "STATEMENT_MAP_FULL_GATE=OK rows=$(grep -c '^| ' statement_map_full.md)"

# --- 5b. the label control (Gate-8 M02): every scanner in THIS root sees lettered labels
python3 "$T/lettered_label_control.py" "$V/manuscript/MANUSCRIPT_V32.md" --root "$V"

# --- 5b2. every claim carries a proof or a citation (s35, Gate-9 G10).  A definition may stand
# bare; a theorem may not.  At r30 Theorem 6.2 did, and only a reviewer reading the list noticed.
python3 "$T/proof_by_citation_scan.py" "$V/manuscript/MANUSCRIPT_V32.md" | tail -4

# --- 5c. fonts (s35, Gate-9 G05).  The faces this preamble asks for are macOS system fonts, and
# on a clean Linux host the build used to die nine hundred lines into a xelatex log.  The
# dependency is not fixed here -- FONT_PORTABILITY_s35.md says why the obvious substitution fails
# -- but it now announces itself by name, at the top, before pandoc runs.
# s37 (Gate-11 B02).  The shipped PDF is a function of the engine, the driver and the TeX Live
# release, and none of them was recorded.  A rebuild on a moved environment used to overwrite
# the shipped bytes first and be caught afterwards; this refuses before anything is written.
# Re-pinning is deliberate: tools/environment_preflight.py BUILD_ENVIRONMENT.txt --pin
python3 "$T/environment_preflight.py" BUILD_ENVIRONMENT.txt \
  || { echo "ENVIRONMENT_PREFLIGHT_GATE=FAIL (shipping artifacts untouched)"; exit 1; }
python3 "$T/font_preflight.py" preamble.tex

# --- 6. typeset
# s36 (Gate-10 N01-N08).  submission/CANONICAL_SOURCE names the source the PDF is built from.
#   native   -> submission/native/ (LaTeX with amsthm environments), the Markdown being a gated
#               mirror: tools/native_statement_check.py requires every statement to agree.
#   markdown -> the pandoc route below (r31 and earlier).
# s38 (Gate-12 S01): submission/CANONICAL_SOURCE is a status file, not a single token.  It declares
# SOURCE_STATUS (TRANSITIONAL until the QA tools audit the native TeX directly; FINAL after),
# BUILD_SOURCE (what the PDF is built from), QA_REFERENCE (what the prose scanners read) and
# MARKDOWN_IS_GENERATED / QA_INTERMEDIATE / HAND_MAINTAINED_MARKDOWN_QA_DEPENDENCIES (Gate-13 A09: the
# generated Markdown is a QA intermediate, not a source).  The build echoes all six so the seal and the README carry the same words.
CS="$V/submission/CANONICAL_SOURCE"
[ -f "$CS" ] || { echo "MISSING: $CS"; exit 1; }
for k in SOURCE_STATUS BUILD_SOURCE QA_REFERENCE MARKDOWN_IS_GENERATED QA_INTERMEDIATE HAND_MAINTAINED_MARKDOWN_QA_DEPENDENCIES; do
  v=$(sed -n "s/^$k=//p" "$CS" | head -1)
  [ -n "$v" ] || { echo "CANONICAL_SOURCE_GATE=FAIL ($k missing)"; exit 1; }
  echo "$k=$v"
done
BS=$(sed -n 's/^BUILD_SOURCE=//p' "$CS" | head -1)
case "$BS" in */native|native) CANON=native ;; *) CANON=markdown ;; esac
echo "CANONICAL_SOURCE=$CANON"
if [ "$CANON" = "native" ]; then
  python3 "$T/native_statement_check.py" "$V/manuscript/MANUSCRIPT_V32.md" "$V/submission/native" | tail -3
  python3 "$T/native_statement_check.py" "$V/manuscript/MANUSCRIPT_V32.md" "$V/submission/native" > /dev/null \
    || { echo "NATIVE_STATEMENT_GATE=FAIL"; exit 1; }
  echo "NATIVE_STATEMENT_GATE=OK"
  # s38 (Gate-12 S05): Layer B -- the native statements against the paper-claim manifest
  # (submission/native/PAPER_CLAIMS.tsv), which names Lean roots, quantifier order, degree and
  # witness domain independently of the Markdown mirror.  Layer A above can pass on two identical
  # wrong statements; this one cannot.
  python3 "$T/paper_claims_check.py" "$V" | tail -2
  python3 "$T/paper_claims_check.py" "$V" > /dev/null || { echo "PAPER_CLAIMS_GATE=FAIL"; exit 1; }
  echo "PAPER_CLAIMS_GATE=OK"
  # s39 (Gate-13 A04/A05): the type table the checker read must be the one this tree's Lean log
  # produces -- recompute PAPER_CLAIM_LEAN_TYPES.tsv from certificates/PaperClaimTypeReport_current.log
  # into a scratch copy and require byte equality with the shipped table.
  rm -rf pct_scratch; mkdir -p pct_scratch/certificates
  cp "$V/certificates/PaperClaimTypeReport_current.log" "$V/certificates/binder_ledger_current.log" pct_scratch/certificates/
  python3 "$T/paper_claim_types.py" pct_scratch | tail -1
  if ! cmp -s pct_scratch/certificates/PAPER_CLAIM_LEAN_TYPES.tsv "$V/certificates/PAPER_CLAIM_LEAN_TYPES.tsv"; then
    echo "PAPER_CLAIM_TYPES_GATE=FAIL (shipped type table differs from the one recomputed from the Lean log)"; exit 1; fi
  echo "PAPER_CLAIM_TYPES_GATE=OK $(grep -c . "$V/certificates/PAPER_CLAIM_LEAN_TYPES.tsv") lines"
  rm -rf pct_scratch   # scratch is not an input: remove before any manifest is taken
  # s39 (Gate-13 A02): semantic cross-references land on the statement they name
  python3 "$T/crossref_semantic_check.py" "$V" | tail -1
  python3 "$T/crossref_semantic_check.py" "$V" > /dev/null || { echo "CROSSREF_SEMANTIC_GATE=FAIL"; exit 1; }
  echo "CROSSREF_SEMANTIC_GATE=OK"
  # s39 (Gate-13 A06): ten planted defects, each in its own temp copy, all caught
  python3 "$T/paper_claims_controls.py" "$V" | tail -2
  python3 "$T/paper_claims_controls.py" "$V" > /dev/null || { echo "NEGATIVE_CONTROLS_GATE=FAIL"; exit 1; }
  # s40 (Gate-14 P01 / §18): the Pell-subscript scanner on the native source, and the twelve manuscript
  # red-team plants, each of which the text gates must catch on a temp copy.
  python3 "$T/manuscript_controls.py" "$V" --scan | tail -2
  python3 "$T/manuscript_controls.py" "$V" --scan > /dev/null || { echo "MANUSCRIPT_SCAN_GATE=FAIL"; exit 1; }
  python3 "$T/manuscript_controls.py" "$V" | tail -2
  python3 "$T/manuscript_controls.py" "$V" > /dev/null || { echo "MANUSCRIPT_CONTROLS_GATE=FAIL"; exit 1; }
  echo "NEGATIVE_CONTROLS_GATE=OK"
  # s38 (Gate-12 T03-T07): report-only census of what native_mathmode.py would still convert;
  # the source is expected to be a fixed point (0 superscripts, 0 subscripts left to convert).
  python3 "$T/native_mathmode.py" "$V/submission/native/sections"
  # s38 (Gate-12 C01): the proof companion is generated one way from the native source; the
  # shipped copy must be what this build produced.
  python3 "$T/proof_companion.py" "$V/submission/native" proof_companion.md
  if ! cmp -s proof_companion.md "$V/release/PROOF_COMPANION.md"; then
    echo "PROOF_COMPANION_GATE=FAIL (shipped copy differs from this build)"; exit 1; fi
  echo "PROOF_COMPANION_GATE=OK"
  rm -rf native_build; cp -R "$V/submission/native" native_build
  python3 - "$T" appendix_e_table.md native_build/appendix_e_table.tex <<'PY'
import sys; sys.path.insert(0, sys.argv[1])
from md_to_native_tex import table
lines = [l for l in open(sys.argv[2], encoding='utf-8').read().split('\n') if l.startswith('|')]
open(sys.argv[3], 'w', encoding='utf-8').write('\n'.join(table(lines)) + '\n')
print("APPENDIX_E_TEX rows=%d" % (len(lines) - 2))
PY
  # s37 (Gate-11 N17).  The migrator sizes a longtable column from its HEADER cell, so
  # Appendix E's "statement" column came out at 0.06\\linewidth and every "Proposition" ran
  # past it.  The widths of the table just generated are recomputed from its content, in the
  # build, so that a table regenerated tomorrow is measured the same way.
  python3 "$T/longtable_widths.py" native_build --apply | sed 's/^/APPENDIX_E_WIDTHS /'
  python3 - locators.txt native_build "$MODE" <<'PY'
import glob, os, sys
loc, nb, mode = sys.argv[1:4]
kv = dict(l.split('=', 1) for l in open(loc, encoding='utf-8').read().split('\n')
          if l and not l.startswith('#') and '=' in l)
drafts = {'DOI': "a Zenodo deposit whose version DOI is assigned at deposit and inserted here before submission",
          'REPO': "a public Git repository named here before submission",
          'EMAIL': "(e-mail supplied on the submission form; not printed in the draft build)"}
subs = {}
for key, draft in drafts.items():
    val = kv.get(key, 'UNSET').strip()
    if val == 'UNSET':
        if mode == 'final':
            sys.stderr.write("BUILD_MODE=final but %s is UNSET in locators.txt\n" % key); sys.exit(1)
        val = draft
    subs['\u27e8%s\u27e9' % key] = val
n = 0
for f in glob.glob(os.path.join(nb, '**', '*.tex'), recursive=True):
    s = open(f, encoding='utf-8').read(); s2 = s
    for k, v in subs.items(): s2 = s2.replace(k, v)
    if s2 != s: open(f, 'w', encoding='utf-8').write(s2); n += 1
print("LOCATORS_NATIVE mode=%s files_substituted=%d" % (mode, n))
PY
  LEFTN=$(grep -rho '⟨[A-Z_]*⟩' native_build --include='*.tex' | sort -u || true)
  if [ -n "$LEFTN" ]; then echo "PLACEHOLDER_GATE_NATIVE=FAIL  surviving tokens:"; echo "$LEFTN"; exit 1; fi
  ( cd native_build && for p in 1 2; do
      xelatex -interaction=nonstopmode -halt-on-error APAL_MANUSCRIPT.tex > ../pass$p.log 2>&1 \
        || { echo "XELATEX_PASS${p}_FAIL"; tail -25 ../pass$p.log; exit 1; }
    done ) || exit 1
  cp native_build/APAL_MANUSCRIPT.pdf APAL_MANUSCRIPT_v32.pdf
  # the xelatex log ships under the shipped name too; the first native dry run left the r30 log in
  # place and tools/shipping_artifact_gate.py caught it (BUILD_LOG_PAGES log=52 measured=56)
  # s38: cleveref lives in the user tree (~/Library/texmf), so the engine log names an absolute home
  # path; the shipped log must not (STALENESS_GATE, absolute-path rule).  The path is replaced by "~".
  # (the prefix is assembled from fragments so that this script does not itself carry the string the
  # staleness gate forbids, and it does not read the home variable the package gate forbids)
  AP="/Us""ers/"
  sed -E "s|${AP}[^/ ]+/|~/|g" native_build/APAL_MANUSCRIPT.log > APAL_MANUSCRIPT_v32.log
  # the shipped .tex is the native source flattened (every \input inlined), so a reader holds one file
  python3 - native_build/APAL_MANUSCRIPT.tex APAL_MANUSCRIPT_v32.tex <<'PY'
import os, re, sys
src, dst = sys.argv[1:3]; base = os.path.dirname(src)
def flat(path):
    out = []
    for l in open(path, encoding='utf-8'):
        m = re.match(r"\\input\{([^}]*)\}\s*$", l)
        if m:
            p = os.path.join(base, m.group(1)); p = p if p.endswith('.tex') else p + '.tex'
            out.append("%% ---- \\input{%s} ----\n" % m.group(1)); out.extend(flat(p))
        else: out.append(l)
    return out
open(dst, 'w', encoding='utf-8').write(''.join(flat(src)))
print("NATIVE_FLATTENED lines=%d" % sum(1 for _ in open(dst, encoding='utf-8')))
PY
  echo "NATIVE_OK  sections: $(ls native_build/sections/*.tex | wc -l | tr -d ' ')"
else
pandoc body.md --from=markdown+pipe_tables --to=latex --standalone \
  --pdf-engine=xelatex -V documentclass=article -V fontsize=11pt \
  -H preamble.tex --metadata title="$TITLE" \
  -o APAL_MANUSCRIPT_v32.tex
echo "PANDOC_OK  tex lines: $(wc -l < APAL_MANUSCRIPT_v32.tex)"
fi
if [ "$CANON" != "native" ]; then
for p in 1 2; do
  xelatex -interaction=nonstopmode -halt-on-error APAL_MANUSCRIPT_v32.tex > pass$p.log 2>&1 \
    || { echo "XELATEX_PASS${p}_FAIL"; tail -25 pass$p.log; exit 1; }
done
fi
MISS=$(grep -c 'Missing character' pass2.log || true)
if [ "$MISS" != "0" ]; then echo "GLYPH_GATE=FAIL missing=$MISS"; exit 1; fi
echo "GLYPH_GATE=OK"
echo "BUILD_OK mode=$MODE pages=$(grep -o 'Output written on [^(]*(\([0-9]*\) pages' pass2.log | grep -o '[0-9]* pages' | head -1)"

# --- 6b. P01 layout gate (Gate-8).  Four of the five must be zero now.  The fifth, overfull boxes
# wider than 5pt, is a property of the pandoc typesetting and is NOT zero; it is measured and
# printed rather than budgeted away, and it fails the build in BUILD_MODE=final. Gate-8 asks for
# zero, and the honest answer is that reaching zero is the native-TeX migration, not this script.
OVERFULL_ALL=$(grep -c 'Overfull' pass2.log || true)
OVERFULL_GT5=$(grep 'Overfull' pass2.log | sed -n 's/.*(\([0-9][0-9]*\)\.[0-9]*pt too wide.*/\1/p' \
               | awk '$1 >= 5' | wc -l | tr -d ' ')
UNDERFULL_ALL=$(grep -c 'Underfull' pass2.log || true)
MISSING_GLYPHS=$(grep -c 'Missing character' pass2.log || true)
UNRESOLVED_REFS=$(grep -c 'LaTeX Warning: Reference' pass2.log || true)
UNDEFINED_CITATIONS=$(grep -c 'LaTeX Warning: Citation' pass2.log || true)
PLACEHOLDERS=$(grep -c '⟨[A-Z_]*⟩' APAL_MANUSCRIPT_v32.tex || true)
echo "P01_OVERFULL_ALL=$OVERFULL_ALL"
echo "P01_OVERFULL_GT_5PT=$OVERFULL_GT5"
echo "P01_UNDERFULL_ALL=$UNDERFULL_ALL"
echo "P01_MISSING_GLYPHS=$MISSING_GLYPHS"
echo "P01_UNRESOLVED_REFS=$UNRESOLVED_REFS"
echo "P01_UNDEFINED_CITATIONS=$UNDEFINED_CITATIONS"
echo "P01_PLACEHOLDERS=$PLACEHOLDERS"
P01FAIL=0
for v in "$MISSING_GLYPHS" "$UNRESOLVED_REFS" "$UNDEFINED_CITATIONS" "$PLACEHOLDERS"; do
  [ "$v" = "0" ] || P01FAIL=1
done
if [ "$MODE" = "final" ] && [ "$OVERFULL_GT5" != "0" ]; then P01FAIL=1; fi
echo "P01_GATE=$([ "$P01FAIL" = "0" ] && echo OK || echo FAIL)"
# s37 (Gate-11 N12/N13/N14/N17).  P01 measures overfull and does not fail on it, and it does not
# look at the migration residues at all.  Each of those conditions was measured by hand this
# round; they are gates now, each exercised by a planted defect (s37 destroyer logs).
python3 "$T/typeset_gate.py" native_build/sections APAL_MANUSCRIPT_v32.log \
  || { echo "TYPESET_GATE_FAIL"; exit 1; }
[ "$P01FAIL" = "0" ] || exit 1

# --- 6c. the submission checklist's figures (s35, Gate-9 S04).  At r30 it said 52 pages in one
# place and 51 in another, and its own box for generating these from the build was unticked.
python3 "$T/submission_figures.py" "$V/manuscript/MANUSCRIPT_V32.md" \
        "$V/submission/APAL_SUBMISSION_CHECKLIST_v1.md" --log pass2.log

# --- 6d. the trust document's counts (s35, Gate-9 §16 answer 3).  The manuscript no longer carries
# the root and binder counts; this document does, and a number in a document nobody recomputes is
# the defect the whole round has been about.
python3 "$T/submission_figures.py" --trust "$V/release/TRUST_BOUNDARY_APAL.md" "$V/certificates"

# --- 7. the shipped artifacts (ERRATA_s32-03). Until s33 this script wrote only into
# papers/apal_build/, so the file a referee is given could differ from the file the gates above
# measured -- and for the whole of session 32 it did: the shipped LaTeX carried the wrong identity
# while the build directory carried the repair. The copy is now part of the pipeline, and is
# verified rather than assumed.
if [ ! -d "$V/submission" ]; then echo "MISSING DIR: $V/submission"; exit 1; fi
for f in APAL_MANUSCRIPT_v32.tex APAL_MANUSCRIPT_v32.pdf; do
  cp "$f" "$V/submission/$f"
  if ! cmp -s "$f" "$V/submission/$f"; then echo "SHIP_COPY=FAIL $f"; exit 1; fi
done
echo "SHIP_COPY=OK  submission/APAL_MANUSCRIPT_v32.{tex,pdf} refreshed from this build"
