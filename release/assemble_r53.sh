#!/usr/bin/env bash
# assemble_r53.sh - r53 = the answer to the reviewer's r52 review (our GATE34).
# s64, 2026-09-30.  Derived from assemble_r52.sh (not edited): identity r53, BASE = r52, FRESH = ~/lean/r49_fresh
#   (no Lean change: run with MPUP_LEAN_UNCHANGED=1, the manifest must equal r52's = r49's),
#   CORRESPONDENCE = the GATE34 set; 3b-bis also ships the Gate-34 checklist and certificates/cas_s64.
#   GATE34 P2 (E-34-1) and E-34-2 are source-text changes only (gen_blueprint.py, TRUST template, native section 12).
#
# (history of assemble_r52.sh follows)
# assemble_r52.sh - r52 = the answer to the reviewer's r51 continuation review (our GATE33).
# s63, 2026-09-28.  Derived from assemble_r51.sh (not edited): identity r52, BASE = r51, FRESH = ~/lean/r49_fresh
#   (no Lean change: run with MPUP_LEAN_UNCHANGED=1, the manifest must equal r51's = r49's),
#   CORRESPONDENCE = the GATE33 set; 3b-bis also ships the Gate-33 checklist and certificates/cas_s63.
#   GATE33 P1 is a template change only (README_BUILD_APAL.template.md: the manual block builds MPUP/DC/RU).
#
# (history of assemble_r51.sh follows)
# assemble_r51.sh - r51 = the answer to the reviewer's r50 continuation review (our GATE32).
# s62, 2026-09-28.  Derived from assemble_r50.sh (not edited): identity r51, BASE = r50, FRESH = ~/lean/r49_fresh
#   (no Lean change: run with MPUP_LEAN_UNCHANGED=1, the manifest must equal r50's = r49's),
#   CORRESPONDENCE = the GATE32 set; 3b-bis also ships the Gate-32 checklist and certificates/cas_s62.
#   GATE32 P0: the clean-room log of record stays in the public core (@FRESH_ROUND@ in PUBLIC_CORE_EXCLUDE),
#   certificates/CLEANROOM_REFERENCE.txt names it, and the re-extracted core runs the clean-room controls.
#
# (history of assemble_r50.sh follows)
# assemble_r50.sh - r50 = the answer to the reviewer's r49 continuation review (our GATE31).
# s61, 2026-09-28.  Derived from assemble_r49.sh (not edited): identity r50, BASE = r49, FRESH = ~/lean/r49_fresh
#   (no Lean change this round: run with MPUP_LEAN_UNCHANGED=1, the manifest must equal r49's),
#   CORRESPONDENCE = the GATE31 set; 3b-bis also ships the Gate-31 checklist and certificates/cas_s61.
#   Partition (7d2): the public core admits the current round's correspondence.
#
# (history of assemble_r49.sh follows)
# assemble_r49.sh - r49 = the answer to the reviewer's r48 continuation review (our GATE30).
# s60, 2026-09-28.  Derived from assemble_r48.sh (not edited): identity r49, BASE = r48, FRESH = ~/lean/r49_fresh,
#   CORRESPONDENCE = the GATE30 set; 3b-bis also ships the Gate-30 checklist, the r49 related work and
#   certificates/cas_s60.  Partition (7d2): the public core admits the current round's correspondence.
#
# (history of assemble_r48.sh follows)
# assemble_r48.sh - r48 = the answer to the reviewer's r47 continuation review (our GATE29).
# s59, 2026-09-27.  Derived from assemble_r47.sh (not edited): identity r48, BASE = r47, FRESH = ~/lean/r48_fresh,
#   CORRESPONDENCE = the GATE29 set; 3b-bis also ships the Gate-29 checklist, related work, D4 plan and
#   certificates/cas_s59.  Partition (7d2): the public core admits the current round's correspondence.
#
# (history of assemble_r47.sh follows)
# assemble_r47.sh - r47 = the answer to the reviewer's r46 continuation review (our GATE28).
# s58, 2026-09-26.  Derived from assemble_r46.sh (not edited): identity r47, BASE = r46, FRESH = ~/lean/r47_fresh,
#   CORRESPONDENCE = the GATE28 set; 3b-bis also ships the Gate-28 checklist, the s58 crosswalk and TCER adapter, and
#   certificates/cas_s58.  Partition (7d2): the public core admits the current round's correspondence.
#
# (history of assemble_r46.sh follows)
# assemble_r46.sh - r46 = the answer to the reviewer's r45 continuation review (our GATE27).
# s57, 2026-09-25.  Derived from assemble_r45.sh (not edited): identity r46, BASE = r45, FRESH = ~/lean/r46_fresh,
#   CORRESPONDENCE = the GATE27 set; 3b-bis also ships the Gate-27 checklist, certificates/cas_s57 and
#   manuscript/PROOF_NOTE_NF.md.  Partition (7d2): the public core admits the current round's correspondence.
#
# (history of assemble_r45.sh follows)
# assemble_r45.sh - r45 = the answer to the reviewer's r44 continuation review (our GATE26).
# s56, 2026-09-25.  Derived from assemble_r44.sh (not edited): identity r45, BASE = r44, FRESH = ~/lean/r45_fresh,
#   CORRESPONDENCE = the GATE26 set; 3b-bis also ships the Gate-26 checklist and certificates/cas_s56.
#
# (history of assemble_r44.sh follows)
# assemble_r44.sh - r44 = the answer to the reviewer's r43 continuation review (our GATE25).
# s55, 2026-09-17.  Derived from assemble_r43.sh, which is NOT edited: it is the script that built
# the sealed r43.  s55 changes:
#   - identity r44, BASE = r43, FRESH default = the r44 cold room ~/lean/r44_fresh,
#     CORRESPONDENCE = the GATE25 trio (letter, task list, disposition) + checklist.
#   - 3b-bis also ships and gates the Gate-25 checklist and the s55 CAS pair plus the D4 certificate
#     checker (certificates/cas_s55/), all cited by LETTER_GATE25; the token gate reads LETTER_GATE25.
#
# assemble_r43.sh - r43 = the answer to the reviewer's r42 continuation review (our GATE24).
# s54, 2026-09-16.  Derived from assemble_r42.sh, which is NOT edited: it is the script that built
# the sealed r42.  s54 changes:
#   - identity r43, BASE = r42, FRESH default = the r43 cold room ~/lean/r43_fresh,
#     CORRESPONDENCE = the GATE24 trio (letter, task list, disposition) + checklist.
#   - 3b-bis also ships and gates the Gate-24 checklist and the s54 CAS re-derivation pair
#     (certificates/cas_s54/), both cited by LETTER_GATE24; the token gate reads LETTER_GATE24.
#   - Lean: four new ResearchUpgrade modules (NormLift, DefiniteBinary, FourSquareFinite,
#     R42Completion); the frozen file count stays 59 (NF gate unchanged).
# assemble_r42.sh - r42 = the answer to the reviewer's r41 continuation review (our GATE23).
# s53, 2026-09-16.  Derived from assemble_r41.sh, which is NOT edited: it is the script that built
# the sealed r41.  s53 changes:
#   - identity r42, BASE = r41, FRESH default = the r42 cold room ~/lean/r42_fresh,
#     CORRESPONDENCE = the GATE23 trio (letter, task list, disposition).
#   - 3b-bis also ships and gates the Gate-23 checklist and the s52 CAS re-derivation pair
#     (certificates/cas_s52/), both cited by the letter.
#   - one more shipped tool, note_anchor_check.py (every Lean name the proof note cites must exist
#     in the shipped source; cited by the letter, E-23-4): 38 tools.
#   - frozen_statements/ResearchUpgrade_STATEMENTS.lean and certificates/definition_bodies*.tsv
#     now cover the r41/r42 ResearchUpgrade modules; the file count stays 59 (NF gate unchanged).
#   - the single-environment branch now emits FRESH_BUILD_COMPARE_DIFFS (the seal template needs it).
#   - the letter's clean-room block is filled from the cold-room log by a script before sealing
#     (E-23-6); the assembly refuses to ship a letter that still carries {{...}} tokens.
# assemble_r41.sh - r41 = the answer to the reviewer's r40 continuation review (GPT Gate23 /
# our GATE22).  s51, 2026-09-14.  Derived from assemble_r40.sh, which is NOT edited: it is the
# script that built the sealed r40.  s51 changes:
#   - identity r41, BASE = r40, CORRESPONDENCE = the GATE22 trio.
#   - NEW step 3b-bis: every artifact the manuscript cites as deposited is copied and gated.
#     r40 cited four that were never in the shipping tree at all, because they live in a THIRD
#     working zone (~/lean/mpup-upgrade/) that was never a source of this assembly.  The
#     reviewer could not see any of them; Theorem 4.2's proof said "deposited with the
#     artifact" of a file that was not.  Fail closed on each.
#   - MPUP_NAME and MPUP_FRESH must be set at assembly: the defaults below carry the r41 names
#     but not the seal date, and the clean room has to be re-run because scripts/ changed
#     (fresh_build_compare.py).  SEAL_INPUT.env still says ROUND=r40, so step 0 fails closed
#     until it is bumped -- that is the ruling point, not a bug.
# assemble_r40.sh - r40 = the round that adds the THIRD Lean library (lean/ResearchUpgrade: the sharp
# injective dimension theorem n <= m, the structural alternative, the sharpness biconditional and the
# capacity corollary).  s50, 2026-09-14.  Derived from assemble_r39.sh; s50 changes:
#   - identity r40, BASE = r39, FRESH = the r40 clean room ~/lean/r40_fresh (Lean CHANGED: the whole
#     ResearchUpgrade library, 86 files; the room's lean tree is its build/ subdirectory, so the path
#     is resolved by FRESH_LEAN below instead of being assumed to be $FRESH/lean).
#   - step 7's manifest recomputation enumerates ResearchUpgrade as well.  Written for two libraries,
#     it would have made a manifest without the third and MANIFEST_MATCH would have failed (the gate
#     is fail-closed, so this was a stop, not a silent omission) -- the third occurrence this session
#     of a mechanism that predates the library (statement_diff.py PROD_DIRS, HypothesisBinderLedger).
#   - CORRESPONDENCE names the r40 letter; the script fails closed until those files exist.
#
# --- inherited header (assemble_r39.sh) ---
# assemble_r39.sh - r39 = the answer to the reviewer's "APAL r38 — 残り二点の修正指示" (= our Gate-17;
# FIX-01 fail-closed core checksum gate, FIX-02 §11 third mechanism).  s43, 2026-09-11.  Derived from
# assemble_r38.sh; s43 changes: identity r39, BASE = r38, FRESH = the r37 clean room UNCHANGED
# (MPUP_LEAN_UNCHANGED=1: no Lean edit this round), one more shipped tool (public_core_controls.py =
# eight planted defective SHA256SUMS manifests that check_checksums must refuse; 37 tools), run at step 7b
# beside the sign-off controls and quoted by the seal as CORE_CHECKSUM_CONTROLS; public_core_release.py
# --verify (step 11, C3) now prints the fail-closed counters (INVALID_LINES, DUPLICATES, BAD_PATHS,
# CORE_CHECKSUM=ok|FAIL).  Nothing else in the assembly changed.
## assemble_r38.sh - r38 = the answer to the reviewer's "APAL最終投稿監査 — r37" (= our Gate-16; its
# homework is the three packets A/B/C).  s42, 2026-09-11.  Derived from assemble_r37.sh; s42 changes:
# identity r38, BASE = r37, FRESH = the r37 clean room UNCHANGED (MPUP_LEAN_UNCHANGED=1: no Lean edit this
# round), two more shipped tools (signoff_controls.py = Packet B's six carry-over regression cases;
# public_core_release.py = Packet C's release layer + public gate; 36 tools), the registry gate, its
# planted controls (14) and the sign-off controls (6) run ON the assembled package at step 7b and are
# quoted by the seal, and step 11 turns the public core into a release of its own: the core payload is
# cut from the sealed zip as before (partition unchanged), then CORE_SEAL / CORE_SOURCE_MANIFEST /
# CORE_SUBMISSION_INPUT_MANIFEST / README_PUBLIC_CORE are generated ON the core, the core gets its own
# SHA256SUMS, and the core zip is re-extracted into an empty directory and judged by
# public_core_release.py --verify (C3); the verdict is posted beside the zips as <name>.core_gate.txt.
## assemble_r37.sh - r37 = APAL Final Gate 2 (s41, 2026-09-11; the reviewer's "APAL最終投稿監査 — r36" /
# "APAL Final Gate 2" = our Gate-15 response). Derived from assemble_r36.sh; s41 changes: identity r37,
# BASE = r36, FRESH = the r37 clean room (Lean CHANGED: F02 relation_phase_diagram_all_positive_arity_of_classical,
# 421 roots), one more shipped tool (generate_signoff_sheet.py, 34 tools) and the sign-off sheet GENERATED into
# release/ at assembly instead of copied from the vault (F05), the public-core exclusion list
# release/PUBLIC_CORE_EXCLUDE.template.txt rendered to release/PUBLIC_CORE_EXCLUDE.txt and applied by
# partition_lists so development-history certificates leave the public core (F08; partition_check and
# release_controls C13 enforce it), and the split archives posted beside the package zip (F09).
#
# assemble_r35.sh - r35 = APAL Submission Gate 9 (s39, 2026-09-06; the reviewer's Gate 9 = our Gate-13 response).
# Derived from assemble_r34.sh; s39 changes: identity r35, FRESH = the r35 clean room (Lean CHANGED: A01),
# three new tools (paper_claims_controls, crossref_semantic_check, paper_claim_types), two new certificates
# (PaperClaimTypeReport_current.log, PAPER_CLAIM_LEAN_TYPES.tsv), release/APPENDIX_F_LEAN_ANCHORS.md (M09),
# CANONICAL_SOURCE fields (A09), and the two-layer public artifact split at the end (R01).
#
# A transcription of assemble_r33.sh with the s38 additions: two more shipped tools
# (paper_claims_check.py = Layer B of the statement gate; definition_fidelity.py = the
# definition-body certificate the trust document now names), the definition-body certificate itself,
# and history/DEVELOPMENT_AUDIT_HISTORY.md (the development history the trust document no longer
# carries).  submission/CANONICAL_SOURCE is a status file now; the assembly prints its status.
# Inherited from r33, the change Gate-10 P0-1 required and the generators it made necessary:
#
#  (Z02) The PDF is BUILT INSIDE THE DISTRIBUTION ROOT, after every package gate, by the shipped
#        release/build_submission_from_package.sh; the shipping path is compared with the build
#        output, and the vault's submission/ is refreshed FROM the package, not the other way round.
#        r31 shipped the r30 PDF because this script copied submission/ from the vault and the
#        build that measured 51 pages ran in a throwaway root.
#  (Z03) tools/shipping_artifact_gate.py runs on the assembled root and again on the re-extracted
#        zip; a seal that disagrees with the file beside it is exit 1.
#  (Z04) correspondence/SEAL_<round>.txt is GENERATED (tools/generate_seal.py) from this script's
#        own measurements (ASSEMBLY_GATES.log, PACKAGE_BUILD.log, SHIPPING_MEASUREMENTS.txt, the
#        certificates and the clean-room records).  release/SEAL_INPUT.env declares the identities.
#  (Z06) release/TRUST_BOUNDARY_APAL.md is GENERATED (tools/generate_trust.py) from its template
#        and the certificates; the r31 document carried two generations of figures at once.
#  (Z08) Superseded seals leave correspondence/ for history/seals/; exactly one seal ships.
#  (L)   Lean source is unchanged this round: MPUP_LEAN_UNCHANGED=1 turns the "must differ from the
#        previous manifest" gate into "must equal it" -- the gate says which it measured.
#
# The zip is not written unless MPUP_SEAL_CONFIRM=<round> is set: sealing is Dr. Fukui's ruling.
set -euo pipefail
V="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PYTHONDONTWRITEBYTECODE=1   # s40 (Gate-14 P05/§18): no bytecode anywhere in the assembled tree
W="${MPUP_WORK:-$HOME/lean/mpup-lean}"
FRESH="${MPUP_FRESH:-$HOME/lean/r49_fresh}"
# s50: the r40 clean room keeps its Lean tree in build/, not lean/.  Resolve it once instead of
# assuming the name in four places.
FRESH_LEAN="${MPUP_FRESH_LEAN:-}"
if [ -z "$FRESH_LEAN" ]; then
  if [ -d "$FRESH/lean" ]; then FRESH_LEAN="$FRESH/lean"; else FRESH_LEAN="$FRESH/build"; fi
fi
PKG="${MPUP_PKGDIR:-$HOME/Downloads}"
BASE="${MPUP_BASE:-mpup_gpt_r52_20260928}"
NAME="${MPUP_NAME:-mpup_gpt_r53_20260930}"
P="$PKG/$BASE"
OUT="$PKG/$NAME"
# s35: the round was written into four places by hand -- the seal file's name, the confirmation
# string, the grep that checks the seal reached the zip, and the correspondence list.  Each of them
# was correct for exactly one round.  Derive it from the package name instead; that is the one place
# it is already stated.
ROUND=$(printf '%s' "$NAME" | sed -n 's/.*_\(r[0-9][0-9]*\)_.*/\1/p')
if [ -z "$ROUND" ]; then echo "GATE round: cannot read a round out of NAME=$NAME"; exit 1; fi
echo "ROUND=$ROUND"
CORRESPONDENCE="${MPUP_CORRESPONDENCE:-LETTER_GATE34.md GPT_REVIEW_GATE34_20260930_A_r52_review.md GPT_REVIEW_GATE34_20260930_B_closeout_tasks_for_claude.md GPT_REVIEW_GATE34_20260930_D_execution_receipt.md GPT_REVIEW_GATE34_20260930_E_source_evidence.md REVIEW_GATE34_DISPOSITION_s64.md GATE34_CHECKLIST.md ERRATA_R53_20260930.md TCER_ADAPTER_s58.md}"
BUILD_MODE_PKG="${MPUP_BUILD_MODE:-draft}"
TS=202609250000.00
need() { if [ ! -f "$1" ]; then echo "MISSING: $1"; exit 1; fi; }
needd() { if [ ! -d "$1" ]; then echo "MISSING DIR: $1"; exit 1; fi; }

# --- 0. seal guard FIRST, and the clean-room evidence this round depends on
for f in SEAL.template.md SEAL_INPUT.env SEAL_WHAT_IS_OPEN.md TRUST_BOUNDARY_APAL.template.md; do
  need "$V/release/$f"; done
if ! grep -q "^ROUND=$ROUND\$" "$V/release/SEAL_INPUT.env"; then
  echo "GATE seal input: release/SEAL_INPUT.env does not declare ROUND=$ROUND"; exit 1; fi
needd "$P"
needd "$FRESH_LEAN"
need "$FRESH_LEAN/source_manifest.sha256"
# s35: this was `need "$FRESH/fresh_build_r30.log"` -- the third place in this script keyed to a
# filename convention, and it stopped the first r31 assembly dead.  The clean room holds one log per
# machine that built it; take them all, whatever the round is called.
FRESH_LOGS=$(ls "$FRESH"/fresh_build*.log 2>/dev/null)
if [ -z "$FRESH_LOGS" ]; then echo "MISSING: no fresh_build*.log in $FRESH"; exit 1; fi
# s62 (GATE32 P0): the round(s) of the clean-room log(s) of the shipped source, rendered into PUBLIC_CORE_EXCLUDE so
# that the log of record stays in the public core under its original name whatever round produced it.
FRESH_ROUND=$(for f in $FRESH_LOGS; do basename "$f" | sed -nE 's/^fresh_build_(r[0-9]+).*$/\1/p'; done | sort -u | paste -s -d'|' -)
if [ -z "$FRESH_ROUND" ]; then echo "MISSING: cannot read the round of the clean-room log(s) in $FRESH"; exit 1; fi

rm -rf "$OUT"; mkdir -p "$OUT"; cp -R "$P/." "$OUT/"; rm -f "$OUT/SHA256SUMS"
# s39 (found on the first r35 assembly): the r34 package shipped the package build's raw engine
# logs (papers/apal_build/pass1.log, pass2.log, native_build/APAL_MANUSCRIPT.log), each carrying an
# absolute home path -- written AFTER the staleness gate had run, so the gate never saw them, and
# inherited here from BASE where the gate now catches them.  Build byproducts are not inputs: drop
# every inherited one, let the package build regenerate what it needs, and scrub again after it.
for f in pass1.log pass2.log native_build pct_scratch; do rm -rf "$OUT/papers/apal_build/$f"; done
# products of the previous package's own build and assembly do not inherit
rm -f "$OUT"/SUBMISSION_INPUT_MANIFEST.sha256 "$OUT"/SHIPPING_MEASUREMENTS.txt "$OUT"/ASSEMBLY_GATES.log "$OUT"/PACKAGE_BUILD.log
AG="$OUT/ASSEMBLY_GATES.log"; : > "$AG"
say() { printf '%s\n' "$*" | tee -a "$AG"; }

# --- 1. manuscript hygiene: exactly one manuscript ships (the r26 defect)
# s35 (Gate-9, self-adversarial pass).  This step used to MOVE the superseded manuscripts into
# history/, where they shipped.  The r30 archive therefore carried fifteen older manuscripts and a
# second file named MANUSCRIPT_V32.md that differed from the shipped one in the sixteen lines of
# the Gate-8 repair: it still said 398 roots and "nineteen, nine and ten".  A referee who opened it
# would have read the figures we had just told them were wrong.  The step written to guarantee that
# one manuscript ships was the step putting the second one in the package.  They are deleted from
# the distribution now; the vault keeps every version, and the vault is the archive of record.
for m in "$OUT"/manuscript/MANUSCRIPT_V*.md; do
  [ -e "$m" ] || continue
  rm -f "$m"
done
rm -rf "$OUT/history/manuscript"
# s35: two more superseded prose sources were shipping under history/ -- an old full manuscript and
# the old native-TeX main file.  Same class, same disposition: the vault keeps them, the
# distribution does not.
rm -f "$OUT"/history/MANUSCRIPT_V*.md "$OUT"/history/submission/APAL_MANUSCRIPT.tex
# s38 (Gate-12 C02/F01): the Markdown is regenerated from the native source here, so the package
# gates that read it (gate5, destroyer, census, prose control, lettered control) judge a build product
# of the TeX and never a hand-maintained mirror.  The vault copy is refreshed from the same run.
python3 "$W/scripts/tex_to_md.py" "$V/submission/native" "$OUT/manuscript/MANUSCRIPT_V32.md"
[ "${MPUP_DRY_RUN:-}" = "1" ] || cp "$OUT/manuscript/MANUSCRIPT_V32.md" "$V/manuscript/MANUSCRIPT_V32.md"
say "MARKDOWN_GENERATED=OK (tex_to_md.py; hand mirror archived in the vault at history/manuscript_hand_mirror/)"

# --- 2. release, written from blank
# s35: the paper promises STATEMENT_MAP_FULL.md ships with the artifact.  Until r31 it shipped
# nowhere and this script did not mention it -- the r29 "build inputs shipped zero times" defect
# again, and caught this round only by reading the sentence and looking for the file.
rm -f "$OUT/release/TRUST_BOUNDARY_APAL.md" "$OUT/release/assemble_r30.sh" "$OUT/release/README_BUILD_APAL.md" "$OUT/release/RELEASE_CHECKLIST_APAL.md"
# s40 (Gate-14 P04/P12): release/ holds state documents only; the two development notes inherited from
# earlier packages move to history/ (kept, not deleted), and README_BUILD / RELEASE_CHECKLIST are
# generated from their templates by generate_trust.py, never copied from the vault.
mkdir -p "$OUT/history/release_notes"
# s40 (Gate-14 §18 release red team): exactly one cover letter ships outside history/; the earlier
# correspondence/COVER_LETTER_APAL.md inherited from previous packages is kept under history/.
mkdir -p "$OUT/history/correspondence_superseded"
if [ -f "$OUT/correspondence/COVER_LETTER_APAL.md" ]; then mv "$OUT/correspondence/COVER_LETTER_APAL.md" "$OUT/history/correspondence_superseded/COVER_LETTER_APAL.md"; fi
for f in SEAL_PACKAGING_RULE_s28.md SOURCE_OF_TRUTH_PLAN_s32.md; do
  if [ -f "$OUT/release/$f" ]; then mv "$OUT/release/$f" "$OUT/history/release_notes/$f"; fi
  if [ -f "$V/release/$f" ] && [ ! -f "$OUT/history/release_notes/$f" ]; then cp "$V/release/$f" "$OUT/history/release_notes/$f"; fi
done
for f in STATEMENT_MAP_FULL.md PROOF_COMPANION.md APPENDIX_F_LEAN_ANCHORS.md APPENDIX_F_COVERAGE.md TRUST_BOUNDARY_APAL.template.md SEAL.template.md SEAL_INPUT.env \
         SEAL_WHAT_IS_OPEN.md README_BUILD_APAL.template.md RELEASE_CHECKLIST_APAL.template.md PUBLIC_CORE_EXCLUDE.template.txt \
         "assemble_${ROUND}.sh" \
         stage_build_inputs.sh build_submission_from_package.sh; do
  need "$V/release/$f"; cp "$V/release/$f" "$OUT/release/"; done
# s41 (Gate-15 F08): render the public-core exclusion list for THIS round; partition_lists reads it, and
# partition_check / release_controls C13 re-read it inside the package.
sed -e "s/@ROUND@/$ROUND/g" -e "s/@FRESH_ROUND@/$FRESH_ROUND/g" "$V/release/PUBLIC_CORE_EXCLUDE.template.txt" > "$OUT/release/PUBLIC_CORE_EXCLUDE.txt"
if grep -q -E '@ROUND@|@FRESH_ROUND@' "$OUT/release/PUBLIC_CORE_EXCLUDE.txt"; then echo "GATE exclude: @ROUND@/@FRESH_ROUND@ not rendered"; exit 1; fi
say "PUBLIC_CORE_EXCLUDE_FRESH_ROUND=$FRESH_ROUND"
say "PUBLIC_CORE_EXCLUDE=rendered patterns=$(grep -cvE '^#|^$' "$OUT/release/PUBLIC_CORE_EXCLUDE.txt")"
# the discarded from-blank draft ships, so the decision not to take Gate-8's D01 literally can be
# inspected rather than taken on trust (ERRATA_GATE8 §2 item 8)
# s40 (Gate-14 §18): the draft is history, not a second trust document; it ships under history/.
rm -rf "$OUT/release/_s34_fromblank_draft" "$OUT/history/release_notes/_fromblank_draft"
mkdir -p "$OUT/history/release_notes/_fromblank_draft"
cp "$V"/release/_s34_fromblank_draft/* "$OUT/history/release_notes/_fromblank_draft/"
if [ -f "$OUT/correspondence/TRUST_BOUNDARY.md" ]; then mkdir -p "$OUT/history/correspondence_superseded"; mv "$OUT/correspondence/TRUST_BOUNDARY.md" "$OUT/history/correspondence_superseded/TRUST_BOUNDARY.md"; fi
mkdir -p "$OUT/history/release"
for f in TRUST_BOUNDARY.md README_BUILD.md RELEASE_CHECKLIST_r13.md assemble_r26.sh; do
  if [ -f "$OUT/release/$f" ]; then mv "$OUT/release/$f" "$OUT/history/release/"; fi; done

# --- 3. submission, written from blank
mkdir -p "$OUT/submission" "$OUT/history/submission"
for f in APAL_COVER_LETTER_v1.md APAL_SUBMISSION_CHECKLIST_v1.md \
         APAL_MANUSCRIPT_v32.pdf APAL_MANUSCRIPT_v32.tex; do
  need "$V/submission/$f"; cp "$V/submission/$f" "$OUT/submission/"; done
need "$V/manuscript/gen_appendix_e_numbered.py"
cp "$V/manuscript/gen_appendix_e_numbered.py" "$OUT/manuscript/"

# --- 3a. S05: the native LaTeX source. It is NOT yet canonical -- step 4 of the source-of-truth
# plan is a ruling, not a consequence -- but it is the round's largest deliverable and a reader
# cannot check the migration without it. It ships as source only; the .log/.aux/.pdf of its own
# build do not.
# s35 (Gate-9 G01/G02).  This block used to ship submission/tex/, and its gate counted the section
# files -- "expected 19" -- rather than comparing them with the source.  A copy that had stopped
# agreeing therefore satisfied the gate by existing, and it had: seven of the fourteen markup-free
# prose rules that the source passes, the fragments failed.  The fragments are retired to
# history/native_tex_r30_pandoc/ and nothing parallel ships.  The migration (N01-N06) resumes in
# r32 from the corrected source; a harness rebuilt from a wrong document was never worth keeping.
if [ -e "$V/submission/tex" ]; then
  echo "GATE submission/tex: the retired parallel source is back in the vault"; exit 1; fi
# s35, found by the first dry run of this script: the guard above watches the VAULT, but $OUT is
# built by copying the PREVIOUS PACKAGE, which still contains submission/tex/.  Retiring the
# fragments from the vault therefore did not stop them shipping; the parallel-prose gate at the end
# caught it, 14 files in one directory.  A fix that removes a source but not the inheritance path
# removes nothing.
rm -rf "$OUT/submission/tex" "$OUT/submission/native"
# s36 (Gate-10 N01-N08): the native LaTeX source ships and is what the PDF is built from;
# submission/CANONICAL_SOURCE says so and build.sh reads it.  The Markdown is a gated mirror.
need "$V/submission/CANONICAL_SOURCE"; cp "$V/submission/CANONICAL_SOURCE" "$OUT/submission/"
needd "$V/submission/native"; cp -R "$V/submission/native" "$OUT/submission/native"
find "$OUT/submission/native" -name '*.bak*' -delete
NNS=$(ls -1 "$OUT"/submission/native/sections/*.tex | wc -l | tr -d ' ')
need "$OUT/submission/native/PAPER_CLAIMS.tsv"
# s41 (Gate-15 F05): the author sign-off sheet is GENERATED from the registry and its Layer-2 review, never
# copied from the vault; author fields survive only while a row's statement hash and type hash are unchanged.
cp "$V/release/AUTHOR_SIGNOFF_SHEET.md" "$OUT/release/AUTHOR_SIGNOFF_SHEET.md"   # carries any filled author fields
( cd "$OUT" && python3 "$W/scripts/generate_signoff_sheet.py" . --native submission/native | tee -a "$AG" ) || { echo "GENERATE_SIGNOFF=FAIL"; exit 1; }
for k in SOURCE_STATUS BUILD_SOURCE QA_REFERENCE MARKDOWN_IS_GENERATED QA_INTERMEDIATE HAND_MAINTAINED_MARKDOWN_QA_DEPENDENCIES; do
  grep -q "^$k=" "$OUT/submission/CANONICAL_SOURCE" || { echo "GATE CANONICAL_SOURCE: $k missing"; exit 1; }; done
say "NATIVE_TEX_IN_PACKAGE=OK sections=$NNS $(tr '\n' ' ' < "$OUT/submission/CANONICAL_SOURCE")"

# --- 3b. proof documents.  s35 ruling on Gate-9 N05, following the ruling on the direction: three of
# these four are earlier drafts of Appendix F, 86 to 88 per cent of their text reproduced there, and
# the appendix carries corrections they do not.  They are not a parallel source and nothing in the
# paper is checked against them, so they ship as history rather than beside the manuscript -- one
# text of record in manuscript/, the drafts under history/ with a note saying what they are.
# FALLBACK_FINITE_SIDE_V31.md is not a draft of the appendix (zero overlap measured) and stays.
need "$V/manuscript/FALLBACK_FINITE_SIDE_V31.md"
cp "$V/manuscript/FALLBACK_FINITE_SIDE_V31.md" "$OUT/manuscript/"
# ...and, for the fourth time this session, remove them from where they arrive rather than only from
# where they are added: $OUT is built by copying the previous package, which still has them in
# manuscript/.  submission/tex, the superseded dispositions and the stale prose all taught this the
# same way, each time by a gate firing rather than by anyone remembering.
rm -f "$OUT"/manuscript/APAL_PROJECTION_PROOF_FULL.md \
      "$OUT"/manuscript/FULL_RANK_PROOF_V2.md \
      "$OUT"/manuscript/QUADRATIC_PROJECTION_DICHOTOMY_FULL_V2.md
mkdir -p "$OUT/history/superseded_appendixF"
for f in APAL_PROJECTION_PROOF_FULL.md FULL_RANK_PROOF_V2.md \
         QUADRATIC_PROJECTION_DICHOTOMY_FULL_V2.md; do
  need "$V/manuscript/$f"; cp "$V/manuscript/$f" "$OUT/history/superseded_appendixF/"; done
need "$V/manuscript/SUPERSEDED_APPENDIX_F_DRAFTS.md"
cp "$V/manuscript/SUPERSEDED_APPENDIX_F_DRAFTS.md" "$OUT/history/superseded_appendixF/README.md"
# s36 (Gate-10 §9 / N07): the provenance and correction record that headed Appendix F through r31
# leaves the manuscript and ships here, beside the drafts it describes.
need "$V/manuscript/APPENDIX_F_PROVENANCE_s36.md"
cp "$V/manuscript/APPENDIX_F_PROVENANCE_s36.md" "$OUT/history/superseded_appendixF/APPENDIX_F_PROVENANCE.md"
NSUP=$(ls -1 "$OUT"/history/superseded_appendixF/*.md | wc -l | tr -d " ")
if [ "$NSUP" != "5" ]; then echo "GATE superseded drafts: expected 5, found $NSUP"; exit 1; fi
echo "SUPERSEDED_DRAFTS_SHIPPED=OK n=$NSUP (as history, not beside the manuscript)"

# --- 3b-bis (s51).  THE SECOND TRAP: a third working zone.  $V and $W were the only sources of
# this assembly, and ~/lean/mpup-upgrade/ is neither, so four cited artifacts shipped nowhere:
# the proof note that Theorem 4.2's proof calls "deposited with the artifact", the two s48 CAS
# checkers and their logs, and the Gate-22 checklist.  They are staged into $V and gated here.
# A citation without a shipped artifact now stops the build instead of reaching a reviewer.
need "$V/manuscript/PROOF_NOTE_DIMENSION.md"
cp "$V/manuscript/PROOF_NOTE_DIMENSION.md" "$OUT/manuscript/"
mkdir -p "$OUT/certificates/cas_s48"
for f in verify_gate22_s48.py verify_gate22_s48.log collision_check_s48.py collision_check_s48.log; do
  need "$V/certificates/cas_s48/$f"; cp "$V/certificates/cas_s48/$f" "$OUT/certificates/cas_s48/"; done
need "$V/correspondence/GATE22_CHECKLIST.md"
cp "$V/correspondence/GATE22_CHECKLIST.md" "$OUT/correspondence/"
# s53: the Gate-23 checklist and the s52 CAS re-derivations cited by LETTER_GATE23.
need "$V/correspondence/GATE23_CHECKLIST.md"
cp "$V/correspondence/GATE23_CHECKLIST.md" "$OUT/correspondence/"
mkdir -p "$OUT/certificates/cas_s52"
for f in rederive_gate23_s52.py rederive_gate23_s52.log rederive_gate23_s52.sage rederive_gate23_s52_sage.log \
         rederive_gate23_note_repair_s52.py rederive_gate23_note_repair_s52.log \
         rederive_gate23_isotropic_pell_s52.py rederive_gate23_isotropic_pell_s52.log; do
  need "$V/certificates/cas_s52/$f"; cp "$V/certificates/cas_s52/$f" "$OUT/certificates/cas_s52/"; done
# s54: the Gate-24 checklist and the s54 CAS re-derivations cited by LETTER_GATE24.
need "$V/correspondence/GATE24_CHECKLIST.md"
cp "$V/correspondence/GATE24_CHECKLIST.md" "$OUT/correspondence/"
mkdir -p "$OUT/certificates/cas_s54"
for f in rederive_gate24_s54.py rederive_gate24_s54.log rederive_gate24_s54.sage rederive_gate24_s54_sage.log; do
  need "$V/certificates/cas_s54/$f"; cp "$V/certificates/cas_s54/$f" "$OUT/certificates/cas_s54/"; done
# s55: the Gate-25 checklist, the s55 CAS pair and the D4 certificate checker cited by LETTER_GATE25.
need "$V/correspondence/GATE25_CHECKLIST.md"
cp "$V/correspondence/GATE25_CHECKLIST.md" "$OUT/correspondence/"
mkdir -p "$OUT/certificates/cas_s55"
for f in leg1_python.py leg1.log leg2_sage.sage leg2.log symmetry_certificate_checker.py symmetry_certificate_checker.log; do
  need "$V/certificates/cas_s55/$f"; cp "$V/certificates/cas_s55/$f" "$OUT/certificates/cas_s55/"; done
# s55: the own-initiative evidence cited by LETTER_GATE25 §6 and OWN_INITIATIVE_s55.md.
needd "$V/certificates/own_s55"
rm -rf "$OUT/certificates/own_s55"; cp -R "$V/certificates/own_s55" "$OUT/certificates/own_s55"
NOWN=$(find "$OUT/certificates/own_s55" -type f | wc -l | tr -d " ")
if [ "$NOWN" != "21" ]; then echo "GATE own_s55: expected 21 files, found $NOWN"; exit 1; fi
# s56: the Gate-26 checklist and the s56 CAS pair and checks cited by LETTER_GATE26.
need "$V/correspondence/GATE26_CHECKLIST.md"
cp "$V/correspondence/GATE26_CHECKLIST.md" "$OUT/correspondence/"
mkdir -p "$OUT/certificates/cas_s56"
for f in leg1_s56.py leg1_s56.log leg2_leg2d.sage leg2_leg2d.log norm_blindspot_scope.py norm_blindspot_scope.log check_source_evidence.py source_evidence_check.log; do
  need "$V/certificates/cas_s56/$f"; cp "$V/certificates/cas_s56/$f" "$OUT/certificates/cas_s56/"; done
# s57: the Gate-27 checklist, the s57 CAS legs and checks, and the proof note cited by LETTER_GATE27.
need "$V/correspondence/GATE27_CHECKLIST.md"
cp "$V/correspondence/GATE27_CHECKLIST.md" "$OUT/correspondence/"
need "$V/correspondence/C1_TCER_CROSSWALK_s57.md"
cp "$V/correspondence/C1_TCER_CROSSWALK_s57.md" "$OUT/correspondence/"
need "$V/manuscript/PROOF_NOTE_NF.md"
cp "$V/manuscript/PROOF_NOTE_NF.md" "$OUT/manuscript/"
mkdir -p "$OUT/certificates/cas_s57"
for f in leg1_s57.py leg1_s57.log leg1_s57_run1_harnessbug.log leg2_s57.sage leg2_s57.log leg2_s57_run1_typeerror.log leg2_s57_run2_precision.log eichler_check.py eichler_check.log check_source_evidence_s57.py source_evidence_check_s57.log source_evidence_check_s57_plant.log plant_A6A7_s57.py plant_A6A7_s57.log; do
  need "$V/certificates/cas_s57/$f"; cp "$V/certificates/cas_s57/$f" "$OUT/certificates/cas_s57/"; done
# s58: the Gate-28 checklist, the s58 crosswalk and TCER adapter, and the s58 CAS legs cited by LETTER_GATE28.
need "$V/correspondence/GATE28_CHECKLIST.md"
cp "$V/correspondence/GATE28_CHECKLIST.md" "$OUT/correspondence/"
need "$V/correspondence/C1_TCER_CROSSWALK_s58.md"
cp "$V/correspondence/C1_TCER_CROSSWALK_s58.md" "$OUT/correspondence/"
need "$V/correspondence/TCER_ADAPTER_s58.md"
cp "$V/correspondence/TCER_ADAPTER_s58.md" "$OUT/correspondence/"
mkdir -p "$OUT/certificates/cas_s58"
for f in leg1_s58.py leg1_s58.log leg1_s58_run1_control_missed.log leg2_s58.sage leg2_s58.log d3_table.py d3_table.log plant_A9A12_s58.py plant_A9A12_s58.log; do
  need "$V/certificates/cas_s58/$f"; cp "$V/certificates/cas_s58/$f" "$OUT/certificates/cas_s58/"; done
# s59: the Gate-29 checklist, related work, D4 plan and the s59 CAS legs cited by LETTER_GATE29.
for f in GATE29_CHECKLIST.md RELATED_WORK_R48_s59.md D4_RESTRUCTURE_PLAN_s59.md; do
  need "$V/correspondence/$f"; cp "$V/correspondence/$f" "$OUT/correspondence/"; done
mkdir -p "$OUT/certificates/cas_s59"
for f in leg1_s59.py leg1_s59.log leg2_s59.sage leg2_s59_run1_harness_fail.log leg2b_s59.sage leg2b_s59.log h3_scale_identity.py h3_scale_identity.log plant_A13A15_s59.py plant_A13A15_s59.log; do
  need "$V/certificates/cas_s59/$f"; cp "$V/certificates/cas_s59/$f" "$OUT/certificates/cas_s59/"; done
# s60: the Gate-30 checklist, the r49 related work and the s60 CAS legs / probes cited by LETTER_GATE30.
for f in GATE30_CHECKLIST.md RELATED_WORK_R49_s60.md; do
  need "$V/correspondence/$f"; cp "$V/correspondence/$f" "$OUT/correspondence/"; done
mkdir -p "$OUT/certificates/cas_s60"
for f in leg1_s60.py leg1_s60.log leg2_s60.sage leg2_s60.log probe_gate30.lean probe_gate30.log probe_gate30b.lean probe_gate30b.log H4_FREEZE_s60.lean compare_H4.log compare_H4_plant.log compare_H4_defplant.log plant_P1618_s60.py plant_P1618_s60.log; do
  need "$V/certificates/cas_s60/$f"; cp -f "$V/certificates/cas_s60/$f" "$OUT/certificates/cas_s60/"; done  # s61: -f, the frozen file is 444 in BASE
# s61: the Gate-31 checklist and the s61 CAS legs / probes cited by LETTER_GATE31.
for f in GATE31_CHECKLIST.md; do
  need "$V/correspondence/$f"; cp "$V/correspondence/$f" "$OUT/correspondence/"; done
mkdir -p "$OUT/certificates/cas_s61"
for f in leg1_s61.py leg1_s61.log leg2_s61.sage leg2_s61.log probe_gate31.lean probe_gate31.log probe_gate31b.lean probe_gate31b.log; do
  need "$V/certificates/cas_s61/$f"; cp "$V/certificates/cas_s61/$f" "$OUT/certificates/cas_s61/"; done
# s62: the Gate-32 checklist and the s62 CAS legs / probe / intake facts cited by LETTER_GATE32.
for f in GATE32_CHECKLIST.md; do
  need "$V/correspondence/$f"; cp "$V/correspondence/$f" "$OUT/correspondence/"; done
mkdir -p "$OUT/certificates/cas_s62"
for f in leg1_s62.py leg1_s62.log leg2_s62.sage leg2_s62.log probe_gate32.lean probe_gate32.log facts_gate32.log facts_gate32b.log; do
  need "$V/certificates/cas_s62/$f"; cp "$V/certificates/cas_s62/$f" "$OUT/certificates/cas_s62/"; done
if grep -q '{{' "$V/correspondence/LETTER_GATE32.md"; then
  echo "GATE letter: LETTER_GATE32.md still carries unfilled {{...}} tokens"; exit 1; fi
# s63: the Gate-33 checklist and the s63 CAS legs / probes / intake facts cited by LETTER_GATE33.
for f in GATE33_CHECKLIST.md; do
  need "$V/correspondence/$f"; cp "$V/correspondence/$f" "$OUT/correspondence/"; done
mkdir -p "$OUT/certificates/cas_s63"
for f in leg1_s63.py leg1_s63.log leg2_s63.sage leg2_s63.log probe_gate33.lean probe_gate33.log probe_gate33b.lean probe_gate33b.log facts_gate33.log excerpts_gate33.log; do
  need "$V/certificates/cas_s63/$f"; cp "$V/certificates/cas_s63/$f" "$OUT/certificates/cas_s63/"; done
if grep -q '{{' "$V/correspondence/LETTER_GATE33.md"; then
  echo "GATE letter: LETTER_GATE33.md still carries unfilled {{...}} tokens"; exit 1; fi
# s64: the Gate-34 checklist and the s64 CAS legs / probe / intake facts cited by LETTER_GATE34.
for f in GATE34_CHECKLIST.md; do
  need "$V/correspondence/$f"; cp "$V/correspondence/$f" "$OUT/correspondence/"; done
mkdir -p "$OUT/certificates/cas_s64"
for f in leg1_s64.py leg1_s64.log leg2_s64.sage leg2_s64.log probe_gate34.lean probe_gate34.log facts_gate34.log coverage_gate34.log excerpts_gate34.log; do
  need "$V/certificates/cas_s64/$f"; cp "$V/certificates/cas_s64/$f" "$OUT/certificates/cas_s64/"; done
if grep -q '{{' "$V/correspondence/LETTER_GATE34.md"; then
  echo "GATE letter: LETTER_GATE34.md still carries unfilled {{...}} tokens"; exit 1; fi
for f in manuscript/PROOF_NOTE_DIMENSION.md certificates/cas_s48/verify_gate22_s48.py \
         certificates/cas_s48/verify_gate22_s48.log \
         certificates/cas_s48/collision_check_s48.py \
         certificates/cas_s48/collision_check_s48.log \
         correspondence/GATE22_CHECKLIST.md correspondence/GATE23_CHECKLIST.md correspondence/GATE24_CHECKLIST.md \
         certificates/cas_s52/rederive_gate23_s52.log certificates/cas_s52/rederive_gate23_isotropic_pell_s52.log \
         certificates/cas_s54/rederive_gate24_s54.log certificates/cas_s54/rederive_gate24_s54_sage.log \
         correspondence/GATE25_CHECKLIST.md certificates/cas_s55/leg1.log certificates/cas_s55/leg2.log \
         certificates/cas_s55/symmetry_certificate_checker.log \
         certificates/own_s55/round2/totality_decision.log certificates/own_s55/round2/rank2_mechanism.log \
         certificates/own_s55/round3/least_certificate_prime.log \
         correspondence/GATE26_CHECKLIST.md \
         certificates/cas_s56/leg1_s56.log certificates/cas_s56/leg2_leg2d.log \
         certificates/cas_s56/norm_blindspot_scope.log certificates/cas_s56/source_evidence_check.log \
         correspondence/GATE27_CHECKLIST.md correspondence/C1_TCER_CROSSWALK_s57.md manuscript/PROOF_NOTE_NF.md \
         certificates/cas_s57/leg1_s57.log certificates/cas_s57/leg2_s57.log certificates/cas_s57/eichler_check.log \
         certificates/cas_s57/source_evidence_check_s57.log certificates/cas_s57/plant_A6A7_s57.log \
         correspondence/GATE28_CHECKLIST.md correspondence/C1_TCER_CROSSWALK_s58.md correspondence/TCER_ADAPTER_s58.md \
         certificates/cas_s58/leg1_s58.log certificates/cas_s58/leg2_s58.log certificates/cas_s58/d3_table.log \
         certificates/cas_s58/plant_A9A12_s58.log \
         correspondence/GATE29_CHECKLIST.md correspondence/RELATED_WORK_R48_s59.md correspondence/D4_RESTRUCTURE_PLAN_s59.md \
         certificates/cas_s59/leg1_s59.log certificates/cas_s59/leg2b_s59.log certificates/cas_s59/plant_A13A15_s59.log \
         correspondence/GATE30_CHECKLIST.md correspondence/RELATED_WORK_R49_s60.md \
         certificates/cas_s60/leg1_s60.log certificates/cas_s60/leg2_s60.log certificates/cas_s60/plant_P1618_s60.log \
         correspondence/GATE31_CHECKLIST.md \
         certificates/cas_s61/leg1_s61.log certificates/cas_s61/leg2_s61.log certificates/cas_s61/probe_gate31.log \
         correspondence/GATE32_CHECKLIST.md \
         certificates/cas_s62/leg1_s62.log certificates/cas_s62/leg2_s62.log certificates/cas_s62/probe_gate32.log \
         correspondence/GATE33_CHECKLIST.md \
         certificates/cas_s63/leg1_s63.log certificates/cas_s63/leg2_s63.log certificates/cas_s63/probe_gate33.log \
         certificates/cas_s63/probe_gate33b.log certificates/cas_s63/facts_gate33.log certificates/cas_s63/excerpts_gate33.log \
         correspondence/GATE34_CHECKLIST.md \
         certificates/cas_s64/leg1_s64.log certificates/cas_s64/leg2_s64.log certificates/cas_s64/probe_gate34.log \
         certificates/cas_s64/facts_gate34.log certificates/cas_s64/coverage_gate34.log certificates/cas_s64/excerpts_gate34.log; do
  need "$OUT/$f"; done
say "CITED_ARTIFACTS_SHIPPED=OK (proof note + s48 CAS pair + logs + Gate-22 checklist)"

# --- 3c. CITATION.cff: ONE source of truth, copied to both places, then gated (S01)
need "$V/release/CITATION.cff"
cp "$V/release/CITATION.cff" "$OUT/release/CITATION.cff"
cp "$V/release/CITATION.cff" "$OUT/CITATION.cff"
if ! cmp -s "$OUT/CITATION.cff" "$OUT/release/CITATION.cff"; then
  echo "GATE CITATION: root and release copies differ"; exit 1; fi
echo "CITATION_ROOT_EQ_RELEASE=OK"

# --- 3c-bis (s63, R-9 / R-7, ruling 21:59 "前例でOK"): the licence files and the CI workflow come from the working
# package, not from BASE (the r51 tree carries the Apache-2.0 text and a CI that neither builds nor audits ResearchUpgrade).
for f in LICENSE LICENSING.md; do need "$V/$f"; cp "$V/$f" "$OUT/$f"; cp "$V/$f" "$OUT/release/$f"; done
need "$V/release/github_workflows/ci.yml"; mkdir -p "$OUT/release/github_workflows"
cp "$V/release/github_workflows/ci.yml" "$OUT/release/github_workflows/ci.yml"
if ! grep -q '^MIT License' "$OUT/LICENSE" || ! cmp -s "$OUT/LICENSE" "$OUT/release/LICENSE"; then echo "GATE LICENSE: not the MIT text in both places"; exit 1; fi
if ! grep -q 'lake build ResearchUpgrade' "$OUT/release/github_workflows/ci.yml" || ! grep -q 'scripts/audit_ru.sh' "$OUT/release/github_workflows/ci.yml"; then
  echo "GATE CI: ResearchUpgrade build or audit missing from the workflow"; exit 1; fi
say "LICENSE_MIT=OK CI_RU_BUILD_AUDIT=OK"

# --- 3d. tools/: the two gate tools AND the four scanners the seal quotes (T07)
mkdir -p "$OUT/tools"
for f in gate5_verify.py fidelity_destroyer.py \
         proof_by_citation_scan.py manuscript_index.py detex_normalize.py m01_internal_refs.py \
         lettered_label_control.py cited_name_census.py statement_diff.py build_appendix_e_tex.py \
         parallel_prose_control.py font_preflight.py submission_figures.py \
         fresh_build_compare.py shipping_artifact_gate.py generate_seal.py generate_trust.py partition_check.py release_controls.py \
         md_to_native_tex.py native_statement_check.py \
         typeset_gate.py environment_preflight.py longtable_widths.py \
         paper_claims_check.py definition_fidelity.py native_mathmode.py proof_companion.py tex_to_md.py \
         paper_claims_controls.py crossref_semantic_check.py paper_claim_types.py manuscript_controls.py generate_signoff_sheet.py signoff_controls.py public_core_release.py public_core_controls.py \
         note_anchor_check.py gen_blueprint.py; do
  need "$W/scripts/$f"; cp "$W/scripts/$f" "$OUT/tools/"; done
NT=$(ls -1 "$OUT"/tools/*.py | wc -l | tr -d ' ')
if [ "$NT" != "39" ]; then echo "GATE tools: expected 39, found $NT"; exit 1; fi   # s53: + note_anchor_check.py; s63: + gen_blueprint.py
say "TOOLS_SHIPPED=OK n=$NT"
# s35, second finding of the first dry run: dropping the superseded disposition file from the list
# of things this script COPIES did not stop it shipping, because $OUT is built from the previous
# package and inherits it.  Session-stamped LOGS are records of runs that happened and stay; a
# superseded disposition file is an INPUT a reader could feed to the destroyer and get a different
# verdict, which is the whole of Gate-9 G07.  Removed by name, not by a sweep of session stamps.
rm -f "$OUT"/certificates/fidelity_destroyer_s*_shipping.tsv
need "$W/certificates/fidelity_destroyer_current.tsv"
cp "$W/certificates/fidelity_destroyer_current.tsv" "$OUT/certificates/"
NDISP=$(ls -1 "$OUT"/certificates/fidelity_destroyer*.tsv | wc -l | tr -d " ")
if [ "$NDISP" != "1" ]; then echo "GATE dispositions: expected 1, found $NDISP"; exit 1; fi
say "DISPOSITIONS_SHIPPED=OK n=$NDISP"

# --- clean-room attestation (s35).  history/certificates/ shows the discipline this project used
# to keep: r24 ships fresh_build_r24.log and fresh_build_r24_studio.log with the SAME source-manifest
# sha, and so does r25 -- two machines, one tree, an attestation worth the name.  r26 has a pair too.
# r29 and r30 have none: one machine each, and the r26 pair was left sitting in certificates/ where
# it read as if the current attestation had two environments.  Nobody compared the shas because
# comparing them was a person's job.  Below it is the script's.
# s35, third attempt, and the first two are worth keeping in view.  (1) Reading the sha out of a log
# chosen by NAME ("fresh_build_r30.log") breaks the first time the round number moves.  (2) Recomputing
# it here from the shipped tree gave a different value than the log -- fresh_build.sh's manifest also
# covers build metadata beyond the three source directories, so the reimplementation was not the same
# rule.  Two wrong ways to learn that a check must use the artifact's own instrument, not a copy of it.
# The clean room $FRESH is what this script copies lean/ from; its log is the current one by
# construction, so read it from there.
# s35: the gate below ran before this copy did, so it judged a certificates/ that had no current
# record and failed correctly on a package that was fine.  An ordering bug in a gate reads exactly
# like the defect it looks for.  Place the records first, then judge them.
mkdir -p "$OUT/certificates"
for f in $FRESH_LOGS; do cp "$f" "$OUT/certificates/$(basename "$f")"; done
SHIP_SHA=$(grep -o 'SRC_MANIFEST_SHA256=[0-9a-f]*' "$FRESH"/fresh_build*.log 2>/dev/null | tail -1 | sed 's/.*=//')
if [ -z "$SHIP_SHA" ]; then echo "GATE clean-room: could not compute the shipped tree manifest"; exit 1; fi
mkdir -p "$OUT/history/certificates"
CUR=0; STALE=0
for f in "$OUT"/certificates/fresh_build_*.log; do
  [ -e "$f" ] || continue
  s=$(grep -o 'SRC_MANIFEST_SHA256=[0-9a-f]*' "$f" | tail -1 | cut -d= -f2)
  if [ "$s" = "$SHIP_SHA" ]; then CUR=$((CUR+1))
  else mv "$f" "$OUT/history/certificates/"; STALE=$((STALE+1)); fi
done
say "CLEANROOM_CURRENT=$CUR  CLEANROOM_AGED_OUT=$STALE  SHIPPED_TREE_SHA=${SHIP_SHA:0:8}"
# s62 (GATE32 P0, R-1): name the clean-room log of record for the shipped source.  The log is kept byte for byte under
# its original name (no copy, no re-dating); the public core's own gate checks it against lean/.
REFLOG=""; for f in "$OUT"/certificates/fresh_build_*.log; do
  [ -e "$f" ] || continue; if grep -qx "SRC_MANIFEST_SHA256=$SHIP_SHA" "$f"; then REFLOG="$f"; break; fi; done
if [ -z "$REFLOG" ]; then echo "CLEANROOM_REFERENCE=FAIL (no shipped log names SRC_MANIFEST_SHA256=$SHIP_SHA)"; exit 1; fi
REFB=$(basename "$REFLOG"); REFROUND=$(echo "$REFB" | sed -nE 's/^fresh_build_(r[0-9]+).*$/\1/p'); REFENV=$(sed -n '3p' "$REFLOG")
if [ -z "$REFROUND" ] || [ -z "$REFENV" ]; then echo "CLEANROOM_REFERENCE=FAIL (round or environment unreadable in $REFB)"; exit 1; fi
if [ "${MPUP_LEAN_UNCHANGED:-}" = "1" ]; then NEWB=no; else NEWB=yes; fi
{ echo "# CLEANROOM_REFERENCE - the clean-room record of the Lean source shipped in this package (written by the assembler)."
  echo "# The log is kept byte for byte under its original name.  A round that does not change the Lean source reuses the"
  echo "# earlier run's log and does not re-date it.  Checked by tools/public_core_release.py --verify (evidence consistency"
  echo "# only: the check does not run Lean)."
  echo "original_name=certificates/$REFB"
  echo "build_round=$REFROUND"
  echo "shipped_in_round=$ROUND"
  echo "environment=$REFENV"
  echo "new_build_performed_for_round=$NEWB"
  echo "log_sha256=$(shasum -a 256 "$REFLOG" | cut -d' ' -f1)"
  echo "source_manifest=certificates/source_manifest_$ROUND.sha256"
  echo "source_manifest_sha256=$SHIP_SHA"
} > "$OUT/certificates/CLEANROOM_REFERENCE.txt"
say "CLEANROOM_REFERENCE=written log=$REFB round=$REFROUND environment=$REFENV new_build=$NEWB"
if [ "$CUR" -lt 1 ]; then echo "CLEANROOM_GATE=FAIL (no clean-room record matches the shipped tree)"; exit 1; fi
if [ "$CUR" -lt 2 ]; then
  echo "CLEANROOM_GATE=SINGLE_ENVIRONMENT ($CUR record for the shipped tree; r24, r25 and r26 shipped two)"
  if [ "${MPUP_ALLOW_SINGLE_ENV:-}" != "1" ]; then
    echo "CLEANROOM_GATE=FAIL (set MPUP_ALLOW_SINGLE_ENV=1 to seal on one machine, and say so in the letter)"; exit 1; fi
  say "CLEANROOM_GATE=OK (single environment, explicitly allowed)"
  # s53: the seal template requires this field; with one record there is nothing to compare.
  # Never exercised since r26, so the single-environment branch left the token unfilled.
  say "FRESH_BUILD_COMPARE_DIFFS=none_single_environment"
else
  # every current record must also agree field by field, not merely on the source sha
  FIRST=""; for f in "$OUT"/certificates/fresh_build_*.log; do
    s=$(grep -o 'SRC_MANIFEST_SHA256=[0-9a-f]*' "$f" | tail -1 | cut -d= -f2)
    [ "$s" = "$SHIP_SHA" ] || continue
    if [ -z "$FIRST" ]; then FIRST="$f"; else
      python3 "$OUT/tools/fresh_build_compare.py" "$FIRST" "$f" | tail -2 | tee -a "$AG"
      python3 "$OUT/tools/fresh_build_compare.py" "$FIRST" "$f" > /dev/null ||         { echo "CLEANROOM_GATE=FAIL (two records for the same tree disagree)"; exit 1; }
    fi; done
  say "CLEANROOM_GATE=OK (two or more environments, fields agree)"
fi

# --- 4. correspondence.  The seal is generated at step 7e, not copied.  Superseded seals leave
# correspondence/ for history/seals/ (Z08): a seal is a claim about ONE package, and six of them
# side by side let a reader pick the wrong one.  Invalidation records travel with them.
for f in $CORRESPONDENCE; do
  need "$V/correspondence/$f"; cp "$V/correspondence/$f" "$OUT/correspondence/"; done
# s40 (Gate-14 P13): every earlier reader report is refreshed from the vault, where it now carries
# REVIEW_STATUS=STALE; an inherited untagged copy must not survive here.
for f in BLANK_SLATE_REVIEW_V30_20260901.md BLANK_SLATE_REVIEW_V31.md; do
  if [ -f "$OUT/correspondence/$f" ]; then need "$V/correspondence/$f"; cp "$V/correspondence/$f" "$OUT/correspondence/$f"; fi; done
mkdir -p "$OUT/history/seals"
for s in "$OUT"/correspondence/SEAL_r*.txt; do [ -e "$s" ] && mv "$s" "$OUT/history/seals/"; done
for f in "$V"/history/seals/SEAL_*_INVALIDATED.md; do [ -e "$f" ] && cp "$f" "$OUT/history/seals/"; done
say "SEALS_AGED_OUT=$(ls -1 "$OUT"/history/seals/SEAL_r*.txt | wc -l | tr -d ' ')"
need "$V/correspondence/README_$ROUND.md"
cp "$V/correspondence/README_$ROUND.md" "$OUT/README.md"
# s38 (Gate-12 H01): the development history leaves release/TRUST_BOUNDARY_APAL.md and ships here.
need "$V/history/DEVELOPMENT_AUDIT_HISTORY.md"
cp "$V/history/DEVELOPMENT_AUDIT_HISTORY.md" "$OUT/history/DEVELOPMENT_AUDIT_HISTORY.md"
say "DEVELOPMENT_HISTORY_SHIPPED=OK"

# --- 3e. frozen_statements REPLACED, and the build's inputs shipped (B01/F01)
rm -rf "$OUT/frozen_statements"; mkdir -p "$OUT/frozen_statements"
cp "$W"/frozen_statements/*_STATEMENTS.lean "$OUT/frozen_statements/"
NF=$(ls -1 "$OUT"/frozen_statements/*_STATEMENTS.lean | wc -l | tr -d ' ')
if [ "$NF" != "59" ]; then echo "GATE frozen_statements: expected 59, found $NF"; exit 1; fi   # s50: 58 -> 59, the third library freezes ResearchUpgrade_STATEMENTS.lean
say "FROZEN_SHIPPED=OK n=$NF"
for f in FinalAxiomReport_current.log statement_diff_current.log binder_ledger_current.log \
         APPENDIX_C_AXIOM_REPORT.log APPENDIX_C_STATEMENT_FIDELITY.log definition_bodies_current.tsv \
         PaperClaimTypeReport_current.log PAPER_CLAIM_LEAN_TYPES.tsv; do
  need "$W/certificates/$f"; cp "$W/certificates/$f" "$OUT/certificates/"; done
say "BUILD_INPUTS_SHIPPED=OK"
# --- 3f. TRUST generated from its template and the certificates just shipped (Z06)
rm -f "$OUT"/certificates/ROOT_FROZEN_RECONCILIATION_s30.md
( cd "$OUT" && python3 tools/generate_trust.py . | tee -a "$AG" ) || { echo "GENERATE_TRUST=FAIL"; exit 1; }
need "$OUT/release/TRUST_BOUNDARY_APAL.md"

# --- 4b. the blank-slate reports of r28's round travel with the package (R01-R04 were not re-run
# this round, by the standing ruling that they wait until the items above are closed).
# s36 (Z08): the reports carry REVIEW_STATUS=STALE / REVIEWED_MANUSCRIPT_SHA256 now, written in the
# vault; the package copy is refreshed from the vault rather than inherited (same file set, minus a
# nohup log that never shipped).
rm -rf "$OUT/referee_simulation"; cp -R "$V/referee_simulation" "$OUT/referee_simulation"
rm -f "$OUT"/referee_simulation/*.nohup.log
NSTALE=$(grep -l '^REVIEW_STATUS=STALE' "$OUT"/referee_simulation/s31/REPORT_*.md | wc -l | tr -d ' ')
say "REVIEW_REPORTS_TAGGED_STALE=$NSTALE"
needd "$OUT/referee_simulation/s31"
NR=$(ls -1 "$OUT"/referee_simulation/s31/REPORT_*.md 2>/dev/null | wc -l | tr -d ' ')
if [ "$NR" != "5" ]; then echo "GATE referee_simulation/s31: expected 5 reports, found $NR"; exit 1; fi
NP=$(ls -1 "$OUT"/referee_simulation/s31/READ*_manuscript_*.pdf 2>/dev/null | wc -l | tr -d ' ')
if [ "$NP" != "2" ]; then echo "GATE referee_simulation/s31: expected 2 read PDFs, found $NP"; exit 1; fi
echo "BLANK_SLATE_IN_PACKAGE=OK reports=$NR pdfs=$NP"
NUNTAGGED=$(grep -L '^REVIEW_STATUS=STALE' "$OUT"/correspondence/BLANK_SLATE_REVIEW_*.md "$OUT"/referee_simulation/*.md "$OUT"/referee_simulation/r18/*.md "$OUT"/referee_simulation/s31/REPORT_*.md 2>/dev/null | wc -l | tr -d ' ')
if [ "$NUNTAGGED" != 0 ]; then echo "GATE stale reports: $NUNTAGGED earlier reader report(s) not tagged REVIEW_STATUS=STALE"; exit 1; fi
say "EARLIER_READER_REPORTS_STALE=OK untagged=0"

# --- 5. literature
for f in NOVELTY_FINAL_GATE_s30.md GS_CROSSWALK.md L01_PRIMARY_SOURCE_s39.md; do
  need "$V/literature/$f"; cp "$V/literature/$f" "$OUT/literature/"; done

# --- 6. certificates and the typeset build
# s35: fidelity_destroyer_s30_shipping.tsv removed from this list (Gate-9 G07) -- it was the
# superseded disposition file and shipping it beside the current one left a reader guessing.
for f in APAL_STATEMENT_MAP.tsv gate5_crosswalk_s30.tsv \
         gate5_verify_s30.tsv GATE5_CHECKLIST_s30.md ROOT_FROZEN_RECONCILIATION_s30.md; do
  need "$W/certificates/$f"; cp "$W/certificates/$f" "$OUT/certificates/"; done
mkdir -p "$OUT/development_notes" "$OUT/papers/apal_build"
for f in README.md OneWitnessNormalForm_STATEMENTS_v3.lean; do
  need "$V/development_notes/$f"; cp "$V/development_notes/$f" "$OUT/development_notes/"; done
# s34: locators.txt and fill_counts.py were NOT shipped before. The package-only build found it
# at once -- the build died on a missing locators.txt, and the fill_counts.py it inherited from r29
# did not know the BROOTS token, so the binder figures would have survived as placeholders. A
# self-containment check is only worth what it catches, and this is what it caught.
for f in build.sh preamble.tex locators.txt BUILD_ENVIRONMENT.txt APAL_MANUSCRIPT_v32.log; do
  need "$V/papers/apal_build/$f"; cp "$V/papers/apal_build/$f" "$OUT/papers/apal_build/"; done
need "$V/manuscript/fill_counts.py"; cp "$V/manuscript/fill_counts.py" "$OUT/manuscript/"

# --- 6a. lean/ REBUILT, not inherited. The tree comes from the clean-room directory, so the bytes
# that ship are the bytes that were built and audited there.
rm -rf "$OUT/lean"
cp -R "$FRESH_LEAN" "$OUT/lean"
rm -rf "$OUT/lean/.lake" "$OUT/lean/logs"
rm -f "$OUT/lean/lake-manifest.json" "$OUT/lean/source_manifest.sha256"
# s55: a cold room launched with a bare `nohup` leaves an empty nohup.out beside fresh_build.sh.
rm -f "$OUT/lean/nohup.out"
cp "$FRESH_LEAN/source_manifest.sha256" "$OUT/certificates/source_manifest_$ROUND.sha256"
# (moved earlier, before the clean-room gate: s35)

# --- 6b. SWEEP: migrate round-stamped files out of the shipping directories. Moves only.
mkdir -p "$OUT/history/submission" "$OUT/history/release"
for d in "$OUT"/manuscript/*_parts; do
  [ -e "$d" ] || continue
  mkdir -p "$OUT/history/manuscript"
  [ -d "$d" ] || continue
  mv "$d" "$OUT/history/manuscript/"
done
for f in APAL_MANUSCRIPT.tex APAL_MANUSCRIPT_r17_skeleton.pdf xelatex_build_r17.log AI_DISCLOSURE.md; do
  if [ -f "$OUT/submission/$f" ]; then mv "$OUT/submission/$f" "$OUT/history/submission/"; fi; done
for f in RELEASE_CHECKLIST.md PUBLIC_ARTIFACT_SPLIT_r17.md PUBLIC_ARTIFACT_SPLIT_r18.md \
         PRE_SUBMISSION_RED_TEAM_SUMMARY.md; do
  if [ -f "$OUT/release/$f" ]; then mv "$OUT/release/$f" "$OUT/history/release/"; fi; done
for a in "$OUT"/release/assemble_r*.sh; do
  [ -e "$a" ] || continue
  case "$(basename "$a")" in assemble_$ROUND.sh) ;; *) mv "$a" "$OUT/history/release/" ;; esac
done

# --- 6c. STALENESS GATE: whitelist over the shipping directories. Detects; never repairs.
# s57: PROOF_NOTE_NF.md (the proof note Propositions A.6/A.7 cite) joins it on the same terms.
# s51: PROOF_NOTE_DIMENSION.md joins the manuscript/ whitelist.  It is NOT a second manuscript and
# does not weaken the r26 protection: that protection is the `NM != 1` count above, which counts
# MANUSCRIPT_V*.md only.  The note is the companion proof document that Theorem 4.2's proof calls
# "deposited with the artifact" -- r40 shipped the citation without the file (E-22-3), so step
# 3b-bis now copies it and fails closed on it.  A file that a gate requires and another gate
# forbids is the shape of this round's own erratum, caught here by the second gate.
# s36: the generators that ran above import each other, so tools/__pycache__ exists by now and a
# .pyc embeds the absolute path of the machine that compiled it; the absolute-path scan below read
# that as shipped machinery (first real assembly).  Byte-code is not shipped; it is removed here
# and again before the checksums.
find "$OUT" -name '__pycache__' -type d -exec rm -rf {} + 2>/dev/null || true
BAD=0
NM=$(ls -1 "$OUT"/manuscript/MANUSCRIPT_V*.md 2>/dev/null | wc -l | tr -d ' ')
if [ "$NM" != "1" ]; then echo "GATE manuscript: expected 1 manuscript, found $NM"; BAD=1; fi
for f in "$OUT"/manuscript/*; do
  case "$(basename "$f")" in
    MANUSCRIPT_V32.md|APPENDIX_E_STATEMENT_MAP.md|\
    PROOF_NOTE_DIMENSION.md|PROOF_NOTE_NF.md|\
    DEPENDENCY_CLOSURE_ALL_R.md|FALLBACK_FINITE_SIDE_V31.md|\
    PROOF_ARCHITECTURE_ALL_R.md|\
    QUADRATIC_UNIVERSALITY_CAPACITY.md|fill_counts.py|gen_appendix_e.py|\
    gen_appendix_e_numbered.py) ;;
    *) echo "GATE manuscript: unexpected $(basename "$f")"; BAD=1 ;;
  esac
done
for f in "$OUT"/submission/*; do
  case "$(basename "$f")" in
    APAL_COVER_LETTER_v1.md|APAL_SUBMISSION_CHECKLIST_v1.md|\
    APAL_MANUSCRIPT_v32.pdf|APAL_MANUSCRIPT_v32.tex|tex|native|CANONICAL_SOURCE) ;;
    *) echo "GATE submission: unexpected $(basename "$f")"; BAD=1 ;;
  esac
done
NA=$(ls -1 "$OUT"/release/assemble_r*.sh 2>/dev/null | wc -l | tr -d ' ')
if [ "$NA" != "1" ]; then echo "GATE release: expected 1 assembler, found $NA"; BAD=1; fi
# the retired title is assembled from fragments: a scanner must not contain its own search term
OLDT="Quadratic Diophantine ""Definitions of ""Injective Graphs"
HITS=$(grep -rl "$OLDT" "$OUT/manuscript" "$OUT/submission" "$OUT/release" 2>/dev/null || true)
if [ -n "$HITS" ]; then echo "GATE old title in a shipping directory:"; echo "$HITS"; BAD=1; fi
# No absolute path may ship in the machinery (T08). The seal quotes this number. The pattern is
# assembled from fragments for the same reason the retired title above is: a scanner that contains
# its own search term reports itself and the gate becomes unpassable (found on the first run).
APAT="/Us""ers/"
AP=$(grep -rl "$APAT" "$OUT/release" "$OUT/tools" "$OUT/papers" 2>/dev/null || true)
if [ -n "$AP" ]; then echo "GATE absolute path in shipped machinery:"; echo "$AP"; BAD=1; fi
if [ "$BAD" != "0" ]; then echo "STALENESS_GATE=FAIL"; exit 1; fi
echo "STALENESS_GATE=OK"

# --- 7. manifest gate: the shipped lean/ must hash to the manifest of the clean-room build
( cd "$OUT/lean" && { find MPUP DiophCompression ResearchUpgrade scripts -type f \( -name '*.lean' -o -name '*.py' -o -name '*.sh' \) -print0; \
    printf '%s\0' MPUP.lean DiophCompression.lean ResearchUpgrade.lean lakefile.lean lean-toolchain; } \
  | LC_ALL=C sort -z | xargs -0 shasum -a 256 | awk '{print $1"  "$2}' > "$OUT/certificates/pkg_manifest_$ROUND.sha256" )
if cmp -s "$OUT/certificates/pkg_manifest_$ROUND.sha256" "$OUT/certificates/source_manifest_$ROUND.sha256"; then \
  say "MANIFEST_MATCH=OK (shipped lean/ == the tree the clean-room built)"; \
  else echo "MANIFEST_MATCH=FAIL"; \
  diff "$OUT/certificates/pkg_manifest_$ROUND.sha256" "$OUT/certificates/source_manifest_$ROUND.sha256" | head -20; exit 1; fi
# The previous round's manifest is compared in the direction the round declares.  A round that
# changed Lean must differ from it; a round that did not (MPUP_LEAN_UNCHANGED=1) must equal it.
PREV_MAN=$(ls -1 "$OUT"/certificates/source_manifest_r*.sha256 | grep -v "_$ROUND.sha256" | sort -V | tail -1)
if [ -z "$PREV_MAN" ]; then echo "GATE manifest: no previous manifest to compare"; exit 1; fi
if [ "${MPUP_LEAN_UNCHANGED:-}" = "1" ]; then
  if cmp -s "$OUT/certificates/pkg_manifest_$ROUND.sha256" "$PREV_MAN"; then
    say "MANIFEST_PREV=EQUAL ($(basename "$PREV_MAN"); Lean source unchanged this round, as declared)"
  else echo "MANIFEST_PREV=FAIL (declared unchanged, but lean/ differs from $(basename "$PREV_MAN"))"; exit 1; fi
  LEAN_CHANGE_STATEMENT="unchanged-since-$(basename "$PREV_MAN" .sha256 | sed 's/source_manifest_//')-manifest-identical"
else
  if cmp -s "$OUT/certificates/pkg_manifest_$ROUND.sha256" "$PREV_MAN"; then
    echo "MANIFEST_PREV=FAIL (identical to $(basename "$PREV_MAN") -- this round's Lean changes are missing)"; exit 1; fi
  say "MANIFEST_PREV=DIFFERS ($(basename "$PREV_MAN"); lean/ changed this round)"
  LEAN_CHANGE_STATEMENT="changed-since-$(basename "$PREV_MAN" .sha256 | sed 's/source_manifest_//')"
fi
say "LEAN_CHANGE_STATEMENT=$LEAN_CHANGE_STATEMENT"
rm -f "$OUT/certificates/pkg_manifest_$ROUND.sha256"

# --- 7b. the two gates must pass ON THE ASSEMBLED PACKAGE (T03/T04)
( cd "$OUT" && python3 tools/gate5_verify.py "$OUT" > "$OUT/gate5_tail.tmp" ) || { tail -8 "$OUT/gate5_tail.tmp"; echo "GATE5=FAIL"; exit 1; }
tail -5 "$OUT/gate5_tail.tmp"
G5=$(grep -o 'ITEMS=[0-9]*  PASS=[0-9]*  FAIL=[0-9]*' "$OUT/gate5_tail.tmp" | tail -1)
say "GATE5_ITEMS=$(printf '%s' "$G5" | sed 's/.*ITEMS=\([0-9]*\).*/\1/') GATE5_PASS=$(printf '%s' "$G5" | sed 's/.*PASS=\([0-9]*\).*/\1/') GATE5_FAIL=$(printf '%s' "$G5" | sed 's/.*FAIL=\([0-9]*\).*/\1/') GATE5_DEFERRED=$(grep -o 'DEFERRED=[0-9]*' "$OUT/gate5_tail.tmp" | tail -1 | cut -d= -f2) ABSOLUTE_PATHS=$(grep -o 'ABSOLUTE_PATHS=[0-9]*' "$OUT/gate5_tail.tmp" | tail -1 | cut -d= -f2)"
rm -f "$OUT/gate5_tail.tmp"
( cd "$OUT" && python3 tools/fidelity_destroyer.py "$OUT" --shipping-only \
    --dispositions certificates/fidelity_destroyer_current.tsv | tail -3 | tee -a "$AG" ) \
  || { echo "DESTROYER=FAIL"; exit 1; }
( cd "$OUT" && cp -R frozen_statements lean/frozen_statements 2>/dev/null || true )
( cd "$OUT" && python3 tools/cited_name_census.py manuscript/MANUSCRIPT_V32.md --lean-root lean --says release/TRUST_BOUNDARY_APAL.md \
    | grep -E 'OUTSIDE_FROZEN|OUTSIDE_BUT_ROOT|COVERED_BY_NEITHER|CENSUS_EXIT' | tee -a "$AG" ) \
  || { echo "CENSUS=FAIL"; exit 1; }
( cd "$OUT" && python3 tools/parallel_prose_control.py "$OUT" \
    | grep -E 'DECLARED_COMPANIONS=|NEAR_MISS_TOP5|TRIGGER_MARGIN|PARALLEL_PROSE_FILES|PARALLEL_PROSE_CONTROL' | tee -a "$AG" ) \
  || { echo "PARALLEL_PROSE=FAIL"; exit 1; }
( cd "$OUT" && python3 tools/lettered_label_control.py manuscript/MANUSCRIPT_V32.md --root "$OUT" \
    | grep -E 'POSITIVE_FOUND|OLD_PATTERN_FOUND|NEGATIVE_DROP|PATTERN_FILES_AGREE|LETTERED_CONTROL_EXIT' | tee -a "$AG" ) \
  || { echo "LETTERED=FAIL"; exit 1; }
rm -rf "$OUT/lean/frozen_statements"
# s42 (Gate-16 P0-1 / P0-2): the paper-claim registry gate, its fourteen planted controls and the six
# sign-off carry-over controls run ON the assembled package; ONE_ROOT_LABELS and SIGNOFF_CONTROLS reach the seal.
( cd "$OUT" && python3 tools/paper_claims_check.py "$OUT" --native submission/native \
    | grep -E 'FORMAL_CLAIMS|REVIEW_ROWS|ONE_ROOT_LABELS|PAPER_CLAIMS' | tee -a "$AG" ) \
  || { echo "PAPER_CLAIMS=FAIL"; exit 1; }
( cd "$OUT" && python3 tools/paper_claims_controls.py "$OUT" --native submission/native \
    | grep -E 'MISSED|NEGATIVE_CONTROLS' | tee -a "$AG" ) \
  || { echo "PAPER_CLAIMS_CONTROLS=FAIL"; exit 1; }
( cd "$OUT" && python3 tools/signoff_controls.py "$OUT" --native submission/native \
    | grep -E '^FAIL|SIGNOFF_CONTROLS' | tee -a "$AG" ) \
  || { echo "SIGNOFF_CONTROLS=FAIL"; exit 1; }
# s43 (Gate-17 FIX-01): the eight planted SHA256SUMS defects that the fail-closed core gate must refuse,
# run on the shipped copy of the tool (temp archives only; no package file is read or written).
( cd "$OUT" && python3 tools/public_core_controls.py \
    | grep -E '^FAIL|CORE_CHECKSUM_CONTROLS' | tee -a "$AG" ) \
  || { echo "CORE_CHECKSUM_CONTROLS=FAIL"; exit 1; }
say "PACKAGE_GATES=OK"

# --- 7c. THE BUILD, INSIDE THE DISTRIBUTION ROOT (Z02).  What ships is what this build wrote.
( cd "$OUT" && bash release/build_submission_from_package.sh "$BUILD_MODE_PKG" 2>&1 | tee "$OUT/PACKAGE_BUILD.log" | tail -25 )
PB_EXIT=$(grep -o 'PACKAGE_BUILD_EXIT=[0-9]*' "$OUT/PACKAGE_BUILD.log" | tail -1 | cut -d= -f2)
if [ "$PB_EXIT" != "0" ]; then echo "PACKAGE_BUILD=FAIL (exit $PB_EXIT)"; exit 1; fi
need "$OUT/SHIPPING_MEASUREMENTS.txt"
for k in GENERATED_PDF_EQ_SHIPPED GENERATED_TEX_EQ_SHIPPED NEW_PDF_CREATED; do
  grep -q "^$k=1\$" "$OUT/SHIPPING_MEASUREMENTS.txt" || { echo "PACKAGE_BUILD=FAIL ($k != 1)"; exit 1; }; done
rm -rf "$OUT/lean/frozen_statements"
say "PACKAGE_BUILD_IN_ROOT=OK mode=$BUILD_MODE_PKG"
# s39: the package build just wrote raw engine logs with absolute paths (the r34 leak).  The shipped
# engine log is papers/apal_build/APAL_MANUSCRIPT_v32.log, already scrubbed by build.sh; the raw
# passes and the scratch tree are removed, and the absolute-path scan is run a second time, after
# the build, over the same three directories the staleness gate covers.
for f in pass1.log pass2.log pct_scratch; do rm -rf "$OUT/papers/apal_build/$f"; done
find "$OUT/papers/apal_build/native_build" -name '*.log' -delete 2>/dev/null || true
find "$OUT" -name '__pycache__' -type d -exec rm -rf {} + 2>/dev/null || true
APAT2="/Us""ers/"
AP2=$(grep -rl "$APAT2" "$OUT/release" "$OUT/tools" "$OUT/papers" 2>/dev/null || true)
if [ -n "$AP2" ]; then echo "POST_BUILD_ABSPATH_GATE=FAIL"; echo "$AP2"; exit 1; fi
say "POST_BUILD_ABSPATH_GATE=OK (release/ tools/ papers/ scanned after the package build)"
# s40 (Gate-14 P01): the subscript scanner over the shipped TeX and the PDF text, after the build wrote them.
( cd "$OUT" && python3 tools/manuscript_controls.py . --scan --shipped | tee -a "$AG" ) || { echo "MANUSCRIPT_SHIPPED_SCAN=FAIL"; exit 1; }

# --- 7c-bis (s63, ruling 22:18): the Blueprint (papers/blueprint/), generated from the shipped native sources, the paper-claim
# registry and the statement map -- never by hand.  Generated twice and byte-compared (determinism); the citation graph is
# rendered to PDF when graphviz is present (the PDF is a rendering, not a record).
# s64: BASE (r52) already carries papers/blueprint/ including a rendered dep_graph.pdf; start from an empty directory so
# that no BASE file survives into this round and the determinism diff compares like with like (r53 dry run 2 failed here).
rm -rf "$OUT/papers/blueprint"
( cd "$OUT" && python3 tools/gen_blueprint.py . papers/blueprint | tee -a "$AG" ) || { echo "BLUEPRINT=FAIL"; exit 1; }
BPT=$(mktemp -d /tmp/mpup_bp.XXXXXX)
( cd "$OUT" && python3 tools/gen_blueprint.py . "$BPT" > /dev/null ) || { echo "BLUEPRINT=FAIL (second run)"; exit 1; }
if ! diff -r "$BPT" "$OUT/papers/blueprint" > /dev/null; then echo "BLUEPRINT_DETERMINISM=FAIL"; exit 1; fi
rm -rf "$BPT"
if command -v dot > /dev/null 2>&1; then dot -Tpdf "$OUT/papers/blueprint/dep_graph.dot" -o "$OUT/papers/blueprint/dep_graph.pdf" || { echo "BLUEPRINT_GRAPH=FAIL"; exit 1; }; fi
find "$OUT" -name '__pycache__' -type d -exec rm -rf {} + 2>/dev/null || true
say "BLUEPRINT_DETERMINISM=OK"

# --- 7d. the vault mirrors the package, not the other way round.  submission/ and the build log
# in the vault are refreshed FROM this build and compared; a vault copy that drifts is caught by
# the next assembly's PREEXISTING_SHIPPED_PDF_SHA256 line.
if [ "${MPUP_DRY_RUN:-}" = "1" ]; then
  say "VAULT_MIRROR=SKIPPED (MPUP_DRY_RUN=1; the vault is not written by a dry run)"
else
  for f in APAL_MANUSCRIPT_v32.pdf APAL_MANUSCRIPT_v32.tex; do
    cp "$OUT/submission/$f" "$V/submission/$f"; cmp -s "$OUT/submission/$f" "$V/submission/$f" || { echo "VAULT_MIRROR=FAIL $f"; exit 1; }; done
  cp "$OUT/papers/apal_build/APAL_MANUSCRIPT_v32.log" "$V/papers/apal_build/APAL_MANUSCRIPT_v32.log"
  cp "$OUT/release/TRUST_BOUNDARY_APAL.md" "$V/release/TRUST_BOUNDARY_APAL.md"
  cp "$OUT/release/README_BUILD_APAL.md" "$V/release/README_BUILD_APAL.md"
  cp "$OUT/release/RELEASE_CHECKLIST_APAL.md" "$V/release/RELEASE_CHECKLIST_APAL.md"
  cp "$OUT/release/AUTHOR_SIGNOFF_SHEET.md" "$V/release/AUTHOR_SIGNOFF_SHEET.md"
  cp "$OUT/certificates/ROOT_FROZEN_RECONCILIATION_current.md" "$W/certificates/ROOT_FROZEN_RECONCILIATION_current.md"
  say "VAULT_MIRROR=OK (submission/, build log, TRUST, reconciliation refreshed from the package)"
fi

# --- 7d2. PARTITION_RECORD (s40, Gate-14 P06).  The public split is computed on the assembled tree
# and recorded INSIDE the package before the file count is predicted, so the shipped artifact carries
# the evidence of its own partition; the two split archives are cut at step 11 from the SAME lists.
partition_lists() {  # $1 = root, $2 = out dir; writes all.lst core.lst hist.lst
  ( cd "$1" && find . -type f ! -name SHA256SUMS ! -name '*.bak*' ! -name '.DS_Store' ! -path '*/__pycache__/*' ! -path '*/logs/*' | LC_ALL=C sort > "$2/all.lst" \
    && grep -E '^\./(lean|frozen_statements|certificates|tools|submission|manuscript|papers|literature|mathematics|structural_theory)/|^\./(README\.md|CITATION\.cff|LICENSE|LICENSE-CC-BY-4\.0\.txt|LICENSING\.md|SHA256SUMS|ASSEMBLY_GATES\.log|PACKAGE_BUILD\.log|SHIPPING_MEASUREMENTS\.txt|SUBMISSION_INPUT_MANIFEST\.sha256|PARTITION_RECORD\.md)$|^\./release/(CITATION\.cff|LICENSE|LICENSE-CC-BY-4\.0\.txt|LICENSING\.md|PROOF_COMPANION\.md|APPENDIX_F_LEAN_ANCHORS\.md|APPENDIX_F_COVERAGE\.md|AUTHOR_SIGNOFF_SHEET\.md|README_BUILD_APAL\.md|README_BUILD_APAL\.template\.md|RELEASE_CHECKLIST_APAL\.md|RELEASE_CHECKLIST_APAL\.template\.md|SEAL\.template\.md|SEAL_INPUT\.env|SEAL_WHAT_IS_OPEN\.md|PUBLIC_CORE_EXCLUDE\.txt|PUBLIC_CORE_EXCLUDE\.template\.txt|STATEMENT_MAP_FULL\.md|TRUST_BOUNDARY_APAL\.md|TRUST_BOUNDARY_APAL\.template\.md|assemble_'"$ROUND"'\.sh|build_submission_from_package\.sh|fresh_build\.sh|lakefile\.lean|stage_build_inputs\.sh)$|^\./release/github_workflows/|^\./correspondence/SEAL_'"$ROUND"'\.txt$|^\./correspondence/(LETTER_GATE34|GATE34_CHECKLIST|REVIEW_GATE34_DISPOSITION_s64|ERRATA_R53_20260930|TCER_ADAPTER_s58|GPT_REVIEW_GATE34_20260930_[A-Za-z0-9_]+)\.md$' "$2/all.lst" > "$2/core0.lst" \
    && python3 -c 'import re,sys; P=[re.compile(l.strip()) for l in open(sys.argv[1],encoding="utf-8") if l.strip() and not l.startswith("#")]; K=[l for l in open(sys.argv[2],encoding="utf-8") if not any(p.match(l.rstrip("\n")[2:]) for p in P)]; open(sys.argv[3],"w",encoding="utf-8").write("".join(K))' release/PUBLIC_CORE_EXCLUDE.txt "$2/core0.lst" "$2/core.lst" \
    && grep -v -x -F -f "$2/core.lst" "$2/all.lst" > "$2/hist.lst" )
}
PREC=$(mktemp -d /tmp/mpup_prec.XXXXXX)
touch "$OUT/PARTITION_RECORD.md"   # listed in core by name; its bytes are written below
partition_lists "$OUT" "$PREC" || { echo "PARTITION_RECORD=FAIL (lists)"; exit 1; }
NALL0=$(wc -l < "$PREC/all.lst" | tr -d ' '); NCORE0=$(wc -l < "$PREC/core.lst" | tr -d ' '); NHIST0=$(wc -l < "$PREC/hist.lst" | tr -d ' ')
NDUP0=$(sort "$PREC/core.lst" "$PREC/hist.lst" | uniq -d | wc -l | tr -d ' ')
if [ $((NCORE0 + NHIST0)) -ne "$NALL0" ] || [ "$NDUP0" != 0 ]; then echo "PARTITION_RECORD=FAIL ($NCORE0 + $NHIST0 != $NALL0, dup=$NDUP0)"; exit 1; fi
if grep -qE '^\./(history|independent_reviews|referee_simulation|drafts|development_notes)/' "$PREC/core.lst"; then echo "PARTITION_RECORD=FAIL (history in core)"; exit 1; fi
{
  echo "# Partition record — public core / development history"
  echo
  echo "Generated by the assembler on the assembled tree, before the seal counted the package. The two archives"
  echo "APAL_PUBLIC_CORE_$NAME.zip and DEVELOPMENT_HISTORY_$NAME.zip are cut from the sealed zip using these"
  echo "same lists; their SHA-256 sums travel beside the zip in $NAME.split.sha256 (they cannot be inside it)."
  echo "SHA256SUMS and correspondence/SEAL_$ROUND.txt are added after this record and land in the public core; the split step verifies that the record equals the zip minus those two files."
  echo
  echo "| set | files |"; echo "|---|---|"
  echo "| package (at record time) | $NALL0 |"; echo "| public core | $NCORE0 |"; echo "| development history | $NHIST0 |"
  echo "| union == package | $([ $((NCORE0 + NHIST0)) -eq "$NALL0" ] && echo yes || echo no) |"; echo "| intersection | $NDUP0 |"
  echo; echo "## Public core"; echo; sed 's|^\./||' "$PREC/core.lst" | sed 's|^|- |'
  echo; echo "## Development history"; echo; sed 's|^\./||' "$PREC/hist.lst" | sed 's|^|- |'
} > "$OUT/PARTITION_RECORD.md"
rm -rf "$PREC"
say "PARTITION_RECORD=OK all=$NALL0 core=$NCORE0 history=$NHIST0 dup=$NDUP0"

# --- 7e. the seal, generated from what was measured above (Z04).  The package file count the seal
# quotes is predicted here: every file now present, plus the seal itself; step 8 checks it.
NPRED=$(( $(find "$OUT" -type f ! -name '*.bak*' ! -name '.DS_Store' ! -path '*/__pycache__/*' ! -path '*/logs/*' | wc -l | tr -d ' ') + 1 ))
say "PACKAGE_FILES_PREDICTED=$NPRED"
( cd "$OUT" && python3 tools/generate_seal.py . | tee -a "$AG" ) || { echo "GENERATE_SEAL=FAIL"; exit 1; }
need "$OUT/correspondence/SEAL_$ROUND.txt"
[ "${MPUP_DRY_RUN:-}" = "1" ] || cp "$OUT/correspondence/SEAL_$ROUND.txt" "$V/correspondence/SEAL_$ROUND.txt"

# --- 7f. the shipping gate, on the assembled root (Z03)
( cd "$OUT" && python3 tools/shipping_artifact_gate.py . ) || { echo "SHIPPING_ARTIFACT_GATE=FAIL (assembled root)"; exit 1; }
# s40 (Gate-14 §18): twelve planted release defects on temp copies of the assembled root; all must be caught.
( cd "$OUT" && python3 tools/release_controls.py "$OUT" | tee -a "$AG" | grep -E 'MISSED|RELEASE_CONTROLS' ) || { echo "RELEASE_CONTROLS=FAIL"; exit 1; }
find "$OUT" -name '__pycache__' -type d -exec rm -rf {} + 2>/dev/null || true

# --- 8. hygiene, checksums
find "$OUT" -name '*.bak*' -delete; find "$OUT" -name '.DS_Store' -delete
find "$OUT" -name '__pycache__' -type d -exec rm -rf {} + 2>/dev/null || true
find "$OUT" -name 'logs' -type d -exec rm -rf {} + 2>/dev/null || true
( cd "$OUT" && find . -type f ! -name SHA256SUMS -print0 | LC_ALL=C sort -z | xargs -0 shasum -a 256 > SHA256SUMS \
  && shasum -a 256 -c SHA256SUMS --quiet && echo "SHA256SUMS OK $(wc -l < SHA256SUMS | tr -d ' ')" )
NSUMS=$(wc -l < "$OUT/SHA256SUMS" | tr -d ' ')
if [ "$NSUMS" != "$NPRED" ]; then echo "GATE package files: seal predicted $NPRED, SHA256SUMS lists $NSUMS"; exit 1; fi
echo "PACKAGE_FILES=$NSUMS (matches the seal)"
find "$OUT" -exec touch -t $TS {} +
echo "ASSEMBLED=$OUT"

# --- 9. the zip. Sealing is a ruling; this step does not take it by default.
if [ "${MPUP_SEAL_CONFIRM:-}" != "$ROUND" ]; then
  echo "ZIP_SKIPPED (set MPUP_SEAL_CONFIRM=$ROUND to write the zip)"; exit 0; fi
( cd "$PKG" && rm -f "$NAME.zip" \
  && find "$NAME" -type f -print0 | LC_ALL=C sort -z | xargs -0 zip -X -q "$NAME.zip" \
  && shasum -a 256 "$NAME.zip" | tee "$NAME.zip.sha256" \
  && stat -f %z "$NAME.zip" && unzip -l "$NAME.zip" | tail -1 \
  && echo "SEAL_IN_ZIP=$(unzip -l "$NAME.zip" | grep -c "correspondence/SEAL_$ROUND.txt")" \
  && echo "MANUSCRIPTS_IN_ZIP=$(unzip -l "$NAME.zip" | grep -c 'manuscript/MANUSCRIPT_V')" )
# --- 10. re-extract the zip somewhere else and judge THAT (Gate-10 §2 step 10)
RX=$(mktemp -d /tmp/mpup_reextract.XXXXXX)
( cd "$RX" && unzip -q "$PKG/$NAME.zip" && cd "$NAME" && shasum -a 256 -c SHA256SUMS --quiet \
  && echo "REEXTRACT_SHA256SUMS=OK" && python3 tools/shipping_artifact_gate.py . ) \
  || { echo "REEXTRACT_GATE=FAIL"; rm -rf "$RX"; exit 1; }
rm -rf "$RX"
echo "REEXTRACT_GATE=OK"

# --- 11. R01 (Gate-13 §14): the public artifact in two layers, generated from the SAME sealed tree.
# APAL_PUBLIC_CORE = what a referee and Zenodo see first: Lean source, frozen statements, current
# certificates, current build scripts, current TRUST, manuscript + proof companion, statement map,
# LICENSE/CITATION, the seal, the AI disclosure (inside the TeX).  DEVELOPMENT_HISTORY = old rounds,
# invalidated seals, raw blind outputs, simulated referee reports, correction chronology, provider
# logs, obsolete drafts, and the reviewer correspondence.  Every file of the sealed package lands in
# exactly one of the two (PARTITION_CHECK), so nothing is dropped or duplicated by the split; the
# full package zip above remains the artifact of record for the reviewer.
SPLIT=$(mktemp -d /tmp/mpup_split.XXXXXX)
( cd "$SPLIT" && unzip -q "$PKG/$NAME.zip" ) || { echo "SPLIT_GATE=FAIL (unzip)"; rm -rf "$SPLIT"; exit 1; }
partition_lists "$SPLIT/$NAME" "$SPLIT" || { echo "SPLIT_GATE=FAIL (lists)"; rm -rf "$SPLIT"; exit 1; }
# the zip adds SHA256SUMS, which the record excluded by name; every other line must agree with the record
( cd "$SPLIT/$NAME" && find . -type f | LC_ALL=C sort > "$SPLIT/all_zip.lst" )
( cd "$SPLIT/$NAME" \
  && NALL=$(wc -l < "$SPLIT/all_zip.lst" | tr -d ' ') && NCORE=$(wc -l < "$SPLIT/core.lst" | tr -d ' ') && NHIST=$(wc -l < "$SPLIT/hist.lst" | tr -d ' ') \
  && grep -qx './SHA256SUMS' "$SPLIT/all_zip.lst" && echo "./SHA256SUMS" >> "$SPLIT/core.lst" && NCORE=$((NCORE + 1)) \
  && if [ $((NCORE + NHIST)) -ne "$NALL" ]; then echo "PARTITION_CHECK=FAIL ($NCORE + $NHIST != $NALL)"; exit 1; fi \
  && if [ "$(sort "$SPLIT/core.lst" "$SPLIT/hist.lst" | uniq -d | wc -l | tr -d ' ')" != 0 ]; then echo "PARTITION_CHECK=FAIL (intersection)"; exit 1; fi \
  && if grep -qE '^\./(history|independent_reviews|referee_simulation|drafts|development_notes)/' "$SPLIT/core.lst"; then echo "PARTITION_CHECK=FAIL (history in core)"; exit 1; fi \
  && sed -n 's|^- |./|p' PARTITION_RECORD.md | LC_ALL=C sort > "$SPLIT/record.lst" \
  && grep -v -x -e './SHA256SUMS' -e "./correspondence/SEAL_$ROUND.txt" "$SPLIT/all_zip.lst" > "$SPLIT/all_minus2.lst" \
  && if ! cmp -s "$SPLIT/record.lst" "$SPLIT/all_minus2.lst"; then echo "PARTITION_CHECK=FAIL (record disagrees with the zip beyond SHA256SUMS and the seal)"; diff "$SPLIT/record.lst" "$SPLIT/all_minus2.lst" | head; exit 1; fi \
  && echo "PARTITION_CHECK=OK all=$NALL core=$NCORE history=$NHIST record_agrees=1" \
  && LC_ALL=C sort -o "$SPLIT/core.lst" "$SPLIT/core.lst" \
  && tr '\n' '\0' < "$SPLIT/hist.lst" | xargs -0 zip -X -q "$PKG/DEVELOPMENT_HISTORY_$NAME.zip" ) \
  || { echo "SPLIT_GATE=FAIL"; rm -rf "$SPLIT"; exit 1; }
# s42 (Gate-16 P0-3, Packet C): the core is a RELEASE of its own.  The payload is exactly core.lst minus the
# parent's SHA256SUMS (a checksum file is not a partition member; the record already excludes it by name);
# the parent's seal, partition record and shipping measurements stay byte for byte as provenance.  Then the
# release layer is generated ON the payload, the core gets its own SHA256SUMS last, and the zip is judged by
# public_core_release.py --verify after re-extraction into an empty directory (C3): the gate reads nothing
# outside the archive and requires no history file.
CORE_DIR="$SPLIT/core_release"; mkdir -p "$CORE_DIR"
( cd "$SPLIT/$NAME" && grep -v -x './SHA256SUMS' "$SPLIT/core.lst" | tr '\n' '\0' | xargs -0 tar -cf - ) | ( cd "$CORE_DIR" && tar -xf - ) \
  || { echo "SPLIT_GATE=FAIL (core payload copy)"; rm -rf "$SPLIT"; exit 1; }
NPAY=$(find "$CORE_DIR" -type f | wc -l | tr -d ' ')
NREC=$(grep -v -x './SHA256SUMS' "$SPLIT/core.lst" | wc -l | tr -d ' ')
if [ "$NPAY" != "$NREC" ]; then echo "SPLIT_GATE=FAIL (core payload $NPAY != list $NREC)"; rm -rf "$SPLIT"; exit 1; fi
PZSHA=$(shasum -a 256 "$PKG/$NAME.zip" | cut -d' ' -f1)
( cd "$CORE_DIR" && python3 tools/public_core_release.py --generate . --round "$ROUND" --parent-zip-sha256 "$PZSHA" --parent-zip-name "$NAME.zip" \
  && find . -type f ! -name SHA256SUMS -print0 | LC_ALL=C sort -z | xargs -0 shasum -a 256 > SHA256SUMS \
  && shasum -a 256 -c SHA256SUMS --quiet && echo "CORE_SHA256SUMS_OK=$(wc -l < SHA256SUMS | tr -d ' ')" \
  && find . -type f -print0 | LC_ALL=C sort -z | xargs -0 zip -X -q "$PKG/APAL_PUBLIC_CORE_$NAME.zip" ) \
  || { echo "SPLIT_GATE=FAIL (core release layer)"; rm -rf "$SPLIT"; exit 1; }
# C3: an empty directory, the core zip alone, the public gate
CX=$(mktemp -d /tmp/mpup_corex.XXXXXX)
( cd "$CX" && unzip -q "$PKG/APAL_PUBLIC_CORE_$NAME.zip" && shasum -a 256 -c SHA256SUMS --quiet && echo "CORE_REEXTRACT_SHA256SUMS=OK" \
  && python3 tools/public_core_release.py --verify . && python3 tools/public_core_controls.py --cleanroom . ) > "$PKG/$NAME.core_gate.txt" 2>&1 \
  || { cat "$PKG/$NAME.core_gate.txt"; echo "CORE_GATE=FAIL (re-extracted core)"; rm -rf "$SPLIT" "$CX"; exit 1; }
cat "$PKG/$NAME.core_gate.txt"; rm -rf "$CX"
( cd "$PKG" && shasum -a 256 "APAL_PUBLIC_CORE_$NAME.zip" "DEVELOPMENT_HISTORY_$NAME.zip" | tee "$NAME.split.sha256" \
  && echo "PUBLIC_CORE_FILES=$(unzip -l "APAL_PUBLIC_CORE_$NAME.zip" | tail -1 | awk '{print $2}') (payload $NPAY + release layer 5)" \
  && echo "DEVELOPMENT_HISTORY_FILES=$(unzip -l "DEVELOPMENT_HISTORY_$NAME.zip" | tail -1 | awk '{print $2}')" ) \
  || { echo "SPLIT_GATE=FAIL (sidecar)"; rm -rf "$SPLIT"; exit 1; }
rm -rf "$SPLIT"
echo "SPLIT_GATE=OK"
