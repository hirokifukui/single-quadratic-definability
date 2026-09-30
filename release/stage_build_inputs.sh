#!/usr/bin/env bash
# stage_build_inputs.sh - copy the build's inputs OUT of the development tree and INTO the root.
#
# This is deliberately a SEPARATE step from the build (s34, Gate-8 B01).  Until s34 the build read
# its inputs live from a working tree outside the distribution, under session-labelled names
# (FinalAxiomReport_s31_*.log, statement_diff_s31.log, binder_ledger_s29.log).  Two consequences,
# both real: the r29 package contained NONE of those files, so the distributed archive could not
# rebuild its own PDF; and the names were pinned to a session, so a later development would not
# have refreshed them and nothing would have said so.
#
# After this script runs, build.sh reads only from the root it lives in.  Staging is a development
# act with a source outside the root; building is not.  Keeping them in one file is what hid the
# dependency for four rounds.
#
# Usage:  MPUP_WORK=/path/to/work  release/stage_build_inputs.sh
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
W="${MPUP_WORK:?set MPUP_WORK to the development tree}"
[ -d "$W" ] || { echo "STAGE=FAIL no such work tree: $W"; exit 1; }
mkdir -p "$ROOT/certificates" "$ROOT/frozen_statements"

n_log=0
for f in FinalAxiomReport_current.log statement_diff_current.log binder_ledger_current.log; do
  [ -f "$W/certificates/$f" ] || { echo "STAGE=FAIL missing input: $f"; exit 1; }
  cp "$W/certificates/$f" "$ROOT/certificates/$f"
  cmp -s "$W/certificates/$f" "$ROOT/certificates/$f" || { echo "STAGE=FAIL copy differs: $f"; exit 1; }
  n_log=$((n_log+1))
done

n_fz=0
for p in "$W"/frozen_statements/*_STATEMENTS.lean; do
  b="$(basename "$p")"
  cp "$p" "$ROOT/frozen_statements/$b"
  cmp -s "$p" "$ROOT/frozen_statements/$b" || { echo "STAGE=FAIL copy differs: $b"; exit 1; }
  n_fz=$((n_fz+1))
done

# the scanners the build and the release checklist run.  They ship at tools/ (T07, r29); before
# s34 two of them did not exist and two more were only in the work tree, so a reader of the
# archive could not re-run the gates the paper describes.
mkdir -p "$ROOT/tools"
n_tool=0
for f in detex_normalize.py fidelity_destroyer.py gate5_verify.py m01_internal_refs.py \
         manuscript_index.py proof_by_citation_scan.py lettered_label_control.py \
         cited_name_census.py statement_diff.py build_appendix_e_tex.py; do
  [ -f "$W/scripts/$f" ] || { echo "STAGE=FAIL missing scanner: $f"; exit 1; }
  cp "$W/scripts/$f" "$ROOT/tools/$f"
  cmp -s "$W/scripts/$f" "$ROOT/tools/$f" || { echo "STAGE=FAIL copy differs: $f"; exit 1; }
  n_tool=$((n_tool+1))
done
echo "STAGED_TOOLS=$n_tool"

# anything frozen in the root that the work tree no longer has is a stale statement file
STALE=0
for p in "$ROOT"/frozen_statements/*_STATEMENTS.lean; do
  b="$(basename "$p")"
  [ -f "$W/frozen_statements/$b" ] || { echo "STAGE_STALE $b"; STALE=$((STALE+1)); }
done

echo "STAGED_LOGS=$n_log"
echo "STAGED_FROZEN=$n_fz"
echo "STALE_FROZEN=$STALE"
echo "STAGE_EXIT=$([ "$STALE" -eq 0 ] && echo 0 || echo 1)"
[ "$STALE" -eq 0 ]
