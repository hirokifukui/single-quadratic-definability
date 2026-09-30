#!/usr/bin/env bash
# rebuild.sh — one-shot rebuild + kernel gate for mpup-lean (GPT r02 §4.3/§4.4, §8-D).
# Records environment, builds, runs `lake env lean` on every MPUP file, prints #print axioms,
# greps forbidden tokens, and exits non-zero if any gate fails. Log = stdout (tee it).
set -u
cd "$(dirname "$0")/.."
LAKE=${LAKE:-$HOME/.elan/bin/lake}
ulimit -n 8192 2>/dev/null || true
echo "=== ENV ==="
date; hostname; uname -srm; sw_vers 2>/dev/null || true
"$HOME/.elan/bin/elan" show 2>/dev/null | sed 's/^/elan: /' || true
cat lean-toolchain
"$LAKE" --version
echo "mathlib (lake-manifest.json):"; python3 - <<'PY'
import json;m=json.load(open('lake-manifest.json'))
for p in m['packages']:
    if p['name']=='mathlib': print(' ',{k:p.get(k) for k in ('type','dir','url','rev','inputRev')})
PY
MLDIR=$(python3 -c "import json;print([p for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='mathlib'][0].get('dir',''))")
if [ -n "$MLDIR" ] && [ -d "$MLDIR/.git" ]; then echo "mathlib git HEAD: $(git -C "$MLDIR" rev-parse HEAD)"; fi
echo "=== MD5 (MPUP/*.lean) ==="; for f in MPUP/*.lean; do printf "%s  %s\n" "$(md5 -q "$f" 2>/dev/null || md5sum "$f" | cut -d' ' -f1)" "$f"; done
echo "=== BUILD ==="; "$LAKE" build MPUP.Gate MPUP.Quantitative; BE=$?; echo "BUILD_EXIT=$BE"
FAIL=$BE
for f in Spec Gate Task1 Obstruction Quantitative; do
  echo "=== lake env lean MPUP/$f.lean ==="
  "$LAKE" env lean "MPUP/$f.lean"; E=$?; echo "EXIT_$f=$E"; [ $E -ne 0 ] && FAIL=1
done
echo "=== GATE: forbidden tokens (fail-fast; s11, GPT r10 必須A-4) ==="
# comment-aware gate (s12, E-r12-1): comments stripped mechanically, then token grep;
# positive control: a planted `sorry` in code is still caught (scripts/forbidden_gate.py header).
if python3 "$(dirname "$0")/forbidden_gate.py" MPUP/*.lean; then
  echo "FORBIDDEN_TOKEN_MATCH=1"
  FAIL=1
else
  echo "FORBIDDEN_TOKEN_MATCH=0"
fi
echo "=== SUMMARY ==="; echo "REBUILD_EXIT=$FAIL"; date; exit $FAIL
