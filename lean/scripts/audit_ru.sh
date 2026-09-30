#!/usr/bin/env bash
# audit_ru.sh — r40 kernel gate for ResearchUpgrade/ (derived from audit_dc.sh by full-token
# namespace substitution; the r05-r14 history below is audit_dc.sh's and is kept for provenance).
# ORIGINAL HEADER FOLLOWS.
# audit_dc.sh — kernel gate for DiophCompression/ (mirror of rebuild.sh, new namespace only). r05: +BoundaryCasesZ ArityMonotonicity GraphToUniversalityN NatGuardZ GraphToUniversalityZ CapacityFunctions UniversalSpectrumLower (s5). r06: +DegreeZero UnifiedLower CapacityBireduction NatGuard SpectrumTransfer (s6). r07: +SemanticQuadratic/Corollaries, SemanticQuadraticGeneral/{Defs,NormalForm,ProjectionDichotomy}, SemanticQuadraticTwoWitness/{Defs2W,Bridge2W} (s7). r08: +SemanticQuadraticTwoWitness/{DefsScaled,SignNormalisation,ScaledLine,Bounds2W,Directions,PellStep,RankTwoAlphaZero,RankTwoGeneric,RankTwoLeaves,RankZero,RankOneNormalForm,Unimodular,RankOneCoupled,RankOne,Assembly2W} (s8). r09: +SemanticQuadraticTwoWitness/{Corollaries2W,Fidelity2W}, SemanticQuadraticMatrix/{AffineGcd,DefsMatrix,AdjugateIdentity,FullRankGeneric}, SemanticQuadraticThreeWitness/Bridge3W (s9). r10: +SemanticQuadraticSingular/{DefsSingular,RadicalLinear,PeriodicModulus,TransferS,FiniteFieldQuadratic,MovingModulus,Unimodular3,BridgeSingular,Assembly3W} +Corollaries3W (s10 homework); forbidden-token regex ^axiom → ^[[:space:]]*axiom (GPT r09 §6). r11 (s11, GPT r10 必須A-4/5/6/7): forbidden-token gate now sets FAIL=1 on match; mathlib commit read from lake-manifest.json (not a sibling checkout); hashes portable (sha256, macOS/Linux); audited file list held in one array used by hash listing, env-lean loop, and token gate.
set -u
cd "$(dirname "$0")/.."
LAKE=${LAKE:-$HOME/.elan/bin/lake}
ulimit -n 8192 2>/dev/null || true

hash_sha256() { if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d" " -f1; else shasum -a 256 "$1" | cut -d" " -f1; fi; }

# r14 (s14, GPT r13 必須D): static FILES array retired — dynamic enumeration of every
# production .lean under ResearchUpgrade/, with ACTUAL/AUDITED/MISSING/EXTRA gates and
# planted positive/negative gate controls. Root cause: the r13 array held 86 entries while
# 89 files existed on disk (QuadraticUniversalityConditional, SemanticQuadraticSingular/
# QuadraticUniversalityCorollaries, WeakenUnknowns were unlisted), so the per-file audit
# claim was false. Dynamic enumeration makes the list and the disk agree by construction;
# the count gates keep the agreement observable in the log.
FILES=()
for _f in $(find ResearchUpgrade -type f -name '*.lean' | LC_ALL=C sort); do
  _rel="${_f#ResearchUpgrade/}"
  FILES+=("${_rel%.lean}")
done
ACTUAL_FILES=$(find ResearchUpgrade -type f -name '*.lean' | wc -l | tr -d ' ')
AUDITED_FILES=${#FILES[@]}
MISSING=0
for _f in $(find ResearchUpgrade -type f -name '*.lean' | LC_ALL=C sort); do
  _rel="${_f#ResearchUpgrade/}"; _rel="${_rel%.lean}"; _hit=0
  for _g in "${FILES[@]}"; do [ "$_g" = "$_rel" ] && _hit=1 && break; done
  [ $_hit -eq 0 ] && MISSING=$((MISSING+1))
done
EXTRA=0
for _g in "${FILES[@]}"; do [ -f "ResearchUpgrade/$_g.lean" ] || EXTRA=$((EXTRA+1)); done
echo "ACTUAL_FILES=$ACTUAL_FILES"
echo "AUDITED_FILES=$AUDITED_FILES"
echo "MISSING=$MISSING"
echo "EXTRA=$EXTRA"
ENUM_FAIL=0
[ "$ACTUAL_FILES" -ne "$AUDITED_FILES" ] && ENUM_FAIL=1
[ "$MISSING" -ne 0 ] && ENUM_FAIL=1
[ "$EXTRA" -ne 0 ] && ENUM_FAIL=1
echo "FILE_ENUM_GATE_FAIL=$ENUM_FAIL"

echo "=== ENV ==="; date; hostname; cat lean-toolchain
MLDIR=$(python3 -c "import json;m=json.load(open('lake-manifest.json'));p=[x for x in m.get('packages',[]) if x.get('name')=='mathlib'];print((p[0].get('dir') or '') if p else '')" 2>/dev/null)
MLREV=$(python3 -c "import json;m=json.load(open('lake-manifest.json'));p=[x for x in m.get('packages',[]) if x.get('name')=='mathlib'];print((p[0].get('rev') or '') if p else '')" 2>/dev/null)
echo "mathlib manifest dir: ${MLDIR:-'(none)'}  manifest rev: ${MLREV:-'(none)'}"
if [ -n "$MLDIR" ]; then echo "mathlib git HEAD (manifest dir): $(git -C "$MLDIR" rev-parse HEAD 2>/dev/null)"; fi

echo "=== SHA256 (audited files) ==="
for f in "${FILES[@]}"; do printf "%s  ResearchUpgrade/%s.lean\n" "$(hash_sha256 "ResearchUpgrade/$f.lean")" "$f"; done

echo "=== BUILD ==="; "$LAKE" build ResearchUpgrade; BE=$?; echo "BUILD_EXIT=$BE"; FAIL=$BE
[ "$ENUM_FAIL" -ne 0 ] && FAIL=1
for f in "${FILES[@]}"; do
  echo "=== lake env lean ResearchUpgrade/$f.lean ==="
  "$LAKE" env lean "ResearchUpgrade/$f.lean"; E=$?; echo "EXIT_$f=$E"; [ $E -ne 0 ] && FAIL=1
done

echo "=== GATE: forbidden tokens (fail-fast) ==="
GATE_FILES=()
for f in "${FILES[@]}"; do GATE_FILES+=("ResearchUpgrade/$f.lean"); done
# comment-aware gate (s12, E-r12-1): comments stripped mechanically, then token grep;
# positive control: a planted `sorry` in code is still caught (scripts/forbidden_gate.py header).
if python3 "$(dirname "$0")/forbidden_gate.py" "${GATE_FILES[@]}"; then
  echo "FORBIDDEN_TOKEN_MATCH=1"
  FAIL=1
else
  echo "FORBIDDEN_TOKEN_MATCH=0"
fi

echo "=== CONTROLS: planted gate positive/negative (r14, scratch only, production tree untouched) ==="
CTRLDIR=$(mktemp -d)
printf 'theorem planted_bad : 1 = 1 := by sorry\n' > "$CTRLDIR/planted_neg.lean"
printf 'theorem planted_good : 1 = 1 := rfl\n' > "$CTRLDIR/planted_pos.lean"
if python3 "$(dirname "$0")/forbidden_gate.py" "$CTRLDIR/planted_neg.lean" >/dev/null; then
  echo "NEG_CONTROL_CAUGHT=1"
else
  echo "NEG_CONTROL_CAUGHT=0"; FAIL=1
fi
if python3 "$(dirname "$0")/forbidden_gate.py" "$CTRLDIR/planted_pos.lean" >/dev/null; then
  echo "POS_CONTROL_FALSE_ALARM=1"; FAIL=1
else
  echo "POS_CONTROL_FALSE_ALARM=0"
fi
rm -rf "$CTRLDIR"

echo "=== FINAL AXIOM REPORT (scripts/FinalAxiomReport.lean) ==="
"$LAKE" env lean scripts/FinalAxiomReport.lean; FR=$?; echo "FINAL_REPORT_EXIT=$FR"; [ $FR -ne 0 ] && FAIL=1

echo "=== SUMMARY ==="; echo "AUDIT_RU_EXIT=$FAIL"; date; exit $FAIL
