#!/usr/bin/env bash
# post_audit_freeze_check.sh — GPT r14 mandatory D (item 9): detect ANY source
# change after the final audit. Reads the "=== SHA256 (audited files) ===" section
# of an audit_dc log, recomputes the hash of every listed file in the CURRENT
# tree, and reports mismatches. Run from the lean root (where DiophCompression/
# lives) immediately before sealing; FREEZE_EXIT=1 forbids sealing.
#   usage: scripts/post_audit_freeze_check.sh <audit_log> [tree_root]
# Anchors (line-initial): FREEZE_LISTED= FREEZE_MISMATCH= FREEZE_MISSING= FREEZE_EXIT=
set -u
LOG="${1:?audit log path}"; ROOT="${2:-.}"
hash_sha256() { if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d" " -f1; else shasum -a 256 "$1" | cut -d" " -f1; fi; }
listed=0; mism=0; miss=0
while read -r h f; do
  [ -z "$f" ] && continue
  listed=$((listed+1))
  if [ ! -f "$ROOT/$f" ]; then echo "FREEZE MISSING  $f"; miss=$((miss+1)); continue; fi
  cur=$(hash_sha256 "$ROOT/$f")
  if [ "$cur" != "$h" ]; then echo "FREEZE CHANGED  $f  audit=${h:0:12} now=${cur:0:12}"; mism=$((mism+1)); fi
done < <(awk '/^=== SHA256 \(audited files\) ===/{on=1; next} /^===/{on=0} on && NF==2 {print $1, $2}' "$LOG")
echo "FREEZE_LISTED=$listed"
echo "FREEZE_MISMATCH=$mism"
echo "FREEZE_MISSING=$miss"
if [ "$listed" -gt 0 ] && [ "$mism" -eq 0 ] && [ "$miss" -eq 0 ]; then echo "FREEZE_EXIT=0"; exit 0; else echo "FREEZE_EXIT=1"; exit 1; fi
