#!/usr/bin/env python3
"""partition_check.py — verify PARTITION_RECORD.md against the package tree (s40, Gate-14 P06 / §18 release red team).

Usage: python3 tools/partition_check.py <root>
Reads <root>/PARTITION_RECORD.md (written by the assembler before the seal counted the package) and checks:
  UNION      every file of the tree is listed exactly once (SHA256SUMS and correspondence/SEAL_r*.txt excepted:
             they are added after the record; they land in the public core)
  INTER      no file is listed under both headings
  LEAN_CORE  every lean/, frozen_statements/ and certificates/ file is in the public core
  HIST_CORE  no history/, independent_reviews/, referee_simulation/, drafts/ or development_notes/ file is in the core
  EXCLUDE    no public-core path matches a pattern of release/PUBLIC_CORE_EXCLUDE.txt (s41, Gate-15 F08);
             PUBLIC_CORE_HISTORY_PATHS=0 is printed
Prints PARTITION_CHECK=OK|FAIL and exits 0/1.  This is a text check against the record: the split archives
themselves are compared with the record by the assembler at the moment they are cut.
"""
import os, re, sys
root = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else ".")
rec = os.path.join(root, "PARTITION_RECORD.md")
if not os.path.exists(rec):
    print("PARTITION_CHECK=FAIL PARTITION_RECORD.md absent"); sys.exit(1)
core, hist, cur = [], [], None
for l in open(rec, encoding="utf-8"):
    if l.startswith("## Public core"): cur = core
    elif l.startswith("## Development history"): cur = hist
    elif l.startswith("- ") and cur is not None: cur.append(l[2:].rstrip("\n"))
tree = []
for dp, dn, fn in os.walk(root):
    dn[:] = [d for d in dn if d not in ("__pycache__", "logs")]
    for f in fn:
        if f.endswith(".bak") or ".bak" in f or f == ".DS_Store": continue
        rel = os.path.relpath(os.path.join(dp, f), root)
        if rel == "SHA256SUMS" or re.match(r"correspondence/SEAL_r\d+\.txt$", rel): continue
        tree.append(rel)
cs, hs, ts = set(core), set(hist), set(tree)
fails = []
inter = cs & hs
missing = ts - (cs | hs); extra = (cs | hs) - ts
dup = len(core) + len(hist) - len(cs | hs)
if inter: fails.append(f"INTER {len(inter)} {sorted(inter)[:3]}")
if missing: fails.append(f"UNION_MISSING {len(missing)} {sorted(missing)[:3]}")
if extra: fails.append(f"UNION_EXTRA {len(extra)} {sorted(extra)[:3]}")
if dup: fails.append(f"DUPLICATE_LINES {dup}")
# s41 (Gate-15 F08): release/PUBLIC_CORE_EXCLUDE.txt (rendered by the assembler from the template, @ROUND@
# already substituted) lists the development-history patterns; a public-core path matching one is a FAIL, and a
# lean/, frozen_statements/ or certificates/ path matching one is expected in the history, not the core.
exc_path = os.path.join(root, "release", "PUBLIC_CORE_EXCLUDE.txt")
exc = []
if os.path.exists(exc_path):
    exc = [re.compile(l.strip()) for l in open(exc_path, encoding="utf-8") if l.strip() and not l.startswith("#")]
    if any("@ROUND@" in e.pattern for e in exc): fails.append("EXCLUDE_UNRENDERED @ROUND@ left in release/PUBLIC_CORE_EXCLUDE.txt")
excluded = lambda x: any(e.match(x) for e in exc)
hist_paths = sorted(x for x in cs if excluded(x))
print(f"PUBLIC_CORE_HISTORY_PATHS={len(hist_paths)}" + (f" {hist_paths[:3]}" if hist_paths else ""))
if hist_paths: fails.append(f"CORE_HAS_HISTORY {len(hist_paths)} {hist_paths[:3]}")
lean_out = sorted(x for x in ts if x.startswith(("lean/", "frozen_statements/", "certificates/")) and x not in cs and not excluded(x))
if lean_out: fails.append(f"LEAN_CORE {len(lean_out)} {lean_out[:3]}")
hist_in = sorted(x for x in cs if x.startswith(("history/", "independent_reviews/", "referee_simulation/", "drafts/", "development_notes/")))
if hist_in: fails.append(f"HIST_CORE {len(hist_in)} {hist_in[:3]}")
print(f"PARTITION_RECORD core={len(cs)} history={len(hs)} tree={len(ts)}")
for f in fails: print("PARTITION_FAIL " + f)
print("PARTITION_CHECK=" + ("OK" if not fails else "FAIL"))
sys.exit(0 if not fails else 1)
