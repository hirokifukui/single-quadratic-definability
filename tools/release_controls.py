#!/usr/bin/env python3
"""release_controls.py — thirteen planted release defects, each of which the shipping gate must catch (s40, Gate-14 §18).

Usage: python3 tools/release_controls.py <assembled_root>
For each control the root is copied to a temp directory, one defect is planted, tools/shipping_artifact_gate.py
is run on the copy, and the named check must be reported FAIL (and the gate must exit 1).  The root itself is
never touched.  Prints RELEASE_CONTROLS_CAUGHT=n/13 and exits 0 only when n == 13.  A control that passes the
gate is a hole in the gate, not a passing control.
"""
import os, re, shutil, subprocess, sys, tempfile, glob
root = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else ".")
gate = os.path.join(root, "tools", "shipping_artifact_gate.py")

def sub(path, pattern, repl, count=1):
    s = open(path, encoding="utf-8").read()
    s2, n = re.subn(pattern, repl, s, count=count, flags=re.M)
    assert n >= 1, (path, pattern)
    open(path, "w", encoding="utf-8").write(s2)

def record_lines(path, heading):
    out, cur = [], None
    for l in open(path, encoding="utf-8"):
        if l.startswith("## "): cur = l.strip()
        elif l.startswith("- ") and cur == heading: out.append(l[2:].strip())
    return out

def plant_record(path, op):
    core = record_lines(path, "## Public core"); hist = record_lines(path, "## Development history")
    lean = [x for x in core if x.startswith("lean/DiophCompression/")][0]
    if op == "core_minus_lean": core.remove(lean)
    elif op == "history_in_core": core.append(hist[0])
    elif op == "union_incomplete": hist.pop()
    elif op == "intersection": hist.append(core[0])
    elif op == "excluded_in_core":   # s41 (Gate-15 F08): a development-history certificate re-listed in the public core
        exc = [re.compile(l.strip()) for l in open(os.path.join(os.path.dirname(path), "release", "PUBLIC_CORE_EXCLUDE.txt"), encoding="utf-8") if l.strip() and not l.startswith("#")]
        x = [h for h in hist if any(e.match(h) for e in exc)][0]; hist.remove(x); core.append(x)
    s = open(path, encoding="utf-8").read()
    head = s.split("## Public core")[0]
    open(path, "w", encoding="utf-8").write(head + "## Public core\n\n" + "".join(f"- {x}\n" for x in core) + "\n## Development history\n\n" + "".join(f"- {x}\n" for x in hist))

C = [
 ("C01 README version one generation old", "README_VERSION",
  lambda r: sub(os.path.join(r, "README.md"), r"^(Version )(\S+)", r"\g<1>0.0.1")),
 ("C02 CITATION date one generation old", "CITATION_ROOT_DATE",
  lambda r: sub(os.path.join(r, "CITATION.cff"), r'^(date-released: ")[^"]+', r"\g<1>2000-01-01")),
 ("C03 seal quotes an old PDF hash", "SEAL_PDF_SHA",
  lambda r: sub(glob.glob(os.path.join(r, "correspondence", "SEAL_r*.txt"))[0], r"^(\s*SHIPPED_PDF_SHA256=)\S+", r"\g<1>" + "0" * 64)),
 ("C04 measurements mutated by a failed build", "MEASUREMENTS_AGREE",
  lambda r: sub(os.path.join(r, "SHIPPING_MEASUREMENTS.txt"), r"^(SHIPPED_PDF_SHA256=)\S+", r"\g<1>" + "1" * 64)),
 ("C05 __pycache__ left in the tree", "NO_PYCACHE",
  lambda r: (os.makedirs(os.path.join(r, "tools", "__pycache__"), exist_ok=True), open(os.path.join(r, "tools", "__pycache__", "x.pyc"), "w").close())),
 ("C06 public core missing a Lean file", "PARTITION_RECORD", lambda r: plant_record(os.path.join(r, "PARTITION_RECORD.md"), "core_minus_lean")),
 ("C07 history file listed in the core", "PARTITION_RECORD", lambda r: plant_record(os.path.join(r, "PARTITION_RECORD.md"), "history_in_core")),
 ("C08 union incomplete after the split", "PARTITION_RECORD", lambda r: plant_record(os.path.join(r, "PARTITION_RECORD.md"), "union_incomplete")),
 ("C09 intersection non-empty after the split", "PARTITION_RECORD", lambda r: plant_record(os.path.join(r, "PARTITION_RECORD.md"), "intersection")),
 ("C10 an old trust document mixed in", "SINGLE_TRUST",
  lambda r: shutil.copy(os.path.join(r, "release", "TRUST_BOUNDARY_APAL.md"), os.path.join(r, "release", "TRUST_BOUNDARY_APAL_old.md"))),
 ("C11 an old cover letter mixed in", "SINGLE_COVER_LETTER",
  lambda r: open(os.path.join(r, "correspondence", "COVER_LETTER_old.md"), "w").write("old cover letter\n")),
 ("C12 a source file mutated after the build", "SOURCE_MANIFEST",
  lambda r: open(glob.glob(os.path.join(r, "lean", "DiophCompression", "*.lean"))[0], "a").write("\n-- planted\n")),
 ("C13 a development-history certificate re-listed in the public core", "PARTITION_RECORD", lambda r: plant_record(os.path.join(r, "PARTITION_RECORD.md"), "excluded_in_core")),
]
caught = 0
for name, expect, plant in C:
    tmp = tempfile.mkdtemp(prefix="relctl_")
    dst = os.path.join(tmp, os.path.basename(root))
    shutil.copytree(root, dst, symlinks=True)
    try:
        plant(dst)
        r = subprocess.run([sys.executable, gate, dst], capture_output=True, text=True, env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
        failed = re.findall(r"^CHECK (\S+) FAIL", r.stdout, re.M)
        ok = (r.returncode != 0) and (expect in failed)
        print(f"{'CAUGHT' if ok else 'MISSED'}\t{name}\texpect={expect}\texit={r.returncode}\tfailed={failed}")
        caught += ok
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
print(f"RELEASE_CONTROLS_CAUGHT={caught}/{len(C)}")
print(f"RELEASE_CONTROLS_EXIT={0 if caught == len(C) else 1}")
sys.exit(0 if caught == len(C) else 1)
