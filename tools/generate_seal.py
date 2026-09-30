#!/usr/bin/env python3
"""generate_seal.py -- correspondence/SEAL_<round>.txt from release/SEAL.template.md and the assembly's
own measurements.  No figure is typed (s36, Gate-10 Z04).

Inputs, all in the distribution root:
    release/SEAL_INPUT.env          identities the assembly declares (ROUND, RELEASE_DATE, ...)
    release/SEAL_WHAT_IS_OPEN.md    the open-items paragraph (prose, not a measurement)
    ASSEMBLY_GATES.log              stdout of the assembler's package gates
    PACKAGE_BUILD.log               stdout of release/build_submission_from_package.sh run in this root
    SHIPPING_MEASUREMENTS.txt       written by that build
    certificates/                   FinalAxiomReport / binder ledger / statement_diff (via submission_figures)
    certificates/fresh_build_*.log  the clean-room records that survived the assembler's ageing
Every {{token}} in the template must be filled from one of these; an unfilled token is exit 1.
A token that could be read from two sources with different values is exit 1 as well.

Usage:  python3 tools/generate_seal.py <package_root> [--print-only]
"""
import glob, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from submission_figures import measure_trust
from generate_trust import frozen_theorems, roots

KV = re.compile(r"\b([A-Z][A-Z0-9_]+)=([^\s()]+)")

def harvest(path, src, bag):
    """bag[key] -> list of (value, source).  Within ONE source the last value wins (a build runs some
    gates twice and prints the same key each time); across sources every distinct value is kept,
    and a template token with two distinct values is a contradiction, reported and fatal."""
    if not os.path.exists(path): return
    local = {}
    for l in open(path, encoding="utf-8", errors="replace"):
        for k, v in KV.findall(l):
            local[k] = v.strip(",;")
    for k, v in local.items():
        bag.setdefault(k, []).append((v, src))

def resolve(bag, needed):
    vals, conflicts = {}, []
    for k in needed:
        if k not in bag: continue
        distinct = sorted(set(v for v, _ in bag[k]))
        if len(distinct) > 1: conflicts.append((k, bag[k]))
        else: vals[k] = distinct[0]
    return vals, conflicts

def main():
    root = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else ".")
    print_only = "--print-only" in sys.argv
    tpl = open(os.path.join(root, "release", "SEAL.template.md"), encoding="utf-8").read()
    needed = set(re.findall(r"\{\{(\w+)\}\}", tpl))
    bag = {}
    # 1. declared identities
    env = os.path.join(root, "release", "SEAL_INPUT.env")
    if not os.path.exists(env): print("GENERATE_SEAL=FAIL release/SEAL_INPUT.env absent"); sys.exit(1)
    for l in open(env, encoding="utf-8"):
        l = l.strip()
        if l and not l.startswith("#") and "=" in l:
            k, v = l.split("=", 1); bag.setdefault(k.strip(), []).append((v.strip(), "input"))
    wio = os.path.join(root, "release", "SEAL_WHAT_IS_OPEN.md")
    bag["WHAT_IS_OPEN"] = [(open(wio, encoding="utf-8").read().rstrip("\n") if os.path.exists(wio) else "", "input")]
    # 2. measurements
    harvest(os.path.join(root, "ASSEMBLY_GATES.log"), "assembly", bag)
    harvest(os.path.join(root, "PACKAGE_BUILD.log"), "build", bag)
    harvest(os.path.join(root, "SHIPPING_MEASUREMENTS.txt"), "shipping", bag)
    for f in sorted(glob.glob(os.path.join(root, "certificates", "fresh_build_*.log"))):
        harvest(f, "cleanroom:" + os.path.basename(f), bag)
    def rd(p):
        return open(p, encoding="utf-8", errors="replace").read() if os.path.exists(p) else ""
    bl, al = rd(os.path.join(root, "PACKAGE_BUILD.log")), rd(os.path.join(root, "ASSEMBLY_GATES.log"))
    for tok, pat, txt, src in (("ABSTRACT_WORDS", r"FIGURE_ABSTRACT_WORDS\s+measured=(\d+)", bl, "build"),
                               ("KEYWORDS", r"FIGURE_KEYWORDS\s+measured=(\d+)", bl, "build"),
                               ("APPENDIX_E_ROWS", r"APPENDIX_E_GATE=OK rows=(\d+)", bl, "build"),
                               ("STATEMENT_MAP_FULL_ROWS", r"STATEMENT_MAP_FULL_GATE=OK rows=(\d+)", bl, "build"),
                               ("TOOLS_SHIPPED", r"TOOLS_SHIPPED=OK n=(\d+)", al, "assembly"),
                               ("FROZEN_SHIPPED", r"FROZEN_SHIPPED=OK n=(\d+)", al, "assembly"),
                               ("DISPOSITIONS_N", r"DISPOSITIONS_SHIPPED=OK n=(\d+)", al, "assembly"),
                               ("PACKAGE_FILES", r"PACKAGE_FILES_PREDICTED=(\d+)", al, "assembly")):
        m = re.search(pat, txt)
        if m: bag[tok] = [(m.group(1), src)]
    cl = "\n".join(rd(f) for f in glob.glob(os.path.join(root, "certificates", "fresh_build_*.log")))
    m = re.search(r"MATHLIB_REV=\[\('([0-9a-f]+)', '\\1'\)\]", cl) or re.search(r"MATHLIB_REV=\[\('([0-9a-f]+)'", cl)
    if m: bag["MATHLIB_REV"] = [(m.group(1), "cleanroom")]
    tc = os.path.join(root, "lean", "lean-toolchain")
    if os.path.exists(tc): bag["TOOLCHAIN"] = [(open(tc).read().strip(), "lean")]
    # 3. certificates
    fig = measure_trust(os.path.join(root, "certificates"))
    fr, rt = frozen_theorems(root), roots(root)
    fig.update(recon_both=len(fr & rt), recon_frozen_not_root=len(fr - rt), recon_root_not_frozen=len(rt - fr))
    for k, v in fig.items(): bag[k] = [(str(v), "certificates")]
    vals, conflicts = resolve(bag, needed)
    if conflicts:
        print("GENERATE_SEAL=FAIL conflicting values:"); [print("  ", c) for c in conflicts]; sys.exit(1)
    out = re.sub(r"\{\{(\w+)\}\}", lambda m: vals[m.group(1)] if m.group(1) in vals else m.group(0), tpl)
    left = sorted(set(re.findall(r"\{\{(\w+)\}\}", out)))
    if left:
        print(f"GENERATE_SEAL=FAIL unfilled tokens {left}"); sys.exit(1)
    if print_only:
        print(out); return
    dest = os.path.join(root, "correspondence", f"SEAL_{vals['ROUND']}.txt")
    open(dest, "w", encoding="utf-8").write(out)
    print(f"GENERATE_SEAL=OK {os.path.relpath(dest, root)} tokens={len(needed)}")

if __name__ == "__main__":
    main()
