#!/usr/bin/env python3
"""static_closure.py — GPT r15 必須E: static import-graph closure of the all-r core.
Traversal: from DiophCompression.QuadraticWitnessInertiaCore, follow every
`import DiophCompression.*` / `import MPUP.*` line transitively (the root is
included). LoC method: len(text.splitlines()) per module (comments and blanks
included; a final line without trailing newline counts as one line).
Anchors: STATIC_CLOSURE_MODULES=<n> DC=<n> MPUP=<n>  STATIC_CLOSURE_LOC=<n>
  STATIC_ABSENT <module>=YES|NO  SMOD <module> (sorted)  STATIC_CLOSURE_EXIT=<0|1>
--negative-control: traverses from a scratch root that imports TreeCoding and
  must report TreeCoding present (exit 1 if the control fails to detect it).
--kernel-list <file>: checks every KMOD line of a kernel_closure log is in the
  static closure (kernel ⊆ static), anchor KERNEL_SUBSET_STATIC=YES|NO.
"""
import os, re, sys
ROOT = "DiophCompression.QuadraticWitnessInertiaCore"
FORBID = ["DiophCompression.TreeCoding", "DiophCompression.UnifiedLower",
          "DiophCompression.QuadraticUniversalityConditional", "DiophCompression.UniversalSpectrumLower"]
def path(m): return m.replace(".", "/") + ".lean"
def closure(root, extra_edges=None):
    seen, stack = set(), [root]
    while stack:
        m = stack.pop()
        if m in seen: continue
        src = None
        if os.path.exists(path(m)): src = open(path(m), encoding="utf-8").read()
        elif extra_edges and m in extra_edges: src = extra_edges[m]
        else: continue
        seen.add(m)
        for l in src.splitlines():
            mm = re.match(r"\s*import\s+(\S+)", l)
            if mm and (mm.group(1).startswith("DiophCompression") or mm.group(1).startswith("MPUP")):
                stack.append(mm.group(1))
    return seen
def main():
    if "--negative-control" in sys.argv:
        fake = {"Ctrl.Root": "import DiophCompression.QuadraticWitnessInertiaCore\nimport DiophCompression.TreeCoding\n"}
        s = closure("Ctrl.Root", fake)
        ok = "DiophCompression.TreeCoding" in s
        print(f"NEGATIVE_CONTROL_TREECODING_DETECTED={'YES' if ok else 'NO'}")
        print(f"STATIC_CLOSURE_EXIT={0 if ok else 1}"); sys.exit(0 if ok else 1)
    s = closure(ROOT)
    ml = sorted(s); dc = [m for m in ml if m.startswith("DiophCompression.")]; mp = [m for m in ml if m.startswith("MPUP.")]
    loc = sum(len(open(path(m), encoding="utf-8").read().splitlines()) for m in ml)
    print(f"STATIC_CLOSURE_ROOT={ROOT}")
    print(f"STATIC_CLOSURE_MODULES={len(ml)} DC={len(dc)} MPUP={len(mp)}")
    print(f"STATIC_CLOSURE_LOC={loc} (method: sum of len(splitlines()) per module)")
    for f in FORBID: print(f"STATIC_ABSENT {f}={'NO' if f in s else 'YES'}")
    for m in ml: print(f"SMOD {m}")
    bad = any(f in s for f in FORBID)
    if "--kernel-list" in sys.argv:
        kf = sys.argv[sys.argv.index("--kernel-list") + 1]
        kmods = re.findall(r"KMOD (\S+)", open(kf).read())
        notin = [k for k in kmods if k not in s]
        print(f"KERNEL_MODULES_READ={len(kmods)}"); print(f"KERNEL_SUBSET_STATIC={'YES' if not notin else 'NO'}")
        for k in notin: print(f"KERNEL_NOT_IN_STATIC {k}")
        st_only = [m for m in ml if m not in kmods]
        print(f"STATIC_ONLY_MODULES={len(st_only)}")
        for m in st_only: print(f"STATIC_ONLY {m}")
        bad = bad or bool(notin)
    print(f"STATIC_CLOSURE_EXIT={1 if bad else 0}"); sys.exit(1 if bad else 0)
main()
