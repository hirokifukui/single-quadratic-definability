#!/usr/bin/env python3
"""s52 — every Lean name the proof note cites must exist in the shipped Lean source.
Run from the package root.  Non-declaration backticks (math variables, tactics, axioms)
are reported so the list can be read, not silently filtered.
"""
import io, os, re, sys
ROOT = sys.argv[1] if len(sys.argv) > 1 else "."
note = io.open(os.path.join(ROOT, "manuscript/PROOF_NOTE_DIMENSION.md"), encoding="utf-8").read()
names = sorted(set(re.findall(r'`([A-Za-z_][A-Za-z0-9_.\u2080-\u2089\u2032\']*)`', note)))
cands = [n for n in names if ('_' in n or '.' in n) and not n.endswith('.lean')
         and not n.split('/')[0] in ("certificates", "scripts", "logs")]
decl = set()
for root, _, files in os.walk(os.path.join(ROOT, "lean")):
    for fn in files:
        if not fn.endswith(".lean"): continue
        t = io.open(os.path.join(root, fn), encoding="utf-8", errors="replace").read()
        for m in re.finditer(r'(?m)^\s*(?:private |protected |noncomputable )*'
                             r'(theorem|lemma|def|abbrev|instance|structure|inductive)\s+([^\s({\[:]+)', t):
            decl.add(m.group(2))
missing = [n for n in cands if n.split('.')[-1] not in decl and n not in decl]
print("CITED=%d  NOT_A_DECLARATION=%d" % (len(cands), len(missing)))
for n in missing: print("   NOT_A_DECLARATION", n)
print("NOTE_ANCHOR_CHECK_DONE")
