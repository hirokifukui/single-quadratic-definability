#!/usr/bin/env python3
"""fill_counts.py — substitute ⟨ROOTS⟩/⟨THMS⟩/⟨DEFS⟩/⟨UNCOND⟩ in a manuscript from the seal-time artefacts (s27, GPT Gate-4 必須A-7).
Usage: python3 manuscript/fill_counts.py <manuscript.md> <FinalAxiomReport.log> <statement_diff.log> <hypothesis_ledger.tsv-or-summary> <out.md>
ROOTS = number of `depends on axioms` lines (wrapped lines joined); THMS/DEFS from THEOREMS=/DEFINITIONS= lines; UNCOND from the ledger summary
line `# ROOTS=… UNCONDITIONAL=…` (stderr of hypothesis_ledger.py, or the binder ledger's UNCONDITIONAL= line). Fails loudly if any token remains."""
import re, sys
ms, far, sd, hl, out = sys.argv[1:6]
t = open(far).read().replace('\n  ', ' ')
roots = len(re.findall(r"depends on axioms", t))
sdt = open(sd).read()
thms = re.search(r'^THEOREMS=(\d+)/', sdt, re.M).group(1); defs = re.search(r'^DEFINITIONS=(\d+)/', sdt, re.M).group(1)
hlt = open(hl).read()
unc = re.search(r'UNCONDITIONAL=(\d+)', hlt).group(1)
# s34: the manuscript used to type the binder ledger's two figures by hand next to a generated
# one, so they aged apart (398/360 survived into r29 while the report had moved).  Both come
# from the ledger now.
broots = re.search(r'BINDER_ROOTS=(\d+)', hlt).group(1)
s = open(ms).read()
for k, v in [('ROOTS', str(roots)), ('THMS', thms), ('DEFS', defs), ('UNCOND', unc), ('BROOTS', broots)]:
    s = s.replace('⟨' + k + '⟩', v)
left = re.findall(r'⟨(ROOTS|THMS|DEFS|UNCOND|BROOTS)⟩', s)
assert not left, left
open(out, 'w').write(s)
print(f"FILLED ROOTS={roots} THMS={thms} DEFS={defs} UNCOND={unc} BROOTS={broots} -> {out}")
