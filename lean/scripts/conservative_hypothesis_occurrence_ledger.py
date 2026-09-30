#!/usr/bin/env python3
"""hypothesis_ledger.py — mechanical trust-boundary ledger (s26, blank-slate referee D2).
For every `#print axioms` root in scripts/FinalAxiomReport.lean, find its declaration in the production tree and
record which external-hypothesis Props occur in its SIGNATURE (text up to the first `:=`). A root whose signature
mentions none of them is UNCONDITIONAL by typing: a Lean theorem cannot use a hypothesis it does not take as an
argument (and the axiom footprint is std-3, so nothing enters as an axiom). Output: TSV (root, hypotheses) + summary.
Usage: python3 scripts/conservative_hypothesis_occurrence_ledger.py (renamed from hypothesis_ledger.py in s27; the exact ledger is scripts/HypothesisBinderLedger.lean) > certificates/hypothesis_ledger_<tag>.tsv"""
import re, os, glob, sys
HYPS = ['GlobalQuadraticSolvabilityDecidable', 'UniformQuadraticSolvabilityOnCodes', 'UniformQuadraticSolvabilityDecidableZZ',
        'QuadraticSolvabilityDecidableZZ', 'DPRM_NN', 'DPRM_ZZ', 'PellClassFiniteness',
        'QuadraticSolvabilityDecidableZ', 'QuadraticSolvabilityDecidableN', 'HardDiophantineSetExists']  # s27: r13-era forms added
roots = re.findall(r'^#print axioms (\S+)', open('scripts/FinalAxiomReport.lean').read(), re.M)
files = glob.glob('DiophCompression/**/*.lean', recursive=True) + glob.glob('MPUP/*.lean')
src = {f: open(f).read() for f in files if not f.endswith('.bak') and '.bak' not in f}
sigs = {}
for f, s in src.items():
    for m in re.finditer(r'^(?:theorem|lemma) (\S+)((?:.|\n)*?):=', s, re.M):
        sigs.setdefault(m.group(1), (f, m.group(2)))
        sigs.setdefault(m.group(1).split('.')[-1], (f, m.group(2)))  # namespaced declarations (A.b) by short name
counts = {h: 0 for h in HYPS}; uncond = 0; missing = []
print('root\tfile\thypotheses_in_signature')
for r in roots:
    short = r.split('.')[-1]
    hit = sigs.get(short)
    if hit is None:
        missing.append(r); print(f'{r}\t?\tNOT_FOUND'); continue
    f, sig = hit
    used = [h for h in HYPS if re.search(r'\b' + re.escape(h) + r'\b', sig)]
    for h in used: counts[h] += 1
    if not used: uncond += 1
    print(f'{r}\t{f}\t{",".join(used) if used else "UNCONDITIONAL"}')
# s28 (GPT Gate-4 §9): the reported quantity is EXTERNAL-INPUT-FREE, not "unconditional" — a root
# without an external input may still carry ordinary mathematical hypotheses. The legacy key
# UNCONDITIONAL is kept for round-to-round comparability and mirrored by the new name.
print(f'# ROOTS={len(roots)} UNCONDITIONAL={uncond} EXTERNAL_INPUT_FREE={uncond} NOT_FOUND={len(missing)} ' +
      ' '.join(f'{h}={c}' for h, c in counts.items()), file=sys.stderr)
