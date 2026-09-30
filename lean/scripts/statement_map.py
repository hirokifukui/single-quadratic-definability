#!/usr/bin/env python3
"""statement_map.py — Appendix E generator (s26, blank-slate referee D1): one row per frozen theorem/definition
(name, frozen file, full signature up to `:=`). The frozen file is the signature of record. Output: Markdown.
Usage: python3 scripts/statement_map.py > manuscript/APPENDIX_E_STATEMENT_MAP.md"""
import glob, re
print('# Appendix E — Statement map (generated from frozen_statements/, signature of record)\n')
print('| Lean name | frozen file | signature |\n|---|---|---|')
n = 0
for f in sorted(glob.glob('frozen_statements/*_STATEMENTS.lean')):
    s = open(f).read()
    for m in re.finditer(r'^(theorem|def|noncomputable def|abbrev|structure|inductive) (\S+)((?:.|\n)*?)(?::=| where|\n\n)', s, re.M):
        kind, name, sig = m.group(1), m.group(2), ' '.join(m.group(3).split())
        sig = sig.replace('|', '\\|')
        print(f'| `{name}` ({kind.split()[-1]}) | {f.split("/")[-1]} | `{sig}` |'); n += 1
print(f'\n{n} declarations.')
