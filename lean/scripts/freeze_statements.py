#!/usr/bin/env python3
"""freeze_statements.py — generate frozen_statements/<Name>_STATEMENTS.lean from a production file (s26).
Usage: python3 scripts/freeze_statements.py DiophCompression/<Name>.lean "<header text>"
Every `theorem` gets its proof replaced by `sorry` (statement cut at the LAST `:=` of the signature block,
which ends at the first line containing `:=`); defs/abbrevs/instances are copied verbatim; the leading
block comment and trailing `#print axioms` lines are dropped. Used for QuadraticCodes / EffectiveDiagonal /
DPRMTransport in s26; the frozen file must still type-check and statement_diff must report FAIL=0."""
import sys, os, re
src_path, header = sys.argv[1], sys.argv[2]
name = os.path.basename(src_path)[:-5]
src = open(src_path).read()
body = src[src.find('import '):]
body = body[:body.find('end DiophCompression')] + 'end DiophCompression\n'
lines = body.split('\n'); out = []; i = 0; n_thm = 0
while i < len(lines):
    l = lines[i]
    if l.startswith('theorem '):
        blk = []
        while True:
            blk.append(lines[i])
            if ':=' in lines[i]:
                break
            i += 1
        stmt = '\n'.join(blk)
        stmt = stmt[:stmt.rfind(':=')].rstrip() + ' := by\n  sorry'
        out.append(stmt); n_thm += 1
        i += 1
        while i < len(lines) and lines[i].strip() != '':
            i += 1
        continue
    out.append(l); i += 1
dst = f'frozen_statements/{name}_STATEMENTS.lean'
open(dst, 'w').write('/-\n  ' + header.strip() + '\n-/\n' + '\n'.join(out))
print(f'{dst}: {n_thm} theorems frozen')
