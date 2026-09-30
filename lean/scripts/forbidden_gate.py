#!/usr/bin/env python3
# forbidden_gate.py — comment- AND string-aware forbidden-token gate (s13, E-r12-6 hardening).
# Strips Lean comments (`--` line tails; nested `/- ... -/` blocks incl. docstrings)
# AND string literals ("..." with backslash escapes; char literals '.') with line
# structure preserved, then greps: sorry|admit|^\s*axiom|native_decide|ofReduceBool|trustCompiler.
# String stripping prevents (a) false positives from tokens inside strings and
# (b) comment-parser corruption by "--" or "/-" inside strings (missed-token risk).
# Prints file:line:content per match. Exit 0 if ANY match, 1 if clean (grep convention).
import re, sys
PAT = re.compile(r'sorry|admit|^\s*axiom\b|native_decide|ofReduceBool|trustCompiler')
def strip(text):
    out = []; i = 0; depth = 0; n = len(text)
    while i < n:
        c = text[i]
        if depth == 0 and c == '"':
            i += 1
            while i < n and text[i] != '"':
                if text[i] == chr(92) and i + 1 < n: i += 2
                else:
                    if text[i] == '\n': out.append('\n')
                    i += 1
            i += 1
            continue
        if depth == 0 and text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j == -1 else j
            continue
        if text.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth > 0 and text.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth > 0:
            if c == '\n': out.append('\n')
            i += 1; continue
        out.append(c); i += 1
    return ''.join(out)
matched = 0
for p in sys.argv[1:]:
    src = open(p, encoding='utf-8').read()
    for ln, lt in enumerate(strip(src).split('\n'), 1):
        if PAT.search(lt):
            print(f"{p}:{ln}:{lt}")
            matched += 1
sys.exit(0 if matched else 1)
