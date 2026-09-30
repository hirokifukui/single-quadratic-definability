#!/usr/bin/env python3
"""detex_normalize.py — turn a LaTeX source into normalised plain text.

Why this exists. S05 moves the source of truth of the paper from Markdown to LaTeX. The 330-item
Gate-5 battery evaluates regular expressions against the manuscript TEXT; if the text is now inside
LaTeX markup, every one of those predicates would fail for a reason that has nothing to do with the
mathematics. So the migration needs a normaliser: LaTeX in, the same running text out, close enough
that the existing predicates keep their meaning. A predicate that then fails is a real change to
what the paper says -- which is exactly the signal the migration must not lose.

It is a normaliser, not a detex: it is allowed to be lossy about layout and must not be lossy about
words, numbers or mathematical symbols.

Usage:  python3 scripts/detex_normalize.py <in.tex> <out.txt>
"""
import re, sys

# Inverse of the champmap table in preamble.tex, plus the escapes pandoc introduces.
MATH = {
    r'\in': '∈', r'\notin': '∉', r'\leq': '≤', r'\geq': '≥', r'\neq': '≠',
    r'\equiv': '≡', r'\mid': '∣', r'\nmid': '∤', r'\to': '→', r'\mapsto': '↦',
    r'\Rightarrow': '⇒', r'\Leftarrow': '⇐', r'\Longrightarrow': '⟹',
    r'\Longleftrightarrow': '⟺', r'\blacksquare': '∎', r'\exists': '∃',
    r'\forall': '∀', r'\subseteq': '⊆', r'\subsetneq': '⊊', r'\infty': '∞',
    r'\surd': '√', r'\wedge': '∧', r'\vee': '∨', r'\cap': '∩', r'\oplus': '⊕',
    r'\emptyset': '∅', r'\circ': '∘', r'\ell': 'ℓ', r'\langle': '⟨', r'\rangle': '⟩',
}
ESCAPES = [(r'\_', '_'), (r'\&', '&'), (r'\%', '%'), (r'\$', '$'), (r'\#', '#'),
           (r'\{', '{'), (r'\}', '}'), (r'\textbackslash', '\\'),
           (r'\textasciitilde', '~'), (r'\textasciicircum', '^'), (r'~', ' ')]
# commands whose ARGUMENT is running text and must survive
KEEP_ARG = ('textbf', 'textit', 'emph', 'texttt', 'text', 'mathrm', 'mathsf', 'mathcal',
            'section', 'subsection', 'subsubsection', 'paragraph', 'caption', 'href',
            'label', 'ref', 'cite', 'footnote', 'item', 'title', 'author')
# environments whose CONTENT is running text and must survive
DROP_ENV_MARKERS = True

def normalize(s):
    s = re.sub(r'(?<!\\)%.*', '', s)                       # comments
    for a, b in MATH.items():
        s = s.replace(a + ' ', b + ' ').replace(a + '{', b + '{').replace(a, b)
    s = re.sub(r'\\begin\{(document|abstract)\}|\\end\{(document|abstract)\}', ' ', s)
    if DROP_ENV_MARKERS:
        s = re.sub(r'\\(begin|end)\{[A-Za-z*]+\}(\[[^\]]*\])?', ' ', s)
    # \cmd{arg} -> arg  for the keep list, repeatedly (nesting)
    keep = '|'.join(KEEP_ARG)
    for _ in range(6):
        s2 = re.sub(r'\\(?:' + keep + r')\*?\{([^{}]*)\}', r'\1', s)
        if s2 == s:
            break
        s = s2
    s = re.sub(r'\\[A-Za-z@]+\*?(\[[^\]]*\])?', ' ', s)    # remaining control sequences
    for a, b in ESCAPES:
        s = s.replace(a, b)
    s = s.replace('$', ' ').replace('{', ' ').replace('}', ' ')
    s = re.sub(r'[ \t]+', ' ', s)
    s = re.sub(r'\n{3,}', '\n\n', s)
    return s

if __name__ == '__main__':
    if len(sys.argv) != 3:
        sys.stderr.write("usage: detex_normalize.py <in.tex> <out.txt>\n"); sys.exit(2)
    src = open(sys.argv[1], encoding='utf-8').read()
    out = normalize(src)
    open(sys.argv[2], 'w', encoding='utf-8').write(out)
    print("IN_CHARS=%d OUT_CHARS=%d OUT=%s" % (len(src), len(out), sys.argv[2]))
