#!/usr/bin/env python3
"""native_mathmode.py -- move the native TeX's typeset-as-text mathematics into math mode (s38, Gate-12 T03-T07).

The migrated source printed superscripts with \\textsuperscript{}, subscripts with an escaped
underscore, and displays as a quote environment of text.  This pass rewrites the three
mechanically, and only the three:
  TOKEN\\textsuperscript{S}           -> $TOKEN^{S}$
  TOKEN\\_\\{S\\}  /  TOKEN\\_s          -> $TOKEN_{S}$
  \\begin{displaytext} FORMULA \\end{displaytext} -> \\[ FORMULA \\]  (only when the body is a formula:
      no English word, no text command; otherwise the display is left as it is and counted)
It never touches \\texttt{}, \\label{}, \\cref{}, \\cite{} or comments, and it is idempotent.
Usage: python3 tools/native_mathmode.py <sections_dir> [--apply]   (default: report only)
Prints MATHMODE_SUPERSCRIPTS=<n> MATHMODE_SUBSCRIPTS=<n> MATHMODE_DISPLAYS=<converted>/<total> MATHMODE_DISPLAYS_LEFT=<n>
"""
import glob, os, re, sys

PROTECT = re.compile(r"\\(?:texttt|label|cref|Cref|cite|input)(?:\[[^\]]*\])?\{[^{}]*\}|%[^\n]*")
TOKEN = r"[^\s{}\\$]+"
WORD = re.compile(r"[A-Za-z]{3,}")
MATHWORDS = {"mod", "deg", "min", "max", "rank", "det", "gcd", "lcm", "for", "and", "or", "if", "then", "with", "all",
             "every", "some", "where", "in", "variables", "of", "iff", "let", "such", "that", "not", "is", "the", "to", "on",
             "either", "else", "rfind", "univ", "Poly", "Fin", "Nat", "Int", "ZZ", "NN", "sorry"}

def _mask(t):
    keep = []
    def sub(m):
        keep.append(m.group(0)); return "\x00%d\x00" % (len(keep) - 1)
    return PROTECT.sub(sub, t), keep
def _unmask(t, keep):
    return re.sub(r"\x00(\d+)\x00", lambda m: keep[int(m.group(1))], t)

def _sub_body(s):
    s = s.replace("\\{", "{").replace("\\}", "}") if s.startswith("\\{") and s.endswith("\\}") else s
    if s.startswith("{") and s.endswith("}"): s = s[1:-1]
    if " " in s and re.search(r"[A-Za-z]{2,}", s):
        return "\\text{" + s + "}"
    return s

def convert(t):
    t, keep = _mask(t)
    n_sup = n_sub = 0
    # superscript with a preceding subscript: TOKEN\_\{S\}\textsuperscript{P} or TOKEN\_s\textsuperscript{P}
    def f_both(m):
        nonlocal n_sup, n_sub; n_sup += 1; n_sub += 1
        return "$%s_{%s}^{%s}$" % (m.group(1), _sub_body(m.group(2)), m.group(3))
    t = re.sub(r"(" + TOKEN + r")\\_(\\\{[^{}]*?\\\}|[A-Za-z0-9∞]+)\\textsuperscript\{([^{}]*)\}", f_both, t)
    def f_sup(m):
        nonlocal n_sup; n_sup += 1
        base = m.group(1)
        if base.endswith("$"): return base[:-1] + "^{%s}$" % m.group(2)
        return "$%s^{%s}$" % (base, m.group(2))
    t = re.sub(r"(" + TOKEN + r")\\textsuperscript\{([^{}]*)\}", f_sup, t)
    def f_sub(m):
        nonlocal n_sub; n_sub += 1
        base = m.group(1)
        if base.endswith("$"): return base[:-1] + "_{%s}$" % _sub_body(m.group(2))
        return "$%s_{%s}$" % (base, _sub_body(m.group(2)))
    t = re.sub(r"(" + TOKEN + r")\\_(\\\{[^{}]*?\\\}|[A-Za-z0-9∞]+)(?![A-Za-z0-9∞])", f_sub, t)
    # displays
    conv = left = 0
    def f_disp(m):
        nonlocal conv, left
        body = m.group(1).strip()
        words = [w for w in WORD.findall(re.sub(r"\\[A-Za-z]+", " ", body)) if w not in MATHWORDS and not w.isupper()]
        if words or "\\emph" in body or "\\textbf" in body or "\x00" in body:
            left += 1; return m.group(0)
        conv += 1
        b = body.replace("\\_\\{", "_{").replace("\\}", "}").replace("\\{", "{")
        b = re.sub(r"\\_([A-Za-z0-9∞]+)", r"_{\1}", b)
        b = re.sub(r"\\textsuperscript\{([^{}]*)\}", r"^{\1}", b)
        b = re.sub(r"\$([^$]*)\$", r"\1", b)           # inline math already made above lives inside the display
        lines = [l.strip() for l in b.split("\n") if l.strip()]
        lines = [re.sub(r" {3,}", r" \\quad ", l) for l in lines]
        if len(lines) == 1: return "\\[\n" + lines[0] + "\n\\]"
        return "\\[\n\\begin{gathered}\n" + " \\\\\n".join(lines) + "\n\\end{gathered}\n\\]"
    t = re.sub(r"\\begin\{displaytext\}\n?(.*?)\n?\\end\{displaytext\}", f_disp, t, flags=re.S)
    return _unmask(t, keep), n_sup, n_sub, conv, left

def main():
    d = sys.argv[1]; apply = "--apply" in sys.argv
    S = U = C = L = 0
    for f in sorted(glob.glob(os.path.join(d, "*.tex"))):
        t = open(f, encoding="utf-8").read()
        t2, s, u, c, l = convert(t)
        S += s; U += u; C += c; L += l
        if apply and t2 != t: open(f, "w", encoding="utf-8").write(t2)
    print("MATHMODE_SUPERSCRIPTS=%d MATHMODE_SUBSCRIPTS=%d MATHMODE_DISPLAYS=%d/%d MATHMODE_DISPLAYS_LEFT=%d APPLIED=%d" % (S, U, C, C + L, L, int(apply)))

if __name__ == "__main__":
    main()
