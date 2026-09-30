#!/usr/bin/env python3
"""native_statement_check.py -- every numbered statement of the native TeX source equals the
Markdown mirror's, after markup normalisation (s36, Gate-10 N06 / N08).

From r32 the PDF is built from submission/native/.  The Markdown (manuscript/MANUSCRIPT_V32.md) is
still what the prose scanners read, so it must not drift from the TeX: this gate extracts every
statement (theorem/lemma/proposition/corollary/definition/remark/example) from both, strips
markup, and requires the texts to agree label by label.  Any statement in one source and not the
other, or any text difference, is printed and is exit 1.

Usage: python3 tools/native_statement_check.py manuscript/MANUSCRIPT_V32.md submission/native
Prints NATIVE_STATEMENTS=<n> MD_STATEMENTS=<n> NATIVE_STATEMENT_MISMATCH=<n> NATIVE_STATEMENT_EXIT=<0|1>
"""
import glob, os, re, sys, unicodedata

KINDS = "Theorem|Lemma|Proposition|Corollary|Definition|Remark|Examples|Example|Conjecture|Notation|Question"
ENV2KIND = {"theorem": "Theorem", "lemma": "Lemma", "proposition": "Proposition", "corollary": "Corollary",
            "definition": "Definition", "remark": "Remark", "example": "Examples", "conjecture": "Conjecture",
            "notation": "Notation", "question": "Question"}

CREF_KIND = {"theorem": "Theorem", "lemma": "Lemma", "proposition": "Proposition", "corollary": "Corollary",
             "definition": "Definition", "remark": "Remark", "example": "Example"}
def _cref(m):
    # s38 (Gate-12 T01): the TeX carries \cref{kind:number}; the Markdown carries the words.
    k, n = m.group(1), m.group(2)
    if k == "sec": return ("Appendix " if n.isalpha() else "Section ") + n
    return CREF_KIND.get(k, k) + " " + n
def norm(s):
    s = re.sub(r"\\[cC]ref\{([a-z]+):([0-9A-Z.]+)\}", _cref, s)
    s = re.sub(r"\\eqref\{eq:([0-9A-Z.]+)\}", r"(\1)", s)
    s = re.sub(r"\\(?:tag|text)\{([^{}]*)\}", r"\1", s)
    s = re.sub(r"\\(texttt|textbf|emph|textit|label|allowbreak|item|begin|end)\{([^{}]*)\}", r"\2", s)
    s = re.sub(r"\\(textbackslash|textasciitilde|textasciicircum)\{\}", "", s)
    s = re.sub(r"\\[a-zA-Z]+\*?", "", s)
    s = s.replace("∎", "")
    s = re.sub(r"\b(itemize|enumerate|displaytext|gathered|equation|align)\b", "", s)
    # s37 (Gate-11 N11): the Markdown carries its list enumerators as literal "1." / "*",
    # the TeX carries them as \item, which the command strip above has already removed.
    # Drop the literal markers so that a list inside a statement compares on its content.
    s = re.sub(r"(?m)^[ \t]*(?:\d+\.|[*+-])[ \t]+", "", s)
    s = s.replace("^", "").replace("~", "")
    # s38 (Gate-12 T03-T07): inline/display math delimiters and \\text{} carry no meaning for the comparison.
    s = s.replace("$", "").replace("_", "")
    s = s.replace("\u0303", "")   # combining tilde: TeX \tilde{W} vs Markdown W̃   # TeX c_{0} vs Markdown c₀ (NFKC: c0)
    s = re.sub(r"[\\{}`*|\[\]\-]", "", s)
    s = unicodedata.normalize("NFKC", s)
    return re.sub(r"\s+", "", s)

def md_statements(path):
    t = open(path, encoding="utf-8").read()
    out = {}; counters = {}
    # s37 (Gate-11 N10): a block indented by whitespace continues the statement it follows.
    # This is the manuscript's own convention for displays and case lists inside a statement.
    # Before s37 the gate compared only the first paragraph, so a conclusion held in an indented
    # display sat outside the compared text on BOTH sides and could be mutated without detection.
    paras = []
    for p in re.split(r"\n\s*\n", t):
        cont = p[:1] in (" ", "\t") or re.match(r"^(?:\d+\.|[*+-])\s", p) is not None
        if paras and cont and p.strip():
            paras[-1] = paras[-1] + "\n\n" + p
        else:
            paras.append(p)
    for p in paras:
        m = re.match(r"^\*\*(%s)\s*([^*]*?)\*\*\s*(.*)$" % KINDS, p, re.S)
        m2 = re.match(r"^\*(Remark|Example) ([A-Z0-9.]+)\s*(?:\((.*?)\))?\.\*\s*(.*)$", p, re.S)
        note = ""
        if m2: kind, num, note, body = m2.group(1), m2.group(2), m2.group(3) or "", m2.group(4)
        elif m:
            kind, num, body = m.group(1), m.group(2).strip(), m.group(3)
            mn = re.match(r"^\((.*?)\)\.\s*(.*)$", body, re.S)
            if mn: note, body = mn.group(1), mn.group(2)
            elif body.startswith("."): body = body[1:].lstrip()
            if num.startswith("("):
                mm = re.match(r"^\((.*)\)\.?$", num); note = mm.group(1) if mm else num; num = ""
            elif num == ".": num = ""
        else: continue
        body = re.split(r"\*\*Proof\.\*\*|\*Proof(?: of [^*]+)?\.\*", body)[0]
        regular = re.fullmatch(r"\d+\.\d+|[A-Z]\.\d+|[IVX]+\.\d+", num)
        if regular: key = (kind, num)
        else:
            n = counters.get(kind, 0); counters[kind] = n + 1; key = (kind, "#%d" % n)
        out[key] = norm(("(" + note + ")." if note else "") + body)
    return out

def tex_statements(native):
    out = {}; counters = {}
    for f in sorted(glob.glob(os.path.join(native, "sections", "*.tex"))):
        t = open(f, encoding="utf-8").read()
        for m in re.finditer(r"\\begin\{(theorem|lemma|proposition|corollary|definition|remark|example|conjecture|notation|question)(Part|\*)?\}(?:\[(.*?)\])?(?:\\label(?:\[[^\]]*\])?\{[^}]*:([^}]*)\})?(.*?)\\end\{\1\2?\}", t, re.S):
            env, star, note, num, body = m.group(1), m.group(2), m.group(3) or "", m.group(4) or "", m.group(5)
            kind = ENV2KIND[env]
            body = body.split("\\begin{proof}")[0]
            if num: key = (kind, num)
            else:
                n = counters.get(kind, 0); counters[kind] = n + 1; key = (kind, "#%d" % n)
            note = re.sub(r"^[IVX]+\.\d+[^;\]]*(;\s*|$)", "", note)   # display-only irregular label
            text = ("(" + note + ")." if note else "") + body
            out[key] = norm(text)
    return out

def main():
    md, native = sys.argv[1], sys.argv[2]
    a, b = md_statements(md), tex_statements(native)
    # unnumbered keys are positional on both sides; align by kind order
    bad = 0
    # compare numbered keys directly
    for k in sorted(set(a) | set(b)):
        if k[1].startswith("#") or "#" in k[1]: continue
        if k not in a: print("ONLY_IN_TEX", k); bad += 1; continue
        if k not in b: print("ONLY_IN_MD", k); bad += 1; continue
        if a[k] != b[k]:
            bad += 1
            i = next((i for i in range(min(len(a[k]), len(b[k]))) if a[k][i] != b[k][i]), min(len(a[k]), len(b[k])))
            print("DIFF", k, "at", i, "md:", a[k][max(0, i - 30):i + 40], "| tex:", b[k][max(0, i - 30):i + 40])
    ua = [a[k] for k in a if "#" in k[1]]; ub = [b[k] for k in b if "#" in k[1]]
    if len(ua) != len(ub): print("UNNUMBERED_COUNT md=%d tex=%d" % (len(ua), len(ub))); bad += 1
    for i, (x, y) in enumerate(zip(ua, ub)):
        if x != y: bad += 1; print("DIFF_UNNUMBERED", i, x[:60], "|", y[:60])
    print("NATIVE_STATEMENTS=%d MD_STATEMENTS=%d NATIVE_STATEMENT_MISMATCH=%d" % (len(b), len(a), bad))
    print("NATIVE_STATEMENT_EXIT=%d" % (1 if bad else 0))
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
