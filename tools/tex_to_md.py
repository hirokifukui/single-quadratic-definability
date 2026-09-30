#!/usr/bin/env python3
"""tex_to_md.py -- the Markdown mirror, generated ONE WAY from the native TeX (s38, Gate-12 C02/F01).

Until r34 manuscript/MANUSCRIPT_V32.md was hand-maintained (archived: history/manuscript_hand_mirror/) beside the TeX and kept equal to it by
native_statement_check.py.  This tool produces that Markdown from submission/native/, so that the
prose scanners (gate5, census, proof-by-citation, destroyer, figures) can keep reading Markdown while
the TeX is the only source.  The conversion inverts md_to_native_tex.py and the s38 math-mode pass:
statement environments -> **Kind N.M** (note). ..., proof -> *Proof.* ... ∎, itemize -> "- ",
\\[..\\] -> indented display, $x_{k}$ -> xₖ, ^{n} -> ⁿ, \\cref -> words, \\cite -> [K].
Usage: python3 tools/tex_to_md.py <native_dir> <out.md>
"""
import glob, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from native_statement_check import ENV2KIND, _cref

SUB = dict(zip("0123456789+-aehijklmnoprstuvx()", "₀₁₂₃₄₅₆₇₈₉₊₋ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓ₍₎"))
SUP = dict(zip("0123456789+-nmrskijt", "⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻ⁿᵐʳˢᵏⁱʲᵗ"))
def _script(s, table, sym):
    if all(c in table for c in s): return "".join(table[c] for c in s)
    return sym + "{" + s + "}" if len(s) > 1 else sym + s

def math_to_unicode(m):
    s = m
    s = re.sub(r"\\(?:text|mathrm|mathsf|operatorname)\{([^{}]*)\}", r"\1", s)
    s = s.replace("\\mid", "|").replace("\\ ", " ")
    s = re.sub(r"\\tilde\{([^{}]*)\}", "\\1\u0303", s)
    # subscripts came from the mirror's ASCII forms (S_m, X_{k+1}, ‖a‖_∞): emit ASCII, braces only when compound
    def _sub(k):
        x = k.group(1)
        if re.fullmatch(r"[0-9]+", x): return "".join(SUB[c] for c in x)          # a₁, SE₂: Unicode in the mirror
        if re.fullmatch(r"[A-Za-z0-9∞′]+", x): return "_" + x                   # S_m, DPRM_NN, ‖a‖_∞
        return "_{" + x + "}"                                                   # X_{k+1}
    s = re.sub(r"_\{([^{}]*)\}", _sub, s)
    s = re.sub(r"\^\{([^{}]*)\}", lambda k: "".join(SUP[c] for c in k.group(1)) if all(c in SUP for c in k.group(1)) else ("^" + k.group(1) if re.fullmatch(r"[A-Za-z0-9]+", k.group(1)) else "^(" + k.group(1) + ")"), s)
    s = s.replace("\\quad", "  ").replace("\\{", "{").replace("\\}", "}")
    s = re.sub(r"(?<=\S) {2,}(?=\S)", " ", s) if "\n" not in s else s
    return s

def inline(s):
    s = re.sub(r"\$([^$]*)\$", lambda m: math_to_unicode(m.group(1)), s)
    s = re.sub(r"\\[cC]ref\{([a-z]+):([0-9A-Z.]+)\}", _cref, s)
    s = re.sub(r"\\eqref\{eq:([0-9A-Z.]+)\}", r"(\1)", s)
    s = re.sub(r"\\cite\{([^}]*)\}", lambda m: "[" + ", ".join(m.group(1).split(",")) + "]", s)
    s = s.replace("\\allowbreak{}", "")
    for _ in range(3):
        s = re.sub(r"\\texttt\{([^{}]*)\}", lambda m: "`" + m.group(1).replace("\\_", "_").replace("\\{", "{").replace("\\}", "}").replace("\\textbackslash{}", "\\") + "`", s)
        s = re.sub(r"\\(?:emph|textit)\{([^{}]*)\}", r"*\1*", s)
        s = re.sub(r"\\textbf\{([^{}]*)\}", r"**\1**", s)
    s = s.replace("\\textbackslash{}", "\\").replace("\\textasciitilde{}", "~").replace("\\textasciicircum{}", "^")
    s = re.sub(r"\\([_{}%&#$])", r"\1", s)
    s = s.replace("~", " ")
    return s

def section_title(f, star, title):
    b = os.path.basename(f)
    m = re.match(r"\d\d_s(\d+)_", b)
    if m and not star: return "## %s. %s" % (m.group(1), title)
    m = re.match(r"\d\d_app([a-f])_", b)
    if m and not star: return "## Appendix %s. %s" % (m.group(1).upper(), title)
    return "## " + title

def convert_file(f):
    t = open(f, encoding="utf-8").read()
    t = re.sub(r"(?m)^%.*\n", "", t)
    out = []
    pos = 0
    tok = re.compile(r"\\section(\*?)\{([^\n]*)\}(?:\\label(?:\[[^\]]*\])?\{[^}]*\})?\n(?:\\addcontentsline\{[^}]*\}\{[^}]*\}\{[^}]*\}\n)?|\\subsection\*\{([^\n]*)\}\n|\\subsubsection\*\{([^\n]*)\}\n"
                     r"|\\begin\{(theorem|lemma|proposition|corollary|definition|remark|example|conjecture|notation|question)(Part|\*)?\}(?:\[((?:[^\[\]]|\[[^\]]*\])*)\])?(?:\\label(?:\[[^\]]*\])?\{([^}]*)\})?(.*?)\\end\{\5\6?\}\n?"
                     r"|\\begin\{proof\}(?:\[([^\]]*)\])?\n?|(\\end\{proof\})\n?", re.S)
    def flush(chunk):
        chunk = re.sub(r"\\begin\{itemize\}\n?(.*?)\\end\{itemize\}", lambda m: "\n".join("- " + x.strip() for x in re.split(r"\\item ", m.group(1))[1:]), chunk, flags=re.S)
        chunk = re.sub(r"\\begin\{enumerate\}\n?(.*?)\\end\{enumerate\}", lambda m: "\n".join("%d. %s" % (i + 1, x.strip()) for i, x in enumerate(re.split(r"\\item ", m.group(1))[1:])), chunk, flags=re.S)
        chunk = re.sub(r"\\begin\{displaytext\}\n?(.*?)\n?\\end\{displaytext\}", lambda m: "\n".join("  " + l for l in m.group(1).strip().split("\n")), chunk, flags=re.S)
        chunk = re.sub(r"\\begin\{equation\}\\tag\{([^}]*)\}\\label\{[^}]*\}\n?(.*?)\n?\\end\{equation\}", lambda m: "  " + math_to_unicode(m.group(2).strip()) + "  (" + m.group(1) + ")", chunk, flags=re.S)
        chunk = re.sub(r"\\\[\n?\\begin\{gathered\}\n?(.*?)\n?\\end\{gathered\}\n?\\\]", lambda m: "\n".join("  " + math_to_unicode(l.strip().rstrip("\\").strip()) for l in m.group(1).split("\\\\")), chunk, flags=re.S)
        chunk = re.sub(r"\\\[\n?(.*?)\n?\\\]", lambda m: "  " + math_to_unicode(m.group(1).strip()), chunk, flags=re.S)
        def table(m):
            body = m.group(1)
            rows = [r for r in body.split("\\\\") if "&" in r]
            def cells(r):
                r = re.sub(r"\\(?:toprule|midrule|bottomrule|endhead)", "", r).strip()
                return [c.strip().replace("\\|", "|") for c in re.split(r"(?<!\\)&", r)]
            out = []
            for i, r in enumerate(rows):
                cs = cells(r)
                out.append("| " + " | ".join(cs) + " |")
                if i == 0: out.append("|" + "---|" * len(cs))
            return "\n".join(out)
        chunk = re.sub(r"\\begin\{longtable\}\{[^\n]*\}\n(.*?)\\end\{longtable\}", table, chunk, flags=re.S)
        chunk = re.sub(r"\\bibitem\[([^\]]*)\]\{[^}]*\} ", r"[\1] ", chunk)
        chunk = re.sub(r"(?m)^\\(?:begin|end)\{thebibliography\}.*\n|^\\renewcommand.*\n|^\\vspace.*\n", "", chunk)
        chunk = chunk.replace("\\input{appendix_e_table}", "\n<!--APPENDIX_E_TABLE-->\n").replace("\\appendix\n", "").replace("\\addcontentsline{toc}{section}{Introduction}\n", "")
        return inline(chunk)
    for m in tok.finditer(t):
        out.append(flush(t[pos:m.start()])); pos = m.end()
        # a heading, a statement head or a proof head opens a paragraph of its own
        if not m.group(11) and out and out[-1].strip() and not out[-1].endswith("\n\n"):
            out[-1] = out[-1].rstrip("\n") + "\n\n"
        if m.group(2) is not None: out.append(section_title(f, m.group(1), inline(re.sub(r"\}\\label(?:\[[^\]]*\])?\{[^}]*$", "", m.group(2)))) + "\n\n")
        elif m.group(3) is not None: out.append("### " + inline(m.group(3)) + "\n\n")
        elif m.group(4) is not None: out.append("#### " + inline(m.group(4)) + "\n\n")
        elif m.group(5) is not None:
            kind, note, lab, body = ENV2KIND[m.group(5)], m.group(7) or "", m.group(8) or "", m.group(9)
            num = lab.split(":")[-1] if lab else ""
            head = "**%s%s**" % (kind, (" " + num) if num else "")
            body = flush(body.strip("\n"))
            # the mirror's convention: a paragraph that continues a statement (display, case list) is indented
            paras_ = [q for q in re.split(r"\n\s*\n", body) if q.strip()]
            body = "\n\n".join([paras_[0]] + ["\n".join(("  " + l if not re.match(r"\s*(?:- |\d+\. )", l) and not l.startswith("  ") else l) for l in q.split("\n")) for q in paras_[1:]]) if paras_ else body
            note = re.sub(r"^[IVX]+\.\d+[^;]*;\s*", "", inline(note))   # display-only irregular label
            if re.fullmatch(r"[IVX]+\.\d+[^;]*\.", (m.group(7) or "").strip()) and not num:
                out.append("**%s %s** %s\n\n" % (kind, (m.group(7) or "").strip(), body.lstrip()))   # display-only label, e.g. Lemma III.2′.
            elif note: out.append(head + " (" + note + "). " + body.lstrip() + "\n\n")
            elif body.lstrip().startswith("("): out.append(head + " " + body.lstrip() + "\n\n")   # note carried in the body (Part statements)
            else: out.append(head + ". " + body.lstrip() + "\n\n")
        elif m.group(11):   # \end{proof}: the tombstone closes the paragraph that is open
            while out and not out[-1].strip(): out.pop()
            if out: out[-1] = out[-1].rstrip() + " ∎\n\n"
        else:               # \begin{proof}[..]: proofs may nest (Part I of Appendix F), so the body flows
            lab = m.group(10)
            out.append("*Proof%s.* " % ((" of " + inline(lab).replace("Proof of ", "")) if lab else ""))
    out.append(flush(t[pos:]))
    s = "".join(out)
    s = re.sub(r"\n{3,}", "\n\n", s)
    return s

def main():
    native, out = sys.argv[1], sys.argv[2]
    fm = open(os.path.join(native, "frontmatter.tex"), encoding="utf-8").read()
    parts = ["# " + re.search(r"\\title\{(.*)\}", fm).group(1) + "\n\n"]
    # frontmatter in the mirror's order: author, funding/competing, keywords, MSC, abstract, rule
    parts.append("**Author.** Hiroki Fukui (Research Institute of Criminal Psychiatry / Sex Offender Medical Center, Tokyo, Japan; Department of Neuropsychiatry, Kyoto University, Kyoto, Japan).\n\n")
    parts.append("**Funding.** This research did not receive any specific grant from funding agencies in the public, commercial, or not-for-profit sectors. **Competing interests.** The author declares no known competing financial interests or personal relationships that could have appeared to influence the work reported in this paper.\n\n")
    kw = re.search(r"\\textbf\{Keywords\.\}\s*(.*)", fm).group(1).strip()
    msc = re.search(r"\\textbf\{MSC 2020\.\}\s*(.*)", fm).group(1).strip()
    parts.append("**Keywords.** " + kw + "\n\n**MSC 2020.** " + msc + "\n\n")
    ab = re.search(r"\\begin\{abstract\}\n(.*?)\\end\{abstract\}", fm, re.S).group(1).strip()
    parts.append("**Abstract.** " + inline(ab) + "\n\n---\n\n")
    for f in sorted(glob.glob(os.path.join(native, "sections", "*.tex"))):
        parts.append(convert_file(f))
    open(out, "w", encoding="utf-8").write("".join(parts))
    print("TEX_TO_MD=%s chars=%d" % (out, sum(len(p) for p in parts)))

if __name__ == "__main__":
    main()
