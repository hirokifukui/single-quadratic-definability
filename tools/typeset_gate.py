#!/usr/bin/env python3
r"""typeset_gate.py -- the typesetting conditions of Gate-11 N12/N13/N14/N17, as a gate.

Why (s37).  Every one of these conditions was measured by hand this round and then asserted in a
letter.  A number nobody recomputes is a claim, not a measurement: the r30 checklist said 52 pages
and 51 pages on two of its own lines.  So each condition is written here, run in the build, and
exercised by a planted defect that must make it exit 1.

Checks (each printed as TYPESET <name> <ok|FAIL> <detail>):
  RAW_BLOCKQUOTE_MARKERS    a line beginning with '>' -- Markdown quote that survived migration
  RAW_STAR_BULLETS          a line beginning with '* ' -- Markdown bullet that survived migration
  RAW_MD_EMPHASIS           *...* on one line -- Markdown emphasis that survived migration
  TEXTASCIICIRCUM           ^ kept as text instead of a superscript
  MALFORMED_DISPLAY_TABLES  a longtable with fewer than two data rows, or a cell holding
                            \textbackslash{} -- the shape a formula takes when the migrator reads
                            its absolute-value bars as column separators
  DUPLICATE_LABELS          the same \label twice
  STATEMENT_WITHOUT_PROOF   a numbered theorem/lemma/proposition/corollary with no proof after it
                            and no explicit pointer to where it is proved
  OVERFULL_GT_5PT           from the xelatex log, when one is given
  UNRESOLVED_REFS           idem
  UNDEFINED_CITATIONS       idem

Usage:  python3 tools/typeset_gate.py <dir-of-sections> [xelatex.log]
Exit 0 = every condition holds.
"""
import glob, os, re, sys

ENVS = r"(?:theorem|lemma|proposition|corollary)(?:Part|\*)?"
# s37: this pattern was first written loose enough that "This is the negative answer to the
# question" counted as a pointer to a proof, and deleting Theorem C.1's proof went undetected.
# A pointer must speak about a proof.
POINTER = re.compile(r"(is proved (in|here|as)|proved in (Appendix|Section|Part)|"
                     r"the (complete )?proof (of [^.]{0,40})?is (Appendix|Section|Part|given)|"
                     r"is what Appendix [A-F] proves|proof of \d|restated at the point)", re.I)

def main():
    root = sys.argv[1]
    log = sys.argv[2] if len(sys.argv) > 2 else None
    files = sorted(glob.glob(os.path.join(root, "*.tex")))
    text = {f: open(f, encoding="utf-8").read() for f in files}
    fails = 0
    def check(name, bad, detail=""):
        nonlocal fails
        if bad: fails += 1
        print("TYPESET %-26s %-4s %s" % (name, "FAIL" if bad else "ok", detail))

    def lines(pred):
        out = []
        for f, t in text.items():
            for i, l in enumerate(t.splitlines(), 1):
                if pred(l): out.append("%s:%d" % (os.path.basename(f), i))
        return out

    bq = lines(lambda l: l.startswith(">"))
    check("RAW_BLOCKQUOTE_MARKERS", bq, "%d %s" % (len(bq), bq[:3]))
    st = lines(lambda l: re.match(r"^\*\s", l))
    # s38 (found by the TeX->Markdown generator diff, not by any gate): three Introduction items read
    # "\item lassical inputs.* Decidability" -- an emphasis regex ate "\emph{C" and left a stray "*".
    # Any asterisk that is not the star of a starred command/environment is Markdown residue.
    stray = []
    for f, t in text.items():
        t2 = re.sub(r"\\(?:section|subsection|subsubsection|newtheorem|paragraph)\*|\\(?:begin|end)\{[a-zA-Z]+\*\}", "", t)
        # b* (a constant vector) is notation; Markdown residue is "*" after a full stop, doubled, or opening a word
        for m in re.finditer(r"(?<=\.)\*(?=\s)|\*\*|(?<=\s)\*(?=[A-Za-z])", t2):
            stray.append("%s:%s" % (os.path.basename(f)[:14], t2[max(0, m.start() - 20):m.start() + 10].replace("\n", " ")))
    check("STRAY_ASTERISKS", stray, "%d %s" % (len(stray), stray[:3]))
    check("RAW_STAR_BULLETS", st, "%d %s" % (len(st), st[:3]))
    em = [f for f, t in text.items()
          if re.search(r"(?<![\\\w])\*[^*\n]{2,120}\*(?!\*)", t)]
    check("RAW_MD_EMPHASIS", em, "%d files" % len(em))
    ci = sum(t.count("\\textasciicircum") for t in text.values())
    check("TEXTASCIICIRCUM", ci, str(ci))

    bad_tables = []
    for f, t in text.items():
        for m in re.finditer(r"\\begin\{longtable\}(\{[^\n]*\})\n(.*?)\\end\{longtable\}", t, re.S):
            spec, body = m.group(1), m.group(2)
            ncol = len(re.findall(r"p\{[0-9.]+\\linewidth\}", spec))
            rows = [r for r in body.splitlines() if "&" in r]
            why = []
            if len(rows) < 2: why.append("rows=%d" % len(rows))
            if "\\textbackslash{}" in body: why.append("textbackslash-in-cell")
            # s37: the r32 anchor table carried eight columns because three rows split on an
            # escaped bar.  A row whose cell count disagrees with the column spec is that defect.
            for r in rows:
                n = len(re.split(r"(?<!\\)&", re.sub(r"\\\\\s*$", "", r.strip())))
                if ncol and n != ncol:
                    why.append("row cells=%d spec=%d" % (n, ncol)); break
            if why:
                bad_tables.append("%s(%s)" % (os.path.basename(f), ",".join(why)))
    check("MALFORMED_DISPLAY_TABLES", bad_tables, "%d %s" % (len(bad_tables), bad_tables[:2]))

    # s38 (Gate-12 T02): references are \cite keys against a thebibliography; a raw "[GS04]" in the
    # body is a citation the TeX reference system never sees, and UNDEFINED_CITATIONS=0 says nothing
    # about it.
    raw = []
    for f, t in text.items():
        if os.path.basename(f).startswith("21_"): continue
        for m in re.finditer(r"\[((?:[A-Z][A-Za-z]*\d{2,}[a-z]?|DDF|Nag|mathlib)(?:,\s*[A-Za-z0-9]+)*)\]", t):
            raw.append("%s:%s" % (os.path.basename(f)[:14], m.group(1)))
    check("RAW_CITATION_KEYS", raw, "%d %s" % (len(raw), raw[:3]))

    # s38 (Gate-12 T01): references are \cref; a hard-coded "Theorem 2.1" / "Section 4" is a number
    # that will not follow a renumbering.  Allowlist: references into Appendix F's Parts (I.n-V.n),
    # whose environments are unnumbered and carry no counter for cleveref.
    hard = []
    for f, t in text.items():
        for m in re.finditer(r"(?<![\w\\{:])(Theorem|Proposition|Lemma|Definition|Corollary|Remark|Examples?) ([0-9A-Z]+\.[0-9]+)(?![\w.]*\})", t):
            if re.fullmatch(r"[IVX]+\.\d+", m.group(2)): continue
            hard.append("%s:%s" % (os.path.basename(f)[:14], m.group(0)))
        for m in re.finditer(r"(?<![\w\\{:])(Section|Appendix) ([0-9]+|[A-F])(?![\w.\-–])", t):
            hard.append("%s:%s" % (os.path.basename(f)[:14], m.group(0)))
    check("HARDCODED_REFERENCES", hard, "%d %s" % (len(hard), hard[:3]))

    # s39 (Gate-13 M05 + a self-found residue): the T01 scan above sees "Theorem 2.1" but not the bare
    # "is 6.3", "via 6.4(d)", "(2.1, 2.2)" of proofs and lists (72 at r34, and one that a renumbering
    # broke silently: "consequences of 1.4 and 1.5").  Every bare n.n that is the number of a labelled
    # statement, outside \cref/\label/\texttt/\cite and outside Appendix F (Part refs) and Appendix C
    # (a cited "§6.2" of BDHMS25), is a finding.
    labels = set()
    for f, t in text.items():
        for m in re.finditer(r"\\label\[\w+\]\{\w+:([0-9A-F]+\.[0-9]+)\}", t): labels.add(m.group(1))
    bare = []
    for f, t in text.items():
        b = os.path.basename(f)
        if b.startswith(("20_", "17_")): continue
        t2 = re.sub(r"\\(cref|crefrange|label|ref|cite|texttt|section\*?)(\[\w+\])?\{[^}]*\}(\{[^}]*\})?", " ", t)
        for m in re.finditer(r"(?<![\w.:$^{\\])([1-9]|[A-F])\.([0-9]+)(?![\d}])", t2):
            if "%s.%s" % (m.group(1), m.group(2)) in labels:
                bare.append("%s:%s" % (b[:14], t2[max(0, m.start() - 12):m.end() + 3].replace("\n", " ")))
    check("BARE_NUMBER_REFERENCES", bare, "%d %s" % (len(bare), bare[:3]))

    # s38 (Gate-12 T03-T07): mathematics is in math mode; a \textsuperscript in a section is an
    # exponent typeset as text (73 of them at r33), and a displaytext environment is a display that
    # is still prose.  The remaining displays are counted, not forbidden (six carry English words).
    ts = sum(t.count("\\textsuperscript") for t in text.values())
    check("TEXTSUPERSCRIPT_EXPONENTS", ts > 0, "%d" % ts)
    dt = sum(t.count("\\begin{displaytext}") for t in text.values())
    print("TYPESET DISPLAYTEXT_REMAINING     %d (counted, not gated)" % dt)
    md = sum(t.count("\\[") for t in text.values()); im = sum(len(re.findall(r"(?<!\\)\$", t)) // 2 for t in text.values())
    print("TYPESET MATH_DISPLAYS=%d MATH_INLINE=%d" % (md, im))

    # s38 (found by the TeX->Markdown generator diff): Definition 8.2 listed its three kinds as three
    # one-item enumerate environments, so the PDF numbered them 1, 1, 1 while the text cites
    # "Definition 8.2(2)".  An enumerate that ends and another that begins within 400 characters
    # (only a display and a sentence between) is a list whose numbering restarted.
    restart = []
    for f, t in text.items():
        for m in re.finditer(r"\\end\{enumerate\}(.{0,400}?)\\begin\{enumerate\}", t, re.S):
            if not re.search(r"\\(?:section|subsection|subsubsection|begin\{(?:theorem|lemma|definition|remark|example|proof|proposition|corollary))", m.group(1)):
                restart.append("%s:%s" % (os.path.basename(f)[:14], m.group(1)[:40].replace("\n", " ")))
    check("ENUMERATE_RESTARTS", restart, "%d %s" % (len(restart), restart[:3]))

    seen, dup = {}, []
    for f, t in text.items():
        for m in re.finditer(r"\\label(?:\[[^\]]*\])?\{([^}]*)\}", t):
            k = m.group(1)
            if k in seen: dup.append(k)
            seen[k] = f
    check("DUPLICATE_LABELS", dup, "%d %s" % (len(dup), dup[:3]))

    noproof = []
    pat = re.compile(r"\\begin\{(" + ENVS + r")\}(?:\[(?:[^\[\]]|\[[^\]]*\])*\])?\s*"
                     r"(?:\\label(?:\[[^\]]*\])?\{([^}]*)\})?(.*?)\\end\{\1\}", re.S)
    for f, t in text.items():
        for m in pat.finditer(t):
            lab = m.group(2) or "(unnumbered)"
            # A proof may not sit immediately after its statement: the manuscript states 2.1 and
            # 2.2 together and then proves them in order.  A statement counts as proved if a proof
            # environment opens within the next window, or if the statement or the paragraph after
            # it says where the proof is.
            # s38 (Gate-12 S03): the window was 3000 characters, so a proof of the NEXT theorem, or
            # a proof several paragraphs on, satisfied the gate for the statement before it
            # (Proposition 1.3 had 991 characters of unrelated prose before its proof and passed).
            # Now a statement counts as proved only if (a) its proof opens after nothing but
            # whitespace and TeX comments, or (b) a statement that follows it after nothing but
            # whitespace/comments is itself proved (the manuscript states 2.1 and 2.2 together and
            # proves them in order), declared by a "% PROOF-GROUP:" comment between them, or (c) the
            # statement text or the paragraph directly after it says where the proof is (POINTER).
            head = t[m.end():]
            gap = re.match(r"(?:\s|%[^\n]*\n)*", head).group(0)
            after = head[len(gap):]
            if after.startswith("\\begin{proof}"): continue
            if "PROOF-GROUP" in gap and re.match(r"\\begin\{(" + ENVS + r")\}", after): continue
            if POINTER.search(head[:600]) and not re.match(r"\\begin\{(" + ENVS + r")", after): continue
            if POINTER.search(m.group(3)): continue
            noproof.append("%s:%s" % (os.path.basename(f)[:14], lab))
    check("STATEMENT_WITHOUT_PROOF", noproof, "%d %s" % (len(noproof), noproof[:4]))

    unbal = []
    for f, t in text.items():
        for e in ("proof", "displaytext", "longtable", "enumerate", "itemize"):
            b_, e_ = t.count("\\begin{%s}" % e), t.count("\\end{%s}" % e)
            if b_ != e_: unbal.append("%s:%s(%d/%d)" % (os.path.basename(f)[:14], e, b_, e_))
    check("UNBALANCED_ENVIRONMENTS", unbal, "%d %s" % (len(unbal), unbal[:3]))

    if log and os.path.exists(log):
        lt = open(log, encoding="utf-8", errors="replace").read()
        big = [x for x in re.findall(r"Overfull \\hbox \(([0-9.]+)pt too wide\)", lt) if float(x) > 5]
        check("OVERFULL_GT_5PT", big, str(len(big)))
        ur = re.findall(r"Reference .* undefined", lt)
        check("UNRESOLVED_REFS", ur, str(len(ur)))
        uc = re.findall(r"Citation .* undefined", lt)
        check("UNDEFINED_CITATIONS", uc, str(len(uc)))
    else:
        print("TYPESET (log checks skipped: no xelatex log given)")

    print("TYPESET_GATE=%s checks_failed=%d" % ("OK" if fails == 0 else "FAIL", fails))
    return 1 if fails else 0

if __name__ == "__main__":
    sys.exit(main())
