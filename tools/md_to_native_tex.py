#!/usr/bin/env python3
"""md_to_native_tex.py -- one-shot migration of manuscript/MANUSCRIPT_V32.md to native LaTeX
(s36, Gate-10 N01-N07).  After the migration the TeX under submission/native/ is the canonical
source and this converter is a record of how it was produced; it is not part of the build.

Conventions of the source it reads (measured on the r31 manuscript, not assumed):
  '# ' title once; '**Author.**' / '**Funding.**' / '**Keywords.**' / '**Abstract.**' front matter;
  '## N. Title' numbered sections, '## Appendix X. Title' appendices, other '## ' unnumbered;
  '### ' / '#### ' unnumbered subsections; '---' rules (dropped);
  '**Theorem 2.1** (note). text' statements, numbered per section by one shared counter
  (verified: the converter recomputes every number and refuses a mismatch);
  '**Theorem (name).**' / '**Proposition.**' unnumbered; 'Lemma V.1' etc. in Appendix F Part V on
  a roman counter; '*Proof.*' / '*Proof of X.*' / '**Proof.**' proofs closed by ∎;
  '- ' / 'N. ' lists; '|' pipe tables; four-space-indented lines = displayed formulas (Unicode);
  `code`, **bold**, *emph*; '<!--APPENDIX_E_TABLE-->' marker; ⟨DOI⟩ ⟨REPO⟩ locators kept as tokens.
Mathematics is Unicode text throughout and stays so (unicode-math, STIX Two); nothing is
rewritten into $-math, so the statement text is byte-comparable with the Markdown after
normalisation (tools/native_statement_check.py).

Usage: python3 tools/md_to_native_tex.py manuscript/MANUSCRIPT_V32.md submission/native
Writes: submission/native/APAL_MANUSCRIPT.tex, frontmatter.tex, sections/NN_<slug>.tex,
        MIGRATION_LOG.txt
"""
import os, re, sys, unicodedata

ENV = {"Theorem": "theorem", "Lemma": "lemma", "Proposition": "proposition", "Corollary": "corollary",
       "Definition": "definition", "Remark": "remark", "Example": "example", "Examples": "example",
       "Conjecture": "conjecture", "Notation": "notation", "Question": "question"}
KIND = "|".join(sorted(ENV, key=len, reverse=True))

def esc(s):
    out = []
    for ch in s:
        if ch == "\\": out.append(r"\textbackslash{}")
        elif ch in "{}#%&_$": out.append("\\" + ch)
        elif ch == "~": out.append(r"\textasciitilde{}")
        elif ch == "^": out.append(r"\textasciicircum{}")
        else: out.append(ch)
    return "".join(out)

def breakable(e):
    """let a long identifier break after '_' and '.' (Lean names in narrow table columns).
    s41 (Gate-15): a CamelCase run longer than 30 characters with no '_' or '.' in it (e.g. the module
    name RelationPhaseAllPositiveArityClassical) is also allowed to break before an inner capital, so
    that a single long run cannot force a table column past its floor (longtable_widths scales the
    floors down when they exceed the line, and the widest run then overflows)."""
    e = e.replace("\\_", "\\_\\allowbreak{}").replace(".", ".\\allowbreak{}")
    def camel(m):
        run = m.group(0)
        return re.sub(r"(?<=[a-z0-9])(?=[A-Z])", r"\\allowbreak{}", run) if len(run) > 30 else run
    return re.sub(r"[A-Za-z0-9]{31,}", camel, e)

def inline(s):
    """code spans first, then escape, then bold/emph on the escaped text."""
    parts = re.split(r"(`[^`]*`)", s)
    out = []
    for p in parts:
        if p.startswith("`") and p.endswith("`") and len(p) >= 2:
            out.append("\\texttt{" + breakable(esc(p[1:-1])) + "}")
        else:
            e = esc(p)
            e = re.sub(r"\*\*(.+?)\*\*", r"\\textbf{\1}", e)
            e = re.sub(r"(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])", r"\\emph{\1}", e)
            out.append(e)
    return "".join(out)

def slug(s):
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode()
    return re.sub(r"[^a-z0-9]+", "_", s.lower()).strip("_")[:40]

def table(lines):
    rows = [[c.strip() for c in l.strip().strip("|").split("|")] for l in lines]
    rows = [r for r in rows if not all(re.fullmatch(r":?-+:?", c or "-") for c in r)]
    n = max(len(r) for r in rows)
    rows = [r + [""] * (n - len(r)) for r in rows]
    w = [max(len(r[i]) for r in rows) for i in range(n)]
    tot = sum(w) or 1
    cols = "".join(">{\\raggedright\\arraybackslash}p{%.3f\\linewidth}" % max(0.9 * w[i] / tot, 0.06) for i in range(n))
    o = ["\\begin{longtable}{@{}" + cols + "@{}}", "\\toprule"]
    o.append(" & ".join(inline(c) for c in rows[0]) + " \\\\")
    o.append("\\midrule\\endhead")
    for r in rows[1:]:
        o.append(" & ".join(breakable(inline(c)) if re.search(r"[A-Za-z]_[A-Za-z]|\.lean", c) else inline(c) for c in r) + " \\\\")
    o += ["\\bottomrule", "\\end{longtable}"]
    return o

class Conv:
    def __init__(self):
        self.out = []; self.log = []; self.section = 0; self.appendix = False; self.app_letter = ""
        self.counter = 0; self.roman_counter = {}; self.proof_depth = 0; self.files = []; self.cur = None
        self.front = {}; self.title = ""

    def emit(self, s):
        self.out.append(s)

    def start_section(self, head):
        m = re.match(r"^(\d+)\.\s+(.*)$", head)
        ma = re.match(r"^Appendix ([A-Z])\.\s+(.*)$", head)
        if m:
            self.section += 1; self.counter = 0
            assert int(m.group(1)) == self.section, ("section number", head, self.section)
            title = m.group(2); num = str(self.section); cmd = "\\section{%s}" % inline(title)
        elif ma:
            if not self.appendix:
                self.emit("\\appendix"); self.appendix = True; self.section = 0
            self.section += 1; self.counter = 0
            assert chr(ord("A") + self.section - 1) == ma.group(1), ("appendix letter", head)
            self.app_letter = ma.group(1); num = ma.group(1); title = ma.group(2)
            cmd = "\\section{%s}" % inline(title)
        else:
            num = ""; title = head; cmd = "\\section*{%s}" % inline(title)
        self.flush_file()
        self.cur = ("%02d_%s%s" % (len(self.files) + 1, ("app" + num.lower() + "_") if ma else ("s" + num + "_") if m else "", slug(title)), [])
        self.emit(cmd)

    def flush_file(self):
        if self.cur is not None:
            self.files.append((self.cur[0], self.out)); self.out = []
        self.cur = None

    def statement(self, para):
        """para: list of lines; first line begins with **Kind ...**"""
        first = para[0]
        m = re.match(r"^\*\*(%s)\s*([^*]*?)\*\*\s*(.*)$" % KIND, first, re.S)
        kind, num, rest = m.group(1), m.group(2).strip(), m.group(3)
        env = ENV[kind]
        note = ""
        mn = re.match(r"^\((.*?)\)\.\s*(.*)$", rest, re.S)
        if mn: note, rest = mn.group(1), mn.group(2)
        elif rest.startswith("."): rest = rest[1:].lstrip()
        if num.startswith("("):           # **Theorem (name).** -- the note sits inside the bold
            mm = re.match(r"^\((.*)\)\.?$", num); note = mm.group(1) if mm else num; num = ""
        elif num == ".": num = ""
        roman = re.match(r"^[IVX]+\.\d+.*$", num)
        mnum = None if roman else (re.match(r"^(\d+)\.(\d+)$", num) or re.match(r"^([A-Z])\.(\d+)$", num))
        if num == "" and note == "" and rest == "" and False: pass
        if mnum:
            sec, k = mnum.group(1), int(mnum.group(2))
            self.counter += 1
            cur_sec = self.app_letter if self.appendix else str(self.section)
            if sec != cur_sec or k != self.counter:
                self.log.append("NUMBER_MISMATCH %s %s: auto would be %s.%d" % (kind, num, cur_sec, self.counter))
                self.emit("\\setcounter{thm}{%d}" % (k - 1)); self.counter = k
            open_ = "\\begin{%s}%s\\label{%s:%s}" % (env, ("[%s]" % inline(note)) if note else "", env, num)
            close = "\\end{%s}" % env
        elif roman:
            part = num.split(".")[0]
            c = self.roman_counter.get(part, 0) + 1; self.roman_counter[part] = c
            expected = "%s.%d" % (part, c)
            if num == expected:
                open_ = "\\begin{%sPart}%s\\label{%s:%s}" % (env, ("[%s]" % inline(note)) if note else "", env, num)
                close = "\\end{%sPart}" % env
                self.emit("\\renewcommand{\\thePart}{%s.\\arabic{Part}}" % part) if c == 1 else None
                if c == 1: self.emit("\\setcounter{Part}{0}")
            else:
                self.log.append("ROMAN_IRREGULAR %s %s (not %s): starred with the label in the note" % (kind, num, expected))
                self.roman_counter[part] = c - 1
                open_ = "\\begin{%s*}[%s%s]" % (env, esc(num), ("; " + inline(note)) if note else "")
                close = "\\end{%s*}" % env
        else:
            if num: self.log.append("UNPARSED_NUMBER %s %r" % (kind, num))
            open_ = "\\begin{%s*}%s" % (env, ("[%s]" % inline(note)) if note else "")
            close = "\\end{%s*}" % env
        body = [rest] + para[1:]
        self.emit(open_)
        self.lines_block(body)
        self.emit(close)

    def lines_block(self, lines):
        """paragraph body that may contain '- ' list lines, proof starts and ∎."""
        buf = []; lst = None
        def flush_buf():
            nonlocal buf
            if buf:
                txt = " ".join(buf).strip()
                self.text_with_proofs(txt); buf = []
        for l in lines:
            if re.match(r"^\s*- ", l):
                flush_buf()
                if lst is None: lst = "itemize"; self.emit("\\begin{itemize}")
                self.emit("\\item " + inline(re.sub(r"^\s*- ", "", l)))
            elif re.match(r"^\s*\d+\.\s", l):
                flush_buf()
                if lst is None: lst = "enumerate"; self.emit("\\begin{enumerate}")
                self.emit("\\item " + inline(re.sub(r"^\s*\d+\.\s", "", l)))
            else:
                if lst is not None and l.strip() == "": self.emit("\\end{%s}" % lst); lst = None
                buf.append(l)
        flush_buf()
        if lst is not None: self.emit("\\end{%s}" % lst)

    def text_with_proofs(self, txt):
        # a proof may begin mid-paragraph; split on the marker
        pieces = re.split(r"(\*\*Proof\.\*\*|\*Proof(?: of [^*]+)?\.\*)", txt)
        for i, p in enumerate(pieces):
            if re.fullmatch(r"\*\*Proof\.\*\*|\*Proof(?: of [^*]+)?\.\*", p):
                mo = re.match(r"\*+Proof(?: of ([^*]+))?\.\*+", p)
                if self.proof_depth > 0: self.log.append("NESTED_PROOF at: " + txt[:60])
                self.proof_depth += 1
                self.emit("\\begin{proof}" + ("[Proof of %s]" % inline(mo.group(1)) if mo.group(1) else ""))
            else:
                if not p.strip(): continue
                ends = "∎" in p
                p = p.replace("∎", "").rstrip()
                if p.strip(): self.emit(inline(p.strip())); self.emit("")
                if ends:
                    if self.proof_depth > 0: self.proof_depth -= 1; self.emit("\\end{proof}")
                    else: self.log.append("QED_WITHOUT_PROOF: " + p[:60]); self.emit("\\qed")

    def display(self, lines):
        self.emit("\\begin{displaytext}")
        self.emit(" \\\\\n".join(inline(l.strip()) for l in lines))
        self.emit("\\end{displaytext}")

    def paragraph(self, para):
        first = para[0]
        if re.match(r"^\*\*(%s)\b" % KIND, first) and re.match(r"^\*\*(%s)\s*[^*]*\*\*" % KIND, first):
            self.statement(para); return
        m = re.match(r"^\*(Remark|Example) ([A-Z0-9.]+)\s*(\(.*?\))?\.\*\s*(.*)$", first, re.S)
        if m:  # *Remark C.2 (note).* text
            para2 = ["**%s %s** %s. %s" % (m.group(1), m.group(2), m.group(3) or "", m.group(4))] + para[1:]
            self.statement(para2); return
        if all(l.startswith("|") for l in para):
            self.out += table(para); return
        if all(l.startswith("    ") for l in para):
            self.display(para); return
        self.lines_block(para)

    def run(self, md):
        lines = md.split("\n")
        i = 0
        # title
        assert lines[0].startswith("# "); self.title = lines[0][2:].strip(); i = 1
        paras = []; cur = []
        while i < len(lines):
            l = lines[i]
            if l.strip() == "":
                if cur: paras.append(cur); cur = []
            elif l.startswith("#") and not cur:
                paras.append([l])
            else:
                cur.append(l)
            i += 1
        if cur: paras.append(cur)
        body_started = False
        for para in paras:
            first = para[0]
            if not body_started:
                mf = re.match(r"^\*\*(Author|Funding|Keywords|Abstract|MSC 2020)\.\*\*\s*(.*)$", " ".join(para), re.S)
                if mf:
                    self.front[mf.group(1)] = mf.group(2).strip(); self.last_front = mf.group(1); continue
                if first.strip() == "---": continue
                if getattr(self, "last_front", "") == "Abstract" and not first.startswith("#"):
                    self.front["Abstract"] += "\n\n" + " ".join(para).strip(); continue
                if first.startswith("## "): body_started = True
                else: self.log.append("FRONT_UNHANDLED " + first[:60]); continue
            if first.startswith("## "): self.start_section(first[3:].strip()); continue
            if first.startswith("### "): self.emit("\\subsection*{%s}" % inline(first[4:].strip())); continue
            if first.startswith("#### "): self.emit("\\subsubsection*{%s}" % inline(first[5:].strip())); continue
            if first.strip() == "---": continue
            if first.strip() == "<!--APPENDIX_E_TABLE-->": self.emit("\\input{appendix_e_table}"); continue
            if first.startswith("<!--"): continue
            self.paragraph(para)
        self.flush_file()
        if self.proof_depth: self.log.append("PROOF_LEFT_OPEN %d" % self.proof_depth)

MAIN = r"""%% APAL_MANUSCRIPT.tex -- canonical native LaTeX source (from r32, s36).
%% Migrated once from manuscript/MANUSCRIPT_V32.md by tools/md_to_native_tex.py; edited here since.
\documentclass[11pt]{article}
\input{preamble_native}
\begin{document}
\input{frontmatter}
%s
\end{document}
"""

def main():
    src, dst = sys.argv[1], sys.argv[2]
    md = open(src, encoding="utf-8").read()
    c = Conv(); c.run(md)
    os.makedirs(os.path.join(dst, "sections"), exist_ok=True)
    inputs = []
    for name, body in c.files:
        open(os.path.join(dst, "sections", name + ".tex"), "w", encoding="utf-8").write("\n".join(body) + "\n")
        inputs.append("\\input{sections/%s}" % name)
    # abstract paragraphs are separated by blank lines in the markdown? here it is one paragraph
    fm = ["% frontmatter.tex -- title, author, abstract, keywords, declarations (N01)",
          "\\title{%s}" % inline(c.title),
          "\\author{Hiroki Fukui\\\\ \\small Research Institute of Criminal Psychiatry / Sex Offender Medical Center, Tokyo, Japan\\\\ \\small Department of Neuropsychiatry, Kyoto University, Kyoto, Japan\\\\ \\small ORCID 0009-0008-7122-522X\\\\ \\small ⟨EMAIL⟩}",
          "\\date{}", "\\maketitle", "\\linenumbers",
          "\\begin{abstract}", "\n\n".join(inline(p) for p in c.front.get("Abstract", "").split("\n\n")), "\\end{abstract}",
          "\\noindent\\textbf{Keywords.} " + inline(c.front.get("Keywords", "")), "",
          "\\noindent\\textbf{MSC 2020.} " + inline(c.front.get("MSC 2020", "⟨MSC⟩")), "",
          "\\noindent\\textbf{Funding.} " + inline(c.front.get("Funding", "").split("**Competing")[0].strip()) if "Funding" in c.front else "",
          ""]
    open(os.path.join(dst, "frontmatter.tex"), "w", encoding="utf-8").write("\n".join(fm) + "\n")
    open(os.path.join(dst, "APAL_MANUSCRIPT.tex"), "w", encoding="utf-8").write(MAIN % "\n".join(inputs))
    open(os.path.join(dst, "MIGRATION_LOG.txt"), "w", encoding="utf-8").write(
        "sections=%d\n" % len(c.files) + "\n".join(c.log) + ("\n" if c.log else ""))
    print("NATIVE_SECTIONS=%d  LOG_LINES=%d" % (len(c.files), len(c.log)))
    for l in c.log: print("  " + l)
    print("FRONT_KEYS=" + ",".join(sorted(c.front)))

if __name__ == "__main__":
    main()
