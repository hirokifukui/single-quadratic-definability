#!/usr/bin/env python3
"""generate_signoff_sheet.py -- regenerate release/AUTHOR_SIGNOFF_SHEET.md (s41, Gate-15 F05).

One row per (paper label, Lean root) of submission/native/PAPER_CLAIMS.tsv, in registry order. Each row carries the
paper statement as it stands in the native TeX (lightly de-TeXed for reading, not normalised), the elaborated Lean
type and its SHA-256 from the Layer-2 review row (PAPER_CLAIMS_REVIEW.tsv, which paper_claims_check.py keeps
current against certificates/PAPER_CLAIM_LEAN_TYPES.tsv), the registry's words, the Layer-2 disposition, and the
four author fields. Author fields are never generated: an existing sheet's filled fields are carried over by
(label, fully-qualified root) when BOTH the row's claim_hash AND its full type_sha256 are unchanged; a row whose
statement or type changed, whose old row lacks either hash, or whose key is duplicated in the old sheet comes back
blank (a duplicated key stops the run), so a signature never outlives what it signed.  (s42, Gate-16 P0-2: the s41
version compared the 16-hex type prefix only and never read claim_hash; tools/signoff_controls.py plants the six
regression cases.)

Usage: python3 tools/generate_signoff_sheet.py <vault_root> [--native <dir>] [--out <file>]
Prints SIGNOFF_ROWS=, SIGNOFF_CARRIED=, SIGNOFF_INVALIDATED=, SIGNOFF_BLANK=; exit 1 if a registry root has no
review row; exit 2 if the existing sheet has two rows with the same (label, root).
"""
import csv, os, re, sys, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from native_statement_check import ENV2KIND

CREF_KIND = {"theorem": "Theorem", "lemma": "Lemma", "proposition": "Proposition", "corollary": "Corollary",
             "definition": "Definition", "remark": "Remark", "example": "Example", "sec": "Section"}

def readable(s):
    s = re.sub(r"\\allowbreak\{\}", "", s)
    s = re.sub(r"\\texttt\{([^{}]*)\}", lambda m: "`" + m.group(1).replace("\\_", "_") + "`", s)
    s = re.sub(r"\\[cC]ref\{([a-z]+):([0-9A-Z.]+)\}", lambda m: CREF_KIND.get(m.group(1), m.group(1)) + " " + m.group(2), s)
    s = re.sub(r"\\eqref\{eq:([0-9A-Z.]+)\}", r"(\1)", s)
    s = re.sub(r"\\(?:mathrm|text|textbf|emph|textit)\{([^{}]*)\}", r"\1", s)
    s = re.sub(r"\\label(?:\[[^\]]*\])?\{[^}]*\}", "", s)
    s = re.sub(r"\\(?:begin|end)\{[a-z*]+\}", " ", s)
    s = s.replace("\\[", " ").replace("\\]", " ").replace("\\item", " ")
    s = re.sub(r"\s+", " ", s).strip()
    return s

def tex_statements_raw(native):
    out = {}
    for f in sorted(glob.glob(os.path.join(native, "sections", "*.tex"))):
        t = open(f, encoding="utf-8").read()
        for m in re.finditer(r"\\begin\{(theorem|lemma|proposition|corollary|definition|remark|example|conjecture|notation|question)(Part|\*)?\}(?:\[(.*?)\])?(?:\\label(?:\[[^\]]*\])?\{[^}]*:([^}]*)\})?(.*?)\\end\{\1\2?\}", t, re.S):
            env, num, body = m.group(1), m.group(4) or "", m.group(5)
            if not num: continue
            body = body.split("\\begin{proof}")[0]
            out[(ENV2KIND[env], num)] = readable(body)
    return out

def parse_existing(path):
    if not os.path.exists(path): return {}
    t = open(path, encoding="utf-8").read(); rows = {}
    for blk in re.split(r"(?m)^## Row \d+ — ", t)[1:]:
        m = re.match(r"(\S+ \S+) ↔ `([^`]+)`", blk)
        if not m: continue
        sha = re.search(r"sha256 ([0-9a-f]{64})\b", blk)          # the FULL type hash; a 16-hex prefix (s41 sheets) is not accepted
        ch = re.search(r"claim_hash ([0-9a-f]{8,64})\b", blk)
        fields = {k: re.search(r"(?m)^%s=(.*?)\s*$" % k, blk) for k in ("AUTHOR_REVIEWER", "AUTHOR_DISPOSITION", "AUTHOR_SIGNOFF_DATE")}
        key = (m.group(1), m.group(2))
        if key in rows:
            print("FAIL existing sheet has two rows for %s <-> %s; refusing to carry anything" % key); sys.exit(2)
        rows[key] = (sha.group(1) if sha else "", ch.group(1) if ch else "",
                     {k: (v.group(1).strip() if v else "") for k, v in fields.items()})
    return rows

def carry(prev, sha, claim_hash):
    """Carry the author fields only when the old row is signed, both hashes are present, and both match exactly."""
    if not prev: return False
    old_sha, old_ch, fields = prev
    if not fields.get("AUTHOR_REVIEWER"): return False
    if not old_sha or not old_ch: return False
    return old_sha == sha and old_ch == claim_hash

def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    vault = os.path.abspath(args[0] if args else ".")
    native = os.path.join(vault, "submission", "native")
    if "--native" in sys.argv: native = sys.argv[sys.argv.index("--native") + 1]
    out_path = os.path.join(vault, "release", "AUTHOR_SIGNOFF_SHEET.md")
    if "--out" in sys.argv: out_path = sys.argv[sys.argv.index("--out") + 1]
    man = list(csv.DictReader(open(os.path.join(native, "PAPER_CLAIMS.tsv"), encoding="utf-8"), delimiter="\t"))
    review = {}
    for q in csv.DictReader(open(os.path.join(native, "PAPER_CLAIMS_REVIEW.tsv"), encoding="utf-8"), delimiter="\t"):
        review[(q["paper_label"], q["Lean_root"].split(".")[-1])] = q
    stmts = tex_statements_raw(native)
    old = parse_existing(out_path)
    rows = []; missing = 0
    for r in man:
        kind, num = r["paper_label"].split(" ", 1)
        for name in [x.strip() for x in r["Lean_root"].split(",") if x.strip()]:
            q = review.get((r["paper_label"], name))
            if q is None: print("FAIL %s: no Layer-2 review row for %s" % (r["paper_label"], name)); missing += 1; continue
            rows.append((r, name, q, stmts.get((kind, num), "(statement not found in the native TeX)")))
    n = len(rows); L = []
    L.append("# Author sign-off sheet — paper statement ↔ Lean type, one row per cited root (%d rows)\n" % n)
    L.append("Generated by `tools/generate_signoff_sheet.py` from the paper-claim registry and its Layer-2 review; regenerated at every assembly. Author fields are carried over only while the row's claim_hash and full type sha256 are both unchanged (s42); a row whose old hashes are missing or whose statement or type changed comes back blank.\n")
    L.append("Purpose (Gate-14 P02 option A / §18): the twelve-point author check the reviewer asked for. Each row shows the paper statement as printed and the fully elaborated Lean type of the cited root, with the registry's recorded domain, free arity, witness domain, degree bound, quantifier pattern and external hypotheses, and the Layer-2 (model) disposition.\n")
    L.append("Points to check on every row: (1) domain, (2) free arity, (3) witness domain, (4) degree bound, (5) quantifier order, (6) external inputs, (7) iff versus implication, (8) finite subset versus whole fibre, (9) direct match versus match via a named theorem, (10) the conclusion as printed is the conclusion of the type, (11) the hypotheses as printed are the hypotheses of the type, (12) the paper claims nothing the type does not.\n")
    L.append("Fill: `AUTHOR_REVIEWER=Hiroki Fukui` · `ASSISTED_BY=Claude` · `AUTHOR_DISPOSITION=MATCH | MATCH VIA <thm> | MISMATCH` · `AUTHOR_SIGNOFF_DATE=YYYY-MM-DD`\n")
    carried = 0; invalidated = 0
    for i, (r, name, q, stmt) in enumerate(rows, 1):
        fq = q["Lean_root"]; sha = q["type_sha256"]
        prev = old.get((r["paper_label"], fq))
        fields = {"AUTHOR_REVIEWER": "", "AUTHOR_DISPOSITION": "", "AUTHOR_SIGNOFF_DATE": ""}
        if carry(prev, sha, r["claim_hash"]):
            fields = prev[2]; carried += 1
        elif prev and prev[2].get("AUTHOR_REVIEWER"):
            invalidated += 1
        L.append("## Row %02d — %s ↔ `%s`\n" % (i, r["paper_label"], fq))
        L.append("**Paper statement.** %s\n" % stmt)
        L.append("**Lean type (elaborated, normalised; sha256 %s; claim_hash %s).** `%s`\n" % (sha, r["claim_hash"], q["normalized_lean_type"]))
        L.append("**Registry.** domain: %s · free arity: %s · witness domain: %s · degree bound: %s · quantifier pattern: %s · external hypotheses: %s\n" %
                 (r["domain"], r["free_arity"], r["witness_domain"], r["degree_bound"], r["quantifier_pattern"], r["external_hypotheses"]))
        L.append("**Layer-2 disposition (%s, %s).** %s\n" % (q["reviewer"], q["date"], q["disposition"]))
        L.append("AUTHOR_REVIEWER=%s  \nASSISTED_BY=Claude  \nAUTHOR_DISPOSITION=%s  \nAUTHOR_SIGNOFF_DATE=%s  \n" % (fields["AUTHOR_REVIEWER"], fields["AUTHOR_DISPOSITION"], fields["AUTHOR_SIGNOFF_DATE"]))
    open(out_path, "w", encoding="utf-8").write("\n".join(L))
    print("SIGNOFF_ROWS=%d" % n); print("SIGNOFF_CARRIED=%d" % carried); print("SIGNOFF_INVALIDATED=%d" % invalidated); print("SIGNOFF_BLANK=%d" % (n - carried))
    print("SIGNOFF_EXIT=%d" % (1 if missing else 0)); sys.exit(1 if missing else 0)

if __name__ == "__main__":
    main()
