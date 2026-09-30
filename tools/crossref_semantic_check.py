#!/usr/bin/env python3
"""crossref_semantic_check.py -- Gate 13 A02 (s39): does a cross-reference land on the statement it means?

\\cref resolves any label; it cannot tell that "the collapse at k = 0 is <ref>" should point at the arity-zero
proposition and not at the r.e. proposition next to it (the r34 defect, Gate-13 P0-2).  This tool reads
submission/native/CROSSREF_RULES.tsv: for each rule (file, anchor_regex with one group capturing the label,
expected_kind, expected_head_keyword) it finds the anchor in the section file, resolves the captured label to
its \\begin{<kind>}[<head>]...\\label[...]{<label>} in any section file, and requires kind == expected_kind and
expected_head_keyword in the head.  Anchor not found, label unresolved, wrong kind, or keyword absent: FAIL.
Prints CROSSREF_RULES=<n> CROSSREF_FAIL=<m> CROSSREF_EXIT=<0|1>.
Usage: python3 tools/crossref_semantic_check.py <root> [--native <dir>]
"""
import csv, glob, os, re, sys

def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = os.path.abspath(args[0] if args else ".")
    native = os.path.join(root, "submission", "native")
    if "--native" in sys.argv: native = sys.argv[sys.argv.index("--native") + 1]
    rules = list(csv.DictReader(open(os.path.join(native, "CROSSREF_RULES.tsv"), encoding="utf-8"), delimiter="\t"))
    labels = {}
    for f in glob.glob(os.path.join(native, "sections", "*.tex")):
        t = open(f, encoding="utf-8").read()
        for m in re.finditer(r"\\begin\{(\w+)\*?\}(\[(?:[^\[\]]|\[[^\]]*\])*\])?\s*\\label\[\w+\]\{([\w:.]+)\}", t):
            labels[m.group(3)] = (m.group(1), m.group(2) or "")
    bad = 0
    for r in rules:
        f = os.path.join(native, "sections", r["file"])
        if not os.path.exists(f):
            print("FAIL rule %r: file missing" % r["file"]); bad += 1; continue
        m = re.search(r["anchor_regex"], open(f, encoding="utf-8").read())
        if not m:
            print("FAIL %s: anchor %r not found" % (r["file"], r["anchor_regex"])); bad += 1; continue
        lab = m.group(1)
        if lab not in labels:
            print("FAIL %s: label %s unresolved" % (r["file"], lab)); bad += 1; continue
        kind, head = labels[lab]
        if kind != r["expected_kind"]:
            print("FAIL %s: %s is a %s, expected %s" % (r["file"], lab, kind, r["expected_kind"])); bad += 1; continue
        if r["expected_head_keyword"] not in head:
            print("FAIL %s: %s head %r lacks %r (reference lands on the wrong statement)" % (r["file"], lab, head[:60], r["expected_head_keyword"])); bad += 1; continue
        print("OK %s -> %s [%s] %r" % (r["anchor_regex"][:30], lab, kind, r["expected_head_keyword"]))
    print("CROSSREF_RULES=%d CROSSREF_FAIL=%d" % (len(rules), bad))
    print("CROSSREF_EXIT=%d" % (1 if bad else 0))
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
