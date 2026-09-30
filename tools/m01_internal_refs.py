#!/usr/bin/env python3
"""M01 - detect references to internal/development artefacts inside the SHIPPING
manuscript and submission directories.  Detection only; no repair.
Search terms are assembled from fragments so the scanner cannot match its own source."""
import os, re, sys, csv

def T(*parts):            # build a term without writing it as one literal
    return "".join(parts)

MS   = T("MANUSCRIPT", "_V")
TERMS = [
    ("T1_old_manuscript_named", re.compile(MS + r"0?\d+")),
    ("T2_earlier_manuscript",   re.compile(T("earl", "ier ") + T("manu", "script"), re.I)),
    ("T3_earlier_document",     re.compile(T("earl", "ier ") + T("docu", "ment"), re.I)),
    ("T4_earlier_round",        re.compile(T("earl", "ier ") + T("rou", "nd"), re.I)),
    ("T5_previous_round",       re.compile(T("prev", "ious ") + T("rou", "nd"), re.I)),
    ("T6_round_token",          re.compile(r"\br" + r"\d{2}\b|\b" + T("rou", "nd") + r"\s+\d+", re.I)),
    ("T7_gate_token",           re.compile(r"\b" + T("Ga", "te") + r"[- ]?\d", re.I)),
    ("T8_this_package",         re.compile(T("this ", "pack") + "age", re.I)),
    ("T9_internal_revision",    re.compile(T("inter", "nal ") + T("revi", "sion"), re.I)),
    ("T10_V2_bare",             re.compile(r"(?<![A-Za-z0-9_])V2(?![0-9])")),
    ("T12_anaphoric_old_lemma", re.compile(r"(Lemma|Theorem|Corollary|Proposition)\s+C\.\d+\s+(there|of )")),
    ("T11_session_token",       re.compile(r"\bs\d{2}\b|\b" + T("sess", "ion") + r"\s+\d+", re.I)),
]

def main(root, outp):
    rows = []
    for d in ("manuscript", "submission"):
        dd = os.path.join(root, d)
        if not os.path.isdir(dd):
            print("MISSING_DIR " + dd); return 2
        for fn in sorted(os.listdir(dd)):
            p = os.path.join(dd, fn)
            if not os.path.isfile(p): continue
            if fn.lower().endswith((".pdf", ".png", ".jpg")):
                rows.append([d + "/" + fn, "-", "T0_binary",
                             "binary artefact: inherits hits of its source", ""])
                continue
            try:
                txt = open(p, encoding="utf-8").read()
            except UnicodeDecodeError:
                rows.append([d + "/" + fn, "-", "T0_undecodable", "not utf-8", ""]); continue
            for i, line in enumerate(txt.splitlines(), 1):
                for tag, rx in TERMS:
                    if rx.search(line):
                        rows.append([d + "/" + fn, str(i), tag, line.strip()[:200], ""])
    with open(outp, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh, delimiter="\t", quoting=csv.QUOTE_MINIMAL)
        w.writerow(["FILE", "LINE", "TERM", "CONTEXT", "DISPOSITION"])
        w.writerows(rows)
    print("SCANNED_ROOT=" + root)
    print("HITS=%d" % len(rows))
    from collections import Counter
    for k, v in sorted(Counter(r[2] for r in rows).items()): print("  %-24s %d" % (k, v))
    for k, v in sorted(Counter(r[0] for r in rows).items(), key=lambda x: -x[1]):
        print("  FILE %-46s %d" % (k, v))
    return 0

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("usage: m01_internal_refs.py <package-or-vault-root> <out.tsv>"); sys.exit(2)
    sys.exit(main(sys.argv[1], sys.argv[2]))
