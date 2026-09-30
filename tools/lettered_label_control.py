#!/usr/bin/env python3
"""lettered_label_control.py - Gate-8 M02/M03 controls for lettered statement labels.

Theorem C.1 was invisible to every scanner in the r29 package because each of them required a
statement label to begin with a digit.  Four independent files carried the same pattern, so the
defect had four homes and one cause.  This file is the guard: it checks the fix positively (a
fixture with C.1, AA.1 and A.10 is seen), negatively (the old pattern sees none of them, so the
control can witness the bug it is protecting against), end-to-end (deleting the lettered theorem
from a copy of the manuscript drops the count), and structurally (all four scanners still carry
the same pattern, so none of them can drift back on its own).

The two pattern literals below are ASSEMBLED FROM PIECES on purpose.  A scanner that contains its
own search term arrests itself - that happened at s33 (ERRATA_s33-03) and the fix was the same.

Usage: python3 scripts/lettered_label_control.py <MANUSCRIPT.md>
Anchors (line-initial): POSITIVE_FOUND, OLD_PATTERN_FOUND, NEGATIVE_DROP, PATTERN_FILES_AGREE,
                        SELF_MATCH, LETTERED_CONTROL_EXIT
"""
import os, re, sys, tempfile

NEWPAT = "(?:" + "[0-9]+" + "|" + "[A-Z]+" + ")" + "\\." + "[0-9]+"
OLDPAT = "[0-9]+" + "\\." + "[0-9]+"
KINDS  = r'Theorem|Definition|Lemma|Corollary|Proposition|Remark|Examples?|Fact'

# basename -> the subdirectories it may live in.  A development tree keeps the scanners in
# scripts/; a distribution ships them in tools/ (T07).  Looking in one place only would make this
# control pass vacuously at the other root, which is the failure mode it exists to prevent.
SCANNERS = ["proof_by_citation_scan.py",
            "build_appendix_e_tex.py",
            "manuscript_index.py",
            "gen_appendix_e_numbered.py"]
SUBDIRS = ["scripts", "tools", "manuscript"]

FIXTURE = ("**Theorem C.1** (`a`). x\n\n"
           "**Lemma AA.1** (`b`). y\n\n"
           "**Corollary A.10** (`c`). z\n\n"
           "**Theorem 7.3** (`d`). w\n")

def main(ms, roots):
    rc = 0
    rx_new = re.compile(r'^\*\*(' + KINDS + r')\s+(' + NEWPAT + r')\*\*', re.M)
    rx_old = re.compile(r'^\*\*(' + KINDS + r')\s+(' + OLDPAT + r')\*\*', re.M)

    want = {"C.1", "AA.1", "A.10"}
    got_new = {m.group(2) for m in rx_new.finditer(FIXTURE)}
    got_old = {m.group(2) for m in rx_old.finditer(FIXTURE)}
    print("POSITIVE_FOUND=%d (%s)" % (len(want & got_new), ", ".join(sorted(want & got_new))))
    print("OLD_PATTERN_FOUND=%d" % len(want & got_old))
    if want - got_new: print("FAIL positive control: missed %s" % sorted(want - got_new)); rc = 1
    if want & got_old: print("FAIL the old pattern was supposed to miss these"); rc = 1

    src = open(ms, encoding="utf-8").read()
    body = src.split("## Appendix F")[0]
    before = len(rx_new.findall(body))
    cut = re.sub(r'^\*\*Theorem\s+C\.1\*\*', '**Theorem C-one**', body, flags=re.M)
    after = len(rx_new.findall(cut))
    print("NEGATIVE_DROP=%d (%d -> %d)" % (before - after, before, after))
    if before - after != 1: print("FAIL negative control: removing Theorem C.1 changed nothing"); rc = 1

    agree, missing = 0, []
    for base in SCANNERS:
        found = None
        for root in roots:
            for sub in SUBDIRS:
                cand = os.path.join(root, sub, base)
                if os.path.exists(cand):
                    found = cand; break
            if found: break
        if not found:
            missing.append(base + " (not found)"); continue
        t = open(found, encoding="utf-8").read()
        if NEWPAT in t: agree += 1
        else: missing.append(found)
    print("PATTERN_FILES_AGREE=%d/%d" % (agree, len(SCANNERS)))
    if missing: print("FAIL scanners without the lettered pattern: %s" % missing); rc = 1

    self_hits = sum(1 for base in SCANNERS if base == os.path.basename(__file__))
    print("SELF_MATCH=%d" % self_hits)
    print("LETTERED_CONTROL_EXIT=%d" % rc)
    return rc

if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.stderr.write(__doc__); sys.exit(2)
    # roots, in order: an explicit --root, then the tree this file sits in, then the manuscript's own
    # --root is EXCLUSIVE.  It used to be merely first in a list, and the fallback silently supplied
    # a scanner the named root did not have -- a control passing on a file that is not in the thing
    # being checked, which is the one outcome a control must never have.
    if "--root" in sys.argv:
        roots = [sys.argv[sys.argv.index("--root") + 1]]
    else:
        roots = [os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                 os.path.dirname(os.path.dirname(os.path.abspath(sys.argv[1])))]
    sys.exit(main(sys.argv[1], roots))
