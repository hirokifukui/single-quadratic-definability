#!/usr/bin/env python3
"""fresh_build_compare.py - compare two clean-room build logs field by field (s35).

Why this exists: at r30 the package shipped two clean-room records, one per machine, and the
sentence around them said they agreed.  They did agree on everything except the number that had
changed: the second machine's record was at 182 source files and the shipped tree at 183, so the
second environment had never built what the package ships.  Nobody compared them because comparing
them was a person's job.  It is this script's job now.

Usage: fresh_build_compare.py <log_A> <log_B>
Exit 1 if any compared field differs or is missing from either log.
"""
import os, re, sys

LEGACY = os.environ.get("MPUP_COMPARE_LEGACY") == "1"

FIELDS = [
    ("SOURCE_MANIFEST_FILES", r"SOURCE_MANIFEST_FILES=(\d+)"),
    ("SRC_MANIFEST_SHA256",   r"SRC_MANIFEST_SHA256=([0-9a-f]{64})"),
    # s35: the first version of this pattern matched nothing and the tool printed "absent from
    # both", which reads like agreement and is not.  A field that is never found is a field that
    # is never compared; the log writes the revision on its own line after the section header.
    ("MATHLIB_REV",           r"(?:MATHLIB_REV=|mathlib[^\n]*?@\s*\"?)([0-9a-f]{40})"),
    ("UPDATE_EXIT",           r"UPDATE_EXIT=(\d+)"),
    ("CACHE_EXIT",            r"CACHE_EXIT=(\d+)"),
    ("PLAIN_BUILD_EXIT",      r"PLAIN_BUILD_EXIT=(\d+)"),
    ("DC_BUILD_EXIT",         r"DC_BUILD_EXIT=(\d+)"),
    ("CORE_BUILD_EXIT",       r"CORE_BUILD_EXIT=(\d+)"),
    ("REBUILD_EXIT",          r"REBUILD_EXIT=(\d+)"),
    ("AUDIT_EXIT",            r"AUDIT_EXIT=(\d+)"),
    ("THEOREMS",              r"THEOREMS=(\d+/\d+)"),
    ("DEFINITIONS",           r"DEFINITIONS=(\d+/\d+)"),
    # s51: this pattern had no line anchor, so it matched inside RU_BUILD_EXIT= and DC_BUILD_EXIT=
    # and reported whichever appeared last.  A field that silently aliases another field is worse
    # than a field that is missing.
    ("BUILD_EXIT",            r"(?m)^BUILD_EXIT=(\d+)"),
    # --- s51: the r40 library.  The comparator was written for two libraries; ResearchUpgrade is
    # the third, and none of its counters was compared.  A reviewer showed this by altering a COPY
    # of one log (RU_BUILD_EXIT=0 -> 1, RU_RECORDS=799 -> 0) and getting DIFFS=0 out of the old
    # comparator.  The original logs agree on all of these; the hole was that nobody asked.
    # Every key below was verified present in BOTH r40 clean-room logs before it was added.
    ("RU_BUILD_EXIT",         r"(?m)^RU_BUILD_EXIT=(\d+)"),
    ("RU_AXIOMS_EXIT",        r"(?m)^RU_AXIOMS_EXIT=(\d+)"),
    ("RU_AXIOM_LINES",        r"(?m)^RU_AXIOM_LINES=(\d+)"),
    ("RU_AXIOM_FREE_LINES",   r"(?m)^RU_AXIOM_FREE_LINES=(\d+)"),
    ("RU_RECORDS",            r"(?m)^RU_RECORDS=(\d+)"),
    # s52: the field that certifies std-3 was the one field never compared.  A reviewer
    # flipped RU_NONSTD3_LINES=0 -> 1 in a COPY of one r41 log and the comparator returned
    # exit 0.  Verified present in BOTH r41 clean-room logs (line 747) before adding.
    ("RU_NONSTD3_LINES",      r"(?m)^RU_NONSTD3_LINES=(\d+)"),
    ("RU_FORBIDDEN",          r"(?m)^RU_FORBIDDEN=(\d+)"),
    ("RU_CAPS_MISSING",       r"(?m)^RU_CAPS_MISSING=(\d+)"),
    ("AUDIT_RU_EXIT",         r"(?m)^AUDIT_RU_EXIT=(\d+)"),
    ("TYPE_REPORT_EXIT",      r"(?m)^TYPE_REPORT_EXIT=(\d+)"),
    ("TYPE_ROWS",             r"(?m)^TYPE_ROWS=(\d+)"),
    ("TYPE_MISSING",          r"(?m)^TYPE_MISSING=(\d+)"),
    ("TYPE_CONTROLS",         r"(?m)^TYPE_CONTROLS=(\S+)"),
    ("TYPE_MUT_CONTROLS",     r"(?m)^TYPE_MUT_CONTROLS=(\S+)"),
    ("STATEMENT_DIFF_EXIT",   r"(?m)^STATEMENT_DIFF_EXIT=(\d+)"),
    ("DEFFID_CHECK_EXIT",     r"(?m)^DEFFID_CHECK_EXIT=(\d+)"),
    ("FROZEN_FILES",          r"(?m)^FROZEN_FILES=(\d+)"),
    ("DUPLICATE_NAMES",       r"(?m)^DUPLICATE_NAMES=(\d+)"),
    ("SOURCE_FREEZE",         r"(?m)^SOURCE_FREEZE=(\S+)"),
]

# s51.  Keys an r40-or-later log MUST carry.  Absent from both logs is a FAILURE, not agreement:
# the old code printed "absent from both" and counted it as nothing, so deleting a counter from
# both environments passed.  Set MPUP_COMPARE_LEGACY=1 to compare pre-r40 logs, which do not have
# these; the mode is explicit so that it cannot be entered by accident.
REQUIRED = [
    "RU_BUILD_EXIT", "RU_RECORDS", "RU_NONSTD3_LINES", "RU_FORBIDDEN", "RU_CAPS_MISSING", "AUDIT_RU_EXIT",
    "TYPE_REPORT_EXIT", "TYPE_ROWS", "TYPE_MISSING", "STATEMENT_DIFF_EXIT", "SOURCE_FREEZE",
]

def grab(path):
    t = open(path, encoding="utf-8", errors="replace").read()
    out = {}
    for name, pat in FIELDS:
        m = re.findall(pat, t)
        if m:
            out[name] = m[-1]
    # the axiom multiset, as a sorted signature rather than a count.
    # s35: the first version counted every "depends on axioms" line in the whole log and reported a
    # difference between two machines that had in fact produced the same result -- the earlier audit
    # sections echo a slightly different set of sample lines, and those are working output, not the
    # attestation.  The attestation is the FINAL THEOREM AXIOM REPORT.  Scoped there, the two logs
    # agree exactly.  A comparison whose scope is wider than the claim manufactures disagreements
    # the same way a narrower one hides them.
    body = t.replace("\n  ", " ")
    i = body.find("FINAL THEOREM AXIOM REPORT")
    if i >= 0:
        body = body[i:]
        out["AXIOM_SCOPE"] = "final-report"
    else:
        out["AXIOM_SCOPE"] = "whole-log (no final report found)"
    ax = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", body)
    if ax:
        from collections import Counter
        c = Counter(tuple(sorted(a.strip() for a in x.split(",") if a.strip())) for x in ax)
        out["AXIOM_MULTISET"] = "; ".join("%s x%d" % ("+".join(k) or "none", v)
                                          for k, v in sorted(c.items()))
    return out

def main(a, b):
    A, B = grab(a), grab(b)
    keys = [n for n, _ in FIELDS] + (["AXIOM_SCOPE", "AXIOM_MULTISET"] if ("AXIOM_MULTISET" in A or
                                                            "AXIOM_MULTISET" in B) else [])
    bad = 0
    for k in keys:
        va, vb = A.get(k), B.get(k)
        if va is None and vb is None:
            if k in REQUIRED and not LEGACY:
                print("  %-22s MISSING FROM BOTH (required since r40)" % k); bad += 1
            else:
                print("  %-22s absent from both" % k)
            continue
        if va is None or vb is None:
            print("  %-22s MISSING  A=%s  B=%s" % (k, va, vb)); bad += 1; continue
        mark = "agree" if va == vb else "DIFFER"
        if va != vb: bad += 1
        show = (va if len(str(va)) < 40 else str(va)[:37] + "...")
        showb = (vb if len(str(vb)) < 40 else str(vb)[:37] + "...")
        print("  %-22s %-6s A=%s  B=%s" % (k, mark, show, showb))
    print("FRESH_BUILD_COMPARE_LEGACY=%d" % (1 if LEGACY else 0))
    print("FRESH_BUILD_COMPARE_DIFFS=%d" % bad)
    print("FRESH_BUILD_COMPARE_EXIT=%d" % (1 if bad else 0))
    return 1 if bad else 0

if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.stderr.write(__doc__); sys.exit(2)
    sys.exit(main(sys.argv[1], sys.argv[2]))
