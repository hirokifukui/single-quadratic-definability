#!/usr/bin/env python3
"""submission_figures.py - compute the submission checklist's figures, and fail when it disagrees.

Why (Gate-9 S04).  The r30 checklist carried its numbers by hand and disagreed with itself: line 3
said the PDF was 52 pages and line 37 said 51, and the abstract was recorded at 235/247 words when
the build produced 244.  One of its own boxes -- "generate the page count, abstract word count,
keyword count, reference count and theorem count from the build" -- was still unticked.  A
checklist a referee is invited to read is a claim like any other, and a claim nobody recomputes is
a claim that ages.

This is the same shape as tools/cited_name_census.py: the development is measured, the document is
parsed, and a disagreement fails the build rather than being noticed later by a reviewer.

Two things the first version of this tool got wrong, both found by running it (s35).  It read the
checklist's LIMIT ("abstract <= 250 words") as the checklist's CLAIM, and it counted numbered
statements over the whole file where the checklist counts them in the body.  Both times it accused
the document of a defect it did not have.  A tool that is wrong in the direction of "the document
is broken" is the dangerous direction, because the repair is to edit the document.  The figures are
therefore read from ONE authoritative block, written in the checklist under a fixed header, and
prose elsewhere is checked only for contradicting it.

A third mistake, same family: the sentence explaining the r30 defect says "at r30 this document
said 52 pages", and the first version of this check arrested that as a live claim.  A scanner that
contains its own search term arrests itself (ERRATA_s33-03).  A figure qualified by a round or
session name is a statement about the past, not a claim about this build, and is skipped.

That rule was itself wrong, and the self-adversarial pass caught it the same day: the checklist's
own summary line reads "brought current at r31 ...: 51 pages", so mentioning a round made the one
live claim in the file exempt -- the very line that carried the original defect.  A historical
figure is now marked, in the text, with [historical]; everything else is checked.

Usage:  python3 tools/submission_figures.py <MANUSCRIPT.md> <CHECKLIST.md> [--pages N | --log pass2.log]
Exit 0 = every figure the checklist states agrees with the measurement.
"""
import os, re, sys

def norm(t):
    return re.sub(r"[`*_]", " ", t)

def measure(man, pages):
    L = open(man, encoding="utf-8").read().split("\n")
    # abstract: from the Abstract paragraph to the keywords line or the first section
    i = next(k for k, l in enumerate(L) if l.startswith("**Abstract"))
    buf = []
    for l in L[i:]:
        if l.startswith("**Keywords") or l.startswith("## ") or l.strip() == "---":
            break
        buf.append(l)
    abs_words = len(norm(" ".join(buf)).replace("Abstract.", " ").split())
    kw = next((l for l in L if l.startswith("**Keywords")), "")
    keywords = len([x for x in re.split(r"[;,]", norm(kw).replace("Keywords.", "")) if x.strip()])
    refs = len([l for l in L if re.match(r"^\[[A-Za-z][A-Za-z0-9+]*\]\s", l)])
    # the numbered-statement count belongs to proof_by_citation_scan.py, which owns the body
    # scope; duplicating it here produced a second number that disagreed with the first.
    return {"pages": pages, "abstract_words": abs_words, "keywords": keywords,
            "references": refs}

BLOCK = "FIGURES (recomputed by tools/submission_figures.py; do not edit by hand)"

def stated(chk):
    """The claims are the authoritative block.  Stray page counts in prose are collected too,
    because a document that contradicts itself is the defect this tool was written for."""
    t = open(chk, encoding="utf-8").read()
    out = {}
    if BLOCK in t:
        blk = t[t.index(BLOCK):]
        blk = blk[:blk.index("```", blk.index("\n"))] if "```" in blk[blk.index("\n"):] else blk
        for m in re.finditer(r"^\s*([a-z_]+)=(\d+)\s*$", blk, re.M):
            out[m.group(1)] = [int(m.group(2))]
        t = t.replace(blk, "")
    HIST = re.compile(r"\[historical\]")
    live = "\n".join(l for l in t.split("\n") if not HIST.search(l))
    stray = sorted(set(int(m.group(1)) for m in re.finditer(r"(\d+)\s+pages", live)))
    if stray:
        out.setdefault("pages", [])
        out["pages"] = sorted(set(out.get("pages", []) + stray))
    return out

TRUST_KEYS = ("axiom_roots", "axiom_roots_with_axioms", "axiom_roots_axiom_free",
              "footprint_all_three", "footprint_propext_only", "footprint_propext_quot",
              "binder_roots", "binder_unconditional", "frozen_theorems", "frozen_definitions",
              "frozen_files")

def measure_trust(cert_dir):
    """Recompute the axiom and binder counts from the shipped certificates (s35, Gate-9 §16.3).
    The manuscript no longer carries these numbers; the trust document does, and a number in a
    document nobody recomputes is the r30 defect."""
    import collections
    far = open(os.path.join(cert_dir, "FinalAxiomReport_current.log"), encoding="utf-8",
               errors="replace").read().split("\n")
    recs = []
    for ln in far:
        if ln.startswith("'"):
            recs.append(ln)
        elif recs and ln.strip():
            recs[-1] = recs[-1].rstrip() + " " + ln.strip()
    dep = [r for r in recs if "depends on axioms" in r]
    free = [r for r in recs if "does not depend on any axioms" in r]
    hist = collections.Counter()
    for r in dep:
        m = re.search(r"depends on axioms:\s*\[(.*?)\]", r)
        if m:
            hist[tuple(sorted(a.strip() for a in m.group(1).split(",") if a.strip()))] += 1
    std = ("Classical.choice", "Quot.sound", "propext")
    got = {"axiom_roots": len(dep) + len(free),
           "axiom_roots_with_axioms": len(dep),
           "axiom_roots_axiom_free": len(free),
           "footprint_all_three": hist[std],
           "footprint_propext_only": hist[("propext",)],
           "footprint_propext_quot": hist[("Quot.sound", "propext")]}
    led = open(os.path.join(cert_dir, "binder_ledger_current.log"), encoding="utf-8",
               errors="replace").read()
    for k, pat in (("binder_roots", r"BINDER_ROOTS=(\d+)"),
                   ("binder_unconditional", r"BINDER_UNCONDITIONAL=(\d+)")):
        m = re.search(pat, led)
        if m: got[k] = int(m.group(1))
    sd = open(os.path.join(cert_dir, "statement_diff_current.log"), encoding="utf-8",
              errors="replace").read()
    for k, pat in (("frozen_theorems", r"THEOREMS=(\d+)/"),
                   ("frozen_definitions", r"DEFINITIONS=(\d+)/"),
                   ("frozen_files", r"FROZEN_FILES=(\d+)")):
        m = re.search(pat, sd)
        if m: got[k] = int(m.group(1))
    return got

def run_trust(doc, cert_dir):
    got = measure_trust(cert_dir)
    says = stated(doc)
    bad = 0
    for k in TRUST_KEYS:
        v, sv = got.get(k), says.get(k)
        print("TRUSTFIG_%-26s measured=%s  document=%s" % (k, v, sv[0] if sv else "-"))
        if v is None or sv is None:
            print("    NOT_CHECKED"); bad += 1; continue
        if sv[0] != v:
            print("    DISAGREES measured=%s stated=%s" % (v, sv[0])); bad += 1
    print("TRUST_FIGURES_MISMATCH=%d" % bad)
    print("TRUST_FIGURES_EXIT=%d" % (1 if bad else 0))
    return 1 if bad else 0

def main():
    if "--trust" in sys.argv:
        pos = [a for a in sys.argv[1:] if not a.startswith("--")]
        return run_trust(pos[0], pos[1])
    pos = [a for a in sys.argv[1:] if not a.startswith("--")]
    man, chk = pos[0], pos[1]
    pages = None
    if "--pages" in sys.argv:
        pages = int(sys.argv[sys.argv.index("--pages") + 1])
    elif "--log" in sys.argv:
        log = open(sys.argv[sys.argv.index("--log") + 1], encoding="utf-8", errors="replace").read()
        m = re.search(r"Output written on [^(]*\((\d+) pages", log)
        pages = int(m.group(1)) if m else None
    got, says = measure(man, pages), stated(chk)
    bad = 0
    for k in ("pages", "abstract_words", "keywords", "references"):
        v = got.get(k)
        s = says.get(k)
        print("FIGURE_%-16s measured=%s  checklist=%s" % (k.upper(), v, s if s is not None else "-"))
        if s is None or v is None:
            continue
        if len(set(s)) > 1:
            print("    DISAGREES_WITH_ITSELF %s" % sorted(set(s))); bad += 1
        elif s[0] != v:
            print("    DISAGREES_WITH_DEVELOPMENT measured=%s stated=%s" % (v, s[0])); bad += 1
    print("SUBMISSION_FIGURES_MISMATCH=%d" % bad)
    print("SUBMISSION_FIGURES_EXIT=%d" % (1 if bad else 0))
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
