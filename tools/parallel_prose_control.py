#!/usr/bin/env python3
"""parallel_prose_control.py - refuse to ship a second prose source of the manuscript.

Why this exists (Gate-9, session 35).  The r30 archive shipped nineteen .tex fragments under
submission/tex/sections/ that were a Pandoc rendering of an OLDER manuscript.  Every prose gate
here reads manuscript/MANUSCRIPT_V32.md, so none of them saw the fragments, and the assembler's
only check on them counted the files rather than comparing them.  Measured at r30: of fourteen
gate rules whose text carries no markup, the source passed fourteen and the fragments failed
seven.  A reader auditing the archive could read either document; one of them was wrong.

The rule is not "the copies must agree" but "there is one prose source".  A copy that must agree
is a copy someone has to keep agreeing, and the r30 evidence is that nobody does.  Files the
build writes from the single source are allowed by path; anything else that reproduces the
manuscript's paragraphs is a parallel source and fails.

Two things the first version of this control got wrong, both found by running it (s35):
  (1) Section titles are the wrong canary.  A fragment file holds one section, so it scored one
      hit and passed, while a GPT review transcript that quotes several titles was arrested.
      Titles are what commentary reuses; paragraphs are what a duplicate reproduces.
  (2) A per-file threshold is the wrong unit.  Nineteen fragments are one parallel source.
  (4) The first version exempted history/ by prefix, on the reasoning that retired material is not
      a source.  Measured on the r30 archive with that exemption removed: history/ carried fifteen
      older manuscripts AND A SECOND FILE NAMED MANUSCRIPT_V32.md, differing from the shipped one
      in sixteen lines -- the sixteen lines of the Gate-8 repair, so the retired copy still printed
      398 roots and "nineteen, nine and ten".  The exemption covered exactly the class of defect
      the control was written to catch.  There is no directory exemption now.
  (3) A per-directory sum alone convicts the innocent.  Review handouts and referee simulations
      quote the paper; at r30 their worst directory reached five shingles in aggregate while no
      single file reached five.  A duplicate concentrates: the retired fragments scored 234, 60,
      31, 28 in single files.  The trigger is therefore per file, and the near-miss table below
      the trigger is printed so the margin is measured on every run rather than assumed.
Canaries are token shingles of the body, matched escaping-blind, derived from the manuscript at
run time, so this control cannot go stale in the way the document it guards did.

The declared companions are exempt and the exemption is printed, never silent.  They reproduce
Appendix F by design and are cited from it; unifying them is Gate-9 N05 and is r32 work under a
ruling, not something this control should decide by deleting.  Their shingle counts are shown on
every run, so the size of the exemption stays visible.

Run this on a DISTRIBUTION root, not on the working vault.  The vault holds drafts, review
handouts and earlier submission builds by design, and they reproduce the paper; on the r30 vault
this control reports seven directories, all of them correct to be there.  What must hold is that
nothing parallel SHIPS, so the assembler runs it on the assembled package and the package-only
build runs it on the extracted archive.

Usage:  python3 tools/parallel_prose_control.py <root> [--manuscript PATH] [--threshold N]
Exit 0 = one prose source.  Exit 1 = a parallel source ships.
"""
import os, re, sys

ALLOWED = (
    "manuscript/MANUSCRIPT_V32.md",          # the single source
    "submission/APAL_MANUSCRIPT_v32.tex",    # written by build.sh step 7 from that source
)
ALLOWED_PREFIX = (
    "papers/apal_build/",   # build working directory: body_raw.md, body.md, the typeset .tex
    # s36 (Gate-10 N01-N08): the native LaTeX source the PDF is built from.  It is not a parallel
    # source in the sense this control exists for -- a second rendering nobody compares -- because
    # tools/native_statement_check.py compares it with the Markdown statement by statement at
    # every build and fails the build on any difference.  Until the Markdown is archived (r33) the
    # two are bound by that gate, and the exemption is printed with the others.
    "submission/native/",
)
# Named one by one, never by prefix: an exemption granted to a directory is an exemption that
# grows without anyone deciding to grant it.
# Review handouts are EXCERPTS: a reviewer was given the passage under review, so some of the
# paper's paragraphs appear there by design.  An excerpt is legitimate; a copy is not, and the
# difference is size.  The set is declared, and any file in it above EXCERPT_CEILING is treated as
# a copy, so quotation cannot grow into reproduction without the gate saying so.
DECLARED_EXCERPTS = ("history/handouts_r14/", "independent_reviews/handouts_r15/",
                     "referee_simulation/",
                     # s55 (Dr. Fukui, r44): the r15 session directories keep the PROMPT.md that was
                     # handed to each blind reviewer -- the launch instructions followed by the handout
                     # itself, and the handouts are already declared above.  The three FULL_RANK_B
                     # prompts reached the threshold at r44 without changing: the three new Appendix A
                     # lemmas shifted the STRIDE sampling phase over the whole manuscript, the same way
                     # the r34 Introduction did to the s37 red-team answers.  The ceiling still bounds
                     # them, so an excerpt cannot grow into a copy unnoticed.
                     "independent_reviews/r15_sessions/",
                     # s38: the red-team answer sheet quotes the fifteen statements it answers (an
                     # excerpt by construction).  It reached the threshold at r34 only because the new
                     # Introduction shifted the STRIDE sampling phase over the whole manuscript, which
                     # is how a sampled control behaves; the ceiling still bounds it.
                     "correspondence/LOGIC_RED_TEAM_ANSWERS_s37.md",
                     # s40 (Gate-14 P02/§18): the author sign-off sheet quotes every registered statement
                     # beside its Lean type -- an excerpt by construction; the ceiling still bounds it.
                     "release/AUTHOR_SIGNOFF_SHEET.md",
                     # s59 (Dr. Fukui, r48): GPT's R47 source-evidence handout quotes the passages under review
                     # (A.8, PROOF_NOTE §5, the A.9 proof) with line numbers, verbatim -- an excerpt by construction.
                     "correspondence/GPT_REVIEW_GATE29_20260927_E_source_evidence.md",
                     # s60 (Dr. Fukui, r49): GPT's R48 source-evidence handout, verbatim excerpts with line numbers.
                     "correspondence/GPT_REVIEW_GATE30_20260928_E_source_evidence.md",
                     # s61 (Dr. Fukui, r50): GPT's R49 source-evidence handout, verbatim excerpts with line numbers.
                     "correspondence/GPT_REVIEW_GATE31_20260928_E_source_evidence.md",
                     # s62 (r51): GPT's R50 source-evidence handout, verbatim excerpts with line numbers.
                     "correspondence/GPT_REVIEW_GATE32_20260928_E_source_evidence.md",
                     # s64 (r53): GPT's R52 source-evidence handout, verbatim excerpts with line numbers.
                     "correspondence/GPT_REVIEW_GATE34_20260930_E_source_evidence.md")
EXCERPT_CEILING = 12
# s41 (Gate-15 F05): the sign-off sheet is GENERATED and quotes the statement of every registered paper claim
# (all 27 labels, 54 rows) beside its Lean type; that is its entire purpose, so it reaches the general
# excerpt ceiling by construction. It carries its own ceiling, still a bound: it must not exceed the
# registered statements it exists to quote (the count is checked against the registry at every run).
PER_FILE_CEILING = {"release/AUTHOR_SIGNOFF_SHEET.md": 30,   # s61: sheet unchanged; 25 -> 30 from the canary sampling phase
                    "correspondence/GPT_REVIEW_GATE29_20260927_E_source_evidence.md": 19,   # s59: 15 in the r48 tree; s63: 19 in the r52 tree (front-matter phase shift)
                    "correspondence/GPT_REVIEW_GATE30_20260928_E_source_evidence.md": 26,   # s60: 24 in the r49 tree; s63: 26 in the r52 tree (front-matter phase shift)
                    "correspondence/GPT_REVIEW_GATE31_20260928_E_source_evidence.md": 47,   # s61: 39 in the r50 dry-run tree; s63: 46 in the r52 tree; s64: 47 in the r53 tree (section 12 phase shift)
                    "correspondence/GPT_REVIEW_GATE32_20260928_E_source_evidence.md": 17,   # s62: 12 in the r51 tree; s63: 16, then 17 in the r52 tree (title page, front matter)
                    "correspondence/GPT_REVIEW_GATE34_20260930_E_source_evidence.md": 16}   # s64: 16 in the r53 dry-run tree
DECLARED_COMPANIONS = (
    "release/PROOF_COMPANION.md",   # s38 (Gate-12 C01): generated from the native source by the build
    "manuscript/APAL_PROJECTION_PROOF_FULL.md",
    # s35 (Gate-9 N05): these three moved out of manuscript/ into history/superseded_appendixF/.
    # They are still declared, because they still reproduce most of Appendix F and the exemption
    # must stay visible; what changed is that a reader can no longer mistake them for a source.
    "history/superseded_appendixF/FULL_RANK_PROOF_V2.md",
    "history/superseded_appendixF/QUADRATIC_PROJECTION_DICHOTOMY_FULL_V2.md",
    "history/superseded_appendixF/APAL_PROJECTION_PROOF_FULL.md",
    "manuscript/FULL_RANK_PROOF_V2.md",
    "manuscript/QUADRATIC_PROJECTION_DICHOTOMY_FULL_V2.md",
    "manuscript/FALLBACK_FINITE_SIDE_V31.md",
)
EXTS = (".tex", ".md", ".txt")
SHINGLE = 12          # tokens; long enough that quotation does not reach it by accident
STRIDE  = 40          # sample the body rather than all of it
THRESH  = 6           # distinct shingles in one file: a duplicate concentrates

def toks(s):
    return re.findall(r"[a-z0-9]+", s.lower())

def main():
    pos = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = pos[0] if pos else "."
    man, thresh = "manuscript/MANUSCRIPT_V32.md", THRESH
    for i, a in enumerate(sys.argv):
        if a == "--manuscript": man = sys.argv[i + 1]
        if a == "--threshold":  thresh = int(sys.argv[i + 1])
    mp = os.path.join(root, man)
    if not os.path.isfile(mp):
        print("PARALLEL_PROSE=ERROR manuscript not found: %s" % mp); return 2

    t = toks(open(mp, encoding="utf-8").read())
    canaries = {" ".join(t[i:i + SHINGLE]) for i in range(0, len(t) - SHINGLE, STRIDE)}
    print("CANARIES=%d SHINGLE=%d THRESHOLD=%d(per directory)" % (len(canaries), SHINGLE, thresh))

    per_file, per_dir, exempt, excerpts = {}, {}, {}, {}
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in (".git", ".lake")]
        for fn in filenames:
            if not fn.endswith(EXTS) or ".bak" in fn: continue
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, root)
            if rel in ALLOWED or rel.startswith(ALLOWED_PREFIX): continue
            companion = rel in DECLARED_COMPANIONS
            excerpt = rel.startswith(DECLARED_EXCERPTS)
            try:
                body = " ".join(toks(open(full, encoding="utf-8", errors="replace").read()))
            except OSError:
                continue
            found = {c for c in canaries if c in body}
            if found:
                if companion:
                    exempt[rel] = len(found); continue
                if excerpt:
                    excerpts[rel] = len(found)
                    if len(found) <= PER_FILE_CEILING.get(rel, EXCERPT_CEILING):
                        continue          # an excerpt of this size is quotation, and is allowed
                per_file[rel] = len(found)
                d = os.path.dirname(rel) or "."
                per_dir.setdefault(d, set()).update(found)

    for rel in DECLARED_COMPANIONS:
        print("DECLARED_COMPANION %s shingles=%d" % (rel, exempt.get(rel, 0)))
    print("DECLARED_COMPANIONS=%d (exempt by name, Gate-9 N05 is to unify them)" % len(exempt))

    if excerpts:
        worst = max(excerpts.values())
        print("DECLARED_EXCERPTS=%d files, largest=%d, ceiling=%d" % (len(excerpts), worst, EXCERPT_CEILING))
        for rel, cap in PER_FILE_CEILING.items():
            print("PER_FILE_CEILING %s shingles=%d ceiling=%d" % (rel, excerpts.get(rel, 0), cap))
    trig = sorted(f for f, n in per_file.items() if n >= thresh)
    bad = sorted({os.path.dirname(f) or "." for f in trig})
    for d in bad:
        files = sorted((f, per_file[f]) for f in per_file if (os.path.dirname(f) or ".") == d)
        print("PARALLEL_PROSE_HIT dir=%s files=%d shingles_max=%d shingles_dir=%d"
              % (d, len(files), max(n for _, n in files), len(per_dir[d])))
        for f, n in files[:25]:
            print("    %s%s  shingles=%d" % ("* " if n >= thresh else "  ", f, n))
    near = sorted(((n, f) for f, n in per_file.items() if n < thresh), reverse=True)[:5]
    print("NEAR_MISS_TOP5 " + ", ".join("%s=%d" % (f, n) for n, f in near))
    print("TRIGGER_MARGIN highest_untriggered=%d trigger=%d" % (near[0][0] if near else 0, thresh))
    print("PARALLEL_PROSE_FILES=%d PARALLEL_PROSE_DIRS=%d" % (len(trig), len(bad)))
    ok = not trig
    print("PARALLEL_PROSE_CONTROL=%s" % ("OK" if ok else "FAIL"))
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
