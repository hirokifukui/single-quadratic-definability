#!/usr/bin/env python3
"""fidelity_destroyer.py - Gate-5 homework group 1 (statement fidelity destroyer).

Sweeps a document root for prose that claims more than the Lean kernel proves.
Reports every hit with file:line so each can be dispositioned by hand.
Exit 0 normally. With --dispositions, exit 1 if any hit lacks a recorded disposition.
The hit list is an inventory; the disposition requirement is the gate.

Usage:  python3 scripts/fidelity_destroyer.py <root> [--shipping-only] [--tsv OUT]

--shipping-only restricts to the files a submission package would ship
(manuscript/MANUSCRIPT_V*.md at the highest version, correspondence/COVER_LETTER*,
submission/*, release/*), which is where an overclaim actually costs us.
"""
import os, re, sys, csv

SKIP = re.compile(r'\.bak|\.archive$|/archive/|/backup|/\.git|/\.lake|/build/')
EXTS = {'.md', '.txt', '.tsv', '.cff', '.yaml', '.yml', '.tex'}

# Each rule: id, severity, regex, what the kernel actually supports.
RULES = [
 ("D1",  "STOP", r'AtomGraphZZ\s*2\s*n\s*(holds\s*)?(if and only if|iff|↔)',
  "kernel has only AtomGraphZZ 2 n -> n <= 2; AtomGraphZZ 2 2 is absent from the tree"),
 ("D2",  "STOP", r'positive half',
  "no positive half at n=2 exists in the tree"),
 ("D3",  "STOP", r'\battained\b',
  "n<=2m attained at m=1 needs AtomGraphZZ 2 2, which is unproved"),
 ("D4",  "WARN", r'\bsharp(ness)?\b',
  "one-sorted sharpness is open; check each use is about something else"),
 ("D5",  "STOP", r'exact (coding )?arity|the exact arity',
  "only 1 <= ca(SE_2) <= 2 is proved"),
 ("D6",  "WARN", r'exactly three',
  "three forms are proof-emitted, not a canonical classification"),
 ("D7",  "WARN", r'\bcanonical\b',
  "certificate kinds are not canonical and may overlap"),
 ("D8",  "WARN", r'mutually exclusive',
  "kinds are not proved mutually exclusive"),
 ("D9",  "WARN", r'effective certificate',
  "witnesses come from Classical.choice; the certificate is not effective"),
 ("D10", "WARN", r'complete parametri|full parametri',
  "no parametrisation of all solutions is proved"),
 ("D11", "WARN", r'exactly the input/output contract',
  "GS bridge is an effective coding-equivalent consequence (ERRATA_GATE4 G9)"),
 ("D12", "WARN", r'independently proves',
  "BranchExhaustion mirrors the typed case analysis; it does not independently prove it"),
 ("D13", "STOP", r'[Aa]ll statements and proofs',
  "Appendix A is conditional and unproved; only Sections 2-9 are formalized"),
 ("D14", "STOP", r'architecture,? not a proof',
  "APAL requires a human-readable proof, not a delegation"),
 ("D15", "STOP", r'For n = 2 there is one',
  "same unproved n=2 claim as D1, in the main text"),
 ("D16", "STOP", r'therefore grow at most quadratically, are computable',
  "computability of total functions comes from totality + Dioph graph, not from the growth bound"),
]

# T04: the shipping set is an EXPLICIT LIST, not a heuristic. The seal quotes a number;
# that number must be a count over a named set of files, or the two can never be compared.
# submission/APAL_MANUSCRIPT_v32.tex is deliberately absent: it is generated from
# manuscript/MANUSCRIPT_V32.md by papers/apal_build/build.sh, so scanning both double-counts.
SHIPPING_SET = (
    'manuscript/MANUSCRIPT_V32.md',
    'submission/APAL_COVER_LETTER_v1.md',
    'submission/APAL_SUBMISSION_CHECKLIST_v1.md',
    'release/TRUST_BOUNDARY_APAL.md',
    'release/README_BUILD_APAL.md',
    'release/RELEASE_CHECKLIST_APAL.md',
    'README.md',
)

def shipping(path, root):
    rel = os.path.relpath(path, root).replace(os.sep, '/')
    return rel in SHIPPING_SET

def main():
    root = sys.argv[1]
    ship_only = '--shipping-only' in sys.argv
    out = None
    if '--tsv' in sys.argv:
        out = sys.argv[sys.argv.index('--tsv') + 1]
    if not os.path.isdir(root):
        if os.path.isfile(root):
            sys.stderr.write(
                "fidelity_destroyer: %s is a file; this tool walks a directory. "
                "Put the file in a directory and pass that.\n" % root)
        else:
            sys.stderr.write("fidelity_destroyer: no such directory: %s\n" % root)
        print("DESTROYER_EXIT=2")
        return 2
    rows = []
    nfiles = 0
    for dp, dn, fn in os.walk(root):
        dn[:] = [d for d in dn if d not in {'.git', '.lake', 'build'}]
        for f in fn:
            p = os.path.join(dp, f)
            if SKIP.search(p.replace(os.sep, '/')):
                continue
            if os.path.splitext(f)[1] not in EXTS:
                continue
            if ship_only and not shipping(p, root):
                continue
            nfiles += 1
            try:
                txt = open(p, encoding='utf-8').read()
            except Exception:
                continue
            for i, line in enumerate(txt.split('\n'), 1):
                for rid, sev, pat, why in RULES:
                    if re.search(pat, line, re.I):
                        rows.append([rid, sev, p, i, line.strip()[:200], why])
    stop = sum(1 for r in rows if r[1] == 'STOP')
    warn = len(rows) - stop
    print(f"SCANNED_FILES={nfiles}")
    print(f"HITS_TOTAL={len(rows)}  STOP={stop}  WARN={warn}")
    by = {}
    for r in rows:
        by.setdefault(r[0], []).append(r)
    for rid, sev, pat, why in RULES:
        print(f"  {rid:4s} {sev:4s} {len(by.get(rid, [])):3d}")
    if ship_only:
        missing = [f for f in SHIPPING_SET if not os.path.exists(os.path.join(root, f))]
        print("SHIPPING_SET_SIZE=%d  MISSING_FROM_SET=%d" % (len(SHIPPING_SET), len(missing)))
        for f in missing:
            print("  MISSING " + f)
    if out:
        with open(out, 'w', newline='', encoding='utf-8') as fh:
            w = csv.writer(fh, delimiter='\t')
            w.writerow(["rule", "severity", "file", "line", "text", "kernel_reality", "disposition"])
            for r in rows:
                rel = os.path.relpath(r[2], root).replace(os.sep, '/')
                w.writerow([r[0], r[1], rel, r[3], r[4], r[5], ""])
        print(f"TSV={out}")

    # T04: every hit must carry a written disposition, or the tool fails.
    undisp = None
    # s35 (Gate-9 G07).  Until s35 this argument was optional, and the command printed in
    # README_BUILD_APAL.md omitted it -- so the check a referee was told to run exited 0 whatever
    # it found.  An inventory with no dispositions to check against is not a gate, and a gate that
    # cannot fail is worse than no gate, because it is quoted as evidence.
    if '--dispositions' not in sys.argv:
        print("DESTROYER=REFUSE  --dispositions <file> is required; without it this check cannot fail")
        sys.exit(2)
    if '--dispositions' in sys.argv:
        dpath = sys.argv[sys.argv.index('--dispositions') + 1]
        known = set()
        with open(dpath, encoding='utf-8') as fh:
            rd = csv.reader(fh, delimiter='\t')
            hdr = next(rd, None)
            for row in rd:
                if len(row) >= 7 and row[6].strip():
                    known.add((row[0], row[2], row[4][:80]))
        undisp = 0
        for r in rows:
            rel = os.path.relpath(r[2], root).replace(os.sep, '/')
            if (r[0], rel, r[4][:80]) not in known:
                undisp += 1
                print("  UNDISPOSITIONED %s %s:%d %s" % (r[0], rel, r[3], r[4][:70]))
        print("UNDISPOSITIONED=%d" % undisp)
    code = 1 if (undisp is not None and undisp > 0) else 0
    print("DESTROYER_EXIT=%d" % code)
    return code

if __name__ == '__main__':
    sys.exit(main())
