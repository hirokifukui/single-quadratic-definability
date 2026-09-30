#!/usr/bin/env python3
"""Split the single FinalAxiomReport into the three APAL trust reports (Gate 5 必須H / GPT Q4).

  APAL_CORE_AXIOM_REPORT.log      roots with NO external input        ("external-input-free", not
                                                                       "unconditional": ordinary
                                                                       mathematical hypotheses may occur)
  APAL_CLASSICAL_INPUT_REPORT.log roots carrying a classical input    (Grunewald-Segal family, DPRM family)
  LEGACY_MPUP_AXIOM_REPORT.log    roots carrying an r13-era MPUP input (appendix / legacy track)

Inputs: the FinalAxiomReport log and the conservative occurrence ledger output.
The split is a PARTITION: the script fails loudly if the three parts do not reconstruct the whole.
Usage: python3 scripts/split_axiom_reports.py <final_axioms.log> <conservative_ledger.tsv> <outdir>
"""
import re, sys, os

LEGACY = {"QuadraticSolvabilityDecidableZ", "QuadraticSolvabilityDecidableN",
          "HardDiophantineSetExists", "PellClassFiniteness"}
CLASSICAL = {"GlobalQuadraticSolvabilityDecidable", "UniformQuadraticSolvabilityOnCodes",
             "UniformQuadraticSolvabilityDecidableZZ", "QuadraticSolvabilityDecidableZZ",
             "DPRM_NN", "DPRM_ZZ"}
STD3 = {"propext", "Classical.choice", "Quot.sound"}

def parse_axioms(path):
    t = open(path).read()
    recs = {}
    for m in re.finditer(r"'(\S+?)' depends on axioms: \[(.*?)\]", t, re.S):
        recs[m.group(1)] = {x.strip() for x in m.group(2).replace("\n", " ").split(",") if x.strip()}
    for m in re.finditer(r"'(\S+?)' does not depend on any axioms", t):
        recs[m.group(1)] = set()
    return recs

def parse_ledger(path):
    hyps = {}
    for line in open(path):
        parts = line.rstrip("\n").split("\t")
        if len(parts) < 3 or line.startswith("#") or parts[0] == "root":
            continue
        root, _file, h = parts[0], parts[1], parts[2]
        hyps[root] = set() if h == "UNCONDITIONAL" else {x.strip() for x in h.split(",") if x.strip()}
    return hyps

def main():
    axpath, ledpath, outdir = sys.argv[1], sys.argv[2], sys.argv[3]
    ax, hyps = parse_axioms(axpath), parse_ledger(ledpath)
    missing = sorted(set(hyps) - set(ax))
    if missing:
        print("FAIL: roots in the ledger with no axiom record: %s" % missing[:5]); sys.exit(1)
    buckets = {"APAL_CORE_AXIOM_REPORT": [], "APAL_CLASSICAL_INPUT_REPORT": [],
               "LEGACY_MPUP_AXIOM_REPORT": []}
    nonstd = []
    for root in sorted(hyps):
        h = hyps[root]
        if h & LEGACY:
            b = "LEGACY_MPUP_AXIOM_REPORT"
        elif h & CLASSICAL:
            b = "APAL_CLASSICAL_INPUT_REPORT"
        elif h:
            print("FAIL: unknown external input on %s: %s" % (root, sorted(h))); sys.exit(1)
        else:
            b = "APAL_CORE_AXIOM_REPORT"
        a = ax[root]
        if not a <= STD3:
            nonstd.append(root)
        buckets[b].append((root, sorted(h), sorted(a)))
    total = sum(len(v) for v in buckets.values())
    if total != len(hyps):
        print("FAIL: partition lost roots (%d vs %d)" % (total, len(hyps))); sys.exit(1)
    seen = [r for v in buckets.values() for r, _, _ in v]
    if len(seen) != len(set(seen)):
        print("FAIL: a root appears in two reports"); sys.exit(1)
    os.makedirs(outdir, exist_ok=True)
    for name, rows in buckets.items():
        with open(os.path.join(outdir, name + ".log"), "w") as f:
            f.write("# %s — %d roots (of %d total). Terminology: external-input-free, NOT unconditional.\n"
                    % (name, len(rows), total))
            for root, h, a in rows:
                f.write("%s\texternal-input=%s\taxioms=[%s]\n"
                        % (root, ",".join(h) if h else "NONE", ", ".join(a)))
    print("TOTAL_ROOTS=%d" % total)
    for name, rows in buckets.items():
        print("%s=%d" % (name, len(rows)))
    print("NONSTD3_ROOTS=%d" % len(nonstd))
    print("PARTITION=OK")

if __name__ == "__main__":
    main()
