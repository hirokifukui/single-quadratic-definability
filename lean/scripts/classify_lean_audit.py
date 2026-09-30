#!/usr/bin/env python3
"""classify_lean_audit.py — GPT r21 必須A.5/A.6: reclassify the lean_audit selection-layer ledger so that
definition-only / root modules (compile OK, no `#print axioms` line) are not displayed as FAIL.
Verdicts: PASS_AXIOM_AUDITED (exit 0, axioms line present, std-3 only, no forbidden token),
          PASS_COMPILE_ONLY   (exit 0, no axioms line — definition-only or root module; NOT a kernel certificate),
          FAIL                (anything else).
Usage: python3 scripts/classify_lean_audit.py <ledger.jsonl> <out.tsv>
The lean_audit tool itself is unchanged (selection layer, TOOLS §17); the release gate remains audit_dc.sh.
"""
import json, sys
FORBID = ("sorryAx", "native_decide", "ofReduceBool", "trustCompiler")
def classify(rec):
    v = str(rec.get("verdict", rec.get("status", ""))).upper()
    reason = " ".join(str(x) for x in rec.get("reasons", [])) or str(rec.get("reason", ""))
    rc = rec.get("exit", rec.get("returncode", rec.get("rc", None)))
    if v.startswith("PASS"): return "PASS_AXIOM_AUDITED"
    if "no axioms line" in reason and (rc == 0 or rc is None): return "PASS_COMPILE_ONLY"
    return "FAIL"
def main():
    src, out = sys.argv[1], sys.argv[2]
    rows = []
    for line in open(src, encoding="utf-8"):
        line = line.strip()
        if not line: continue
        try: rec = json.loads(line)
        except json.JSONDecodeError: continue
        if rec.get("summary"): continue
        f = rec.get("file", rec.get("path", "?"))
        reason = " ".join(str(x) for x in rec.get("reasons", [])) or str(rec.get("reason", ""))
        rows.append((f, classify(rec), reason[:120]))
    counts = {}
    for _, c, _ in rows: counts[c] = counts.get(c, 0) + 1
    with open(out, "w", encoding="utf-8") as g:
        g.write("# file\tverdict\treason\n")
        for f, c, r in sorted(rows): g.write(f"{f}\t{c}\t{r}\n")
        g.write(f"# TOTAL={len(rows)} " + " ".join(f"{k}={v}" for k, v in sorted(counts.items())) + "\n")
    print(f"LEAN_AUDIT_CLASSIFIED total={len(rows)} " + " ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    print(f"LEAN_AUDIT_FAIL={counts.get('FAIL', 0)}")
main()
