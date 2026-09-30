#!/usr/bin/env python3
"""paper_claim_types.py -- Gate 13 A04 (s39): certificates/PAPER_CLAIM_LEAN_TYPES.tsv from the Lean type report.

Input : certificates/PaperClaimTypeReport_current.log  (stdout of scripts/PaperClaimTypeReport.lean:
        rows  name \t kind \t n_binders \t normalized_pretty_type \t axioms ; summary lines TYPE_*)
        certificates/binder_ledger_current.log          (HypothesisBinderLedger: external binders per root)
Output: certificates/PAPER_CLAIM_LEAN_TYPES.tsv with columns
        fully_qualified_name  kind  n_binders  normalized_pretty_type  type_sha256  external_binders  axiom_footprint
type_sha256 = SHA-256 of the UTF-8 bytes of normalized_pretty_type exactly as printed by Lean (so anyone can
recompute it from the log with sha256sum).  external_binders = explicit/implicit/instance/wrapped columns of the
binder ledger joined on the name ("-" when the theorem carries none; "n/a" for any non-theorem root, e.g. a def,
and for names outside the ledger).
Exit 1 if the Lean log lacks TYPE_CONTROLS=4/4 or TYPE_MUT_CONTROLS=4/4 or reports TYPE_MISSING>0 or any row is malformed.
Usage: python3 scripts/paper_claim_types.py [<root>]      (root holds certificates/)
"""
import hashlib, os, sys
root = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith("--") else ".")
log = os.path.join(root, "certificates", "PaperClaimTypeReport_current.log")
bl = os.path.join(root, "certificates", "binder_ledger_current.log")
out = os.path.join(root, "certificates", "PAPER_CLAIM_LEAN_TYPES.tsv")
lines = open(log, encoding="utf-8").read().split("\n")
if "TYPE_CONTROLS=4/4" not in lines:
    print("PAPER_CLAIM_TYPES_FAIL=controls"); sys.exit(1)
if "TYPE_MUT_CONTROLS=4/4" not in lines:
    print("PAPER_CLAIM_TYPES_FAIL=mutation-controls"); sys.exit(1)
miss = [l for l in lines if l.startswith("TYPE_MISSING=")]
if not miss or not miss[0].startswith("TYPE_MISSING=0"):
    print("PAPER_CLAIM_TYPES_FAIL=missing %s" % miss); sys.exit(1)
ext = {}
for l in open(bl, encoding="utf-8"):
    p = l.rstrip("\n").split("\t")
    if len(p) >= 9 and p[0] != "root":
        binders = [x for x in p[1:5] if x != "-"]
        ext[p[0]] = ",".join(binders) if binders else "-"
rows = []
for l in lines:
    p = l.split("\t")
    if len(p) != 5 or p[0] == "fully_qualified_name" or p[0].startswith("TYPE_") or p[0].startswith("CONTROL"):
        if len(p) > 1 and not (p[0] == "fully_qualified_name" or p[0].startswith("TYPE_") or p[0].startswith("CONTROL")):
            print("PAPER_CLAIM_TYPES_FAIL=malformed %r" % l[:80]); sys.exit(1)
        continue
    name, kind, nb, typ, ax = p
    h = hashlib.sha256(typ.encode("utf-8")).hexdigest()
    # s50: the external-binder column is a TRUST-BOUNDARY claim about a THEOREM's hypotheses.  A `def` makes
    # no such claim, so it keeps "n/a" (the documented meaning: not a ledger subject) even now that the binder
    # ledger carries a row for it -- a computed "-" there is vacuously true and would read, in the sign-off
    # sheet, exactly like a theorem proved without any external hypothesis.
    ext_col = ext.get(name, "n/a") if kind == "theorem" else "n/a"
    rows.append((name, kind, nb, typ, h, ext_col, ax))
with open(out, "w", encoding="utf-8") as f:
    f.write("fully_qualified_name\tkind\tn_binders\tnormalized_pretty_type\ttype_sha256\texternal_binders\taxiom_footprint\n")
    for r in rows: f.write("\t".join(r) + "\n")
print("PAPER_CLAIM_TYPES=%d" % len(rows))
print("PAPER_CLAIM_TYPES_DISTINCT_SHA=%d" % len(set(r[4] for r in rows)))
print("PAPER_CLAIM_TYPES_EXIT=0")
