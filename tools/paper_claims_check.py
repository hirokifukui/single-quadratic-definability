#!/usr/bin/env python3
"""paper_claims_check.py -- Layer B of the statement gate (s38, Gate-12 §9 / S05).

Layer A (native_statement_check.py) compares the native TeX with the Markdown mirror: it is a
migration-consistency check and passes when both sources carry the same wrong statement.  This tool
compares the native TeX against a MANIFEST of what each main theorem is supposed to say, written
independently of either prose source: submission/native/PAPER_CLAIMS.tsv.

Each row names a paper label, the Lean root(s) it cites, the domain / arities / witness domain /
degree bound / quantifier pattern / external hypotheses as words, and three machine-checked fields:
  must_contain     '|'-separated tokens that must occur IN THIS ORDER in the normalized statement
  must_not_contain '|'-separated tokens that must not occur
  claim_hash       md5 of the normalized statement text (native_statement_check.norm) at the time
                   the row was written; a statement that changes must be re-registered on purpose.
Every Lean root named must be a root of certificates/FinalAxiomReport_current.log or a theorem in
frozen_statements/.  Any failure is exit 1.

Gate 13 (s39, A03/A05): two more checks.
  lean_type_sha256   '|'-separated, one per Lean root in the same order: the SHA-256 of the root's normalized
                     elaborated type as printed by scripts/PaperClaimTypeReport.lean and tabulated in
                     certificates/PAPER_CLAIM_LEAN_TYPES.tsv.  A root is resolved by unique suffix match of its
                     fully qualified name; ambiguity, absence, or a hash mismatch is a FAIL.  Substituting an
                     unrelated root, or changing a root's type (e.g. an implicit degree 4 -> d), now fails.
  coverage           every \begin{theorem|lemma|proposition|corollary} in the native TeX whose head names a Lean
                     declaration (\texttt{...}) must have a row.  FORMAL_CLAIMS_FOUND / _REGISTERED / _MISSING are
                     computed from the TeX at run time; MISSING>0 is a FAIL.
WHAT THIS TOOL IS: a model-assisted, author-approved paper-claim registry with tamper detection.  It detects unreviewed changes to
registered paper statements and to the Lean root types they cite.  The semantic correspondence between a paper
statement and a Lean type is a model reading approved by the author (submission/native/PAPER_CLAIMS_REVIEW.tsv); it is not established by
text hashing.

Usage: python3 tools/paper_claims_check.py <root> [--native <dir>] [--rehash] [--retype]
   <root> holds certificates/, frozen_statements/, submission/native/PAPER_CLAIMS.tsv
   --rehash rewrites claim_hash from the current statements (registration; never in a gate)
   --retype rewrites lean_type_sha256 from the current type table (registration; never in a gate)
"""
import csv, hashlib, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from native_statement_check import tex_statements, norm
import native_statement_check as _nsc

# s56 (GATE26 #73): the claim gate must see signs.  norm() deletes ASCII '-', so a deleted minus sign left the
# claim_hash unchanged.  Map '-' to U+2212 (which norm() keeps) before normalising, for the claim text and for
# the must_contain / must_not_contain tokens.  native_statement_check.py itself is unchanged.
_MATH = re.compile(r"\$[^$]*\$|\\\[.*?\\\]", re.S)

def norm_claim(s):
    # only minus signs INSIDE math ($...$, \\[...\\]) are kept; prose hyphens are dropped as before
    return norm(_MATH.sub(lambda m: m.group(0).replace("-", "\u2212"), s))

def tex_statements_claim(native):
    saved = _nsc.norm
    _nsc.norm = norm_claim
    try:
        return _nsc.tex_statements(native)
    finally:
        _nsc.norm = saved
from generate_trust import frozen_theorems, roots

def frozen_defs(root):
    """Frozen `def`s (a paper Definition cites a def, not a theorem; e.g. UniformQuadraticFiberStructureZZ)."""
    import glob
    names = set()
    for f in glob.glob(os.path.join(root, "frozen_statements", "*_STATEMENTS*.lean")):
        for l in open(f, encoding="utf-8"):
            m = re.match(r"\s*(?:noncomputable )?def +([A-Za-z0-9_.']+)", l)
            if m: names.add(m.group(1))
    return names

def type_table(root):
    """fully_qualified_name -> type_sha256 from certificates/PAPER_CLAIM_LEAN_TYPES.tsv."""
    t = {}
    p = os.path.join(root, "certificates", "PAPER_CLAIM_LEAN_TYPES.tsv")
    if not os.path.exists(p): return None
    for l in open(p, encoding="utf-8"):
        q = l.rstrip("\n").split("\t")
        if len(q) >= 5 and q[0] != "fully_qualified_name": t[q[0]] = q[4]
    return t

def resolve(name, table):
    """unique suffix match: 'foo' -> 'A.B.foo'; returns (fqn, error)"""
    if name in table: return name, None
    hits = [k for k in table if k.endswith("." + name)]
    if len(hits) == 1: return hits[0], None
    if not hits: return None, "no type fingerprint for %s" % name
    return None, "ambiguous root %s: %s" % (name, ", ".join(sorted(hits)))

HEAD_RE = re.compile(r"\\begin\{(theorem|lemma|proposition|corollary)\}(\[(?:[^\[\]]|\[[^\]]*\])*\])?\s*\\label\[\w+\]\{\w+:([0-9]+\.[0-9]+|[A-Z]\.[0-9]+)\}")

def formal_claims_found(native):
    """paper labels of every numbered theorem/lemma/proposition/corollary whose head names a Lean declaration"""
    import glob
    found = set()
    for f in sorted(glob.glob(os.path.join(native, "sections", "*.tex"))):
        for m in HEAD_RE.finditer(open(f, encoding="utf-8").read()):
            head = m.group(2) or ""
            if "\\texttt{" in head:
                found.add("%s %s" % (m.group(1).capitalize(), m.group(3)))
    return found

def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = os.path.abspath(args[0] if args else ".")
    native = os.path.join(root, "submission", "native")
    if "--native" in sys.argv: native = sys.argv[sys.argv.index("--native") + 1]
    man = os.path.join(native, "PAPER_CLAIMS.tsv")
    rehash = "--rehash" in sys.argv
    retype = "--retype" in sys.argv
    ttab = type_table(root)
    if ttab is None:
        print("FAIL: certificates/PAPER_CLAIM_LEAN_TYPES.tsv missing (run scripts/PaperClaimTypeReport.lean + paper_claim_types.py)")
        print("PAPER_CLAIMS_EXIT=1"); sys.exit(1)
    stmts = tex_statements_claim(native)
    rt = roots(root); fr = frozen_theorems(root) | frozen_defs(root)
    known = rt | fr | {n.split(".")[-1] for n in rt} | {n.split(".")[-1] for n in fr}
    rows = list(csv.DictReader(open(man, encoding="utf-8"), delimiter="\t"))
    bad = 0; out_rows = []
    for r in rows:
        kind, num = r["paper_label"].split(" ", 1)
        key = (kind, num)
        if key not in stmts:
            print("FAIL %s: no such statement in the native TeX" % r["paper_label"]); bad += 1; out_rows.append(r); continue
        text = stmts[key]
        names = [x.strip() for x in r["Lean_root"].split(",") if x.strip()]
        want = [x.strip() for x in (r.get("lean_type_sha256") or "").split("|")] if r.get("lean_type_sha256") else []
        got = []
        for i, name in enumerate(names):
            if name not in known:
                print("FAIL %s: Lean root %s is neither a root nor frozen" % (r["paper_label"], name)); bad += 1
            fqn, err = resolve(name, ttab)
            if err:
                print("FAIL %s: %s" % (r["paper_label"], err)); bad += 1; got.append(""); continue
            got.append(ttab[fqn])
            if not retype:
                if i >= len(want) or not want[i]:
                    print("FAIL %s: no lean_type_sha256 registered for %s" % (r["paper_label"], name)); bad += 1
                elif want[i] != ttab[fqn]:
                    print("FAIL %s: lean_type_sha256 for %s is %s, current type is %s (root substituted or type changed; re-register deliberately)" % (r["paper_label"], name, want[i][:12], ttab[fqn][:12])); bad += 1
        if retype: r["lean_type_sha256"] = "|".join(got)
        pos = 0
        for tok in [t for t in r["must_contain"].split("|") if t]:
            t = norm_claim(tok)
            i = text.find(t, pos)
            if i < 0:
                print("FAIL %s: token %r not found in order" % (r["paper_label"], tok)); bad += 1; break
            pos = i + len(t)
        for tok in [t for t in r["must_not_contain"].split("|") if t]:
            if norm_claim(tok) in text:
                print("FAIL %s: forbidden token %r present" % (r["paper_label"], tok)); bad += 1
        h = hashlib.md5(text.encode("utf-8")).hexdigest()[:12]
        if rehash: r["claim_hash"] = h
        elif r["claim_hash"] != h:
            print("FAIL %s: claim_hash %s != current %s (statement changed; re-register deliberately)" % (r["paper_label"], r["claim_hash"], h)); bad += 1
        out_rows.append(r)
    if rehash or retype:
        fields = list(rows[0].keys())
        if "lean_type_sha256" not in fields: fields.append("lean_type_sha256")
        with open(man, "w", encoding="utf-8", newline="") as f:
            w = csv.DictWriter(f, fieldnames=fields, delimiter="\t", lineterminator="\n")
            w.writeheader(); [w.writerow(r) for r in out_rows]
        print("PAPER_CLAIMS_REHASHED=%d" % len(out_rows) if rehash else "PAPER_CLAIMS_RETYPED=%d" % len(out_rows))
    # coverage (A03; lemmas added s56): every numbered theorem/lemma/proposition/corollary that names a Lean declaration must be registered
    found = formal_claims_found(native)
    registered = set(r["paper_label"] for r in rows)
    missing = sorted(found - registered)
    print("FORMAL_CLAIMS_FOUND=%d" % len(found))
    print("FORMAL_CLAIMS_REGISTERED=%d" % len(found & registered))
    print("FORMAL_CLAIMS_MISSING=%d%s" % (len(missing), (" " + ", ".join(missing)) if missing else ""))
    if missing and not (rehash or retype): bad += len(missing)
    # Layer 2 (A04): every registered (label, root) needs a Layer-2 review row whose claim_hash and type_sha256 are current
    rv = os.path.join(native, "PAPER_CLAIMS_REVIEW.tsv")
    if os.path.exists(rv):
        review = {}
        for q in csv.DictReader(open(rv, encoding="utf-8"), delimiter="\t"):
            review[(q["paper_label"], q["Lean_root"].split(".")[-1])] = (q["claim_hash"], q["type_sha256"], q["disposition"])
        stale = 0; unreviewed = 0
        for r in out_rows:
            hs = (r.get("lean_type_sha256") or "").split("|")
            for i, name in enumerate([x.strip() for x in r["Lean_root"].split(",") if x.strip()]):
                key = (r["paper_label"], name)
                if key not in review:
                    print("FAIL %s: no Layer-2 review row for %s" % key); unreviewed += 1; continue
                ch, th, disp = review[key]
                if ch != r["claim_hash"] or (i < len(hs) and hs[i] and th != hs[i]):
                    print("FAIL %s: Layer-2 review of %s is stale (statement or type changed since it was reviewed)" % key); stale += 1
                elif not disp.strip():
                    print("FAIL %s: Layer-2 review of %s has no disposition" % key); unreviewed += 1
        print("REVIEW_ROWS=%d REVIEW_UNREVIEWED=%d REVIEW_STALE=%d" % (len(review), unreviewed, stale))
        if not (rehash or retype): bad += stale + unreviewed
        # Gate 15 (s41, F01/F02) / Gate 16 (s42, P0-1): labels listed in PAPER_CLAIMS_ONE_ROOT.txt must cite exactly
        # ONE root whose Layer-2 disposition is EXACT -- the paper theorem and the Lean root have the same
        # hypotheses and conclusion -- and that root must be listed FIRST (it is the principal root the paper
        # names).  Any further root on the row is allowed only with a disposition beginning COROLLARY (a weaker
        # consequence the theorem header also cites, never counted as the correspondence); a second EXACT row, a
        # bundle root, or a MATCH VIA row fails.
        one = os.path.join(native, "PAPER_CLAIMS_ONE_ROOT.txt")
        if os.path.exists(one):
            labels = [l.strip() for l in open(one, encoding="utf-8") if l.strip()]
            okc = 0
            for lab in labels:
                rr = [r for r in out_rows if r["paper_label"] == lab]
                names = [x.strip() for x in rr[0]["Lean_root"].split(",") if x.strip()] if rr else []
                disps = [(nm, review.get((lab, nm), ("", "", ""))[2].strip().upper()) for nm in names]
                exact = [nm for nm, d in disps if d.startswith("EXACT")]
                other = [(nm, d) for nm, d in disps if not d.startswith("EXACT") and not d.startswith("COROLLARY")]
                if not rr: print("FAIL %s: listed in PAPER_CLAIMS_ONE_ROOT.txt but not registered" % lab); bad += 1
                elif len(exact) != 1: print("FAIL %s: must cite exactly one Lean root with an EXACT disposition, has %d (%s)" % (lab, len(exact), ", ".join(exact) or "-")); bad += 1
                elif names[0] != exact[0]: print("FAIL %s: the EXACT root %s must be listed first, the row lists %s first" % (lab, exact[0], names[0])); bad += 1
                elif other: print("FAIL %s: the single root %s must carry an EXACT disposition and every other root COROLLARY; %s has %r" % (lab, exact[0], other[0][0], other[0][1][:40])); bad += 1
                else: okc += 1
            print("ONE_ROOT_LABELS=%d/%d" % (okc, len(labels)))
    else:
        print("REVIEW_ROWS=0 (PAPER_CLAIMS_REVIEW.tsv absent)"); bad += 1
    print("PAPER_CLAIMS=%d PAPER_CLAIMS_FAIL=%d" % (len(rows), bad))
    print("PAPER_CLAIMS_EXIT=%d" % (1 if bad else 0))
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
