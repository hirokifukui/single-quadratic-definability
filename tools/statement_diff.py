#!/usr/bin/env python3
"""statement_diff.py — GPT r14 mandatory E: ONE dynamic statement-fidelity check.

For every frozen statement file (frozen_statements/*_STATEMENTS.lean) and every
`theorem`/`def` declared in it, locate the production declaration OF THE SAME
NAME anywhere under the production tree (DiophCompression/ and MPUP/), and
compare the statement text verbatim (declaration keyword up to the first
':=', whitespace-normalized). Robust to file moves: no frozen→production file
pairing is hard-coded.

Usage (from the package root or the lean root):
  python3 scripts/statement_diff.py                # report; exit 1 on any FAIL
  python3 scripts/statement_diff.py --negative-control
  python3 scripts/statement_diff.py --unicode-control  # subscript-identifier controls (s25)
                                                   # two planted faults must be caught

Environment: STMT_BASE (default: frozen_statements, else drafts),
             LEAN_BASE (default: lean if it exists, else .).
Output anchors (line-initial, grep-able):
  FROZEN_FILES=<n>  THEOREMS=<ok>/<all>  DEFINITIONS=<ok>/<all>  DUPLICATE_NAMES=<n>
  FAIL=<n>  SDIFF_EXIT=<0|1>
"""
import os, re, sys, glob

def pick(env, cands):
    v = os.environ.get(env)
    if v: return v
    for c in cands:
        if os.path.isdir(c): return c
    return cands[0]

BASE = pick("STMT_BASE", ["frozen_statements", "drafts"])
LEAN = pick("LEAN_BASE", ["lean", "."])
# r40 (s49): `ResearchUpgrade` is a THIRD lean_lib, a sibling of DiophCompression/ and MPUP/ under
# lean/ (see lakefile.lean).  Without it in the production index every frozen ResearchUpgrade
# statement is reported FAIL MISSING -- the tool predates the library, and a directory that is not
# indexed is a gate that inspects nothing.  A missing directory is skipped by glob, so naming a
# library that a given checkout does not carry is harmless.
PROD_DIRS = [os.path.join(LEAN, "DiophCompression"), os.path.join(LEAN, "MPUP"),
             os.path.join(LEAN, "ResearchUpgrade")]

# Lean identifier characters: ASCII letters/digits/_/./', and every non-ASCII code point up to U+10FFFF.
# NOTE (s25, GPT Gate-1 §2B): the range end MUST be written \U0010FFFF (8 hex digits). The earlier
# \u10FFFF was read by Python as \u10FF followed by the literal "FF", so identifiers containing characters
# above U+10FF (e.g. subscript ₂ = U+2082) were cut at that character (primrec₂_solCheck → primrec).
DECL = re.compile(r'^((?:noncomputable )?(theorem|def)) +([A-Za-z0-9_.\u00C0-\U0010FFFF\']+)', re.M)
DECL_OLD_BUGGY = re.compile(r'^((?:noncomputable )?(theorem|def)) +([A-Za-z0-9_.\u00C0-\u10FFFF\']+)', re.M)  # kept ONLY for the unicode control

def decls(txt):
    out = []
    for m in DECL.finditer(txt):
        tail = txt[m.start():]
        cut = re.search(r':=|\swhere\b', tail)
        if not cut: continue
        stmt = re.sub(r'\s+', ' ', tail[:cut.start()]).strip()
        out.append((m.group(3), m.group(2), stmt))
    return out

def load(p):
    with open(p, encoding="utf-8") as f: return f.read()

def readlist(p):
    if not os.path.exists(p): return []
    return [l.strip() for l in load(p).splitlines() if l.strip() and not l.startswith("#")]

def production_index():
    idx = {}   # name -> list of (file, kind, stmt)
    for d in PROD_DIRS:
        for p in glob.glob(os.path.join(d, "**", "*.lean"), recursive=True):
            if "/audit_smoke" in p or "/probe" in p: continue
            for n, k, s in decls(load(p)):
                idx.setdefault(n, []).append((os.path.relpath(p, LEAN), k, s))
    return idx

def run(frozen_override=None, drop=None, quiet=False):
    files = sorted(glob.glob(os.path.join(BASE, "*_STATEMENTS*.lean")))
    if not files:
        print(f"ERROR: no frozen files under {BASE}"); return None
    superseded = readlist(os.path.join(BASE, "SUPERSEDED.txt"))
    open_files = readlist(os.path.join(BASE, "OPEN_STATEMENTS.txt"))
    files = [f for f in files if os.path.basename(f) not in superseded]
    idx = production_index()
    t_ok = t_all = d_ok = d_all = fails = dups = 0
    open_ok = open_all = 0
    for f in files:
        txt = load(f)
        if os.path.basename(f) in open_files:
            # frozen-open registry: statements stated, no production proof expected
            for n, k, s in decls(txt):
                open_all += 1
                if n not in idx: open_ok += 1
                else: print(f"NOTE OPEN-BUT-PRESENT {os.path.basename(f)}:{n} (registry stale?)")
            continue
        if frozen_override and os.path.basename(f) == frozen_override[0]:
            txt = frozen_override[1](txt)
        for n, k, s in decls(txt):
            if drop and n == drop: cands = []
            else: cands = idx.get(n, [])
            if k == "theorem": t_all += 1
            else: d_all += 1
            if len(cands) > 1: dups += 1
            hit = [c for c in cands if c[2] == s]
            if hit:
                if k == "theorem": t_ok += 1
                else: d_ok += 1
                if not quiet: print(f"  OK   {os.path.basename(f)}:{n}  <- {hit[0][0]}")
            else:
                fails += 1
                if not cands:
                    print(f"FAIL MISSING {os.path.basename(f)}:{n}")
                else:
                    print(f"FAIL DIFF    {os.path.basename(f)}:{n}  (in {cands[0][0]})")
                    print(f"    frozen: {s}")
                    print(f"    prod  : {cands[0][2]}")
    print(f"FROZEN_FILES={len(files)}")
    print(f"SUPERSEDED_SKIPPED={len(superseded)}")
    print(f"OPEN_REGISTRY={open_ok}/{open_all}")
    print(f"THEOREMS={t_ok}/{t_all}")
    print(f"DEFINITIONS={d_ok}/{d_all}")
    print(f"DUPLICATE_NAMES={dups}")
    print(f"FAIL={fails}")
    return fails

def unicode_control():
    """Positive/negative controls for Unicode-subscript identifiers (GPT Gate-1 必須A-6)."""
    sample = "theorem primrec₂_int_add (x : ℕ) : x = x := rfl\ndef foo₃'.bar (n : ℕ) : ℕ := n\n"
    names_new = [m.group(3) for m in DECL.finditer(sample)]
    names_old = [m.group(3) for m in DECL_OLD_BUGGY.finditer(sample)]
    pos = names_new == ["primrec₂_int_add", "foo₃'.bar"]
    neg = names_old == ["primrec", "foo"]          # the old regex truncates: the control must SEE the bug
    print(f"UNICODE_CONTROL_NEW_NAMES={names_new}")
    print(f"UNICODE_CONTROL_OLD_NAMES={names_old}")
    print(f"UNICODE_CONTROL_POSITIVE={1 if pos else 0}")
    print(f"UNICODE_CONTROL_OLD_TRUNCATES={1 if neg else 0}")
    # end-to-end negative control: rename a subscripted frozen name to a subscripted name absent from production;
    # with a correct parser this must be reported as FAIL MISSING (old parser: matched the truncated prefix).
    def rename(txt):
        return txt.replace("theorem primrec₂_solCheck", "theorem primrec₂_solCheckXX", 1)
    f3 = run(frozen_override=("ComputabilityFragments_STATEMENTS.lean", rename), quiet=True)
    e2e = f3 is not None and f3 >= 1
    print(f"UNICODE_CONTROL_E2E_MISSING_CAUGHT={1 if e2e else 0}")
    ok = pos and neg and e2e
    print(f"UNICODE_CONTROL_EXIT={0 if ok else 1}")
    return ok

def main():
    if "--unicode-control" in sys.argv:
        sys.exit(0 if unicode_control() else 1)
    if "--negative-control" in sys.argv:
        # control 1: mutate the statement of the first declaration in ComputabilityFragments_STATEMENTS.lean
        def mutate(txt):
            m = DECL.search(txt)
            cut = txt.find(":=", m.start())
            return txt[:cut] + " ∧ False " + txt[cut:]
        # (s25 repair: the r14 targets AllR_TARGET_STATEMENTS.lean / quadraticWitnessInertiaZ are no longer in
        #  frozen_statements, so both controls silently returned 0 — retargeted to frozen items that exist.)
        f1 = run(frozen_override=("ComputabilityFragments_STATEMENTS.lean", mutate), quiet=True)
        # control 2: pretend one production declaration does not exist
        f2 = run(drop="relation_phase_diagram", quiet=True)
        ok = (f1 is not None and f1 >= 1) and (f2 is not None and f2 >= 1)
        print(f"NEG_CONTROL_MUTATE_CAUGHT={1 if f1 else 0}")
        print(f"NEG_CONTROL_MISSING_CAUGHT={1 if f2 else 0}")
        print(f"NEG_CONTROL_EXIT={0 if ok else 1}")
        sys.exit(0 if ok else 1)
    fails = run(quiet="--quiet" in sys.argv)
    code = 1 if (fails is None or fails > 0) else 0
    print(f"SDIFF_EXIT={code}")
    sys.exit(code)

if __name__ == "__main__":
    main()
