#!/usr/bin/env python3
"""generate_trust.py -- release/TRUST_BOUNDARY_APAL.md from its template and the shipped certificates.

s36 (Gate-10 P0-4 / Z06).  The r31 trust document carried two sets of figures: a table typed at
r30 (394 / 375 / 55) and a block recomputed at r31 (413 / 394 / 56), in one file, both presented as
current.  Its reconciliation paragraph (366 / 89 / 51) had been advanced by hand from the r30
certificate (347 / 89 / 51) and matched nothing measurable: recomputed from the shipped report and
frozen statements it is 370 / 85 / 47.  Nothing in the document is typed any more.  Every figure is
a {{token}} in release/TRUST_BOUNDARY_APAL.template.md, filled here from certificates/ and
frozen_statements/, and an unfilled token is exit 1.

Usage:  python3 tools/generate_trust.py <package_root>
Writes: release/TRUST_BOUNDARY_APAL.md
        certificates/ROOT_FROZEN_RECONCILIATION_current.md
"""
import datetime, glob, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from submission_figures import measure_trust  # the same instrument the build's --trust check uses

DECL = re.compile(r'^((?:noncomputable )?(theorem|def)) +([A-Za-z0-9_.\u00C0-\U0010FFFF\']+)')

def frozen_theorems(root):
    names = set()
    for f in sorted(glob.glob(os.path.join(root, "frozen_statements", "*_STATEMENTS*.lean"))):
        ns = []
        for l in open(f, encoding="utf-8"):
            m = re.match(r"\s*namespace\s+(\S+)", l)
            if m: ns.append(m.group(1)); continue
            m = re.match(r"\s*end\s+(\S+)", l)
            if m and ns and ns[-1] == m.group(1): ns.pop(); continue
            m = DECL.match(l)
            if m and m.group(2) == "theorem": names.add(".".join(ns + [m.group(3)]))
    return names

def roots(root):
    t = open(os.path.join(root, "certificates", "FinalAxiomReport_current.log"), encoding="utf-8", errors="replace").read()
    return set(re.findall(r"^'([^']+)'", t, re.M))

def main():
    root = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else ".")
    cert = os.path.join(root, "certificates")
    fig = measure_trust(cert)
    fr, rt = frozen_theorems(root), roots(root)
    if len(fr) != fig.get("frozen_theorems"):
        print(f"GENERATE_TRUST=FAIL frozen theorem count {len(fr)} != statement_diff {fig.get('frozen_theorems')}"); sys.exit(1)
    if len(rt) != fig.get("axiom_roots"):
        print(f"GENERATE_TRUST=FAIL root count {len(rt)} != axiom report {fig.get('axiom_roots')}"); sys.exit(1)
    both = fr & rt
    fig.update(recon_both=len(both), recon_frozen_not_root=len(fr - rt), recon_root_not_frozen=len(rt - fr),
               generated_on=datetime.date.today().isoformat())
    tpl = open(os.path.join(root, "release", "TRUST_BOUNDARY_APAL.template.md"), encoding="utf-8").read()
    out = re.sub(r"\{\{(\w+)\}\}", lambda m: str(fig[m.group(1)]) if m.group(1) in fig else m.group(0), tpl)
    left = sorted(set(re.findall(r"\{\{(\w+)\}\}", out)))
    if left:
        print(f"GENERATE_TRUST=FAIL unfilled tokens {left}"); sys.exit(1)
    open(os.path.join(root, "release", "TRUST_BOUNDARY_APAL.md"), "w", encoding="utf-8").write(out)
    # s40 (Gate-14 P03/P04/P12): the build README, the release checklist and the root README's version
    # line are rendered from the same figures and from release/SEAL_INPUT.env, so no shipping document
    # can carry a count or a version the certificates and the seal do not.
    env = {}
    envp = os.path.join(root, "release", "SEAL_INPUT.env")
    if os.path.exists(envp):
        for l in open(envp, encoding="utf-8"):
            l = l.strip()
            if l and not l.startswith("#") and "=" in l:
                k, v = l.split("=", 1); env[k.strip()] = v.strip()
    fig.update(citation_version=env.get("CITATION_VERSION", "{{citation_version}}"),
               release_date=env.get("RELEASE_DATE", "{{release_date}}"),
               round=env.get("ROUND", "{{round}}"))  # s62: README_BUILD manifest recipe
    for tname, oname in (("README_BUILD_APAL.template.md", "README_BUILD_APAL.md"),
                         ("RELEASE_CHECKLIST_APAL.template.md", "RELEASE_CHECKLIST_APAL.md")):
        tp = os.path.join(root, "release", tname)
        if not os.path.exists(tp):
            print(f"GENERATE_TRUST=FAIL missing template release/{tname}"); sys.exit(1)
        t = open(tp, encoding="utf-8").read()
        o = re.sub(r"\{\{(\w+)\}\}", lambda m: str(fig[m.group(1)]) if m.group(1) in fig else m.group(0), t)
        left = sorted(set(re.findall(r"\{\{(\w+)\}\}", o)))
        if left:
            print(f"GENERATE_TRUST=FAIL unfilled tokens in {tname}: {left}"); sys.exit(1)
        open(os.path.join(root, "release", oname), "w", encoding="utf-8").write(o)
    rp = os.path.join(root, "README.md")
    if os.path.exists(rp):
        r = open(rp, encoding="utf-8").read()
        r2 = re.sub(r"\{\{(\w+)\}\}", lambda m: str(fig[m.group(1)]) if m.group(1) in fig else m.group(0), r)
        left = sorted(set(re.findall(r"\{\{(\w+)\}\}", r2)))
        if left:
            print(f"GENERATE_TRUST=FAIL unfilled tokens in README.md: {left}"); sys.exit(1)
        if r2 != r:
            open(rp, "w", encoding="utf-8").write(r2)
    with open(os.path.join(cert, "ROOT_FROZEN_RECONCILIATION_current.md"), "w", encoding="utf-8") as f:
        f.write("# Root / frozen-statement reconciliation (generated by tools/generate_trust.py, %s)\n\n" % fig["generated_on"])
        f.write("Identity: a frozen `theorem` qualified by its `namespace` stack equals the root name printed by\n"
                "`FinalAxiomReport`.  Counts are recomputed from the shipped `certificates/FinalAxiomReport_current.log`\n"
                "and `frozen_statements/`; the lists below are the two differences.\n\n")
        f.write("| set | size |\n|---|---|\n")
        f.write(f"| roots of the axiom report | {len(rt)} |\n| frozen theorem statements | {len(fr)} |\n| both | {len(both)} |\n")
        f.write(f"| frozen but not a root | {len(fr-rt)} |\n| root but not a frozen theorem | {len(rt-fr)} |\n\n")
        f.write("## Root but not a frozen theorem\n\n" + "".join(f"- `{n}`\n" for n in sorted(rt - fr)))
        f.write("\n## Frozen but not a root\n\n" + "".join(f"- `{n}`\n" for n in sorted(fr - rt)))
    print("GENERATE_TRUST=OK " + " ".join(f"{k}={fig[k]}" for k in sorted(fig) if k != "generated_on"))

if __name__ == "__main__":
    main()
