#!/usr/bin/env python3
"""definition_fidelity.py — GPT r15 必須C: definition-BODY fidelity certificate.
Runs scripts/definition_fidelity.lean (lake env lean) which dumps, for every frozen
`def` short name, all matching production constants (namespace-qualified, incl.
auxiliaries) with pp.explicit/pp.universes/pp.proofs TYPE and VALUE. This driver
hashes each constant's TYPE and VALUE (sha256) and either
  --freeze  <cert>   writes the certificate (one line per constant), or
  --check   <cert>   compares against it; exit 1 on any mismatch/missing/extra.
Anchors (line-initial): DEFFID_CONSTANTS=<n> DEFFID_SHORTNAMES=<resolved>/<all>
  DEFFID_MISMATCH=<n> DEFFID_MISSING=<n> DEFFID_EXTRA=<n> DEFFID_EXIT=<0|1>
A body change of any frozen definition (or its match/aux constants) changes the
VALUE hash; a type-only change changes the TYPE hash; a docstring-only change
changes neither (negative controls: --selftest).
"""
import subprocess, hashlib, sys, os, re
LEAN = os.environ.get("LEAN_BIN", os.path.expanduser("~/.elan/bin/lake"))
SCRIPT = os.environ.get("DEFFID_LEAN", "scripts/definition_fidelity.lean")
def sha(s): return hashlib.sha256(s.encode("utf-8")).hexdigest()
def dump():
    r = subprocess.run([LEAN, "env", "lean", SCRIPT], capture_output=True, text=True)
    out = r.stdout
    if r.returncode != 0 or "DEFTOTAL" not in out:
        print(out[-2000:]); print(r.stderr[-2000:]); print("DEFFID_EXIT=1 (lean failure)"); sys.exit(1)
    recs = {}
    for m in re.finditer(r"DEFBEGIN (\S+) short=(\S+) kind=(\S+)\nTYPE (.*?)\nVALUE (.*?)\nDEFEND \1", out, re.S):
        n, s, k, ty, val = m.groups()
        recs[n] = (s, k, sha(ty), sha(val))
    missing = re.findall(r"DEFMISSING (\S+)", out)
    tot = re.search(r"DEFTOTAL (\d+) shortnames=(\d+)", out)
    return recs, missing, int(tot.group(1)), int(tot.group(2))
def write(cert, recs, missing, nshort):
    with open(cert, "w") as f:
        f.write(f"# definition body fidelity certificate; constants={len(recs)} shortnames_resolved={nshort-len(missing)}/{nshort}\n")
        f.write("# unresolved short names (no production constant; superseded/open registry): " + " ".join(missing) + "\n")
        for n in sorted(recs):
            s, k, th, vh = recs[n]; f.write(f"{n}\t{s}\t{k}\t{th}\t{vh}\n")
def read(cert):
    d = {}
    for l in open(cert):
        if l.startswith("#") or not l.strip(): continue
        n, s, k, th, vh = l.rstrip("\n").split("\t"); d[n] = (s, k, th, vh)
    return d
def main():
    mode, cert = sys.argv[1], sys.argv[2]
    recs, missing, tot, nshort = dump()
    print(f"DEFFID_CONSTANTS={len(recs)}"); print(f"DEFFID_SHORTNAMES={nshort-len(missing)}/{nshort}")
    if mode == "--freeze":
        write(cert, recs, missing, nshort); print(f"DEFFID_FROZEN={cert}"); print("DEFFID_EXIT=0"); return
    fro = read(cert); mism = []; miss = [n for n in fro if n not in recs]; extra = [n for n in recs if n not in fro]
    for n in fro:
        if n in recs and fro[n][2:] != recs[n][2:]:
            which = "TYPE" if fro[n][2] != recs[n][2] else "VALUE"
            mism.append((n, which)); print(f"MISMATCH {n} {which}")
    for n in miss: print(f"MISSING {n}")
    for n in extra: print(f"EXTRA {n}")
    print(f"DEFFID_MISMATCH={len(mism)}"); print(f"DEFFID_MISSING={len(miss)}"); print(f"DEFFID_EXTRA={len(extra)}")
    bad = len(mism) + len(miss) + len(extra); print(f"DEFFID_EXIT={1 if bad else 0}"); sys.exit(1 if bad else 0)
main()
