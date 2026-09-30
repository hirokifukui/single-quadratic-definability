#!/usr/bin/env python3
"""shipping_artifact_gate.py -- the shipped typeset artifact against what the seal says about it.

s36 (Gate-10 Z03).  The r31 archive shipped the r30 PDF (52 pages, sha d11b58...) under a seal that
said 51 pages and b1d672...: the seal quoted a build that ran in a throwaway root, and nothing
compared the seal with the file beside it.  This gate is that comparison.  It re-measures the
archive itself -- page count, hashes, manifests -- and reads the seal, README and CITATION as
claims.  Any disagreement is exit 1 and is named.

Usage:
    python3 tools/shipping_artifact_gate.py <package_root>
    python3 tools/shipping_artifact_gate.py --pages <pdf>          # print the page count and exit

What is checked (every line printed as CHECK <name> <ok|FAIL> <detail>):
    SEAL_PRESENT              exactly one correspondence/SEAL_r*.txt, and it is the package's round
    SEAL_PAGES                seal PDF_PAGES == measured page count of submission/*.pdf
    SEAL_PDF_SHA              seal SHIPPED_PDF_SHA256 == sha256(submission/*.pdf)
    SEAL_TEX_SHA              seal SHIPPED_TEX_SHA256 == sha256(submission/*.tex)
    GENERATED_PDF_EQ_SHIPPED  papers/apal_build/*.pdf byte-equal to submission/*.pdf
    GENERATED_TEX_EQ_SHIPPED  papers/apal_build/*.tex byte-equal to submission/*.tex
    BUILD_LOG_PAGES           papers/apal_build/*.log "Output written on ... (N pages" == measured
    SOURCE_MANIFEST           seal SOURCE_MANIFEST_SHA256 == recomputed (lean, frozen_statements, manuscript)
    SUBMISSION_MANIFEST       seal SUBMISSION_INPUT_MANIFEST_SHA256 == sha256(SUBMISSION_INPUT_MANIFEST.sha256)
                              and that file == recomputed with the same rule
    MEASUREMENTS_AGREE        SHIPPING_MEASUREMENTS.txt (written by the build) agrees with the seal on
                              every key both carry
    README_ROUND              README.md names the seal's round and no other round's seal or letter
    README_STALE_TOKENS       none of: Session 34, Gate 4, LETTER_GATE9, SEAL_r30, r30 archive
    CITATION_VERSION          CITATION.cff version == seal CITATION_VERSION (root and release/ copies)
    CITATION_DATE             CITATION.cff date-released == seal RELEASE_DATE
    TRUST_DUPLICATE_KEYS      release/TRUST_BOUNDARY_APAL.md: a key stated twice must carry one value
    TRUST_FIGURES             the trust document's figure block == the certificates (via submission_figures)
Page count is taken from pdfinfo when present, else pypdf, else the xelatex log; the source used is
printed, because a count from the log is a claim by the build and not a measurement of the file.
"""
import hashlib, os, re, subprocess, sys, glob
sys.dont_write_bytecode = True  # s40: the gate must not leave the __pycache__ it then checks for

def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()

def pages(pdf):
    try:
        out = subprocess.run(["pdfinfo", pdf], capture_output=True, text=True, timeout=60).stdout
        m = re.search(r"^Pages:\s+(\d+)", out, re.M)
        if m: return int(m.group(1)), "pdfinfo"
    except Exception:
        pass
    try:
        import pypdf
        return len(pypdf.PdfReader(pdf).pages), "pypdf"
    except Exception:
        pass
    return None, "none"

def kv(path):
    d = {}
    if not os.path.exists(path): return d
    for l in open(path, encoding="utf-8", errors="replace"):
        m = re.match(r"^\s*([A-Z][A-Z0-9_]+)=(\S+)\s*$", l)
        if m: d[m.group(1)] = m.group(2)
    return d

def manifest_sha(root, dirs):
    files = []
    for d in dirs:
        for dp, dn, fn in os.walk(os.path.join(root, d)):
            if "__pycache__" in dp: continue
            for f in fn:
                if not f.endswith(".pyc"): files.append(os.path.relpath(os.path.join(dp, f), root))
    files.sort()  # LC_ALL=C sort of relative paths
    body = "".join(f"{sha(os.path.join(root,f))}  {f}\n" for f in files)
    return hashlib.sha256(body.encode()).hexdigest(), len(files)

SUB_DIRS = "papers/apal_build submission tools release certificates manuscript frozen_statements".split()
def submission_manifest_text(root):
    files = []
    for d in SUB_DIRS:
        for dp, dn, fn in os.walk(os.path.join(root, d)):
            if "__pycache__" in dp: continue
            for f in fn:
                if re.search(r"\.(aux|log|out|pdf|pyc)$", f): continue
                if f.startswith("body") and f.endswith(".md"): continue
                if f == "appendix_e_table.md" or ".bak" in f: continue
                files.append(os.path.relpath(os.path.join(dp, f), root))
    files.sort()
    return "".join(f"{sha(os.path.join(root,f))}  {f}\n" for f in files), len(files)

def main():
    if len(sys.argv) >= 3 and sys.argv[1] == "--pages":
        n, src = pages(sys.argv[2])
        if n is None: sys.exit(1)
        print(n); return
    root = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else ".")
    fails = 0
    def check(name, ok, detail=""):
        nonlocal fails
        print(f"CHECK {name} {'ok' if ok else 'FAIL'} {detail}".rstrip())
        if not ok: fails += 1

    seals = sorted(glob.glob(os.path.join(root, "correspondence", "SEAL_r*.txt")),
                   key=lambda s: int(re.search(r"SEAL_r(\d+)", s).group(1)))
    # the round is the package's, read from its directory name when it carries one; older seals
    # belong in history/seals/, so correspondence/ must hold exactly the current one
    m = re.search(r"_(r\d+)_\d{8}$", os.path.basename(root))
    round_ = m.group(1) if m else (re.search(r"SEAL_(r\d+)", seals[-1]).group(1) if seals else "r?")
    cur = [s for s in seals if os.path.basename(s) == f"SEAL_{round_}.txt"]
    check("SEAL_PRESENT", len(seals) == 1 and len(cur) == 1,
          f"round={round_} n_in_correspondence={len(seals)} {[os.path.basename(s) for s in seals]}")
    if not cur:
        print(f"SHIPPING_ARTIFACT_GATE=FAIL checks_failed={fails}"); sys.exit(1)
    seal = kv(cur[0])
    pdf = os.path.join(root, "submission", "APAL_MANUSCRIPT_v32.pdf")
    tex = os.path.join(root, "submission", "APAL_MANUSCRIPT_v32.tex")
    bpdf = os.path.join(root, "papers", "apal_build", "APAL_MANUSCRIPT_v32.pdf")
    btex = os.path.join(root, "papers", "apal_build", "APAL_MANUSCRIPT_v32.tex")
    blog = os.path.join(root, "papers", "apal_build", "APAL_MANUSCRIPT_v32.log")
    have = all(os.path.exists(p) for p in (pdf, tex))
    check("SHIPPING_FILES_PRESENT", have)
    if have:
        n, src = pages(pdf)
        check("SEAL_PAGES", n is not None and seal.get("PDF_PAGES") == str(n), f"seal={seal.get('PDF_PAGES')} measured={n} via={src}")
        check("SEAL_PDF_SHA", seal.get("SHIPPED_PDF_SHA256") == sha(pdf), f"seal={str(seal.get('SHIPPED_PDF_SHA256'))[:12]} file={sha(pdf)[:12]}")
        check("SEAL_TEX_SHA", seal.get("SHIPPED_TEX_SHA256") == sha(tex), f"seal={str(seal.get('SHIPPED_TEX_SHA256'))[:12]} file={sha(tex)[:12]}")
        check("GENERATED_PDF_EQ_SHIPPED", os.path.exists(bpdf) and sha(bpdf) == sha(pdf))
        check("GENERATED_TEX_EQ_SHIPPED", os.path.exists(btex) and sha(btex) == sha(tex))
        if os.path.exists(blog):
            m = re.search(r"Output written on \S+ \((\d+) pages", open(blog, encoding="utf-8", errors="replace").read())
            check("BUILD_LOG_PAGES", m is not None and n is not None and int(m.group(1)) == n, f"log={m.group(1) if m else None} measured={n}")
        else:
            check("BUILD_LOG_PAGES", False, "no build log shipped")
    srcsha, nsrc = manifest_sha(root, ["lean", "frozen_statements", "manuscript"])
    check("SOURCE_MANIFEST", seal.get("SOURCE_MANIFEST_SHA256") == srcsha, f"seal={str(seal.get('SOURCE_MANIFEST_SHA256'))[:12]} recomputed={srcsha[:12]} files={nsrc}")
    smf = os.path.join(root, "SUBMISSION_INPUT_MANIFEST.sha256")
    if os.path.exists(smf):
        txt, nsub = submission_manifest_text(root)
        check("SUBMISSION_MANIFEST", seal.get("SUBMISSION_INPUT_MANIFEST_SHA256") == sha(smf) and open(smf).read() == txt,
              f"seal={str(seal.get('SUBMISSION_INPUT_MANIFEST_SHA256'))[:12]} file={sha(smf)[:12]} recomputed_eq_file={open(smf).read()==txt} files={nsub}")
    else:
        check("SUBMISSION_MANIFEST", False, "SUBMISSION_INPUT_MANIFEST.sha256 absent (build not run in this root)")
    meas = kv(os.path.join(root, "SHIPPING_MEASUREMENTS.txt"))
    if meas:
        bad = [k for k in meas if k in seal and meas[k] != seal[k]]
        check("MEASUREMENTS_AGREE", not bad, f"keys_compared={len([k for k in meas if k in seal])} disagree={bad}")
    else:
        check("MEASUREMENTS_AGREE", False, "SHIPPING_MEASUREMENTS.txt absent")
    readme = os.path.join(root, "README.md")
    rt = open(readme, encoding="utf-8").read() if os.path.exists(readme) else ""
    other_seals = sorted(set(re.findall(r"SEAL_(r\d+)", rt)) - {round_})
    letter = seal.get("LETTER", "")
    other_letters = sorted(set(re.findall(r"LETTER_GATE\d+", rt)) - ({letter} if letter else set()))
    check("README_ROUND", bool(rt) and (f"{round_}" in rt.splitlines()[0]) and not other_seals and not other_letters,
          f"round={round_} other_seals={other_seals} other_letters={other_letters}")
    stale = [t for t in ["Session 34", "Gate 4 ", "LETTER_GATE9", "SEAL_r30", "r30 archive"] if t in rt]
    check("README_STALE_TOKENS", not stale, f"{stale}")
    # s40 (Gate-14 P03): the README's own version/date line must equal the seal's, not just its round word.
    mv = re.search(r"^Version\s+(\S+)\s+\(`CITATION\.cff`\),\s+(\d{4}-\d{2}-\d{2})\.", rt, re.M)
    check("README_VERSION", mv is not None and mv.group(1) == seal.get("CITATION_VERSION"), f"readme={mv.group(1) if mv else None} seal={seal.get('CITATION_VERSION')}")
    check("README_DATE", mv is not None and mv.group(2) == seal.get("RELEASE_DATE"), f"readme={mv.group(2) if mv else None} seal={seal.get('RELEASE_DATE')}")
    # s40 (Gate-14 P04/P12): the generated release documents must carry the certificates' figures and no
    # unfilled token, and no release document may carry round/gate/session vocabulary (MH-11, whole folder).
    try:
        sys.path.insert(0, os.path.join(root, "tools"))
        from submission_figures import measure_trust
        fig = measure_trust(os.path.join(root, "certificates"))
    except Exception as e:
        fig = None; check("RELEASE_DOCS_FIGURES", False, f"measure_trust failed: {e}")
    if fig is not None:
        need = [str(fig[k]) for k in ("axiom_roots", "frozen_theorems", "frozen_definitions", "frozen_files", "binder_roots", "binder_unconditional")]
        for doc in ("README_BUILD_APAL.md", "RELEASE_CHECKLIST_APAL.md"):
            dp = os.path.join(root, "release", doc)
            dt = open(dp, encoding="utf-8").read() if os.path.exists(dp) else ""
            missing = [v for v in need if not re.search(r"(?<![\d.])" + re.escape(v) + r"(?![\d])", dt)]
            check("RELEASE_DOCS_FIGURES", bool(dt) and not missing and "{{" not in dt, f"{doc} missing={missing} unfilled={'{{' in dt}")
    roundwords = []
    # state documents only: the seal's open-items paragraph (SEAL_WHAT_IS_OPEN.md) is round correspondence by design
    for doc in [os.path.join(root, "release", d) for d in ("README_BUILD_APAL.md", "RELEASE_CHECKLIST_APAL.md", "TRUST_BOUNDARY_APAL.md",
                                                            "STATEMENT_MAP_FULL.md", "PROOF_COMPANION.md", "APPENDIX_F_LEAN_ANCHORS.md", "APPENDIX_F_COVERAGE.md")]:
        if not os.path.exists(doc): continue
        dt = open(doc, encoding="utf-8", errors="replace").read()
        hits = sorted(set(re.findall(r"\b(?:r\d{2}|Gate[- ]\d+|[Ss]ession \d+|s\d{2}(?![\w.]))\b", dt)))
        if hits: roundwords.append((os.path.basename(doc), hits[:6]))
    check("RELEASE_ROUND_WORDS", not roundwords, f"{roundwords}")
    # s40 (Gate-14 §18 release red team): bytecode, a second trust document or cover letter, and the partition record.
    pyc = [dp for dp, dn, fn in os.walk(root) if os.path.basename(dp) == "__pycache__"]
    check("NO_PYCACHE", not pyc, f"{[os.path.relpath(p, root) for p in pyc][:3]}")
    trusts = sorted(os.path.relpath(p, root) for p in glob.glob(os.path.join(root, "**", "TRUST_BOUNDARY*.md"), recursive=True)
                    if not p.endswith(".template.md") and "/history/" not in p.replace(os.sep, "/"))
    check("SINGLE_TRUST", trusts == ["release/TRUST_BOUNDARY_APAL.md"], f"{trusts}")
    covers = sorted(os.path.relpath(p, root) for p in glob.glob(os.path.join(root, "**", "*COVER_LETTER*.md"), recursive=True)
                    if "/history/" not in p.replace(os.sep, "/"))
    check("SINGLE_COVER_LETTER", len(covers) == 1, f"{covers}")
    prec = os.path.join(root, "PARTITION_RECORD.md")
    pc = os.path.join(root, "tools", "partition_check.py")
    if os.path.exists(prec) and os.path.exists(pc):
        r = subprocess.run([sys.executable, pc, root], capture_output=True, text=True)
        check("PARTITION_RECORD", r.returncode == 0, (r.stdout.strip().splitlines() or [""])[-1])
    else:
        check("PARTITION_RECORD", False, "PARTITION_RECORD.md or tools/partition_check.py absent")
    for name, path in (("CITATION_ROOT", os.path.join(root, "CITATION.cff")), ("CITATION_RELEASE", os.path.join(root, "release", "CITATION.cff"))):
        ct = open(path, encoding="utf-8").read() if os.path.exists(path) else ""
        v = re.search(r'^version:\s*"?([^"\n]+)"?', ct, re.M); d = re.search(r'^date-released:\s*"?([^"\n]+)"?', ct, re.M)
        check(name + "_VERSION", v is not None and v.group(1).strip() == seal.get("CITATION_VERSION"), f"cff={v.group(1) if v else None} seal={seal.get('CITATION_VERSION')}")
        check(name + "_DATE", d is not None and d.group(1).strip() == seal.get("RELEASE_DATE"), f"cff={d.group(1) if d else None} seal={seal.get('RELEASE_DATE')}")
    trust = os.path.join(root, "release", "TRUST_BOUNDARY_APAL.md")
    if os.path.exists(trust):
        seen = {}; dup = []
        for l in open(trust, encoding="utf-8"):
            m = re.match(r"^\s*([a-z][a-z0-9_]+)=(\S+)\s*$", l) or \
                re.match(r"^\|\s*([a-z][a-z0-9_]+)\b[^|]*\|\s*(\d+)\s*\|\s*$", l)  # keyed table rows count too
            if m:
                k, v = m.groups()
                if k in seen and seen[k] != v: dup.append((k, seen[k], v))
                seen.setdefault(k, v)
        check("TRUST_DUPLICATE_KEYS", not dup, f"keys={len(seen)} conflicts={dup}")
        sf = os.path.join(root, "tools", "submission_figures.py")
        if os.path.exists(sf):
            r = subprocess.run([sys.executable, sf, "--trust", trust, os.path.join(root, "certificates")], capture_output=True, text=True)
            check("TRUST_FIGURES", r.returncode == 0, (r.stdout.strip().splitlines() or [""])[-1])
    else:
        check("TRUST_DUPLICATE_KEYS", False, "trust document absent")
    print(f"SHIPPING_ARTIFACT_GATE={'OK' if fails == 0 else 'FAIL'} checks_failed={fails}")
    sys.exit(0 if fails == 0 else 1)

if __name__ == "__main__":
    main()
