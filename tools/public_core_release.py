#!/usr/bin/env python3
"""public_core_release.py -- the public core as a release of its own (s42, Gate-16 P0-3 / Packet C).

r37's APAL_PUBLIC_CORE zip was a correct partition of the full package (445 + 657 = 1102, no overlap, no
loss) but not a self-verifying release: it carried the parent's SHA256SUMS (1101 entries, 657 of them for
files that are not in the core), and the parent's seal, whose source and submission manifests are measured
over the full tree.  `sha256sum -c` failed, the shipping gate failed three checks, and the development gate
(gate5) demanded history files that leave the core by design.

Two layers, as the reviewer prescribed:
  provenance   the parent's partition record, seal and shipping measurements stay in the core BYTE FOR BYTE
               (they are payload members of the partition); a third party can still subtract the release
               metadata named in CORE_SEAL.txt and check core + history == full package.
  release      the core gets metadata computed on ITSELF -- CORE_SEAL.txt, CORE_SOURCE_MANIFEST.sha256,
               CORE_SUBMISSION_INPUT_MANIFEST.sha256, README_PUBLIC_CORE.md and its own SHA256SUMS -- and a
               gate that reads only the core: `--verify` in an empty directory into which only the core zip
               was expanded.  No development gate is run on the core; gate5's history rules are development
               gates and are named as such in README_PUBLIC_CORE.md.

s43 (Gate-17 FIX-01): the SHA256SUMS check is fail-closed (check_checksums); tools/public_core_controls.py
plants eight defective manifests and requires each to be refused.

Usage:
  python3 tools/public_core_release.py --generate <core_dir> --round rNN --parent-zip-sha256 <hex> [--parent-zip-name <name>]
      writes the four release files into <core_dir> (SHA256SUMS is written by the caller LAST); prints
      CORE_RELEASE_FILES=... and CORE_PAYLOAD_FILES=...
  python3 tools/public_core_release.py --verify <core_dir>
      prints CORE_CHECKSUM_MISSING= CORE_CHECKSUM_MISMATCH= CORE_SOURCE_MANIFEST= CORE_SUBMISSION_MANIFEST=
             CORE_PDF= REQUIRED_HISTORY_FILES= CURRENT_CLAIMS_FAIL= PUBLIC_LOCAL_IMPORTS_MISSING= BUILD_ENTRY=
             CORE_SHIPPING_EXIT=0|1; exit accordingly.  Every file the gate reads is listed in
             REQUIRED_FILES and none of them may lie under a history path.
"""
import hashlib, os, re, subprocess, sys, glob
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

RELEASE_FILES = ["CORE_SEAL.txt", "CORE_SOURCE_MANIFEST.sha256", "CORE_SUBMISSION_INPUT_MANIFEST.sha256", "README_PUBLIC_CORE.md"]
HISTORY_DIRS = ("history/", "independent_reviews/", "referee_simulation/", "drafts/", "development_notes/", "mathematics/RED_TEAM", "structural_theory/GATE")
SRC_DIRS = ["lean", "frozen_statements", "manuscript"]

def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""): h.update(b)
    return h.hexdigest()

def walk_files(root, dirs):
    out = []
    for d in dirs:
        for dp, dn, fn in os.walk(os.path.join(root, d)):
            dn[:] = [x for x in dn if x != "__pycache__"]
            for f in fn:
                if f.endswith(".pyc") or f == ".DS_Store": continue
                out.append(os.path.relpath(os.path.join(dp, f), root).replace(os.sep, "/"))
    return sorted(out)

def manifest_text(root, files):
    return "".join("%s  %s\n" % (sha(os.path.join(root, f)), f) for f in files)

def submission_text(root):
    from shipping_artifact_gate import submission_manifest_text
    return submission_manifest_text(root)

def kv_file(path):
    d = {}
    for l in open(path, encoding="utf-8", errors="replace"):
        for k, v in re.findall(r"\b([A-Z][A-Z0-9_]+)=([^\s()]+)", l): d[k] = v.strip(",;")
    return d

def payload_files(core):
    all_ = []
    for dp, dn, fn in os.walk(core):
        dn[:] = [x for x in dn if x != "__pycache__"]
        for f in fn:
            if f == ".DS_Store": continue
            all_.append(os.path.relpath(os.path.join(dp, f), core).replace(os.sep, "/"))
    return sorted(f for f in all_ if f not in RELEASE_FILES and f != "SHA256SUMS")

README_TEXT = """# Public core of the mpup {round} artifact — a self-verifying release

This archive is the PUBLIC CORE cut from the sealed full package `{parent}` (SHA-256 `{psha}`):
the Lean development (`lean/`), the frozen statements and certificates, the shipped tools, the native
manuscript source and the built PDF, the release documents, and the current correspondence.  The
development history (earlier rounds' reviews, homework, red-team notes, superseded drafts) is in the
companion DEVELOPMENT_HISTORY archive; the two archives partition the full package without overlap.

## Verify this archive on its own (nothing else needed)

    shasum -a 256 -c SHA256SUMS            # every file of THIS archive
    python3 tools/public_core_release.py --verify .

The second command checks `CORE_SEAL.txt` against the archive: its source manifest (`lean/`,
`frozen_statements/`, `manuscript/`), its submission-input manifest, the PDF and TeX hashes and the page
count, the paper-claim registry (`tools/paper_claims_check.py`), the local `DiophCompression`/`MPUP`
imports, and the build entry (`release/README_BUILD_APAL.md`, `release/build_submission_from_package.sh`,
`lean/lakefile.lean`, `lean/lean-toolchain`, `lean/fresh_build.sh`), and the clean-room record of the Lean source
(`certificates/CLEANROOM_REFERENCE.txt` names the original build log; the log must be present byte for byte, must
name the source manifest shipped here, and that manifest must equal the one recomputed from `lean/`).  The record
is the log of the run that built this source; when a round does not change the Lean source, the earlier run's log
is kept under its original name and is not re-dated.  It reads no file outside this archive and prints
`REQUIRED_HISTORY_FILES=0`.  Expected: `CORE_SHIPPING_EXIT=0`.

Then, if you want to rebuild: `bash release/build_submission_from_package.sh` (typesetting) and, for the
kernel, `release/README_BUILD_APAL.md` (clean-room Lean build; mathlib and toolchain pinned in `lean/`).

## Provenance layer (kept byte for byte; do not run its gates here)

`PARTITION_RECORD.md`, `correspondence/SEAL_{round}.txt`, `SHIPPING_MEASUREMENTS.txt`,
`SUBMISSION_INPUT_MANIFEST.sha256` and `ASSEMBLY_GATES.log`/`PACKAGE_BUILD.log` are the FULL PACKAGE's
records and are members of the partition; they are unchanged here so that core + history reproduces the
full package.  Their figures (source manifest, submission manifest, the parent's checksum entries, gate5's 363 rules)
describe the full tree, not this archive, and `tools/shipping_artifact_gate.py` / `tools/gate5_verify.py`
are development gates that require history files by design: they are meant for the full package and
fail here for that reason alone.  The release layer named in `CORE_SEAL.txt` under CORE_RELEASE_FILES is
what this archive adds; subtract it (and `SHA256SUMS`) to recover the partition payload.
"""

def generate(core, round_, psha, pname):
    core = os.path.abspath(core)
    for f in RELEASE_FILES + ["SHA256SUMS"]:
        p = os.path.join(core, f)
        if os.path.exists(p): os.remove(p)
    payload = payload_files(core)
    src = walk_files(core, SRC_DIRS)
    open(os.path.join(core, "CORE_SOURCE_MANIFEST.sha256"), "w", encoding="utf-8").write(manifest_text(core, src))
    stxt, nsub = submission_text(core)
    open(os.path.join(core, "CORE_SUBMISSION_INPUT_MANIFEST.sha256"), "w", encoding="utf-8").write(stxt)
    pdfs = sorted(glob.glob(os.path.join(core, "submission", "*.pdf"))); texs = sorted(glob.glob(os.path.join(core, "submission", "*.tex")))
    if len(pdfs) != 1 or len(texs) != 1: print("CORE_GENERATE=FAIL submission/ must hold one pdf and one tex"); sys.exit(1)
    from shipping_artifact_gate import pages
    npages, psrc = pages(pdfs[0])
    pseal = os.path.join(core, "correspondence", "SEAL_%s.txt" % round_)
    if not os.path.exists(pseal): print("CORE_GENERATE=FAIL parent seal %s absent" % pseal); sys.exit(1)
    fig = kv_file(pseal)
    lines = ["CORE_SEAL %s - the public core measured on itself" % round_,
             "Generated by tools/public_core_release.py --generate on the core payload; SHA256SUMS is written afterwards",
             "over every file including this one, and tools/public_core_release.py --verify re-measures the archive.",
             "",
             "ROUND=%s" % round_,
             "PARENT_ZIP_NAME=%s" % pname,
             "PARENT_ZIP_SHA256=%s" % psha,
             "PARENT_SEAL=correspondence/SEAL_%s.txt" % round_,
             "PARENT_SEAL_SHA256=%s" % sha(pseal),
             "CORE_PAYLOAD_FILES=%d" % len(payload),
             "CORE_RELEASE_FILES=%s" % ",".join(RELEASE_FILES + ["SHA256SUMS"]),
             "CORE_SOURCE_MANIFEST_FILES=%d" % len(src),
             "CORE_SOURCE_MANIFEST_SHA256=%s" % hashlib.sha256(manifest_text(core, src).encode()).hexdigest(),
             "CORE_SUBMISSION_INPUT_MANIFEST_FILES=%d" % nsub,
             "CORE_SUBMISSION_INPUT_MANIFEST_SHA256=%s" % hashlib.sha256(stxt.encode()).hexdigest(),
             "SHIPPED_PDF=%s" % os.path.relpath(pdfs[0], core),
             "SHIPPED_PDF_SHA256=%s" % sha(pdfs[0]),
             "SHIPPED_TEX_SHA256=%s" % sha(texs[0]),
             "PDF_PAGES=%s" % npages,
             "PDF_PAGES_VIA=%s" % psrc,
             "KERNEL_ROOTS_PER_PARENT_SEAL=%s" % fig.get("BINDER_ROOTS", "?"),
             "DEVELOPMENT_GATES_NOT_FOR_THIS_ARCHIVE=tools/shipping_artifact_gate.py,tools/gate5_verify.py,tools/partition_check.py",
             ""]
    open(os.path.join(core, "CORE_SEAL.txt"), "w", encoding="utf-8").write("\n".join(lines))
    open(os.path.join(core, "README_PUBLIC_CORE.md"), "w", encoding="utf-8").write(README_TEXT.format(round=round_, parent=pname, psha=psha))
    print("CORE_PAYLOAD_FILES=%d" % len(payload)); print("CORE_RELEASE_FILES=%d" % (len(RELEASE_FILES) + 1))
    print("CORE_SOURCE_MANIFEST_FILES=%d CORE_SUBMISSION_INPUT_MANIFEST_FILES=%d PDF_PAGES=%s" % (len(src), nsub, npages))
    print("CORE_GENERATE=OK")

SUMS_LINE = re.compile(r"^([0-9a-f]{64})  (.+)$")

def check_checksums(core):
    """Fail-closed SHA256SUMS check (s43, Gate-17 FIX-01).  The r38 parser dropped unparsable lines silently,
    tested archive coverage only when at least one line had parsed, and accepted a manifest with zero valid
    entries; an empty or garbage SHA256SUMS therefore verified.  Now every one of these fails the archive:
    manifest absent, empty, zero valid entries, any unparsable line, any duplicate path, any absolute path or
    parent traversal, any listed file missing or with a wrong digest, any archive file not listed.  The set
    comparison (listed vs actual) always runs.  Returns a dict; ok=True only for a clean archive."""
    core = os.path.abspath(core)
    r = dict(listed=0, missing=0, mismatch=0, unlisted=0, invalid=0, duplicate=0, badpath=0, ok=False, reason="")
    sums = os.path.join(core, "SHA256SUMS")
    if not os.path.isfile(sums): r["reason"] = "SHA256SUMS absent"; return r
    names = set(); nonempty = 0
    for raw in open(sums, encoding="utf-8", errors="replace"):
        l = raw.rstrip("\n").rstrip("\r")
        if l == "": continue
        nonempty += 1
        m = SUMS_LINE.match(l)
        if not m: r["invalid"] += 1; continue
        rel = re.sub(r"^\./", "", m.group(2))
        parts = rel.split("/")
        if rel == "" or rel.startswith("/") or ".." in parts or "." in parts or "\\" in rel or rel.endswith("/"):
            r["badpath"] += 1; continue
        if rel in names: r["duplicate"] += 1; continue
        names.add(rel); r["listed"] += 1
        p = os.path.join(core, rel)
        if not os.path.isfile(p): r["missing"] += 1
        elif sha(p) != m.group(1): r["mismatch"] += 1
    if nonempty == 0: r["reason"] = "SHA256SUMS empty"; return r
    for dp, dn, fn in os.walk(core):
        dn[:] = [x for x in dn if x != "__pycache__"]
        for f in fn:
            rp = os.path.relpath(os.path.join(dp, f), core).replace(os.sep, "/")
            if rp != "SHA256SUMS" and rp not in names: r["unlisted"] += 1
    if r["listed"] == 0: r["reason"] = "no valid entry"
    elif r["invalid"]: r["reason"] = "invalid lines"
    elif r["badpath"]: r["reason"] = "absolute or traversing path"
    elif r["duplicate"]: r["reason"] = "duplicate entries"
    elif r["missing"] or r["mismatch"] or r["unlisted"]: r["reason"] = "missing/mismatch/unlisted"
    else: r["ok"] = True
    return r

# s62 (GATE32 P0): the clean-room record of the shipped Lean source must be IN the core.  r50 reused r49's cold room
# (same source) and the round-named exclusion sent that record to the history archive, so the core carried no build
# record at all.  Whether a record is current is decided by its source manifest, not by its round number.
LEAN_MANIFEST_DIRS = ["MPUP", "DiophCompression", "ResearchUpgrade", "scripts"]
LEAN_MANIFEST_TOP = ["MPUP.lean", "DiophCompression.lean", "ResearchUpgrade.lean", "lakefile.lean", "lean-toolchain"]

def lean_manifest_text(core):
    """The Lean source manifest exactly as lean/fresh_build.sh writes it (paths relative to lean/)."""
    base = os.path.join(core, "lean"); files = []
    for d in LEAN_MANIFEST_DIRS:
        for dp, dn, fn in os.walk(os.path.join(base, d)):
            for f in fn:
                if f.endswith((".lean", ".py", ".sh")):
                    files.append(os.path.relpath(os.path.join(dp, f), base).replace(os.sep, "/"))
    files += LEAN_MANIFEST_TOP
    return "".join("%s  %s\n" % (sha(os.path.join(base, f)), f) for f in sorted(files, key=lambda x: x.encode()))

def check_cleanroom_reference(core):
    """certificates/CLEANROOM_REFERENCE.txt names the original clean-room log and the source manifest it attests.
    Checks: both files present in the core; the log's bytes match the recorded sha256; the log names exactly one
    SRC_MANIFEST_SHA256 and it equals the manifest's sha256; the manifest equals the one recomputed from lean/;
    FRESH_EXIT=0, SOURCE_FREEZE=OK, RU_BUILD_EXIT=0 occur exactly once.  Evidence consistency only: this does not
    run Lean and does not prove the log authentic."""
    r = {"ok": False, "reason": "", "log": "", "src": ""}
    ref = os.path.join(core, "certificates", "CLEANROOM_REFERENCE.txt")
    if not os.path.isfile(ref): r["reason"] = "MISSING_REFERENCE"; return r
    kv = {}
    for l in open(ref, encoding="utf-8"):
        if "=" in l and not l.startswith("#"):
            k, v = l.rstrip("\n").split("=", 1); kv[k.strip()] = v.strip()
    logrel, manrel = kv.get("original_name", ""), kv.get("source_manifest", "")
    for rel in (logrel, manrel):
        if not rel.startswith("certificates/") or ".." in rel.split("/"): r["reason"] = "BAD_REFERENCE_PATH"; return r
    r["log"] = logrel
    logp, manp = os.path.join(core, logrel), os.path.join(core, manrel)
    if not os.path.isfile(logp): r["reason"] = "MISSING_BUILD_RECORD"; return r
    if not os.path.isfile(manp): r["reason"] = "MISSING_MANIFEST"; return r
    if sha(logp) != kv.get("log_sha256"): r["reason"] = "LOG_SHA256_MISMATCH"; return r
    msha = sha(manp); r["src"] = msha
    if kv.get("source_manifest_sha256") != msha: r["reason"] = "REFERENCE_MANIFEST_MISMATCH"; return r
    text = open(logp, encoding="utf-8", errors="replace").read()
    if re.findall(r"^SRC_MANIFEST_SHA256=([0-9a-f]{64})$", text, re.M) != [msha]: r["reason"] = "SOURCE_HASH_MISMATCH"; return r
    if open(manp, encoding="utf-8").read() != lean_manifest_text(core): r["reason"] = "MANIFEST_NOT_SHIPPED_SOURCE"; return r
    for key, val in (("FRESH_EXIT", "0"), ("SOURCE_FREEZE", "OK"), ("RU_BUILD_EXIT", "0")):
        if re.findall(r"^" + key + r"=(\S*)\s*$", text, re.M) != [val]: r["reason"] = "BAD_OR_MISSING_" + key; return r
    r["ok"] = True; r["reason"] = "MATCHED_SHIPPED_SOURCE"; return r

def verify(core):
    core = os.path.abspath(core); fails = 0; required = []
    def R(p): required.append(p); return os.path.join(core, p)
    # 1 checksums (s43, Gate-17 FIX-01: fail-closed -- see check_checksums)
    ck = check_checksums(core); required.append("SHA256SUMS")
    print("CORE_CHECKSUM_LISTED=%d CORE_CHECKSUM_MISSING=%d CORE_CHECKSUM_MISMATCH=%d CORE_CHECKSUM_UNLISTED=%d "
          "CORE_CHECKSUM_INVALID_LINES=%d CORE_CHECKSUM_DUPLICATES=%d CORE_CHECKSUM_BAD_PATHS=%d CORE_CHECKSUM=%s"
          % (ck["listed"], ck["missing"], ck["mismatch"], ck["unlisted"], ck["invalid"], ck["duplicate"], ck["badpath"],
             "ok" if ck["ok"] else "FAIL " + ck["reason"]))
    fails += (not ck["ok"])
    # 2 seal
    seal_p = R("CORE_SEAL.txt")
    if not os.path.exists(seal_p): print("CORE_SEAL=FAIL absent"); fails += 1; seal = {}
    else: seal = kv_file(seal_p)
    src = walk_files(core, SRC_DIRS); srcsha = hashlib.sha256(manifest_text(core, src).encode()).hexdigest()
    ok = seal.get("CORE_SOURCE_MANIFEST_SHA256") == srcsha and open(R("CORE_SOURCE_MANIFEST.sha256"), encoding="utf-8").read() == manifest_text(core, src) if os.path.exists(os.path.join(core, "CORE_SOURCE_MANIFEST.sha256")) else False
    print("CORE_SOURCE_MANIFEST=%s files=%d seal=%s recomputed=%s" % ("ok" if ok else "FAIL", len(src), str(seal.get("CORE_SOURCE_MANIFEST_SHA256"))[:12], srcsha[:12])); fails += (not ok)
    stxt, nsub = submission_text(core); ssha = hashlib.sha256(stxt.encode()).hexdigest()
    smf = R("CORE_SUBMISSION_INPUT_MANIFEST.sha256")
    ok = os.path.exists(smf) and open(smf, encoding="utf-8").read() == stxt and seal.get("CORE_SUBMISSION_INPUT_MANIFEST_SHA256") == ssha
    print("CORE_SUBMISSION_MANIFEST=%s files=%d seal=%s recomputed=%s" % ("ok" if ok else "FAIL", nsub, str(seal.get("CORE_SUBMISSION_INPUT_MANIFEST_SHA256"))[:12], ssha[:12])); fails += (not ok)
    from shipping_artifact_gate import pages
    pdf = seal.get("SHIPPED_PDF", "")
    if pdf and os.path.exists(os.path.join(core, pdf)):
        R(pdf); n, via = pages(os.path.join(core, pdf)); psha = sha(os.path.join(core, pdf))
        texs = sorted(glob.glob(os.path.join(core, "submission", "*.tex")))
        tsha = sha(texs[0]) if len(texs) == 1 else ""
        ok = seal.get("SHIPPED_PDF_SHA256") == psha and seal.get("SHIPPED_TEX_SHA256") == tsha and str(n) == seal.get("PDF_PAGES")
        print("CORE_PDF=%s pages=%s via=%s sha=%s tex=%s" % ("ok" if ok else "FAIL", n, via, psha[:12], tsha[:12])); fails += (not ok)
    else:
        print("CORE_PDF=FAIL shipped pdf absent"); fails += 1
    # 3 current claims (the registry gate, self-contained: certificates/, frozen_statements/, submission/native)
    pcc = R("tools/paper_claims_check.py"); R("submission/native/PAPER_CLAIMS.tsv"); R("submission/native/PAPER_CLAIMS_REVIEW.tsv")
    r = subprocess.run([sys.executable, pcc, core, "--native", os.path.join(core, "submission", "native")], capture_output=True, text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
    m = re.search(r"PAPER_CLAIMS_FAIL=(\d+)", r.stdout); cf = int(m.group(1)) if m else -1
    m2 = re.search(r"ONE_ROOT_LABELS=(\d+/\d+)", r.stdout)
    print("CURRENT_CLAIMS_FAIL=%d ONE_ROOT_LABELS=%s exit=%d" % (cf, m2.group(1) if m2 else "?", r.returncode)); fails += (cf != 0 or r.returncode != 0)
    # 4 local imports
    mods = set(); miss = set()
    for f in glob.glob(os.path.join(core, "lean", "**", "*.lean"), recursive=True):
        mods.add(os.path.relpath(f, os.path.join(core, "lean"))[:-5].replace(os.sep, "."))
    for f in glob.glob(os.path.join(core, "lean", "**", "*.lean"), recursive=True):
        for mm in re.findall(r"^import\s+((?:DiophCompression|MPUP)[\w.]*)", open(f, encoding="utf-8", errors="replace").read(), re.M):
            if mm not in mods: miss.add(mm)
    print("PUBLIC_LOCAL_IMPORTS_MISSING=%d %s" % (len(miss), sorted(miss)[:5])); fails += bool(miss)
    # 5 build entry
    entry = ["release/README_BUILD_APAL.md", "release/build_submission_from_package.sh", "lean/lakefile.lean", "lean/lean-toolchain", "lean/fresh_build.sh", "papers/apal_build/build.sh"]
    absent = [e for e in entry if not os.path.exists(R(e))]
    print("BUILD_ENTRY=%s absent=%s" % ("ok" if not absent else "FAIL", absent)); fails += bool(absent)
    # 5b (s62) the clean-room record of the shipped Lean source
    cr = check_cleanroom_reference(core)
    if cr["log"]: R(cr["log"])
    required.append("certificates/CLEANROOM_REFERENCE.txt")
    print("CLEANROOM_REFERENCE=%s log=%s src=%s" % ("ok" if cr["ok"] else "FAIL " + cr["reason"], cr["log"] or "-", cr["src"][:12] or "-"))
    fails += (not cr["ok"])
    # 6 the gate's own footprint: nothing it read lies under a history path
    hist = [p for p in required if p.startswith(HISTORY_DIRS)]
    print("REQUIRED_FILES=%d REQUIRED_HISTORY_FILES=%d %s" % (len(required), len(hist), hist[:3])); fails += bool(hist)
    print("CORE_SHIPPING_EXIT=%d" % (0 if fails == 0 else 1)); sys.exit(0 if fails == 0 else 1)

def main():
    a = sys.argv[1:]
    def opt(k, default=None):
        return a[a.index(k) + 1] if k in a else default
    if "--generate" in a:
        generate(opt("--generate"), opt("--round"), opt("--parent-zip-sha256", ""), opt("--parent-zip-name", ""))
    elif "--verify" in a:
        verify(opt("--verify"))
    else:
        print(__doc__); sys.exit(2)

if __name__ == "__main__":
    main()
