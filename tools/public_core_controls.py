#!/usr/bin/env python3
"""public_core_controls.py -- Gate-17 FIX-01 (s43): planted regression controls for the public core's SHA256SUMS gate.

The reviewer showed that r38's tools/public_core_release.py --verify returned CORE_SHIPPING_EXIT=0 on a core whose
SHA256SUMS was empty or consisted of one unparsable line: unparsable lines were dropped silently, the
listed-vs-actual comparison ran only if a line had parsed, and zero valid entries was not a failure.  Each control
below builds a small synthetic archive in a temp directory (three files in two directories), writes its correct
SHA256SUMS in the shipped form ("./" prefix, sorted), plants ONE defect, and calls check_checksums() from
tools/public_core_release.py -- the same function --verify runs.  No shipped archive is read or written.
  1 correct manifest                      -> must PASS (positive control)
  2 empty manifest                        -> must FAIL
  3 one unparsable line only              -> must FAIL
  4 duplicate entry                       -> must FAIL
  5 one entry deleted                     -> must FAIL (unlisted file)
  6 unlisted file added to the archive    -> must FAIL
  7 wrong digest on one entry             -> must FAIL
  8 parent-traversal path in the manifest -> must FAIL
Prints one line per control and CORE_CHECKSUM_CONTROLS=<n>/8; exit 1 unless all eight behave.
Usage: python3 tools/public_core_controls.py

s62 (GATE32 task 2): `--cleanroom <core_dir>` runs three controls on a copy of a real (split) public core for
check_cleanroom_reference(): the core as given must PASS; the core with the referenced log deleted must FAIL; the
core whose log names a different source manifest must FAIL.  Prints CLEANROOM_REF_CONTROLS=<n>/3.  The core given
is not modified (only lean/, certificates/ are copied to a temp directory).
"""
import hashlib, os, shutil, sys, tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from public_core_release import check_checksums, check_cleanroom_reference  # noqa: E402

FILES = {"a.txt": b"alpha\n", "sub/b.txt": b"beta\n", "sub/deep/c.bin": bytes(range(64))}

def build(root):
    for rel, data in FILES.items():
        p = os.path.join(root, rel); os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, "wb").write(data)
    return correct_lines(root)

def correct_lines(root):
    lines = []
    for rel in sorted(FILES):
        h = hashlib.sha256(open(os.path.join(root, rel), "rb").read()).hexdigest()
        lines.append("%s  ./%s" % (h, rel))
    return lines

def write_sums(root, lines):
    open(os.path.join(root, "SHA256SUMS"), "w", encoding="utf-8").write("".join(l + "\n" for l in lines))

def main():
    cases = []
    def case(name, expect_ok, plant):
        d = tempfile.mkdtemp(prefix="mpup_corectl_"); lines = build(d)
        plant(d, lines); r = check_checksums(d)
        got = r["ok"]; ok = (got == expect_ok)
        print("%s control %d %-38s expect=%s got=%s %s" % ("ok  " if ok else "FAIL", len(cases) + 1, name,
              "PASS" if expect_ok else "FAIL", "PASS" if got else "FAIL", "" if got else "(" + r["reason"] + ")"))
        cases.append(ok); shutil.rmtree(d, ignore_errors=True)
    case("correct manifest", True, lambda d, L: write_sums(d, L))
    case("empty manifest", False, lambda d, L: write_sums(d, []))
    case("one unparsable line only", False, lambda d, L: write_sums(d, ["this is not a checksum line"]))
    case("duplicate entry", False, lambda d, L: write_sums(d, L + [L[0]]))
    case("one entry deleted", False, lambda d, L: write_sums(d, L[1:]))
    def add_unlisted(d, L):
        open(os.path.join(d, "sub", "extra.txt"), "wb").write(b"unlisted\n"); write_sums(d, L)
    case("unlisted file added", False, add_unlisted)
    def wrong_digest(d, L):
        h, p = L[0].split("  ", 1); h = ("0" if h[0] != "0" else "1") + h[1:]; write_sums(d, [h + "  " + p] + L[1:])
    case("wrong digest", False, wrong_digest)
    def traversal(d, L):
        h, p = L[0].split("  ", 1); write_sums(d, [h + "  ../" + p[2:]] + L[1:])
    case("parent-traversal path", False, traversal)
    n = sum(cases); print("CORE_CHECKSUM_CONTROLS=%d/%d" % (n, len(cases)))
    print("CORE_CHECKSUM_CONTROLS_EXIT=%d" % (0 if n == len(cases) else 1)); sys.exit(0 if n == len(cases) else 1)

def cleanroom_controls(core):
    core = os.path.abspath(core); res = []
    def one(name, expect_ok, plant):
        d = tempfile.mkdtemp(prefix="mpup_crctl_")
        for sub in ("lean", "certificates"): shutil.copytree(os.path.join(core, sub), os.path.join(d, sub))
        plant(d); r = check_cleanroom_reference(d); ok = (r["ok"] == expect_ok)
        print("%s cleanroom control %d %-40s expect=%s got=%s (%s)" % ("ok  " if ok else "FAIL", len(res) + 1, name,
              "PASS" if expect_ok else "FAIL", "PASS" if r["ok"] else "FAIL", r["reason"]))
        res.append(ok); shutil.rmtree(d, ignore_errors=True)
    def ref(d):
        kv = {}
        for l in open(os.path.join(d, "certificates", "CLEANROOM_REFERENCE.txt"), encoding="utf-8"):
            if "=" in l and not l.startswith("#"): k, v = l.rstrip("\n").split("=", 1); kv[k.strip()] = v.strip()
        return kv
    one("original log as shipped", True, lambda d: None)
    one("referenced log deleted", False, lambda d: os.remove(os.path.join(d, ref(d)["original_name"])))
    def other_source(d):
        kv = ref(d); lp = os.path.join(d, kv["original_name"]); t = open(lp, encoding="utf-8").read()
        h = kv["source_manifest_sha256"]; bad = ("0" if h[0] != "0" else "1") + h[1:]
        t = t.replace("SRC_MANIFEST_SHA256=" + h, "SRC_MANIFEST_SHA256=" + bad); open(lp, "w", encoding="utf-8").write(t)
        # keep the recorded log hash consistent with the planted bytes, so only the source mismatch can fail it
        rp = os.path.join(d, "certificates", "CLEANROOM_REFERENCE.txt"); rt = open(rp, encoding="utf-8").read()
        rt = rt.replace("log_sha256=" + kv["log_sha256"], "log_sha256=" + hashlib.sha256(t.encode("utf-8")).hexdigest())
        open(rp, "w", encoding="utf-8").write(rt)
    one("log names another source manifest", False, other_source)
    n = sum(res); print("CLEANROOM_REF_CONTROLS=%d/%d" % (n, len(res)))
    print("CLEANROOM_REF_CONTROLS_EXIT=%d" % (0 if n == len(res) else 1)); sys.exit(0 if n == len(res) else 1)

if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--cleanroom":
        cleanroom_controls(sys.argv[2])
    else:
        main()
