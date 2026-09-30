#!/usr/bin/env python3
"""signoff_controls.py -- Gate-16 P0-2 (s42): planted regression controls for the author sign-off carry-over.

The reviewer showed (with a test approval field, not the author's signature) that the s41 generator carried an
approval across a paper-statement change because it compared only the 16-hex type prefix and never read
claim_hash.  Each control below copies the native directory and the tools to a temp tree, writes a SYNTHETIC old
sheet there with one signed row (AUTHOR_REVIEWER=TEST_CONTROL_NOT_AN_AUTHOR_SIGNATURE), plants one change, runs
tools/generate_signoff_sheet.py --out into the temp tree, and checks whether the test approval was carried.  The
live sheet (release/AUTHOR_SIGNOFF_SHEET.md) is never read or written by this script.
  1 paper claim_hash changed, type unchanged        -> must NOT carry
  2 type_sha256 changed, claim_hash unchanged       -> must NOT carry
  3 root changed (key no longer matches)            -> must NOT carry
  4 both hashes and root unchanged                  -> must carry (positive control)
  5 old row's hashes missing (16-hex prefix only)   -> must NOT carry
  6 old row unsigned, hashes unchanged              -> must stay unsigned
Prints one line per control and SIGNOFF_CONTROLS=<n>/6; exit 1 unless all six behave.
Usage: python3 tools/signoff_controls.py <root> [--native <dir>]
"""
import csv, os, re, shutil, subprocess, sys, tempfile

TEST = "TEST_CONTROL_NOT_AN_AUTHOR_SIGNATURE"

def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = os.path.abspath(args[0] if args else ".")
    native = os.path.join(root, "submission", "native")
    if "--native" in sys.argv: native = os.path.abspath(sys.argv[sys.argv.index("--native") + 1])
    tools = os.path.dirname(os.path.abspath(__file__))
    man = list(csv.DictReader(open(os.path.join(native, "PAPER_CLAIMS.tsv"), encoding="utf-8"), delimiter="\t"))
    review = list(csv.DictReader(open(os.path.join(native, "PAPER_CLAIMS_REVIEW.tsv"), encoding="utf-8"), delimiter="\t"))
    # the probe row: the first registry row whose (label, first root) has a review row
    probe = None
    for r in man:
        name = r["Lean_root"].split(",")[0].strip()
        for q in review:
            if q["paper_label"] == r["paper_label"] and q["Lean_root"].split(".")[-1] == name:
                probe = (r, q); break
        if probe: break
    if not probe: print("FAIL no probe row"); sys.exit(1)
    r, q = probe
    label, fq, sha, ch = r["paper_label"], q["Lean_root"], q["type_sha256"], r["claim_hash"]

    def old_sheet(label_, fq_, sha_, ch_, signed):
        return ("# synthetic old sheet (control)\n\n## Row 01 — %s ↔ `%s`\n\n**Paper statement.** x\n\n"
                "**Lean type (elaborated, normalised; sha256 %s; claim_hash %s).** `t`\n\n"
                "AUTHOR_REVIEWER=%s  \nASSISTED_BY=Claude  \nAUTHOR_DISPOSITION=%s  \nAUTHOR_SIGNOFF_DATE=%s  \n"
                % (label_, fq_, sha_, ch_, TEST if signed else "", "MATCH" if signed else "", "2026-01-01" if signed else ""))

    flip = lambda h: ("0" if h[0] != "0" else "1") + h[1:]
    cases = [
        ("C1 paper claim_hash changed, type same",   old_sheet(label, fq, sha, flip(ch), True),        False),
        ("C2 type_sha256 changed, claim_hash same",  old_sheet(label, fq, flip(sha), ch, True),        False),
        ("C3 root changed",                          old_sheet(label, fq + "_other", sha, ch, True),   False),
        ("C4 unchanged (positive control)",          old_sheet(label, fq, sha, ch, True),              True),
        ("C5 old hashes missing (16-hex prefix)",    old_sheet(label, fq, sha[:16] + "…", "", True),   False),
        ("C6 unsigned row, unchanged",               old_sheet(label, fq, sha, ch, False),             False),
    ]
    ok = 0
    for name, sheet, expect_carry in cases:
        t = tempfile.mkdtemp(prefix="signoff_ctrl_")
        try:
            shutil.copytree(native, os.path.join(t, "native"))
            shutil.copytree(tools, os.path.join(t, "tools"))
            out = os.path.join(t, "SHEET.md"); open(out, "w", encoding="utf-8").write(sheet)
            p = subprocess.run([sys.executable, os.path.join(t, "tools", "generate_signoff_sheet.py"), root,
                                "--native", os.path.join(t, "native"), "--out", out],
                               capture_output=True, text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
            txt = open(out, encoding="utf-8").read() if os.path.exists(out) else ""
            carried = TEST in txt
            m = re.search(r"SIGNOFF_CARRIED=(\d+)", p.stdout)
            n_carried = int(m.group(1)) if m else -1
            good = (carried == expect_carry) and (n_carried == (1 if expect_carry else 0)) and p.returncode == 0
            print("%s\t%s\tcarried=%s expected=%s SIGNOFF_CARRIED=%d exit=%d" % ("OK" if good else "FAIL", name, carried, expect_carry, n_carried, p.returncode))
            ok += good
        finally:
            shutil.rmtree(t, ignore_errors=True)
    print("SIGNOFF_CONTROLS=%d/6" % ok); print("SIGNOFF_CONTROLS_EXIT=%d" % (0 if ok == 6 else 1))
    sys.exit(0 if ok == 6 else 1)

if __name__ == "__main__":
    main()
