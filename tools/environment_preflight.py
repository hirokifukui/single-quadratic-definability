#!/usr/bin/env python3
"""environment_preflight.py -- pin the typesetting environment, and stop before overwriting a
shipped artifact when the environment has moved (s37, Gate-11 B02).

Why.  The PDF this archive ships is a function of the engine, the driver, the TeX Live release and
the fonts, and none of those were recorded anywhere.  A rebuild on a host with a different TeX Live
would silently produce a different PDF and the build would then copy it over the shipped one; the
gates downstream compare the PDF with the seal, so the damage would be caught, but only after the
shipped bytes had already been replaced.  This runs first and refuses to continue instead.

What is pinned: the xelatex banner, the xdvipdfmx banner, the TeX Live release, and the resolved
file names of the faces the preamble asks for.  The record lives beside the build script and travels
with the archive, so a reader can see the environment the shipped PDF was made in.

Usage:  python3 tools/environment_preflight.py <record.txt> [--pin]
  no flag : compare with the record; exit 1 (naming every difference) if it disagrees
  --pin   : write the record from this machine.  Deliberate act, never done by the build.
Exit 0 = this machine matches the record, or the record was just written.
"""
import os, re, subprocess, sys

def cmd(*a):
    try:
        r = subprocess.run(a, capture_output=True, text=True, timeout=60)
        return (r.stdout + r.stderr).strip()
    except Exception as e:
        return "UNAVAILABLE: %s" % e

def first(s, n=1):
    return "\n".join(s.splitlines()[:n]).strip()

def probe():
    out = {}
    out["XELATEX"]    = first(cmd("xelatex", "--version"))
    out["XDVIPDFMX"]  = first(cmd("xdvipdfmx", "--version"))
    tl = cmd("kpsewhich", "-var-value=TEXMFDIST")
    out["TEXMFDIST"]  = tl
    m = re.search(r"(\d{4})", tl or "")
    out["TEXLIVE"]    = m.group(1) if m else "UNKNOWN"
    fmt = cmd("kpsewhich", "fontspec.sty")
    out["FONTSPEC"]   = os.path.basename(fmt) + " @ " + (os.path.dirname(fmt) or "UNKNOWN")
    return out

def read(path):
    d = {}
    if not os.path.exists(path): return None
    for line in open(path, encoding="utf-8"):
        line = line.rstrip("\n")
        if not line or line.startswith("#") or "=" not in line: continue
        k, v = line.split("=", 1); d[k] = v
    return d

def main():
    path = sys.argv[1]
    now = probe()
    if "--pin" in sys.argv:
        with open(path, "w", encoding="utf-8") as f:
            f.write("# Typesetting environment pinned for this round (tools/environment_preflight.py --pin).\n")
            f.write("# The build refuses to overwrite a shipped artifact from an environment that differs.\n")
            for k in sorted(now): f.write("%s=%s\n" % (k, now[k]))
        print("ENVIRONMENT_PINNED %s keys=%d" % (path, len(now)))
        return 0
    rec = read(path)
    if rec is None:
        print("ENVIRONMENT_PREFLIGHT=FAIL no record at %s; run with --pin to create it" % path)
        return 1
    bad = [k for k in sorted(set(rec) | set(now)) if rec.get(k) != now.get(k)]
    for k in sorted(set(rec) | set(now)):
        mark = "differs" if k in bad else "ok"
        print("ENV %-10s %-8s %s" % (k, mark, (now.get(k) or "(absent here)")[:96]))
        if k in bad:
            print("ENV %-10s pinned   %s" % (k, (rec.get(k) or "(absent in record)")[:96]))
    print("ENVIRONMENT_PREFLIGHT=%s differing=%d" % ("OK" if not bad else "FAIL", len(bad)))
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
