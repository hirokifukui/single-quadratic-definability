#!/usr/bin/env python3
"""font_preflight.py - name the font that is missing, before xelatex buries it (s35, Gate-9 G05).

Why.  The Gate-9 review built the distributed archive on a clean Linux host and got

    fontspec Error: The font "STIX Two Text" cannot be found

nine hundred lines into a xelatex log, from a build whose requirements list mentioned elan,
mathlib, Python and disk space and no fonts at all.  Measured here: none of the three faces the
preamble asks for is in the TeX tree; STIX Two and Menlo are macOS system fonts.  The archive
depends on the operating system and does not say so anywhere.

This does not fix the dependency -- see papers/apal_build/FONT_PORTABILITY_s35.md for why the
substitution that suggests itself fails, and for the three routes.  It makes the dependency ANNOUNCE itself:
the fonts the preamble actually asks for are read out of the preamble, probed one by one, and a
missing one is named in the first lines of the build rather than the middle of a TeX log.

Usage:  python3 tools/font_preflight.py <preamble.tex>
Exit 0 = every declared face resolves.  Exit 1 = at least one does not, and it is named.
"""
import os, re, subprocess, sys, tempfile

XELATEX = os.environ.get("XELATEX", "xelatex")

def declared(preamble):
    """Faces the preamble asks for, in declaration order, deduplicated."""
    src = open(preamble, encoding="utf-8").read()
    src = "\n".join(l for l in src.split("\n") if not l.lstrip().startswith("%"))
    out = []
    for m in re.finditer(r"\\set(main|sans|mono|math)font\{([^}]+)\}", src):
        kind, name = m.group(1), m.group(2).strip()
        if (kind, name) not in out:
            out.append((kind, name))
    # faces named inside the optional argument (BoldFont = ..., ItalicFont = ...)
    for m in re.finditer(r"(?:Bold|Italic|BoldItalic|Upright)Font\s*=\s*([^,\]\s]+)", src):
        name = m.group(1).strip()
        if ("face", name) not in out:
            out.append(("face", name))
    return out

def probe(name, kind):
    """Ask xelatex itself whether the face resolves; it is the only authority that matters."""
    cmd = r"\setmathfont" if kind == "math" else r"\setmainfont"
    doc = (r"\documentclass{article}\usepackage{fontspec}"
           + (r"\usepackage{unicode-math}" if kind == "math" else "")
           + cmd + "{" + name + "}" + r"\begin{document}x\end{document}" + "\n")
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "probe.tex")
        open(p, "w", encoding="utf-8").write(doc)
        try:
            r = subprocess.run([XELATEX, "-interaction=nonstopmode", "-halt-on-error", "probe.tex"],
                               cwd=d, capture_output=True, text=True, timeout=120)
        except (OSError, subprocess.TimeoutExpired) as e:
            return False, "xelatex could not be run: %s" % e
        if r.returncode == 0:
            return True, ""
        log = (r.stdout or "") + (r.stderr or "")
        m = re.search(r"(cannot be found|not found|Font .* does not exist)", log)
        return False, m.group(0) if m else "xelatex exit %d" % r.returncode

def main():
    preamble = sys.argv[1] if len(sys.argv) > 1 else "papers/apal_build/preamble.tex"
    if not os.path.isfile(preamble):
        print("FONT_PREFLIGHT=ERROR preamble not found: %s" % preamble); return 2
    faces = declared(preamble)
    print("FONT_PREFLIGHT_DECLARED=%d" % len(faces))
    bad = []
    for kind, name in faces:
        ok, why = probe(name, kind)
        print("  %-6s %-28s %s%s" % (kind, name, "OK" if ok else "MISSING", "" if ok else "  -- " + why))
        if not ok:
            bad.append(name)
    if bad:
        print("FONT_PREFLIGHT_MISSING=%s" % ", ".join(bad))
        print("FONT_PREFLIGHT=FAIL  install the faces above, or see papers/apal_build/FONT_PORTABILITY_s35.md")
        return 1
    print("FONT_PREFLIGHT=OK")
    return 0

if __name__ == "__main__":
    sys.exit(main())
