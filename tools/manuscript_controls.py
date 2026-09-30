#!/usr/bin/env python3
"""manuscript_controls.py -- the reviewer's twelve manuscript red-team plants (s40, Gate-14 §18), plus the
Pell-subscript scanner (Gate-14 P01).

Two modes.
  --scan <root> [--native <dir>]   the gate: scans the shipped native TeX (and the PDF text when pdftotext is
                                   present) for the split subscript that shipped in the §8 proof
                                   (p_{xX ... / p_{yY ... / p_xX_k / p_yY_k).  BAD_SUBSCRIPT_OCCURRENCES=0 passes.
  <root> [--native <dir>]          the controls: each plant is applied to a temp copy of the native tree and
                                   must be caught, by --scan (plant 1) or by tools/paper_claims_check.py (plants
                                   2-12: claim_hash, must_contain / must_not_contain, external-hypothesis rows).
Honest scope: these are TEXT checks.  A plant is caught because a registered statement changed, or because a
must_contain / must_not_contain phrase fired; the semantic reading of a statement against its Lean type is the
Layer-2 review, not this tool.
"""
import os, re, shutil, subprocess, sys, tempfile, glob
BAD = [r"p_\{xX", r"p_\{yY", r"p_xX_k", r"p_yY_k", r"p_\{x X\}_k"]

def scan(root, native, shipped=False):
    """shipped=False: the native source only (safe before the build, when submission/ still holds the previous
    round's typeset files); shipped=True: also the flattened TeX and the PDF text, i.e. after the build."""
    hits = []
    files = sorted(glob.glob(os.path.join(native, "sections", "*.tex")))
    if shipped: files.append(os.path.join(root, "submission", "APAL_MANUSCRIPT_v32.tex"))
    for f in files:
        if not os.path.exists(f): continue
        s = open(f, encoding="utf-8", errors="replace").read()
        for b in BAD:
            for m in re.finditer(b, s): hits.append((os.path.relpath(f, root), m.group(0)))
    pdf = os.path.join(root, "submission", "APAL_MANUSCRIPT_v32.pdf")
    if shipped and os.path.exists(pdf) and shutil.which("pdftotext"):
        t = subprocess.run(["pdftotext", pdf, "-"], capture_output=True, text=True).stdout
        for b in (r"p_?\{?xX", r"p_?\{?yY", r"pxXk", r"pyYk"):
            for m in re.finditer(b, t): hits.append(("submission/APAL_MANUSCRIPT_v32.pdf", m.group(0)))
    print(f"BAD_SUBSCRIPT_OCCURRENCES={len(hits)}" + (f" {hits[:5]}" if hits else ""))
    # Gate 15 (s41, F10/F11): two typesetting defects the reviewer read off the r36 PDF.  Inline math is
    # tokenised per line on unescaped $; the odd segments are math.  (a) a \cref inside a math segment
    # (it typesets the reference in math italics); (b) the word "definable" inside a math segment (the
    # malformed "$ℤ^{n} → ℤ SE_{2}-definable$" of the Corollary 4.2 proof).  Display math \[ ... \] is
    # checked for \cref as well.
    cref_in = []; defin = []
    for f in sorted(glob.glob(os.path.join(native, "sections", "*.tex"))):
        s = open(f, encoding="utf-8", errors="replace").read(); rel = os.path.relpath(f, root)
        for m in re.finditer(r"\\\[(.*?)\\\]", s, re.S):
            if "\\cref" in m.group(1): cref_in.append((rel, "display", m.group(1)[:60]))
        for ln, line in enumerate(s.split("\n"), 1):
            segs = re.split(r"(?<!\\)\$", line)
            for k in range(1, len(segs), 2):
                if "\\cref" in segs[k]: cref_in.append((rel, ln, segs[k][:60]))
                if "definable" in segs[k]: defin.append((rel, ln, segs[k][:60]))
    print(f"CREF_INSIDE_MATH={len(cref_in)}" + (f" {cref_in[:5]}" if cref_in else ""))
    print(f"MALFORMED_SE2_DEFINABLE_PHRASE={len(defin)}" + (f" {defin[:5]}" if defin else ""))
    return len(hits) + len(cref_in) + len(defin)

def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = os.path.abspath(args[0] if args else ".")
    native = os.path.join(root, "submission", "native")
    if "--native" in sys.argv: native = os.path.abspath(sys.argv[sys.argv.index("--native") + 1])
    if "--scan" in sys.argv:
        n = scan(root, native, shipped="--shipped" in sys.argv); print("MANUSCRIPT_SCAN_EXIT=%d" % (1 if n else 0)); sys.exit(1 if n else 0)
    tools = os.path.dirname(os.path.abspath(__file__))
    def tex(f, old, new):
        def m(t):
            p = os.path.join(t, "native", "sections", f); s = open(p, encoding="utf-8").read()
            assert s.count(old) == 1, (f, old, s.count(old)); open(p, "w", encoding="utf-8").write(s.replace(old, new))
        return m
    controls = [
      ("M01 Pell subscript p_x X_k -> p_{xX_k}", tex("08_s8_structured_infinite_fibres.tex", "$\\mathrm{denom}·output_{k} = p_{c} + p_{x} X_{k} + p_{y} Y_{k}$", "$\\mathrm{denom}·output_{k} = p_{c} + p_{xX_k} + p_{yY_k}$"), "scan", ""),
      ("M02 Theorem 3.3 computability derived from growth", tex("03_s3_definable_total_functions.tex", "are computable (witness search on the graph, then read off the unique output)", "are computable (they follow from the quadratic growth bound)"), "claims", "Theorem 3.3"),
      ("M03 Theorem 8.3 certificate called effective", tex("08_s8_structured_infinite_fibres.tex", "Every structured certificate yields a generic certificate and hence proves the fibre infinite", "Every structured certificate yields an effective certificate and hence proves the fibre infinite"), "claims", "Theorem 8.3"),
      ("M04 Theorem 8.5 whole fibre decomposed", tex("08_s8_structured_infinite_fibres.tex", "or carries a structured certificate of one of the three kinds", "or is the whole fibre decomposed into one of the three kinds"), "claims", "Theorem 8.5"),
      ("M05 Theorem 8.3 three kinds called canonical", tex("08_s8_structured_infinite_fibres.tex", "Every structured certificate yields a generic certificate", "Every canonical certificate yields a generic certificate"), "claims", "Theorem 8.3"),
      ("M06 Corollary 4.4 threshold weakened to n >= 3 (s50: re-pointed, the old anchor was deleted when section 4 was rewritten)", tex("04_s4_injective_dimension_theorem.tex", "for $n ≥ 2$", "for $n ≥ 3$"), "claims", "Corollary 4.4"),
      ("M07 Corollary 6.6 GS global uniformity overclaimed", tex("06_s6_relation_phase_diagram.tex", "Then $\\mathrm{SE}_{2}(k) ⊊ \\mathrm{REC}(k)$ for every $k ≥ 1$, in particular at arity one", "Then, by a single algorithm uniform in k, $\\mathrm{SE}_{2}(k) ⊊ \\mathrm{REC}(k)$ for every $k ≥ 1$, in particular at arity one"), "claims", "Corollary 6.6"),
      ("M08 Theorem 6.8 DPRM dependence deleted", tex("06_s6_relation_phase_diagram.tex", "Assume $\\mathrm{UniformQuadraticSolvabilityOnCodes}$ and $\\mathrm{DPRM}_{NN}$. Then for every $k ≥ 1$:", "Assume $\\mathrm{UniformQuadraticSolvabilityOnCodes}$. Then for every $k ≥ 1$:"), "claims", "Theorem 6.8"),
      ("M09 Theorem 4.1 injectivity swapped for functionality", tex("04_s4_injective_dimension_theorem.tex", "and injective then $n ≤ m$", "and total then $n ≤ m$"), "claims", "Theorem 4.1"),
      ("M10 Definition 8.4 ∃C∀a -> ∀a∃C", tex("08_s8_structured_infinite_fibres.tex", ":⟺ ∃ C ∈ ℕ, ∀ a ∈ ℤ^{n}, \\\\", ":⟺ ∀ a ∈ ℤ^{n}, ∃ C ∈ ℕ, \\\\"), "claims", "Definition 8.4"),
      ("M11 Theorem 2.1 degree 2 -> 3", tex("02_s2_finite_fibre_height_and_cardinality.tex", "Let $P ∈ \\mathrm{Poly}\\ (n+m)\\ r$ with $\\mathrm{totalDegree}\\ P ≤ 2$.", "Let $P ∈ \\mathrm{Poly}\\ (n+m)\\ r$ with $\\mathrm{totalDegree}\\ P ≤ 3$."), "claims", "Theorem 2.1"),
      ("M13 \\cref moved inside inline math in §11", tex("10_s11_relation_to_the_literature.tex", "theorem $n ≤ m$, its converse", "theorem $n ≤ m (\\cref{theorem:4.1})$, its converse"), "scan", ""),
      ("M14 Theorem 4.1 statement: definable pulled into math (s50: re-pointed)", tex("04_s4_injective_dimension_theorem.tex", "is $\\mathrm{SE}_{2}$-definable and injective", "is $SE_{2}-definable$ and injective"), "scan", ""),
      ("M12 Theorem 6.3 SE_2 ⊆ REC made unconditional", tex("06_s6_relation_phase_diagram.tex", "Assume $\\mathrm{QuadraticSolvabilityDecidableZZ}$. Then $\\mathrm{SE}_{2}(k) ⊆ \\mathrm{REC}(k)$ for all $k$", "Unconditionally, $\\mathrm{SE}_{2}(k) ⊆ \\mathrm{REC}(k)$ for all $k$"), "claims", "Theorem 6.3"),
    ]
    caught = 0
    for name, mut, gate, label in controls:
        t = tempfile.mkdtemp(prefix="msc_")
        for d in ("certificates", "frozen_statements"): shutil.copytree(os.path.join(root, d), os.path.join(t, d))
        shutil.copytree(native, os.path.join(t, "native"))
        mut(t)
        if gate == "scan":
            n = scan(t, os.path.join(t, "native")); ok = n > 0; line = f"SCAN_HITS={n}"
        else:
            p = subprocess.run([sys.executable, os.path.join(tools, "paper_claims_check.py"), t, "--native", os.path.join(t, "native")], capture_output=True, text=True, env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
            out = p.stdout + p.stderr
            ok = p.returncode != 0 and any(("FAIL" in l and label in l) for l in out.split("\n"))
            line = next((l for l in out.split("\n") if "FAIL" in l and label in l), "")[:110]
        caught += ok
        print("%s\t%s\t%s" % ("CAUGHT" if ok else "MISSED", name, line))
        shutil.rmtree(t)
    print("MANUSCRIPT_CONTROLS_CAUGHT=%d/%d" % (caught, len(controls)))
    print("MANUSCRIPT_CONTROLS_EXIT=%d" % (0 if caught == len(controls) else 1))
    sys.exit(0 if caught == len(controls) else 1)

if __name__ == "__main__":
    main()
