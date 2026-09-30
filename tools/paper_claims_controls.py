#!/usr/bin/env python3
"""paper_claims_controls.py -- Gate 13 A06 (s39): planted negative controls for the paper-claim registry.

Each control copies <root> (certificates/, frozen_statements/, tools/) and the native directory to a fresh temp
tree, plants ONE defect there, runs the gate, and requires it to FAIL naming the mutated label.  Nothing live is
touched; the controls are planted by this script, never borrowed from a live defect.  Controls (the reviewer's
A06 list, plus the A02 cross-reference control):
  1 Proposition 1.2  SE_4 -> SE_5 in the statement            (paper-text mutation; claim_hash + must_not_contain)
  2 Theorem 2.1      Lean root -> wtCount_closed_form          (root substitution; lean_type_sha256)
  3 Definition 8.4   ∃C ∀a -> ∀a ∃C                             (quantifier swap; claim_hash + must_not_contain)
  4 Theorem 8.5      "or carries a structured certificate" -> "equals the infinite family"
  5 Theorem 2.1      witness domain Z -> N  (a ∈ ℤⁿ -> a ∈ ℕⁿ)  (claim_hash + must_contain order)
  6 Theorem 6.8      the external hypotheses deleted            (claim_hash + must_contain)
  7 Theorem 2.1      degree 2 -> 3                              (claim_hash + must_not_contain)
  8 Theorem 6.8      k = 0 collapse reference -> Proposition 1.3 (crossref_semantic_check)
  9 Theorem 2.1      lean_type_sha256 edited to the type of an unrelated root (manifest tampering; type table wins)
 10 Theorem 2.1      a declaration of the same short name in another namespace (suffix resolution must refuse ambiguity)
 11 Theorem 7.1      second root re-added beside the direct wrapper (ONE_ROOT)
 12 Theorem 6.8      direct row demoted to MATCH VIA (ONE_ROOT)
 13 Theorem 8.5      weak corollary row re-promoted to EXACT (Gate-16 P0-1, s42)
 14 Theorem 8.5      weak root listed before the strong root (Gate-16 P0-1, s42)
 15 Lemma A.3        conclusion -Δh² -> +Δh²                    (sign flip; claim_hash; GATE26 s56)
 16 Lemma A.3        conclusion -Δh² -> Δh² (minus deleted)     (sign deletion; needs the sign-aware norm; GATE26 s56)
Prints one line per control and NEGATIVE_CONTROLS_CAUGHT=<n>/<total>; exit 1 unless all are caught.
Usage: python3 tools/paper_claims_controls.py <root> [--native <dir>]
"""
import os, re, shutil, subprocess, sys, tempfile

def run(cmd, cwd):
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr

def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = os.path.abspath(args[0] if args else ".")
    native = os.path.join(root, "submission", "native")
    if "--native" in sys.argv: native = os.path.abspath(sys.argv[sys.argv.index("--native") + 1])
    tools = os.path.dirname(os.path.abspath(__file__))
    S = "sections/"
    def tex(f, old, new):
        def m(t):
            p = os.path.join(t, "native", S + f); s = open(p, encoding="utf-8").read()
            assert s.count(old) == 1, (f, old, s.count(old)); open(p, "w", encoding="utf-8").write(s.replace(old, new))
        return m
    def tsv(old, new):
        def m(t):
            p = os.path.join(t, "native", "PAPER_CLAIMS.tsv"); s = open(p, encoding="utf-8").read()
            assert s.count(old) == 1, (old, s.count(old)); open(p, "w", encoding="utf-8").write(s.replace(old, new))
        return m
    def swap_type(t):
        p = os.path.join(t, "native", "PAPER_CLAIMS.tsv"); rows = open(p, encoding="utf-8").read().split("\n")
        hdr = rows[0].split("\t"); i = hdr.index("lean_type_sha256")
        r21 = [k for k, r in enumerate(rows) if r.startswith("Theorem 2.1\t")][0]
        rc1 = [k for k, r in enumerate(rows) if r.startswith("Theorem C.1\t")][0]
        a = rows[r21].split("\t"); b = rows[rc1].split("\t"); a[i] = b[i].split("|")[-1]; rows[r21] = "\t".join(a)
        open(p, "w", encoding="utf-8").write("\n".join(rows))
    def ambiguous_ns(t):
        p = os.path.join(t, "certificates", "PAPER_CLAIM_LEAN_TYPES.tsv"); rows = open(p, encoding="utf-8").read().rstrip("\n").split("\n")
        src = [r for r in rows if r.split("\t")[0].endswith(".singleQuadratic_finiteFiber_height_vector")][0].split("\t")
        src[0] = "ControlNS.singleQuadratic_finiteFiber_height_vector"; rows.append("\t".join(src))
        open(p, "w", encoding="utf-8").write("\n".join(rows) + "\n")
    def second_root(t):
        # re-add apal_full_phase_diagram_classical beside the 7.1 root, with its correct type hash and a review row,
        # so that only the one-root rule can object
        p = os.path.join(t, "native", "PAPER_CLAIMS.tsv"); rows = open(p, encoding="utf-8").read().split("\n")
        hdr = rows[0].split("\t"); ir = hdr.index("Lean_root"); ih = hdr.index("lean_type_sha256")
        tt = {r.split("\t")[0]: r.split("\t")[4] for r in open(os.path.join(t, "certificates", "PAPER_CLAIM_LEAN_TYPES.tsv"), encoding="utf-8").read().rstrip("\n").split("\n")[1:]}
        k = [k for k, r in enumerate(rows) if r.startswith("Theorem 7.1\t")][0]; a = rows[k].split("\t")
        a[ir] += ", apal_full_phase_diagram_classical"; a[ih] += "|" + tt["DiophCompression.apal_full_phase_diagram_classical"]; rows[k] = "\t".join(a)
        open(p, "w", encoding="utf-8").write("\n".join(rows))
        q = os.path.join(t, "native", "PAPER_CLAIMS_REVIEW.tsv"); rv = open(q, encoding="utf-8").read().rstrip("\n").split("\n")
        h = rv[0].split("\t"); base = [r for r in rv if r.startswith("Theorem 7.1\t")][0].split("\t")
        base[h.index("Lean_root")] = "DiophCompression.apal_full_phase_diagram_classical"; base[h.index("type_sha256")] = tt["DiophCompression.apal_full_phase_diagram_classical"]
        base[h.index("disposition")] = "MATCH VIA 6.7 (planted control)"; rv.append("\t".join(base))
        open(q, "w", encoding="utf-8").write("\n".join(rv) + "\n")
    def via_row(t):
        q = os.path.join(t, "native", "PAPER_CLAIMS_REVIEW.tsv"); s = open(q, encoding="utf-8").read()
        old = "EXACT: the paper assumes UniformQuadraticSolvabilityOnCodes and DPRM_NN and the root assumes exactly these two"
        assert s.count(old) == 1; open(q, "w", encoding="utf-8").write(s.replace(old, "MATCH VIA 6.4: the paper assumes UniformQuadraticSolvabilityOnCodes and DPRM_NN and the root assumes exactly these two"))
    def weak_exact(t):
        q = os.path.join(t, "native", "PAPER_CLAIMS_REVIEW.tsv"); s = open(q, encoding="utf-8").read()
        old = "COROLLARY (per-fibre bounded-or-structured consequence of the first root"
        assert s.count(old) == 1; open(q, "w", encoding="utf-8").write(s.replace(old, "EXACT (per-fibre bounded-or-structured consequence of the first root"))
    def weak_first(t):
        p = os.path.join(t, "native", "PAPER_CLAIMS.tsv"); s = open(p, encoding="utf-8").read()
        old = "Theorem 8.5\tuniformQuadraticFiberStructureZZ_of_quadratic, singleQuadratic_fiber_bounded_or_structurallyInfinite\t"
        assert s.count(old) == 1
        s = s.replace(old, "Theorem 8.5\tsingleQuadratic_fiber_bounded_or_structurallyInfinite, uniformQuadraticFiberStructureZZ_of_quadratic\t")
        rows = s.rstrip("\n").split("\n"); hdr = rows[0].split("\t"); ih = hdr.index("lean_type_sha256")
        k = [k for k, r in enumerate(rows) if r.startswith("Theorem 8.5\t")][0]; a = rows[k].split("\t")
        a[ih] = "|".join(reversed(a[ih].split("|"))); rows[k] = "\t".join(a)
        open(p, "w", encoding="utf-8").write("\n".join(rows) + ("\n" if s.endswith("\n") else ""))
    controls = [
      ("C1 Proposition 1.2 SE_4->SE_5", tex("01_s1_fragments_se2_rec_re_pp2_se4.tex", "$SE_{4}(k) = PP_{2}(k) = \\mathrm{Dioph}(k)$", "$SE_{5}(k) = PP_{2}(k) = \\mathrm{Dioph}(k)$"), "claims", "Proposition 1.2"),
      ("C2 Theorem 2.1 root->wtCount_closed_form", tsv("Theorem 2.1\tsingleQuadratic_finiteFiber_height_vector\t", "Theorem 2.1\twtCount_closed_form\t"), "claims", "Theorem 2.1"),
      ("C3 Definition 8.4 ∃C∀a->∀a∃C", tex("08_s8_structured_infinite_fibres.tex", ":⟺ ∃ C ∈ ℕ, ∀ a ∈ ℤ^{n}, \\\\", ":⟺ ∀ a ∈ ℤ^{n}, ∃ C ∈ ℕ, \\\\"), "claims", "Definition 8.4"),
      ("C4 Theorem 8.5 structured->equals the family", tex("08_s8_structured_infinite_fibres.tex", "or carries a structured certificate of one of the three kinds", "or equals the infinite family of one of the three kinds"), "claims", "Theorem 8.5"),
      ("C5 Theorem 2.1 witness/parameter domain Z->N", tex("02_s2_finite_fibre_height_and_cardinality.tex", "all $a ∈ ℤ^{n}$ with $‖a‖_{∞} ≤ N$: if $\\mathrm{fiberVecZZ}", "all $a ∈ ℕ^{n}$ with $‖a‖_{∞} ≤ N$: if $\\mathrm{fiberVecZZ}"), "claims", "Theorem 2.1"),
      ("C6 Theorem 6.8 external hypotheses deleted", tex("06_s6_relation_phase_diagram.tex", "Assume $\\mathrm{UniformQuadraticSolvabilityOnCodes}$ and $\\mathrm{DPRM}_{NN}$. Then for every $k ≥ 1$:", "For every $k ≥ 1$:"), "claims", "Theorem 6.8"),
      ("C7 Theorem 2.1 degree 2->3", tex("02_s2_finite_fibre_height_and_cardinality.tex", "Let $P ∈ \\mathrm{Poly}\\ (n+m)\\ r$ with $\\mathrm{totalDegree}\\ P ≤ 2$.", "Let $P ∈ \\mathrm{Poly}\\ (n+m)\\ r$ with $\\mathrm{totalDegree}\\ P ≤ 3$."), "claims", "Theorem 2.1"),
      ("C8 Theorem 6.8 k=0 reference -> Proposition 1.3", tex("06_s6_relation_phase_diagram.tex", "The collapse at $k = 0$ is \\cref{proposition:1.4}.", "The collapse at $k = 0$ is \\cref{proposition:1.3}."), "crossref", "proposition:1.3"),
      ("C9 Theorem 2.1 lean_type_sha256 replaced by C.1's", swap_type, "claims", "Theorem 2.1"),
      ("C10 Theorem 2.1 root name duplicated in another namespace", ambiguous_ns, "claims", "Theorem 2.1"),
      ("C11 Theorem 7.1 second root re-added beside the direct wrapper", second_root, "claims", "Theorem 7.1"),
      ("C12 Theorem 6.8 direct row demoted to MATCH VIA", via_row, "claims", "Theorem 6.8"),
      ("C13 Theorem 8.5 weak corollary row re-promoted to EXACT", weak_exact, "claims", "Theorem 8.5"),
      ("C14 Theorem 8.5 weak root listed first", weak_first, "claims", "Theorem 8.5"),
      ("C15 Lemma 10.3 -Δh^2 -> +Δh^2", tex("10_s10_definable_functions.tex", "then $B^{2} - 4AC = -Δh^{2}$ for some rational $h$", "then $B^{2} - 4AC = +Δh^{2}$ for some rational $h$"), "claims", "Lemma 10.3"),
      ("C16 Lemma 10.3 minus deleted", tex("10_s10_definable_functions.tex", "then $B^{2} - 4AC = -Δh^{2}$ for some rational $h$", "then $B^{2} - 4AC = Δh^{2}$ for some rational $h$"), "claims", "Lemma 10.3"),
    ]
    caught = 0
    for name, mut, gate, label in controls:
        t = tempfile.mkdtemp(prefix="pcc_")
        for d in ("certificates", "frozen_statements"): shutil.copytree(os.path.join(root, d), os.path.join(t, d))
        shutil.copytree(native, os.path.join(t, "native"))
        mut(t)
        script = "paper_claims_check.py" if gate == "claims" else "crossref_semantic_check.py"
        rc, out = run([sys.executable, os.path.join(tools, script), t, "--native", os.path.join(t, "native")], t)
        ok = rc != 0 and any(("FAIL" in l and label in l) for l in out.split("\n"))
        caught += ok
        print("%s\t%s\texit=%d\t%s" % ("CAUGHT" if ok else "MISSED", name, rc, next((l for l in out.split("\n") if "FAIL" in l and label in l), "")[:110]))
        shutil.rmtree(t)
    print("NEGATIVE_CONTROLS_CAUGHT=%d/%d" % (caught, len(controls)))
    print("NEGATIVE_CONTROLS_EXIT=%d" % (0 if caught == len(controls) else 1))
    sys.exit(0 if caught == len(controls) else 1)

if __name__ == "__main__":
    main()
