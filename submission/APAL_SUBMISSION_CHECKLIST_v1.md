# APAL submission checklist

Current state of the submission (native LaTeX source in `submission/native/`, Introduction present).
Counts below come from the FIGURES block, recomputed by `tools/submission_figures.py` at every build;
a count stated elsewhere in this file that contradicts the block fails the build. The numbered-statement
count is owned by `tools/proof_by_citation_scan.py`; the paper-claim registry has one row per numbered
theorem, proposition and corollary that names a Lean declaration, and per lemma whose heading names one
(`submission/native/PAPER_CLAIMS.tsv`),
and Appendix E prints those rows. The development history of this file is in
`history/DEVELOPMENT_AUDIT_HISTORY.md`.

## Journal requirements (Annals of Pure and Applied Logic, Elsevier)

| requirement | current state |
|---|---|
| abstract ≤ 250 words | see FIGURES (whitespace count; the Gate-13 target was 220–230; the r40 section 4 additions bring it to 240, inside the 250 limit) |
| keywords ≤ 7 | 6 |
| MSC 2020 | present: 03D25 primary; 11D09, 11U05, 03B35, 11Y50, 68V15 secondary |
| title on one line | "Structure and computability of the single-quadratic existential fragment over the integers", 90 characters |
| AI declaration before references | present (Declaration on AI-assisted tools) |
| AI use described at methods level | present (Methods section) |
| line numbers in the PDF | present, every line (lineno, modulo 1) |
| data / artifact availability with DOI | DOI to be reserved before the final build |
| complete references, all citations resolved | see FIGURES (27 entries: the Gate-13 chase, the r40 additions, the three r44 additions for Lemma 10.4, the r46 addition KK26 for Proposition 10.7 and the r49 addition Clu03 for Section 11); 0 cited-but-unlisted |

## Figures

```
FIGURES (recomputed by tools/submission_figures.py; do not edit by hand)
pages=70
abstract_words=250
keywords=6
references=27
```

## Content gates cleared before submission

- [x] No unproved sharpness claim anywhere in the shipping documents.  The sharpness now claimed
      (an injective SE₂-definable ℤⁿ → ℤᵐ exists iff n ≤ m) is proved in both directions.
- [x] Attribution of the n = 2, m = 1, witness-free polynomial case to Lew–Rosenberg, of the
      nonzero-discriminant cone version to Gjaldbæk, and of the square-values lemma to
      Davenport–Lewis–Schinzel 1964, all with the primary sources read.
- [x] The coding arity at n = 2, left open in the previous version, is now SETTLED (ca(SE₂) = 1);
      Appendix A.1 and Appendix B say so and record that it was previously open.  No document
      still calls it open.
- [x] One-sorted and mixed semantics distinguished in a table.
- [x] Computability attributed to totality plus a Diophantine graph for functions, and to the
      quadratic decider for relations.
- [x] Certificate forms described as produced by the proof.
- [x] `BranchExhaustion` described as a documentation layer.
- [x] Grunewald–Segal bridge described as an effective coding-equivalent consequence.
- [x] Conditional appendix removed from the submission.
- [x] The projection theorem proved in full, in the paper, not delegated.
- [x] Trust boundary, build README and release checklist written for this round.

## Still to do before the button is pressed

- [x] LaTeX build: `papers/apal_build/build.sh`, xelatex + pandoc, 0 missing glyphs, 0 errors.
- [x] Page count, abstract word count, keyword count and reference count are generated from the
      build artifact (FIGURES block), not typed here.
- [ ] Reserve the artifact DOI and insert it into the manuscript and the citation file.
- [x] Neighbour confirmation pass run with zbMATH Open and publisher records (MathSciNet is behind a subscription); bibliographic identity and abstracts confirmed, reviews and bodies not read.
- [x] GS crosswalk closed from the published abstracts and a third party's printed statement; the level of evidence is recorded row by row in `literature/GS_CROSSWALK.md`.
- [ ] Blank-slate review of the finished PDF, four roles.
- [ ] Final clean-room build and package freeze after the last source edit.
- [ ] Competing interests: generate the declaration with Elsevier's declarations tool and upload the resulting .docx
      with the submission (Guide for Authors of Annals of Pure and Applied Logic, read 2026-09-28); the manuscript
      carries the matching sentence on its title page.
- [ ] Upload the editable source (`submission/APAL_MANUSCRIPT_v32.tex` and what it inputs), not the PDF alone: the
      Guide asks for editable source files at first submission.
