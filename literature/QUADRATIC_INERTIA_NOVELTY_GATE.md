# QUADRATIC_INERTIA_NOVELTY_GATE — external novelty search log (s12, GPT r11 mandatory G)

Status: **first-pass search done (zbMATH Open, 2026-08-28); novelty NOT yet
externally established.** Discipline: a miss is recorded as "not found under
query Q", never as "absent from the literature". Reviews are secondary
literature; verbatim audits go to the original papers.

## Primary sources located (homework group 7 anchors — decidability of quadratic solvability)

| ref | zbMATH | relevance |
|---|---|---|
| Grunewald–Segal, *How to solve a quadratic equation in integers*, Math. Proc. Camb. Philos. Soc. (1981), MSC 11D09/03B25/11U05, DOI 10.1017/S030500410005787X | 3737745 | decidability algorithm, arbitrary integral quadratics — candidate input to U_ℤ(r,2)=0 [UNVERIFIED until verbatim audit: does it cover affine quadratics in any number of variables, uniformly in coefficients?] |
| Grunewald–Segal, *On the integer solutions of quadratic equations*, J. Reine Angew. Math. (2004), MSC 11D72/11E12/11U05, DOI 10.1515/crll.2004.023 | 2092068 | later, stronger treatment; same audit questions |
| Siegel, *Zur Theorie der quadratischen Formen*, Nachr. Akad. Wiss. Gött. (1972), MSC 11E16/11H55/11C20 | 3397605 | classical decidability source for quadratic representability |
| Matiyasevich–Robinson, *Reduction of an arbitrary diophantine equation to one in 13 unknowns*, Acta Arith. (1975), MSC 11D41/03D80/11U05 | 3438960 | classical degree/unknowns trade-off (degree ≥ 4 side); related-work section |

## Search axes attempted (zbMATH structured syntax; misses are per-query only)

1. `ti:"quadratic" & ti:"Diophantine" & any:"projection" & any:"parametric"` — miss.
2. `any:"Diophantine" & any:"graph" & any:"existential" & any:"quadratic" & any:"capacity"` — miss.
3. `any:"quadratic Diophantine" & any:"decidable" & any:"algorithm"` — 1 irrelevant hit (hyperbolic links).
4. `au:"Grunewald" & au:"Segal" & any:"quadratic"` — 2 primary hits (above).
5. `au:"Siegel" & ti:"quadratischen" & py:1972` — 1 primary hit (above).
6. `any:"Diophantine representation" & any:"degree" & any:"number of variables" & any:"trade-off"` — miss.
7. `au:"Matiyasevich" & any:"reduction" & any:"unknowns"` — 1 primary hit (above).
8. `any:"injective polynomial" & any:"pairing" & any:"integers" & any:"two variables"` — miss. (Fueter–Pólya-adjacent axis; retry with named-theorem queries next pass.)
9. `any:"quadratic form" & any:"linear progression" & any:"represented values" & any:"infinitely many"` — miss.

## Second pass (s13, 2026-08-28; GPT r12 eight named axes)

10. `any:"quadratic Diophantine" & any:"linear modulus" & any:"divisibility"` — miss.
11. `any:"existential rank" & any:"Diophantine" & any:"bounded degree"` — miss.
12. `any:"projection" & any:"integer points" & any:"finite or infinite" & any:"quadric"` — miss.
13. `any:"polynomial injection" & any:"graph" & any:"Diophantine representation"` — miss.
14. `any:"Fueter-Polya" & any:"quadratic" & any:"pairing"` — **1 hit**:
    Vsemirnov, *Two elementary proofs of the Fueter–Pólya theorem on pairing
    polynomials*, St. Petersbg. Math. J. (2002), Zbl 1821768, MSC 11C08/11D79/05A15.
    Triage: Fueter–Pólya = uniqueness of the two Cantor quadratics among
    BIJECTIVE ℕ²→ℕ quadratic pairings. Our lower bound uses INJECTIVITY only
    and no bijectivity claim; no capacity/witness content. Non-competing;
    related-work citation for the quadratic-pairing lower bound. [L, not yet
    read — verbatim read before citing.]
15. `any:"saturated submodule" & any:"quadratic form" & any:"congruence"` — miss
    (the SNF-free decomposition line: still "not found under query", so the
    positioning stays "structural lemma, no novelty claim" per r12 ruling).
16. `any:"uniformly bounded" & any:"or infinite" & any:"integer solutions" & any:"quadratic"` — miss.
17. `any:"number of unknowns" & any:"degree" & any:"universal" & any:"Diophantine" & any:"pairs"` — miss.

Second-pass verdict: the eight GPT axes are now each covered by at least one
structured query; no competing result surfaced; one adjacent citation gained
(Vsemirnov 2002). Discipline unchanged: every miss is per-query, not an
absence claim. Remaining before any "first" wording: MathSciNet pass
(institutional, Dr. Fukui), verbatim reads of Vsemirnov/Pasten/EMSW23/
Nathanson/Lew–Rosenberg, and the author 1-pagers to BDHMS and DDF.

## 群6 completion tally (s13b)

Items 1–10 (query axes): covered across s12 (9 queries) + s13 (8 axes) +
s13b (2 more: German compound, arithmetic-orbit phrasing) — all miss.
Item 11 German: `any:"quadratische diophantische Gleichung" & any:"Parameter"` — miss.
Item 12 French: `any:"équation diophantienne quadratique" & any:"projection"` — miss.
Item 13 Russian citation chains: partial — Vsemirnov (Russian school) surfaced
via item 14-axis; systematic chain drilling folded into the MathSciNet pass.
Items 14/15/16 (MathSciNet, citing-Lagarias, citing-DDF): Dr. Fukui-gated
(institutional access).
Item 17 Grechuk–Agbanwa full paper: DONE s13 (read in full, non-competing).
Item 18 related Lean formalizations: recorded — GA26 (Lean-verified
infinitude line), AFP DPRM (Isabelle→ crosswalk), mathlib Dioph namespace;
none contain capacity content.
Item 19 exact-phrase engine search: DONE s13b — hits are homonyms only
(coding-theory "graph capacity", spectral-graph "inertia", quantum "witness
capacity"); no competing mathematics; feeds the paper's naming section.
Item 20 author inquiry responses: Dr. Fukui-gated (1-pagers to BDHMS and
DDF; drafts on the r12 follow-up list).

Score: 16/20 executable-now items done; 4 gated on institutional access or
correspondence, all marked. Red condition (no "first" wording) unchanged
until those close.

## Remaining (r12 follow-up)

- GPT's eight named axes not yet exhausted (moving linear modulus; bounded-degree
  existential rank; finite-or-uniformly-bounded projection dichotomy phrasing
  variants; polynomial injection graphs). Retry with synonym sets; add MathSciNet
  via institutional access (Dr. Fukui) if needed.
- SNF-free congruence decomposition: search "saturated submodule complement
  congruence quadratic form" line before any positioning stronger than
  "structural lemma".
- CLAIM_BY_CLAIM_CROSSWALK.md: skeleton below; fill after verbatim audits.
- 1-page summaries to BDHMS and DDF authors: drafted after novelty first pass
  completes (r12).
