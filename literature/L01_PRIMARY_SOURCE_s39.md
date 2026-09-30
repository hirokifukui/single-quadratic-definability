# L01 — primary-source novelty audit of the seven claims (Gate-13 §16 / L01), session 39, 2026-09-06

Vocabulary as prescribed: PRIMARY BODY VERIFIED / ABSTRACT ONLY / METADATA ONLY / UNRESOLVED. This file adds to
`literature/NOVELTY_FINAL_GATE_s30.md` (rows) and `certificates/L04_*` (s31/s32) without editing them. What was
read today is stated; what could not be read is stated as such and not converted into a guess.

| # | claim | nearest work | status (s39) | evidence today |
|---|---|---|---|---|
| 1 | uniform finite-fibre height (one constant per equation, all parameter points) | Die03 (PLMS 86, DOI 10.1112/S0024611502013898); Cas55, Mas98, Fuk13 | **STATEMENT VERIFIED IN A PEER-REVIEWED SURVEY** (Fukshansky 2013, Contemp. Math. 587, Theorem 6.1, read in full from arXiv:1204.1938v1, 16 pages, 8,544 words); body of Die03 itself ABSTRACT ONLY (Wiley PDF: HTTP 403 today) | Theorem 6.1 there (attributed to Dietmann, N = 2 to Kornhauser): for Q = F + L + A with F nonsingular, IF Q has an integral zero THEN it has one with sup-norm ≪_N |Q|^{c(N)} (c(3) = 2100, c(4) = 84, polynomial for N ≥ 5; exponential for N = 2), the bound in the height |Q| of the coefficient vector. Our Theorem 2.1 bounds EVERY point of a FINITE fibre by C·N² with C depending on P alone and N on the parameter, uniformly over all parameter points; Dietmann bounds ONE zero of ONE equation in terms of its own coefficients and asserts nothing about finiteness or about the other zeros. Neither statement implies the other; the survey's Theorem 1.1 (Cassels) is the homogeneous version with the same shape. Cas55 is thereby also covered by the survey's statement; Mas98 remains CITATION CHAIN ONLY. |
| 2 | finite-fibre cardinality with the same constant | none identified | **UNRESOLVED** | zbMATH Open negative search (s31) stands; absence of a neighbour is not evidence. |
| 3 | definable-function quadratic growth | derived from 1 | DERIVED (inherits row 1) | — |
| 4 | injective dimension n ≤ 2m for one equation | none for the single-equation fragment | **UNRESOLVED** | as row 2. |
| 5 | polynomial graph classification by total degree | folklore one way | **METADATA ONLY** | no printed statement of the folklore direction located. |
| 6 | finite-or-structured theorem (bounded-or-structured summit) | GA26, arXiv:2607.06627v1 | **PRIMARY BODY VERIFIED** (s35; re-verified s39) | 2026-09-06: PDF fetched (13 pages, 222,538 bytes, `fetch_pdf/GA26_arxiv_2607.06627.pdf`), full text 7,424 words. Occurrences: "uniform" 0, "depending only" 0, "certificate" 0, "infinite subset" 0, "finite fibre/fiber" 0, "bounded by" 0, "every parameter/all parameters" 0, "Pell" 2. Its results are Propositions about specific equations (3.1, 4.1, 4.2, 4.4); its own introduction says the method "is not guaranteed to work for all polynomials". No parameter, no uniformity, no dichotomy. Neither result contains the other. |
| 7 | moving-modulus orbit construction | GA26 (Pell side) | **PRIMARY BODY VERIFIED** (s35; re-verified s39) | same reading; GA26 produces infinitude by a tangent construction over a fixed form, not a typed certificate over a parameter family. |

**What this closes and what it does not.** Rows 6 and 7 rest on the primary body. Rows 2 and 4 have no
neighbour and stay UNRESOLVED by construction. Row 1 now rests on the printed statement in a peer-reviewed survey (the body of Die03 itself is still
unread, 403); row 5 needs a citable statement of the folklore direction; those remaining reads are library reads, not reachable from this machine
(403 today), and are a ruling for Dr. Fukui — the manuscript's Section 10 and the cover letter claim novelty only
at the level this table supports. GS04's body (L03) is likewise unread; the manuscript states the input at
published-abstract level, as the reviewer's §16 asks.

## Citation chase (Gate-13 §16: parametric integral quadrics / finite-fold and single-fold Diophantine definitions / definable-function growth / small integral zeros / bounded-degree existential fragments), s39

Queries run against zbMATH Open on 2026-09-06 (structured syntax; a miss is "not found by this query", not absence):
- `ti:"finite-fold" & Diophantine` → 3: Matiyasevich 2010 *Towards finite-fold Diophantine representations* (J. Math. Sci., DOI 10.1007/s10958-010-0179-4); Cantone–Casagrande–Fabris–Omodeo 2021 *The quest for Diophantine finite-fold-ness*; Tyszka 2013. **Added [Mat10]** and a one-sentence distinction in §10: finite-fold bounds the *witness* multiplicity per parameter point; our finite fibres are on the *output* side with witnesses unrestricted.
- `ti:"single-fold" & Diophantine` → 1 (Tyszka 2015, a computability remark); not adjacent to a structural statement; not added.
- `au:Jones & ti:"Universal Diophantine equation"` → Jones 1982, JSL (DOI 10.2307/2273588). **Added [Jon82]** as the classical degree–unknowns trade-off (bounded-degree existential fragments).
- `au:Skolem & ti:"Diophantische Gleichungen" & py:1938` → Skolem 1938, Ergebnisse 5. **Added [Sko38]**: Theorem 6.2 and the Introduction attributed the degree reduction to Skolem without a reference.
- `ti:quadratic & ti:Diophantine & ti:definab*`, `ti:"existential" & ti:"degree" & (Diophantine|polynomial)` → miss; `ti:Diophantine & ti:degree & ti:unknowns` → Nagell 1954 (binary quadratics), already the [Nag] line.
- small integral zeros: the Cassels–Dietmann–Fukshansky family is row 1 above; nothing beyond it surfaced under these queries.
- definable-function growth: no hit on growth of Diophantine-definable total functions by degree; row 3 stays DERIVED.
References 13 → 16; every added entry's bibliographic identity is from zbMATH Open metadata (DOI where zbMATH gives one), no page numbers typed from memory except Jones (JSL 47, 549–571).
