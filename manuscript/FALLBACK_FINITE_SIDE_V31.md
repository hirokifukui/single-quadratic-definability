# Finite-side fallback of v3.1 (kept in parallel, per the pre-submission checklist)

**What this is.** A record of which parts of the submission manuscript survive if the structured summit
(Theorem 8.5) ever has to be withdrawn — for instance if a referee finds an error in the projection
dichotomy of Section 9, on which 8.5 rests.

**The fallback paper is Sections 1–7 and 10–11 verbatim, plus Section 9 in its bounded form only
(Theorem 9.2), plus Appendices B–E.** Nothing in Sections 1–7 uses Section 8. Concretely:

- Theorem 2.1 uses Theorem 9.2 (the *bounded* dichotomy), not 9.3 (the data-carrying one) and not 8.5.
- Theorems 2.2, 3.2–3.5, 4.1, 4.2, 5.1 depend only on 2.1.
- Sections 6 and 7 depend on 2.1 (through 3.2 and 3.5) and on the classical inputs; no arrow of either
  phase diagram passes through Section 8.
- Appendix C (the universal-pair obstruction) is independent of everything else.

**What would be lost.** Section 8 in its entirety, Theorem 9.3, contribution items (7), (8) and (9)'s
second half of Section 10, and the third and fourth clauses of the Abstract. The Abstract of the
fallback stops after the internal constraints and the phase diagrams.

**What would NOT be lost.** The finite-fibre theory, the definable-function theory, the graph
classification, the dimension bound, both phase diagrams, the diagonalization lemma, and the whole of
Section 11. That is the paper's floor, and it is unconditional except where the classical inputs are
named as hypotheses.

**Why this is recorded rather than written out.** Duplicating 7,000 words to delete two sections would
create a second document to keep in sync, which is a worse risk than the one it guards against. The
dependency claims above are checkable against the formalization: no declaration used in Sections 1–7
imports `SummitClosure.lean`, and `FiniteFiberGrowth.lean` imports only the bounded dichotomy.
