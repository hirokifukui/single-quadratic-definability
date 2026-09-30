# QUADRATIC_DECIDABILITY_AUDIT — homework group 1 / r13 mandatory A (s13, 2026-08-28)

Status: **[V-fulltext] — CLOSED 2026-08-28 (s13, same day)**. GS04 full text
purchased by Dr. Fukui and audited verbatim; every promotion criterion of §6
is discharged. The natural-language statement of U=0 may now cite [GS04]
UNCONDITIONALLY. The Lean layer stays hypothesis-form by design (mathlib
absence, not literature uncertainty).

## 1. Sources and access status

| src | full ref | DOI / access | status |
|---|---|---|---|
| GS81 | Grunewald–Segal, *How to solve a quadratic equation in integers*, Math. Proc. Camb. Philos. Soc. 89(1) (1981) 1–5 | 10.1017/S030500410005787X — Cambridge paywalled (fetch 2026-08-28: /abs/ redirect) | abstract+extract+references secured verbatim from publisher page |
| GS04 | Grunewald–Segal, *On the integer solutions of quadratic equations*, J. Reine Angew. Math. 569 (2004) 13–45 | 10.1515/crll.2004.023 — De Gruyter bot-blocked (HTTP 202) | abstract secured verbatim (RG mirror of publisher abstract) |
| Sie72 | Siegel, *Zur Theorie der quadratischen Formen*, Nachr. Akad. Wiss. Gött. Math.-Phys. Kl. II (1972) 21–46 | DigiZeitschriften e.V. (per Semantic Scholar [PDF] flag) | located, not yet fetched |
| Bri79 | Britton, *Integer solutions of systems of quadratic equations*, Math. Proc. Camb. Philos. Soc. 86 (1979) 385–389 | Cambridge paywalled | reference secured (GS81 ref (2)); GS81 answers Britton's question |
| GA26 | Grechuk–Agbanwa, *On the polynomial values represented by quadratic forms*, arXiv:2607.06627 (2026-07-07) | **open — full PDF on disk** `fetch_pdf/grechuk_agbanwa_2607.06627.pdf` | full text read s13 |

## 2. Verbatim scope anchors (shortest sufficient quotes, attributed)

- GS81 (publisher extract, opening sentence): the paper sketches "an effective
  procedure to decide whether an arbitrary quadratic equation" (displayed
  formula elided on publisher page) "with rational coefficients, has a solution
  in integers"; it adds the extension to orders in number fields. [V]
- GS04 (publisher abstract): "an algorithm that decides whether an arbitrary
  quadratic equation with rational coefficients (in arbitrarily many unknowns)
  has a solution in positive integers"; the algorithm "is in fact more
  general": integral solutions "restricted to lie in the region bounded by an
  arbitrary finite collection of rational affine hyperplanes"; if finite, it
  lists them. [V]
- Secondary usage (GA26 §1, on disk): the degree-≤2 case of F(y,z)=P(x) —
  an INHOMOGENEOUS three-variable quadratic — "covered by the general
  algorithm of Grunewald and Segal" [14 = GS04]. [V, triangulation]
- Secondary usage (RG citing text): GS04 gives a "decision procedure ... for
  quadrics Q(x_1,...,x_{n+1}) = 0 ... subject to finitely many specified
  congruences and linear inequalities". [V, triangulation]

## 3. Homework group 1, items 1–5 (audit questions), per-item verdict

1. **対象変数数** — GS04 abstract verbatim: "arbitrarily many unknowns". **[V]**
2. **affine (inhomogeneous) を含むか** — "equation" (not "form") in both titles
   and abstracts; GS04's hyperplane-region generality; GA26 applies GS04 to an
   inhomogeneous 3-variable quadratic. **[V-triangulated; full-text confirm of
   GS81 displayed formula pending]**
3. **integer vs positive integer** — GS81: integers [V]. GS04: positive
   integers AND arbitrary hyperplane-bounded regions, hence both ℤ- and
   ℕ-solution versions [V]. This is why both `QuadraticSolvabilityDecidableZ`
   and `...N` are licensed.
4. **effectivity（係数からの入力）** — "effective procedure" (GS81), "algorithm"
   (GS04), both verbatim. **[V]**
5. **parameter 代入後も algorithm input** — own derivation: substituting a ∈ ℕ^n
   into an integer polynomial of total degree ≤ 2 yields an integer quadratic
   in the unknowns (constants cannot raise degree); its coefficients are
   explicit integers, hence valid algorithm input. **[P-hand]**

## 4. Items 6–13 — discharged in Lean (s13)

File `DiophCompression/QuadraticUniversalityConditional.lean` (md5 873876cd,
production; frozen statements drafts/..._STATEMENTS.lean md5 7ec7ea1f,
diff 11/11, planted negative controls 2/2):

- (6) fixed polynomial → membership decider: `withinZ_degree_two_is_decidable`.
- (7,8) nonrecursive Diophantine set: `HardDiophantineSetExists` hypothesis
  (DPRM + halting; machine-verified in Isabelle AFP `DPRM_Theorem`, not in
  mathlib pin d46bd45 → hypothesis, never a bare axiom).
- (9) 一様表現選択の不要性: encoded structurally — `QuadraticSolvabilityDecidableZ`
  is the PER-POLYNOMIAL (non-uniform) form; the proof consumes only the single
  hard set's fixed representing polynomial.
- (10) `not_universalAchievableZ_one_degree_two` [P std-3, conditional].
- (11) arity-0 achievability + `universalCapacityZ_spec` (existing [P]).
- (12) `universalCapacityZ_degree_two_eq_zero` [P std-3, conditional].
- (13) ℕ-witness version: YES — same argument; GS04's positive-integer /
  region algorithm licenses `QuadraticSolvabilityDecidableN`;
  `universalCapacityN_degree_two_eq_zero` [P std-3, conditional].

All 6 theorems: `#print axioms` = [propext, Classical.choice, Quot.sound],
EXIT=0, forbidden-token grep CLEAN (2026-08-28, agora, lake env lean).

## 5. Item 14 — systems of quadratic equations

Decidability **collapses for systems**: Skolem degree reduction (classical,
1938) rewrites any polynomial equation as a SYSTEM of quadratics by
introducing product variables (y_{ij} = x_i x_j etc.), so solvability of
quadratic systems over ℤ is equivalent to Hilbert's 10th problem —
undecidable (Matiyasevich 1970). Hence the single-equation restriction is not
an artifact but exactly the decidability boundary; Britton (1979) studied the
systems side and posed the single-equation question GS81 answered. Referee
objection 8-3 ("one-equation restriction artificial?") is answered by this
dichotomy. [V-standard; Skolem original-text citation to be added at
manuscript stage]

## 6. Promotion criteria (before the paper states U=0 UNCONDITIONALLY)

**ALL CLOSED (2026-08-28, GS04 full text on disk:
`upstream/gs04/grunewald_segal_2004_crelle569.pdf`, md5 18169af7, 33 pp).**

Verbatim findings (page refs to the Crelle print, 13–45):

- **Displayed equation (1), p. 14**: f(X_1,...,X_n) = Σ_{i,j} a_ij X_i X_j
  + Σ_j b_j X_j + c = 0, coefficients a_ij, b_j, c rational — INHOMOGENEOUS
  affine quadratic, any n. Criterion (affine + arbitrarily many unknowns): [V].
- **Theorem 0.1, pp. 15–16 (verbatim)**: "There is a (uniform) algorithm ...
  Given a quadratic equation (1), let S denote the set of all solutions y of
  (1) in Z^n that satisfy a given congruence (4) and a given set of
  inequalities (5). (a) The algorithm decides whether the set S is finite or
  infinite; (b) if the set S is finite, it lists the elements of S." Plus the
  note that the algorithm "decides the solvability subject to (4) and (5)".
  → ℤ-solvability: trivial congruence, k = 0 inequalities. ℕ-solvability:
  positive-quadrant region, stated in §0.1 as the special case that motivated
  the paper. Both criteria: [V].
- **Uniformity**: "(uniform)" is in the theorem statement — STRICTLY STRONGER
  than the per-polynomial hypothesis `QuadraticSolvabilityDecidableZ/N`
  (the Lean hypothesis is weaker than the cited theorem; correct direction).
- **Degree-doubling remark, p. 14 (verbatim import)**: ℕ-solvability of P = 0
  reduces via Lagrange to ℤ-solvability of a P* of TWICE the degree — the
  authors state this is why the ℕ/ℤ distinction "can no longer be ignored
  when we are considering equations of given degree". This verbatim-confirms
  the s13 licensing split: `...N` needs GS04's positive-integer theorem;
  GS81 + Lagrange would NOT suffice at fixed degree 2.
- **Siegel 1972 [11]**: confirmed inside GS04 §0.1 as "an effective procedure
  for deciding whether (1) has a solution in integers" — antecedent confirmed
  at secondhand-verbatim; DigiZeitschriften fetch now OPTIONAL.
- **GS81 [6]**: confirmed inside GS04 §0.1 as "a simpler procedure ...
  elaborated in §2 below" for the ℤ case — GS81 purchase now UNNECESSARY
  (its content is subsumed and restated in GS04 §2).
- **Context finds**: question originated with Harvey Friedman (Peano
  incompleteness); degree-4-in-110-unknowns undecidability cited as the
  contrast; degree 3 stated open; quotable verdict "the corresponding
  problem in degree 2 is decidable" (p. 14).

## 7. GA26 novelty triage (read in full, s13)

GA26 asks: fixed binary quadratic form F, univariate P — is P(x) ∈ F(ℤ²)
infinitely often (Grechuk length-ordered Problem 1.1 program). Tangent-line
construction → Pell-type auxiliary equation; headline: x⁶−4 ∈ S₂ infinitely
often, closing y²+x³y+z²+1=0; Lean-formalized via Aristotle. **No overlap**
with graph capacity / projection dichotomy / witness–arity trade-offs /
universality capacity: no uniform-in-linear-part constants, no capacity
notion, no parameter counting. Position: related work (adjacent Lean-verified
quadratic-Diophantine result), not competing. Their §1 also independently
confirms GS04's role as the general degree-2 decision algorithm.
