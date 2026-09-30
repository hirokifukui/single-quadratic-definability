# QUADRATIC_UNIVERSALITY_CAPACITY — the three-level classification at degree 2
(s13, 2026-08-28; homework group 1 items 15–20; GPT r12 mandatory A
deliverable. Revised s14 per GPT r13 必須C: the degree-2 table now separates
the proven ℤ-witness capacities from the open ℕ-witness graph capacity, and
the U = 0 positioning as a [GS04] corollary is stated at the head.)

## 1. Citation-accurate natural-language theorem (homework 17)

**Theorem (quadratic universality capacity; conditional presentation).**
Let U_ℤ(r,2) denote the largest arity n such that every Diophantine set
A ⊆ ℕⁿ is representable by a single integer polynomial P_A of total degree
≤ 2 in the n parameters and at most r integer unknowns (quantifier order
∀A ∃P_A: the polynomial may depend on A, only the budget (r, 2) is
uniform — `UniversalAchievableZ`, Definitions.lean). Then, for every r,

    U_ℤ(r,2) = 0,   and likewise   U_ℕ(r,2) = 0.

*Proof (natural language, unconditional modulo the cited literature).* By
Grunewald–Segal [GS81; GS04], integer (resp. positive-integer, and more
generally hyperplane-region-restricted) solvability of a single quadratic
equation with rational coefficients in any number of unknowns is decidable.
Suppose some Diophantine A ⊆ ℕ¹ were represented by a fixed polynomial P of
total degree ≤ 2 with r integer unknowns. For each a ∈ ℕ, substituting a
yields an explicit integer quadratic in the unknowns; applying the GS
algorithm to it decides membership of a in A. No uniform choice of
representing polynomial across Diophantine sets is required: the single
fixed P is hard-coded into the decision procedure. By DPRM [Mat70] there is
a Diophantine A ⊆ ℕ that is not recursive (e.g. via the halting problem).
Contradiction; so no Diophantine-universal quadratic pair exists at arity 1,
and by arity downward closure at no arity ≥ 1. At arity 0 the only subsets
of ℕ⁰ are ∅ and the one-point set, each represented by a constant equation,
so U(r,2) = 0. ∎

*Positioning.* U = 0 is a direct corollary of [GS04] decidability combined
with [Mat70]; the contribution of this paper is its placement as the bottom
level of the capacity classification and the exactness of the gaps against
G_ℤ = 2 and S = r + 3 — the classification, not the decidability input.

Citations: [GS81] MPCPS 89 (1981) 1–5, DOI 10.1017/S030500410005787X;
[GS04] Crelle 569 (2004) 13–45, DOI 10.1515/crll.2004.023; [Mat70]
Matiyasevich, Dokl. Akad. Nauk SSSR 191 (1970) 279–282; [Sie72] Nachr. Akad.
Wiss. Gött. II (1972) 21–46 (classical antecedent). Scope audit:
literature/QUADRATIC_DECIDABILITY_AUDIT.md — **CLOSED [V-fulltext]
2026-08-28**: GS04 Theorem 0.1 audited verbatim (uniform algorithm; affine
quadratic, rational coefficients, any n; ℤ via trivial constraints, ℕ via the
positive quadrant; nonnegative versus strictly positive witness conventions
are immaterial — the region form of Theorem 0.1 admits the closed quadrant
directly, and a unit shift of the unknowns interconverts the two). The paper may state U = 0 unconditionally citing [GS04]
(+[Mat70]); GS81 and Siegel 1972 cited as antecedents without further audit
need (both confirmed inside GS04 §0.1).

## 2. The Lean layer (item 15–16)

`DiophCompression/QuadraticUniversalityConditional.lean` (md5 873876cd):
hypotheses `QuadraticSolvabilityDecidableZ/N` (per-polynomial, non-uniform)
and `HardDiophantineSetExists` (DPRM+halting; AFP-verified, absent from
mathlib pin) — six theorems, all std-3, culminating in
`universalCapacityZ_degree_two_eq_zero` / `...N...`. Formal computability
vocabulary: mathlib `ComputablePred` over `Primcodable (Fin n → ℕ)`.

## 3. The exact S/G/U table at degree 2 (item 19)

### 3.1 ℤ-witness capacities (proven)

| capacity | value | status |
|---|---|---|
| S(2, r+1) (syntactic) | r + 3 | [P std-3] (r11) |
| G_ℤ(r,2) | 2 | [P std-3] (r11, all r) |
| U_ℤ(r,2) = U_ℕ(r,2) | 0 | [P-cond std-3] Lean; **NL unconditional, [GS04 Thm 0.1]+[Mat70], audit [V-fulltext]** |

    U = 0  <  G_ℤ = 2  <  S = r + 3        (for every r)

Reading: one quadratic equation can *name* r+3 parameters syntactically,
can *semantically graph-encode* exactly 2 with ℤ-witnesses, and can
*universally represent* none. The three notions separate already at degree
2, with gaps 2 and r+1. The universality row covers both witness semantics
because the [GS04] algorithm decides both the ℤ-restricted and the
quadrant-restricted problem.

### 3.2 ℕ-witness graph capacity (open)

G_ℕ(r, 2) is OPEN and appears in no proven row above. The r10 attempt at
G_ℕ = 2 is in KILL status (the quadrant-sign mechanism does not close;
underflow entry preserved). Nothing in §3.1 depends on it.

## 4. Referee objections and answers (item 18, U-relevant subset)

- **"U=0 is a corollary of GS decidability — trivial?"** The inputs are
  classical (GS + DPRM); the *statement* U(r,2)=0 in the capacity framework,
  its exactness against G=2 and S=r+3, and the kernel-checked conditional
  reduction are what is new. We claim the classification, not the decidability.
- **"U≤3 was already in r12 — why is 0 better?"** U≤3 came from the counting
  obstruction and is not sharp; U=0 is exact and turns the table into a
  complete three-level classification (GPT r12 §2 assessment adopted).
- **"One-equation restriction artificial?"** No: systems of quadratics are
  H10-complete (Skolem degree reduction), so degree 2 with ONE equation is
  precisely the decidability boundary; the capacity theory lives exactly on
  that boundary. (AUDIT §5.)
- **"Why hypothesis form in Lean?"** mathlib lacks both GS and MRDP; bare
  axioms for them would violate the project's safe-axiom gate (METHODOLOGY
  §5); conditionality lives honestly in the hypotheses. Promotion path: AFP
  DPRM crosswalk (safe-axiom candidate, Dr. Fukui gate) or future mathlib.

## 5. Abstract reflection (item 20) — draft sentence for the paper abstract

"At degree two the three capacities separate completely: a single quadratic
Diophantine equation with r integer witnesses syntactically names r+3
parameters, graph-encodes exactly two, and universally represents none
(U_ℤ(r,2)=0 < G_ℤ(r,2)=2 < S(2,r+1)=r+3), the last equality via the
Grunewald–Segal decision procedure against DPRM."
