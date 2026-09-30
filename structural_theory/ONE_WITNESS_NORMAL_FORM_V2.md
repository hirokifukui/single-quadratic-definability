# ONE_WITNESS_NORMAL_FORM_V2 — corrected statement (必須F), s25 2026-09-01
Draft: `drafts/OneWitnessNormalForm_STATEMENTS_v2.lean` (type-checks; sorry bodies; NOT frozen).

## Why v1 was wrong (ERRATA_GATE1 E11)
v1 (`GATE1_F_G_STATEMENTS.md:53–54`) wrote the one-witness fibre as E ∪ (affine lines) ∪ (Pell orbits). The equation
c − u² = 0 (one witness, degree 2) has fibre {0, 1, 4, 9, …}: not finite, not a finite union of arithmetic progressions
(quadratic gaps), not a finite union of unit orbits (exponential growth). My own case map (v1 line 65, Δ = 0 rank 1 →
"polynomial progression of degree ≤ 2") already contradicted the formal line. The review caught it.

## v2 statement (conditional)
For P ∈ ℤ[a₁..a_n, c, u] of total degree ≤ 2 and a fixed input a, there exist a finite set E ⊆ ℤ, finitely many
integer polynomials q of degree ≤ 2, and finitely many generalized Pell families f (unit orbit on x² − D y² = N,
c-projection by a linear form, exponent restricted to a congruence class) with
  fiber(P, a) = E ∪ ⋃_q q(ℤ) ∪ ⋃_f orbitSet(f).
Divisor families (product of two rational linear forms = nonzero constant) are FINITE for a fixed input and are
absorbed in E; the tag survives only in the branch crosswalk (GPT §6 lists them separately — same mathematics).
Hypothesis `PellClassFiniteness` (Nagell): finitely many unit orbits of solutions of x² − D y² = N, effective class
representatives. Disclosed Prop, never an `axiom` (METHODOLOGY §5: a classical theorem not in mathlib is a hypothesis
until formalized). Answer to LETTER_GATE1 Q3: GPT accepts the conditional assembly.

## Case map (by the binary quadratic part in (c, u))
| Δ | shape | fibre contribution | kernel class files (r = 1) |
|---|---|---|---|
| definite (Δ < 0) | ellipse | finite → E | D1 (?) |
| Δ = 0, rank 1 | (αc + βu)² + linear | degree-≤2 polynomial progression (parabola), or finite, or empty | D2/D3 (?) |
| Δ > 0 square | product of two rational linear forms | constant ≠ 0: finite (divisor set) → E; = 0: two lines → degree-1 progressions | D4/D6 (?) |
| Δ > 0 nonsquare | indefinite irreducible | finitely many classes × unit orbits, with congruence sub-orbits | D7/D9, PellPow.lean (?) |
(?) = crosswalk to Class_D*.lean not yet read (UNDERFLOW s24-04; Class_D5/D8 do not exist — numbering gap).

## Open formal items before freeze
`PellFamily.orbitSet` and the orbit clause of `PellClassFiniteness` are written as placeholders (`sorry` / `True`);
the v2 freeze requires the explicit orbit recursion (x_{k+1}, y_{k+1}) = (x_k ux + D y_k uy, x_k uy + y_k ux) and the
exact union equality; effectivity of E, Q, F is a separate (paper-level) claim.
