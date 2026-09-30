# Phase −1 crosswalk: Grunewald–Segal vs. our Definition 1.5 (started s29, 2026-09-02)

Status (revised 2026-09-03): **all rows closed to the level of the published abstracts and of a
third-party published statement. No row now rests on an unread body.** Rows 4 and 8, previously
marked [BODY], are settled below; the level of evidence is named in each. Row 6 was never a body
question — it is a comparison, and it is made in Section 10 of the manuscript.** Everything below was obtained from publicly readable abstracts and front matter, and is
paraphrased, not transcribed.

## The two papers, and which one is the load-bearing citation

| | GS 1981 | GS 2004 |
|---|---|---|
| Reference | Math. Proc. Camb. Philos. Soc. **89** (1981) 1–5; DOI 10.1017/S030500410005787X; Zbl 3737745; MR0591965 | J. Reine Angew. Math. **569** (2004) 13–45; DOI 10.1515/crll.2004.023; MR2055712 |
| Self-description | the authors call it a *sketch* of an effective procedure, written in answer to a question of Britton (MPCPS 86 (1979) 385–389) | a full paper presenting the algorithm |
| Equation | arbitrary quadratic with rational coefficients | arbitrary quadratic with rational coefficients, **in arbitrarily many unknowns** |
| Decides | existence of a solution in integers | existence of a solution in **positive** integers |
| Extra output | none stated | solutions restricted to a region cut out by finitely many rational affine hyperplanes; **if the solution set is finite the algorithm lists it, and if infinite it says so** |
| Also proved | — | a density-at-infinity theorem for arithmetic-group orbits on an indefinite quadric of rank ≥ 3 |
| Third-party assessment | Masser (Bull. LMS 30 (1998) 24–28) describes the 1981 procedure as involved but completely effective | — |

**Consequence for the manuscript.** Our fragment fixes the degree and leaves the number of unknowns
free. The phrase *in arbitrarily many unknowns* appears in the 2004 abstract, not in the 1981 one.
The load-bearing citation for Definition 1.5 is therefore **GS 2004**, with GS 1981 as the announcement
and sketch. Citing only [GS81] understates what is being assumed and where it was proved.

## Crosswalk rows

| # | Their claim (paraphrased from published abstracts) | Our object | Verdict |
|---|---|---|---|
| 1 | The input is an arbitrary quadratic equation with rational coefficients in arbitrarily many unknowns (2004) | `QuadraticCode` = (witness arity, list of terms), and `quadraticCode_surjective`: every polynomial of total degree ≤ 2 is the polynomial of a code | matches; our coding is a coefficient table, theirs is the equation itself |
| 2 | Rational coefficients are allowed | `rational_clearing_int_points`: multiplying by a nonzero rational does not change the integer solutions | matches |
| 3 | The algorithm decides solvability, uniformly in that input | `UniformQuadraticSolvabilityOnCodes` | this is the uniformity we assume; an algorithm whose *input* is an arbitrary equation is uniform in the equation by construction |
| 4 | Solutions sought in the positive integers (2004) | our fibres are over ℤ; the passage between ℤ and ℕ is `infinite_integer_set_pos_or_neg` and the output-negation layer | **CLOSED.** The published abstract answers the question the row posed, and the answer is the second alternative: the algorithm "considers **integral** solutions restricted to lie in the region bounded by an arbitrary finite collection of rational affine hyperplanes". Taking the empty collection gives unrestricted integral solutions, so the ℤ form is contained in the 2004 statement itself and does not have to be reconstructed. The headline sentence of that abstract is about positive integers, which is why the convention has to be stated; the region form is what makes ℤ available. [GS81]'s abstract is about integers directly, but describes itself as a sketch. Evidence: publisher abstracts, not the printed body. |
| 5 | Solutions may be restricted to a region bounded by rational affine hyperplanes (2004) | not used by us | strictly more than we assume |
| 6 | If the solution set is finite the algorithm lists it; if infinite it says so (2004) | Theorem 8.5 (bounded or structured certificate) and Theorems 2.1–2.2 | **NOT the same statement — see below. This row is the novelty-critical one.** |
| 7 | The number-field version (1981, asserted without proof) | not used | out of scope |
| 8 | The procedure's complexity / bounds | our constants are non-effective (Remark 2.3) | **CLOSED, negatively.** Neither abstract states a bound: 2004 gives a decision procedure that lists a finite solution set and reports infinitude otherwise, and its auxiliary number-theoretic result (Γ-translates of a rational point are dense at ∞ in a component of the quadric) is qualitative. Independent published confirmation: Dietmann, PLMS (3) **86** (2003), 545–582, states in its own abstract that "for s = 3 and s = 4 no polynomial bounds Λ_s(H) were previously known" — a third party asserting, in print and one year before [GS04] appeared, that no such bound was available in this line. Remark 2.3 therefore need not cite a bound from [GS04], and does not. Evidence: two published abstracts. |

## Row 6, stated carefully — the comparison the manuscript owes

Grunewald–Segal 2004 decide, for one given equation, whether the solution set (in a region) is finite,
and list it when it is. That is an **algorithmic, per-equation** statement: run the procedure, get an
answer about that equation.

Our Theorem 2.1 is a **uniform, parametric** statement: for a fixed equation with a parameter block,
ONE constant C bounds the height of every finite fibre over every parameter point, quadratically in the
parameter height. An algorithm that answers finiteness per instance does not give such a C, and it is
not established that one can be extracted from it: their procedure decides an instance, ours asserts a rate
in the parameters.

Our Theorem 8.5 is a **structural** statement about the infinite case: not "the algorithm says infinite"
but "the fibre carries a certificate of one of three named kinds, with the arithmetic data pinning the
output map". Row 6 is the closest published statement to ours, and it is the one that must be discussed
in Section 10 rather than left to a novelty search.

## What the printed text would still add, and why nothing rests on it

Rows 4 and 8 are closed above from the publisher abstracts and, for row 8, from a third party's
printed statement. What the article body would add is confirmation rather than content: the exact
wording of the ℤ-versus-ℕ passage, and certainty that no bound appears in a lemma. We have therefore
stopped marking them [BODY], and instead record the level of evidence in each row, because a row that
says "we could not check" and a row that says "we checked the abstracts and this is what they say"
are different claims and the second one is the true one.

One question genuinely does need the body, and it is not on this table: whether the 2004 finiteness
test is uniform over a *parameter block* rather than being applied one equation at a time. Nothing in
our development assumes that it is. Definition 1.5 assumes uniformity in the coefficient table, which
the 2004 statement supplies by construction since the table is its input; uniformity over parameters
is what Theorem 2.1 proves for itself and does not import. So the open question is a matter of
curiosity about their paper, not a dependency of ours.

**Bibliographic data verified 2026-09-03.** [GS04] = J. Reine Angew. Math. **569** (2004), 13–45,
DOI 10.1515/crll.2004.023, zbMATH Zbl 2092068, MR2055712 (2005d:11047), MSC 11D72 / 11E12 / 11U05.
[GS81] = Math. Proc. Cambridge Philos. Soc. **89** (1981), 1–5, MR0591965 (82j:10029).

---

## Retrieval attempt for the body (s35, Gate-9 L01)

The review asks for the published body rather than the abstract. It was attempted here, and the
attempt is recorded so that the next reader does not repeat it or assume it was never made.

    zbMATH Open       au:Grunewald & au:Segal & py:2004
                      -> Zbl 2092068, "On the integer solutions of quadratic equations",
                         J. Reine Angew. Math. (2004), MSC 11D72 / 11E12 / 11U05,
                         DOI 10.1515/crll.2004.023
    fetch of the DOI  https://doi.org/10.1515/crll.2004.023
                      -> redirects to degruyterbrill.com/document/doi/10.1515/crll.2004.023/html
                      -> HTTP 202, a landing page, no document text

The bibliographic identity is confirmed to the level of the indexing record. The body is behind a
subscription and is not readable from this machine. What that leaves is what the rows below already
say: every one of them rests on the published abstract, on publisher front matter, or on a
third-party printed statement, and each names which.

**The disposition this supports.** Definition 1.5 is stated in the manuscript as an explicit
hypothesis, not as a theorem imported from [GS04]; nothing in the development is unconditional on
the strength of an unread body. The crosswalk's job is to say honestly how close our hypothesis is
to what [GS04] is understood to prove, and at what level of evidence. Raising a row to
PRIMARY BODY VERIFIED needs the printed volume: a library copy of J. Reine Angew. Math. 569, or an
offprint. That is a request to be made of a person, not of this machine, and it is the only part of
Gate-9 L01 that remains open.

### A second third-party printed statement about [GS04] (s35)

Reading GA26 (arXiv:2607.06627v1) for the novelty gate produced, incidentally, a second independent
printed statement about what Grunewald–Segal provides. Section 1 of that paper says that when P has
degree at most two, equation F(y,z) = P(x) "is itself a quadratic Diophantine equation in three
variables" and that "in principle, such equations are covered by the general algorithm of Grunewald
and Segal for integer solutions of quadratic equations", citing the same work; Section 2 repeats
that "there is a general algorithm for answering this question for all quadratic equations".

This does not read the body of [GS04], and no row is raised to PRIMARY BODY VERIFIED on it. What it
adds is a second author group, in 2026, describing the same procedure in the same terms as the
abstract and as Masser's 1998 assessment. Three independent descriptions agreeing is not the body;
it is a stronger form of the evidence the rows already declare, and the rows say which they rest on.
