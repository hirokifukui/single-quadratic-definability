# Recon: the "search bounds" literature — the nearest quantitative neighbours of Theorem 2.1
(s29, 2026-09-02; found by searching, from public abstracts and reference lists)

## Why this file exists

Section 10 of v3.1 compared our finite-fibre bounds only with the existential-rank programme and with
classical binary-form theory. That was the wrong neighbourhood. The nearest quantitative literature is
**search bounds for Diophantine equations**, a line running from Cassels 1955 to the present, and it was
absent from the manuscript. A referee working on quadratic forms would think of it within a page.

## The line

- **Cassels (1955)**, Proc. Camb. Phil. Soc. **51**, 262–264: for an isotropic integral quadratic form F
  in n variables there is a nonzero integral zero z with |z| ≪_n |F|^((n−1)/2), where |F| is the largest
  coefficient. This is the origin of the subject.
- **Masser (1998)**, Bull. LMS **30**, 24–28: the rational analogue, and the remark that the
  Grunewald–Segal integer procedure is involved but completely effective.
- **Dietmann (2003)**, Proc. LMS (3) **86**, 545–582: the closest statement to ours. For an INHOMOGENEOUS
  Q ∈ ℤ[X₁,…,X_s] of degree 2 with coefficient height ≤ H and **nonsingular** homogeneous quadratic part,
  and **s ≥ 3**: there is a polynomial bound Λ_s(H) such that if Q = 0 has an integer solution at all, it
  has one with |x_i| ≤ Λ_s(H). New for s = 3, 4; improvements for s ≥ 5.
- **Fukshansky**, *Heights and quadratic forms: on Cassels' theorem and its generalizations*, Contemp.
  Math. **587** (2013), 77–94: the survey of the whole direction, with the many refinements (zeros
  avoiding sublattices, avoiding unions of varieties, over number fields, over quaternion algebras).

## How our Theorem 2.1 differs — stated carefully, three ways

1. **Smallest solution versus every element of a finite fibre.** Cassels and Dietmann bound the SMALLEST
   solution: if a solution exists, a small one exists. Theorem 2.1 bounds EVERY element of the fibre,
   given that the fibre is finite. These are different quantifiers and neither implies the other: a
   finite fibre can have a small smallest element and a large largest one.
2. **Coefficient height versus parameter height, with the constant fixed in advance.** Their bound is a
   function of the coefficient height H of the one equation in front of them. Ours fixes the equation
   with a parameter block and asserts ONE constant C, depending on that equation alone, with
   |c| ≤ C·N² for every parameter point of height ≤ N. Specialising our parameters does give an equation
   whose coefficient height is polynomial in N, so the two are related in kind; but a per-instance
   smallest-solution bound does not by itself produce a constant uniform over the parameter family, and
   the exponent 2 in our statement is uniform in the number of unknowns, whereas Dietmann's exponent
   ρ(s) grows with s.
3. **Hypotheses.** Dietmann assumes s ≥ 3 and a nonsingular quadratic part. Theorem 2.1 assumes only
   total degree ≤ 2: the quadratic part may be singular or zero, and the number of unknowns is arbitrary,
   including 0 and 1. The singular case is precisely where our Section 9 does its work.

## Consequence for the effectivity remark (2.3)

Dietmann's bounds are explicit. Our constant C is not, and the only non-explicit ingredient is the
constant K of the projection dichotomy. If an effective K is ever wanted, that literature is where the
technique would come from, and Remark 2.3 should point at it rather than merely confessing.

## What is NOT claimed

We do not claim our theorems are independent of this line, and we do not claim priority against it. We
claim the statements are different in the three ways above. Whether a uniform-in-parameters bound can be
extracted from Dietmann's methods is a reasonable question for a referee to raise, and the manuscript
now raises it itself.
