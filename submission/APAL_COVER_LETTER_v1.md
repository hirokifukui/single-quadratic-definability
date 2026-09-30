Dear Editors,

I submit the manuscript "Structure and computability of the single-quadratic existential fragment
over the integers" for consideration in Annals of Pure and Applied Logic.

The paper studies SE₂, the relations on ℤᵏ definable by a single polynomial equation of total degree
at most two with an unrestricted number of existentially quantified integer unknowns. Solvability of a
single quadratic equation is decidable by the Grunewald–Segal procedure, whereas unrestricted Diophantine
solvability is undecidable; the paper asks what one equation of total degree two can define. The theorems
are about definability and computability, and the quadratic arithmetic is the engine, not the subject,
which is why I believe the paper belongs in a logic journal.

The principal result classifies the SE₂-definable total functions. A function f : ℤⁿ → ℤᵐ with two or more
outputs is SE₂-definable exactly when it has a common slope: f(a + Mt) = f(a) + Bt for a modulus M and an
integer matrix B. A scalar function is SE₂-definable exactly when it has a common slope, agrees with a
rational polynomial of total degree at most two, or is of a parity-affine two-branch kind; the three
families overlap, and none of them can be dropped. The classification is stated in the Introduction and
proved in Section 10.

The necessary directions use an eventual representation result for positive definite ternary lattice
cosets (TCER). Lemma 10.8 derives it, in ordinary mathematics, from the published work of Kane and Kim; the
Lean development takes TCER as an explicit hypothesis and does not prove it. The converse constructions,
the classification of the functions definable without unknowns, and the bound n ≤ m for SE₂-definable
injections ℤⁿ → ℤᵐ, which is realized by an injection for every n ≤ m, use no such input. Under the same input the paper
also shows that a ↦ (f(a), 0) is SE₂-definable exactly when f has a common slope, and that every
SE₂-definable function has a presentation whose unknowns are unique. Without any such input, the map a ↦ ⌊a/3⌋ needs
exactly one unknown in this format.

The finite-fibre bounds, the structured description of infinite fibres and the computability phase
diagrams are also proved. Two classical inputs, code-uniform decidability of integer quadratic solvability
and DPRM over ℕ, enter the phase diagrams as named hypotheses, and Section 12 lists which result uses
which input. Section 11 compares the classification with the arithmetic, logical and encoding results on
which it builds.

The paper gives ordinary mathematical proofs throughout; the Lean 4 development is additional
verification, not a request that referees read code instead of proofs. Its fixed source, statement and
definition certificates, explicit-hypothesis reports and reproduction instructions accompany the
submission. The version-specific artifact locator will be inserted in the data availability section
before submission.

A declaration on AI-assisted tools appears before the references, in accordance with Elsevier's policy on
generative AI and AI-assisted technologies. Responsibility for every mathematical claim in the paper, its
presentation and the use of the cited literature is mine.

Yours sincerely,

Hiroki Fukui
Research Institute of Criminal Psychiatry / Sex Offender Medical Center, Tokyo, Japan;
Department of Neuropsychiatry, Kyoto University, Kyoto, Japan
fukui@somec.org
ORCID 0009-0008-7122-522X
