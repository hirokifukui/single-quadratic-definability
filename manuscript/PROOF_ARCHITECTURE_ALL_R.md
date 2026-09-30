# Proof architecture — Quadratic Witness Inertia (six lemmas; human-readable, independent of Lean)

Revision s13 (2026-08-28), per GPT r12 §3.1: L3 split into L3A/L3B; L4 restated
as the MOVING-linear-modulus leaf with the four-branch analysis; L3/L4 remain
separate lemmas (merger prohibited).

**Main theorem (projection dichotomy).** Fix an integer-coefficient homogeneous
quadratic H(c, u₁, …, u_r) in the output variable c and r witness variables.
There is a constant K_H such that for every integer linear part ℓ and constant q,
the projection set

  S = { c ∈ ℕ : ∃ u ∈ ℤ^r, H(c,u) + ℓ·(c,u) + q = 0 }

is either infinite or contained in [0, K_H·((1+|ℓ|₁)² + |q|)].

**Capacity corollary.** In an injective graph representation every input fiber is
a singleton, so the infinite branch is excluded. Restricting parameters to
a ∈ [0,N]^n makes the linear coefficients O(N) and the constant O(N²), hence
every represented output is O(N²). About N^n inputs inject into O(N²) outputs,
forcing n ≤ 2. The witness-free quadratic tupling map achieves n = 2, so
G_ℤ(r,2) = 2 for every r.

The dichotomy is proved through six lemmas.

---

## Lemma 1 (full-rank adjugate reduction)

Write the quadratic part of F(c,u) = H + ℓ + q in matrix form:
F = A c² + c(B·u) + uᵀCu + (linear) with A ∈ ℤ, B ∈ ℤ^r, C ∈ M_r(ℤ), and set
G = C + Cᵀ (the Gram matrix), N = det G. If N ≠ 0, put Y = Gu + cB + m where m
is the witness part of the linear form. Multiplying F by 2N and completing the
square with the adjugate,

  2N·F(c,u) = Yᵀ·adj(G)·Y + αc² + βc + γ

for integers α, β, γ polynomial in the data. Restricting u to a suitable
integer line reduces the fiber condition to a two-variable quadratic
(Pell-type or definite), for which the finite/infinite dichotomy with a
uniform height bound in (|ℓ|₁, |q|) is classical and was established for
every r in the full-rank layer. No division is performed: 2N is a
multiplier, not a denominator.

## Lemma 2 (integral radical decomposition)

If det G = 0, let K = ker G ∩ ℤ^r. Then K is a saturated submodule (if kx ∈ K
for k ≠ 0 then Gx = 0), so ℤ^r/K is finitely generated and torsion-free, hence
free (PID), hence the exact sequence 0 → K → ℤ^r → ℤ^r/K → 0 splits.
Concatenating a basis of K with a lift of a basis of the quotient gives
U ∈ GL_r(ℤ) with

  UᵀGU = [ G₀ 0 ; 0 0 ],  det G₀ ≠ 0.

This is a congruence transformation (Uᵀ·U on the same side), NOT a Smith
normal form (which is a left–right equivalence P·Q and does not preserve
quadratic forms). Although C itself need not be symmetric and UᵀCU can keep
nonzero entries in the radical block, the quadratic value only sees the
symmetric part: 2·uᵀCu = uᵀ(C+Cᵀ)u, so a vanishing Gram block means the
quadratic value is invariant under radical translations; the factor 2 cancels
in the torsion-free ring ℤ.

## Lemma 3A (nonzero-minor periodicity)

After Lemma 2 the radical variables w₁,…,w_s enter only linearly, with
coefficients aᵢ(c) = bᵢc + mᵢ. Let g(c) = gcdᵢ(bᵢc + mᵢ).
For all i, j: g(c) divides bⱼ(bᵢc+mᵢ) − bᵢ(bⱼc+mⱼ) = bⱼmᵢ − bᵢmⱼ.

If some pair minor bᵢmⱼ − bⱼmᵢ ≠ 0, then g(c) divides that fixed nonzero
integer, so the value of g is constrained to its divisors and the solvability
condition modulo the radical variables (a congruence of the c-polynomial
modulo g(c)) is periodic in c. A periodic nonempty subset of ℕ is infinite.
Hence in this branch the projection is empty or infinite — in particular
unusable for singleton graph fibers.

## Lemma 3B (proportional compression)

If all pair minors vanish, every pair (bᵢ, mᵢ) is proportional to one
primitive pair (b₀, μ₀): (bᵢ, mᵢ) = λᵢ(b₀, μ₀). Then, existentially,

  ∃ w₁,…,w_s with Σ aᵢ(c)wᵢ = t  ⟺  ∃ w with (b′c + μ′)w = t,

where (b′, μ′) is the primitive pair scaled by gcd(λ). This is a two-sided
equivalence (Bézout in both directions), so any number of radical variables
compresses exactly to ONE coupled radical variable. Lemmas 3A and 3B are
distinct mechanisms and are kept as separate lemmas: 3A produces an
empty-or-infinite verdict, 3B produces a normal form for the remaining leaves.

## Lemma 4 (quotient-rank-zero leaf: the moving linear modulus)

After Lemmas 2 and 3B with k₀ = rank G₀ = 0, the fiber condition is

  ∃ w ∈ ℤ : Q(c) + (bc + μ)·w = 0,  i.e.  (bc + μ) ∣ Q(c),

with Q(c) = A c² + l c + q. The modulus bc + μ MOVES with c when b ≠ 0 —
this is not a fixed-modulus periodicity. The mechanism is the remainder
identity (Lean: `linear_modulus_divides_quadratic_remainder`):

  R := A μ² − b l μ + b² q
     = b²·Q(c) − (bc + μ)·(A(bc + μ) + (bl − 2Aμ)),

so (bc + μ) ∣ Q(c) forces (bc + μ) ∣ R. Four branches:

* **b ≠ 0, R ≠ 0** (bounded): every fiber point satisfies |bc + μ| ≤ |R|,
  so c is confined to an explicit interval; R is quadratic in (|l|, |μ|, |q|),
  giving the uniform bound shape K·((1+|l|+|μ|)² + |q|) with
  K = |A| + |b| + |b|² + 2.
* **b ≠ 0, R = 0** (congruence sub-split): with L(c) = Abc + bl − Aμ the
  identity reads b²·Q(c) = (bc+μ)·L(c), so for bc+μ ≠ 0 the divisibility
  (bc+μ) ∣ Q(c) is EQUIVALENT to the fixed congruence b² ∣ L(c). If that
  linear congruence is solvable, a full arithmetic progression mod b² lies
  in the fiber — infinite; if unsolvable, S contains at most the single c
  with bc+μ = 0 — bounded.
* **b = 0, μ ≠ 0** (fixed modulus): the divisibility μ ∣ Q(c) is genuinely
  periodic in c; nonempty implies infinite.
* **b = 0, μ = 0** (no coupled variable): the condition degenerates to
  Q(c) = 0; either A = l = q = 0 (every c solves — infinite) or a nonzero
  quadratic with at most two roots — bounded.

## Lemma 5 (moving-modulus prime progression, k₀ ≥ 2)

Normal form: F(c,u) + (bc+μ)w = 0 with F nondegenerate of rank k₀ ≥ 2,
b > 0. Suppose a solution with t₀ = bc₀ + μ > 0 exists. Choose a prime
p ≡ 1 (mod 2|det(C+Cᵀ)|·b·t₀), p large. Write p − 1 = bj and c₁ = c₀ + t₀j.
Then bc₁ + μ = t₀ + t₀(p−1) = t₀p. Modulo t₀ the original solution persists;
modulo p a root exists because a nondegenerate quadratic form of rank ≥ 2
over F_p (p odd, p ∤ det) is universal; gcd(t₀, p) = 1 lets CRT glue the two
congruences into a witness for the strictly larger output c₁. Iterating gives
an infinite fiber. If instead bc + μ ≤ 0 for all solutions, then c ≤ |μ|,
which is within the uniform bound.

The k₀ = 1 case is the rank-one coupled dichotomy (closed at r08; Lean
`quotient_rank_one_dichotomy`), which applies verbatim after the compression
of Lemma 3B; it is an established component invoked by the assembly, not one
of the six lemmas under blind review.

## Assembly

Every branch ends in "infinite" or "c ≤ K_H·((1+|ℓ|₁)²+|q|)". The dispatch is:
det G ≠ 0 → Lemma 1; det G = 0 → Lemma 2 normal form → Lemma 3A (a nonzero
minor kills the branch) or Lemma 3B (compression) → by k₀: 0 → Lemma 4,
1 → rank-one component, ≥ 2 → Lemma 5. The capacity corollary then follows by
the counting argument stated at the top; the lower bound G_ℤ(r,2) ≥ 2 is
witnessed by the quadratic tupling map with no witnesses, which also yields
the arity-spectrum inertia GraphAchievableZ(n,r,2) ⟺ GraphAchievableZ(n,0,2).

## Independent re-proof gate (11 sessions, pending)

Per GPT r12 §6 Q2: L1:1, L2:2, L3A:2, L3B:2, L4:1, L5:2 blind sessions plus
one global destroyer session (attacks the assembly, not a single lemma).
Sessions do not see the Lean sources; discrepancies are arbitrated by CAS.
Status: NOT YET RUN (planned as r13 必須C; plan document to be written).
