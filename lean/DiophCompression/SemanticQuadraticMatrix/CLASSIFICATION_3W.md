# CLASSIFICATION_3W — three witnesses, degree 2: the r = 3 case map (r09, session 9, 2026-08-27)

Status claim (exact): **the full-rank branch is a complete kernel proof for every r ≥ 2** (not only r = 3);
the singular branch is a hand case map with the open core localised, no Lean, no claim of completeness.
Nothing here is "complete by hand" (E-r08-1 discipline): every sentence about the singular branch is
either a proved lemma (named) or a labelled [OPEN] item.

## 0. Setting and sign conventions (GPT r08 §6 禁止事項)

Fiber polynomial with r witnesses: F(c,u) = A c² + c (B·u) + W(u) + ℓ c + m·u + q, W(u) = uᵀ C u for an integer
matrix C (`DefsMatrix.lean`: `fqM`, `witnessQuad`). Gram matrix G = C + Cᵀ (symmetric, even diagonal,
uᵀGu = 2W(u)); **no diagonal coefficient is ever divided by 2**. N = det G is the *signed* determinant. G⁻¹ is
never used; only adj G with G·adj G = adj G·G = N·1 (`witnessGram_mulVec_adjugate`, `adjugate_mulVec_witnessGram`).
W̃(Y) = Yᵀ (adj G) Y is the adjugate form (`adjugateQuad`).

**Parity remark (r = 3).** adj G = N·G⁻¹. For G definite, G⁻¹ has the sign of G and N has the sign
sign(G)ʳ; hence for r odd adj G is **positive definite whenever G is definite** (either sign), and for G
indefinite adj G is indefinite. So at r = 3, W̃ is never negative definite. The Lean assembly does **not** use
this: it splits on the *values* of W̃ (both signs / ≥ 0 everywhere / ≤ 0 everywhere), which is a trichotomy of
propositions, and treats each with the same lemmas — so the argument is parity-free and applies to every r ≥ 2.

Identity (`general_rank_identity`, all r):  2N·F(c,u) = W̃(Y) + α c² + β c + γ, with Y = G u + c B + m,
α = 2NA − Bᵀ(adj G)B, β = 2Nℓ − 2Bᵀ(adj G)m, γ = 2Nq − mᵀ(adj G)m. Sage gate: 6000 random (r = 1..5)
instances, bad 0 (`scouting/s9_matrix_identity_check.sage`).

Scaled line (`general_scaled_line_*`): c = c₀ + N t, u = u₀ + s·(adj G)w − t·(adj G)B keeps u integral and
moves Y by (N s)·w; along it 2N·F = 2N·F(c₀,u₀) + N·fq(Nα, 0, N·W̃(w), 2αc₀+β, 2·Y₀·(adj G)w, 0)(t, s)
(`general_scaled_line_fq`) — a one-witness fiber form in (t, s) with no ts term.

## 1. Full rank (N ≠ 0) — complete, all r ≥ 2 (`FullRankGeneric.lean`, 21 theorems std-3)

Case map by (sign pattern of W̃) × (sign of α). Every leaf is a named theorem.

| W̃ on ℤʳ | α < 0 | α = 0 | α > 0 |
|---|---|---|---|
| both signs | direction σ=+1 (`indefinite_signed_nonsquare_direction_M`) → `full_rank_dichotomy_of_direction` | `full_rank_alpha_zero_dichotomy` (progression for every β ≠ 0) | direction σ=−1 → generic |
| ≥ 0 everywhere | −αW̃ ≥ 0 ⇒ positive definite (`eq_zero_of_adjugateQuad_eq_zero`) ⇒ `definite_signed_nonsquare_direction_M` → generic | `full_rank_alpha_zero_dichotomy` (β < 0: progression along w with W̃(w) > 0, `exists_adjugateQuad_sign`; β > 0: root bound c ≤ \|γ\|) | root bound `full_rank_root_bound` (c ≤ \|β\|+\|γ\|) |
| ≤ 0 everywhere | root bound | α = 0 theorem (mirror) | −αW̃ ≥ 0 ⇒ definite direction → generic |

Mechanisms:
- Generic (α ≠ 0, direction w with αW̃(w) < 0 and −αW̃(w) non-square): per fiber element (c₀,u₀) either
  α(2αc₀+β) ≤ 0 (then 2|α|c₀ ≤ |β|, `bounded_branch_sharp`) or the scaled line carries a one-witness Pell form
  with X₀ = −4|N|·W̃(w)·(2αc₀+β) > 0 and `pell_infinite_of_X_pos` gives infinitely many c (`fiberSetM_infinite_of_line`).
- α = 0: β = 0 ⇒ membership is |N|-periodic (`alpha_zero_beta_zero_periodic_M`, shift u ↦ u − ε(adj G)B);
  β ≠ 0 with βW̃(w) < 0 ⇒ progression s = βk, t = −2kB₀ − Nβk²W̃(w) gives c → ∞; else βW̃ ≥ 0 ⇒ c ≤ |γ|.
- Directions: both signs ⇒ restriction of W̃ to span(w₊,w₋) is a x² + b xy + c y² with ac < 0 (so disc > 0),
  and the r08 lemmas `split_/anisotropic_signed_nonsquare_direction` apply verbatim; semidefinite ⇒ with N ≠ 0
  positive definite (two-parameter argument: εW̃(qw + v) ≥ 0 for all integers q forces the pairing to vanish,
  hence adj G·w = 0, hence N w = 0), and the restriction to two coordinates i ≠ j is a definite binary form with
  even cross term 2·(adj G)ᵢⱼ(−α), so `definite_nonsquare_direction` applies.
- Bounds: |β| ≤ (2|N| + 2Σᵢⱼ|Bᵢ(adj G)ᵢⱼ|)(1+|ℓ|+Σ|mᵢ|), |γ| ≤ (2|N| + Σᵢⱼ|(adj G)ᵢⱼ|)((1+Σ|mᵢ|)²+|q|)
  (`betaMatrix_abs_le`, `gammaMatrix_abs_le`), so every bounded branch lands inside `fboundM K ℓ m q`.

r = 3 specialisation and the MvPolynomial bridge (`Bridge3W.lean`): `eval_quaternary_homogeneous_quadratic`
(ten monomials, r = 3 analogue of Bridge2W), `witnessMatrixOf H` (upper-triangular C(H) on variables 1..3),
`quadraticProjectionDichotomyZ_three_full_rank : IsHomogeneous 2 → det(C(H)+C(H)ᵀ) ≠ 0 → DichotomyG H`.

What is **not** claimed: `QuadraticProjectionDichotomyZ 3` itself (needs the singular branch), hence no value
of G_ℤ(3,2). The general-r MvPolynomial bridge (degree-2 support ⇒ symmetric matrix) is not formalised; only
the r = 3 enumeration is (UNDERFLOW 2A).

## 2. Singular witness block (N = 0) — case map, [OPEN] core localised

Let ρ = rank G ∈ {0,1,2} (rank over ℚ; over ℤ we use the Smith normal form of G). A unimodular change of the
witness variables (the r = 2 tool `Unimodular.lean` generalises coordinate-wise; [OPEN] to formalise for r = 3)
puts G into block form with a nondegenerate ρ×ρ block on variables u' and a radical of dimension 3 − ρ on
variables v. In these coordinates F(c,u',v) = A c² + c(B'·u') + W'(u') + ℓc + m'·u' + q + Σᵢ (bᵢ c + mᵢ) vᵢ:
**the radical variables enter linearly with the affine coefficients aᵢ(c) = bᵢc + mᵢ** (`AffineGcd.lean`).

### 2.1 ρ = 0 (G = 0, W ≡ 0). F = A c² + ℓ c + q + Σ (bᵢ c + mᵢ) vᵢ (three radical variables).
- b = m = 0 (no witness at all): one-variable quadratic, finite fiber unless identically zero ⇒ dichotomy (r06 D1-type).
- otherwise: the fiber condition is g(c) ∣ A c² + ℓ c + q where g(c) = gcdᵢ(bᵢc + mᵢ) (`affineGcd`).
  * some pair minor bᵢmⱼ − bⱼmᵢ ≠ 0: g(c) ≥ 1 for every c (`affineGcd_pos_of_pairMinor_ne_zero`), g is
    D-periodic with D = minorContent ≠ 0 and g ≤ |D| (`affineGcd_periodic_of_minorContent_ne_zero`), so the
    fiber condition is a finite union of congruence classes ∩ divisibility by a bounded modulus ⇒ periodic in c
    ⇒ infinite or empty by `periodic_infinite_or_empty` (this is the r = 2 rank-0 argument with the r08
    "Per" tool; [OPEN] to write the r = 3 version — mechanical).
  * all pair minors zero: one primitive direction (b₀,m₀) with (bᵢ,mᵢ) = λᵢ(b₀,m₀)
    (`all_pairMinors_zero_iff_rank_one_affine_family`), g(c) = gcd(λ)·|b₀c + m₀| (`affineGcd_of_rank_one_family`):
    exactly the r = 2 rank-0 coupled case with modulus gcd(λ)·(b₀c+m₀) ⇒ r08 `RankZero` argument verbatim
    (divisibility of a quadratic by a linear form in c: bounded unless the quadratic is a multiple). [OPEN: transcribe.]

### 2.2 ρ = 1 (W' = k u'², k ≠ 0). F = A c² + B₁' c u' + k u'² + ℓ c + m₁' u' + q + Σᵢ₌₁² (bᵢc + mᵢ) vᵢ.
- b = m = 0: r = 1 problem (r06 `FiberDichotomy`, complete).
- pair minor b₁m₂ − b₂m₁ ≠ 0: g(c) ≥ 1 always and D-periodic; the condition "g(c) divides the one-witness value
  A c² + B₁'cu' + ku'² + ℓc + m₁'u' + q for some u'" is, for each residue class of c mod D, a fixed modulus
  divisibility of a binary quadratic in (c, u'): this is a *coupled radical with bounded modulus* — the r08
  `RankOneCoupled` prime-step argument applies with the modulus fixed (not growing with c), which is the easier
  case. [OPEN: write it; expected to reduce to the r = 2 rank-1 leaf plus a congruence filter.]
- all pair minors zero: one coupled radical with coefficient gcd(λ)·(b₀c + m₀) ⇒ literally the r = 2 rank-1
  coupled case (`RankOneCoupled`, `dichotomy2_rank_one_normal`) after the unimodular change. [OPEN: transcribe.]

### 2.3 ρ = 2 (W' a nondegenerate binary form on u' = (u₁',u₂'), N' = det G' ≠ 0). F = A c² + c(B'·u') + W'(u')
+ ℓc + m'·u' + q + (b c + m) v (one radical variable).
- b = m = 0: r = 2 problem (r08, complete).
- b = 0, m ≠ 0: the radical variable contributes a fixed modulus m: fiber ⟺ ∃ u' with F₂(c,u') ≡ 0 (mod m).
  Since the u'-block is nondegenerate of rank 2, for every prime p ∤ 2N' the form W' represents every residue
  mod p (our remark (iii) to GPT), so the congruence has a solution for every c modulo the p-part; the finitely
  many primes p ∣ 2N'·m give a periodic filter in c ⇒ infinite or empty. [OPEN: the Hensel/lifting step at
  p^e and at p ∣ 2N' — this is the genuinely new arithmetic of r = 3; the r08 `square_mod_prime_of_one_mod_eight_abs`
  tool is the p ∣ 2 prototype.]
- b ≠ 0: coupled radical with modulus bc + m growing with c: fiber ⟺ (bc + m) ∣ F₂(c,u') for some u'. This is the
  rank-2 analogue of `RankOneCoupled`: reduce F₂ modulo the linear form, i.e. substitute c ≡ −m/b and study the
  binary quadratic 2N'·F₂ ≡ W̃'(Y') + α'c² + β'c + γ' (mod bc + m). [OPEN] — **this is the open core of r = 3**:
  a rank-2 nondegenerate block modulo a moving linear modulus. Expected shape of the answer: for p ∤ 2N' the
  block represents all residues so only the primes of 2N'·(pair minors) and the archimedean constraint from
  Y' remain; a bounded-modulus reduction as in 2.1/2.2 is plausible but not written.

### 2.4 What the singular branch would need in Lean (r10 plan)
1. A unimodular normal form for a singular symmetric 3×3 integer matrix (rank ρ, radical of dimension 3−ρ) —
   generalising `Unimodular.lean` (r = 2, rank 1).
2. The transcriptions marked [OPEN: transcribe] (2.1 both, 2.2 all-minors-zero), each a copy of an r08 leaf
   with vector bookkeeping.
3. The two genuinely new pieces: 2.2 non-zero-minor (bounded modulus, rank-1 block) and 2.3 (rank-2 block with
   fixed or moving modulus). GPT's 宿題群 3.1 ("rank ≥ 2 nondegenerate block mod p represents every residue")
   is the key lemma for 2.3; it is false for rank 1 (W = u²) and must be frozen with rank ≥ 2.

## 3. Named theorems (r09 layer, all `[propext, Classical.choice, Quot.sound]` or subsets)
`AffineGcd`: affineGcd_nonneg, affineGcd_dvd_affineCoeff, affineGcd_eq_zero_iff, affineGcd_dvd_pairMinor,
affineGcd_dvd_minorContent, affineGcd_pos_of_pairMinor_ne_zero, affineGcd_periodic,
affineGcd_periodic_of_minorContent_ne_zero, all_pairMinors_zero_iff_rank_one_affine_family, affineGcd_of_rank_one_family.
`AdjugateIdentity`: witnessGram_transpose, witnessGram_diag, adjugate_witnessGram_transpose,
dotProduct_witnessGram_mulVec, adjugate_pairing_comm, witnessGram_mulVec_adjugate, det_smul_mem_gramRange,
adjugateQuad_add_smul, general_rank_identity, general_scaled_line_preserves_lattice, general_scaled_line_identity,
general_scaled_line_solution. `FullRankGeneric`: 21 theorems (§1). `Bridge3W`: 7 theorems (§1).

## 4. Singular sweep (calibration, `scouting/s9_singular_sweep.sage`, md5 5ba5d01f)
240 random instances in normal coordinates (the fiber set is invariant under unimodular changes of u), fiber sets computed **exactly** on c ∈ [0,60] through the divisibility criterion of §2 (ρ = 2: (bc+m₃) ∣ F₂(c,u') for some u' mod |bc+m₃|; ρ = 1: g(c) ∣ F₁(c,u') for some u' mod g; ρ = 0: g(c) ∣ Ac²+ℓc+q; modulus 0 ⇒ exact zero). Planted control (ρ = 2, b = 0): the set must be |m₃|-periodic — 54/54. All 149 "periodic"-predicted instances show a period ≤ 20 in the window. The 86 §2.3 instances (b ≠ 0) are all infinite-looking and none empty; no finite-looking instance anywhere; 0 flags. Calibration only (small coefficients, window 60); the §2.3 mechanism remains [OPEN].
