# PROOF_NOTE_NF — the general coset normal form (weak and full), ordinary proofs

s57 (2026-09-25, agora); §0 and §5 revised s58 (2026-09-26, GATE28 E-28-1, E-28-5); ordinary proofs of Lemmas 5.1–5.4 and §6 (scalar classification) added s59 (2026-09-27, GATE29 A2 / E-29-3, B–D). Companion to PROOF_NOTE_DIMENSION. Every statement below is a Lean declaration of
`ResearchUpgrade/` (std-3 unless marked [C]); the Lean name is given with each. [C] = conditional on the explicit hypothesis
TCER (`TCERBridge.TernaryCosetEventualRepresentation`), never an axiom. Source for TCER: `correspondence/TCER_ADAPTER_s58.md` (Kane–Kim to the Lean statement; paper Lemma 10.8). s60 (GATE30): the paper's Appendix A normal forms are now Section 10, with the same numbers (A.k → 10.k); the draft crosswalk `C1_TCER_CROSSWALK_s58.md`, cited here before, ships only with the development history.

## 0. Setting

A total function f : ℤⁿ → ℤᵐ is defined by one quadratic equation P(a, z) = 0 in the inputs a and the unknowns
z = (b, u) ∈ ℤ^{m+r} (outputs b, witnesses u). Write the quadratic part in z as Q, its polar form as
polar(x, y) = Q(x+y) − Q(x) − Q(y) (so polar(x, x) = 2Q(x)), the radical Rad = {x : polar(x, ·) = 0}, and d = polar rank.
The case m = 0 is automatic (`generalFullNF_iff_branches`), and the branch Q ≡ 0 is treated separately (§1). In the remaining
branches m > 0 and Q(v) ≠ 0 for some integer v, and totality gives an integer solution z₀ at every input a. Under these
hypotheses and output uniqueness the linear part in z at input a vanishes on the rational radical (`zLinQ_radicalQ_eq_zero`:
0 < m, `OutputUnique`, `SolZ a z₀`, ∃ v, Q(v) ≠ 0). Output uniqueness alone does not give this: P(a, b) = b − a is total and
output-unique, with Q ≡ 0, Rad = everything and linear coefficient 1. In these branches only, there is an affine
centre family c(a) (`exists_affine_centre_of_all_inputs`) and
  P(a, z) = Q(z − c(a)) − R(a)            (`completeSquare`, `cr_eval_cast`),
with residual R(a) a rational quadratic polynomial. **Full NF**: one modulus M ≥ 1 and, for every residue class ρ,
a vector quadratic polynomial agreeing with f on ρ + Mℤⁿ (`FullVectorCosetNF`). **Weak NF**: the same on one class.

Branches (`branch_exhaustive`): Q ≡ 0; a non-radical isotropic vector; quotient-anisotropic and semidefinite; quotient-anisotropic
and indefinite. `generalFullNF_iff_branches` (s56) makes the general full NF the conjunction of the four branch statements.

## 1. Two branches are already full (A3, A4)

**Q ≡ 0** (`linearBranchFullNF_holds`). Then polar ≡ 0 (`zPolar_eq_zero_of_zQuadQ_zero`). With m ≥ 2 an output-unique
solution set forces m ≤ 1 (`m_le_one_of_linear`). With m = 1 the scalar relation already built for the weak form
(`weakVectorCosetNF_of_linearBranch`) is fed to the full no-witness theorem `nInputNoWitness_full` (of which the weak one was a
corollary) and to `fullVectorCosetNF_of_scalar`.

**Quotient-anisotropic indefinite** (`anisotropicIndefiniteFullNF_holds`). The proof of the weak form already shows that every
solution's off-centre vector z − c(a) lies in Rad (Pell contradiction). With that, `fullVectorCosetNF_of_offCentre_radical`
gives a global affine form. (The lemma used there, `fullVectorCosetNF_of_isotropic_fallback`, returns only the WEAK form despite
its name.) Hence `generalFullNF_iff_isotropic_and_semidefinite`, and with TCER `generalFullNF_iff_isotropic_of_TCER` [C].

## 2. Isotropic branch, polar rank ≥ 3: no off-radical solution (Eichler)

**Eichler transformation** (`zQuadQ_eichler`). If Q(e) = 0 and polar(e, v) = 0, then
  E(x) = x + polar(x,e)·v − (polar(x,v) + Q(v)·polar(x,e))·e
satisfies Q(E x) = Q(x). (Expand; the cross terms cancel because polar(v,e) = 0 and Q(e) = 0.)

**Output constraints** (`eichler_output_constraints`). Let z be an integer solution at input a, x = z − c(a). For t ∈ ℚ,
applying E with v replaced by t·v gives x + tA + t²B with A = polar(x,e)v − polar(x,v)e, B = −Q(v)polar(x,e)e, and
Q(x + tA + t²B) = Q(x) = R(a). Choose M ≥ 1 with MA, MB integral. Then z ± MA + M²B are integer solutions at the same input.
Output uniqueness at t = M and t = −M gives, for every output coordinate j, A_j = 0 and B_j = 0:
  polar(x,e)·v_j = polar(x,v)·e_j,   Q(v)·polar(x,e)·e_j = 0.                (★)
(No polynomial identity is needed; two points suffice.)

**Rank tests.** A non-radical isotropic e has an isotropic partner e' with polar(e, e') = 1 (`exists_isotropic_partner`).
If Q vanishes on {e, e'}^⊥ then every functional polar(u, ·) lies in the span of polar(e, ·), polar(e', ·), so d ≤ 2
(`polarRank_le_two_of_null_complement`); conversely an anisotropic w in that complement gives three independent functionals,
d ≥ 3 (`three_le_polarRank_of_complement`).

**Vanishing** (`outputs_vanish_on_perp`). Let d ≥ 3, Q(e) = 0, polar(x, e) ≠ 0. By the rank test there is w ⊥ e with Q(w) ≠ 0;
(★) with v = w gives e_j = 0, and then (★) gives v_j = 0 for every v ⊥ e.

**No off-radical solution** (`false_of_offRadical_of_three_le_polarRank`). Suppose x ∉ Rad. There is an isotropic e₁ with
polar(x, e₁) ≠ 0 (`exists_isotropic_nonorthogonal_of_nonradical`); take its partner e₂. We need a second isotropic e₃ with
polar(x, e₃) ≠ 0 and polar(e₁, e₃) ≠ 0. If polar(x, e₂) ≠ 0 take e₃ = e₂. Otherwise take w ⊥ e₁, e₂ with Q(w) ≠ 0 and
  e(s) = s·e₁ − (Q(w)/s)·e₂ + w:
Q(e(s)) = 0, polar(e₁, e(s)) = −Q(w)/s ≠ 0, polar(x, e(s)) = s·polar(x, e₁) + polar(x, w), non-zero for s = 1 or s = 2.
Both e₁^⊥ and e₃^⊥ then have zero output coordinates, and e₃ itself does; writing the unit vector of output 0 as
(u − γ e₃) + γ e₃ with u − γe₃ ⊥ e₁ gives 1 = 0.

**Consequence** (`isotropicBranchFullNF_of_three_le_polarRank`). All off-centre vectors lie in Rad, so
`fullVectorCosetNF_of_offCentre_radical` gives a global affine form.

(The reviewer's route compressed the radical and used hyperbolic coordinates; working in the original coordinates avoids the
isotropy-transfer and basis-construction obligations.)

## 3. Isotropic branch, polar rank ≤ 2: constant residual (scaling)

**Structure** (`hyperbolic_form_of_polarRank_le_two`). With e₁ = e₀ isotropic non-radical and its partner e₂, d ≤ 2 forces Q ≡ 0
on {e₁, e₂}^⊥ (else d ≥ 3), hence Q(u) = polar(u, e₂)·polar(u, e₁) and u − polar(u,e₂)e₁ − polar(u,e₁)e₂ ∈ Rad.
On X·e₁ + Y·e₂ + ρ (ρ radical) the form is X·Y (`zQuadQ_hyperbolic_section`).

**Divisor lemma** (`exists_scaling_divisor`). Let F(k) = αk² + βk + γ ∈ ℤ[k] with (α, β) ≠ (0, 0) and K ≥ 1. Pick k₁ ∈ {0,1,2}
with F(k₁) ≠ 0. For k₀ = k₁ + K·F(k₁)·s one has F(k₀) = F(k₁)·μ(s), μ(s) = 1 + sX + s²Y, X = K(2αk₁ + β), Y = αK²F(k₁),
(X, Y) ≠ (0, 0). Among s = 1..5 some μ(s) ∉ {0, 1} (linear arithmetic). Put λ = μ(s): λ ∉ {0,1}, λ ≡ 1 (mod K), λ | F(k₀);
then λ | F(k₀ + λj) for all j. (No prime-power roots, no Hensel lifting; λ may be negative.)

**Constant residual** (`constResidual_of_isotropic_polarRank_le_two`). Suppose R is not constant. Along an input line a = t·a₁,
R = At² + Bt + R(0) with (A, B) ≠ (0, 0); pick t₀ with R(t₀a₁) ≠ 0 and an integer solution z₀ there; x₀ = z₀ − c,
X₀ = polar(x₀, e₂) ≠ 0 (since X₀Y₀ = R ≠ 0), ρ₀ = x₀ − X₀e₁ − Y₀e₂ ∈ Rad. The section
  Z(t) = c(t a₁) + X₀ e₁ + (R(t a₁)/X₀) e₂ + ρ₀
solves the equation and is a rational quadratic in t through z₀; with t = t₀ + Mk it is integral for all k. Write
R/X₀ = F(k)/D' with F ∈ ℤ[k] non-constant. With K clearing X₀e₁ and e₂/D', take λ, k₀ from the divisor lemma and
k = k₀ + λj. The scaled point c + λX₀ e₁ + (F(k)/(λD')) e₂ + ρ₀ is again a solution (value λX₀ · F/(λD') = R), and it differs
from Z by ((λ−1)/K)·[K X₀ e₁] − ((λ−1)/K)(F/λ)·[K e₂/D'], an integer vector. Output uniqueness at output 0 (which sees e₁ or e₂:
the unit vector decomposes as polar(·,e₂)e₁ + polar(·,e₁)e₂ + radical, and radical vectors have zero outputs) gives
F(k₀ + λj)·e₂,₀ = λD'X₀·e₁,₀ for every j. If e₂,₀ = 0 this forces e₁,₀ = 0, impossible; otherwise F takes one value at three
points of the progression, so α = β = 0 (`quad_const_of_three`), impossible.

**Consequence** (`isotropicBranchFullNF_of_polarRank_le_two`). R is constant; the constant-residual transport
`constResidual_fullVectorCosetNF` (no definiteness hypothesis) gives the full NF with a common slope.

Controls (CAS, both legs, `s57_evidence/cas_s57/`): b(2u+1) = 0 is split rank 2 with R ≡ 0 and output unique, so the rank ≥ 3
impossibility does not extend to rank 2; (4b+1)(4u+1) = 1 has the single solution (0,0) and R ≡ 1, so "R ≡ 0" would be a false
strengthening.

## 4. Confluence

`isotropicBranchFullNF_holds` (d ≤ 2 or d ≥ 3). Hence, unconditionally,
  **GeneralFullNF ↔ SemidefiniteFullNF**                      (`generalFullNF_iff_semidefiniteFullNF`),
and with TCER (s56 `semidefiniteFullNF_allRanks_of_TCER`)
  **GeneralFullNF** [C]                                        (`generalFullNF_of_TCER`),
  **every f in the original class SingleQuadraticDefinableFunctionZZ has a full vector coset NF** [C]  (`sealedFullNF_of_TCER`),
with one modulus for all residue classes. The weak forms (`generalWeakNF_of_TCER`, `sealedWeakNF_of_TCER`, s56) follow.

## 5. The semidefinite branch of polar rank ≥ 3: where TCER enters

**Setting.** After the positive definite reduction (the radical is split off), Q is positive definite, m > 0, the centre
c(a) = c₀ + C·a is affine, and f is total and output-unique. Goal: R is constant (`ConstantResidualRigidity`); then
`constResidual_fullVectorCosetNF` gives the full NF. Polar rank 2 is settled without TCER (`rankTwo_CCR`). TCER enters only through
`ccr_of_TCER` → `semidefiniteFullNF_allRanks_of_TCER` [C]. Below S[x] = xᵀSx for an integral symmetric 3 × 3 matrix S, and
e₁ = (1, 0, 0).

**Step 0 (a line).** Let d ≥ 3 and suppose R is not constant. `residual_line_of_nonconstant` gives a₀, v and rationals A, B with
R(a₀ + tv) = At² + Bt + R(a₀) for all t ∈ ℤ and A > 0; R ≥ 0 at every input, since R(a) = Q(z − c(a)) for a solution z. Moving
along the line gives a₁ with R(a₁) > 0 (otherwise R vanishes at t = 0, 1, 2 and the quadratic is zero). If the discriminant of the
line at a₁ is zero, `discriminantZero_line_const` gives a contradiction. Otherwise Lemmas 5.1–5.5 give one input with two integer
solutions of different output (`lineCollision_rankThree_of_TCER` [C]), contradicting output uniqueness.

**Lemma 5.1 (fixed ternary slice; `fixedCoset_slice`).** Fix an output coordinate j₀ and an integer solution z₀ at a₁, with
R(a₁) > 0, A > 0 and non-zero discriminant along the line. There are a positive definite integral symmetric 3 × 3 matrix S,
integers d, M ≥ 1, a non-zero p ∈ ℤ³, integers A' > 0 and B' with B'² − 4A'·S[e₁] ≠ 0, and rationals α, β, γ with β ≠ 0, such that
for all k ∈ ℤ and x ∈ ℤ³:
  S[e₁ + dx] = A'(Mk)² + B'(Mk) + S[e₁]  ⟹  there is an integer solution z at input a₁ + Mk·v with
  z_{j₀} = α + β·(p · (e₁ + dx)) + γk.
One fixed coset e₁ + dℤ³ carries solutions along the whole line, and output j₀ is affine in p · (point) with non-zero slope β.
Only this implication is used; no totality of the ternary slice is assumed.

*Proof.* Put w = z₀ − c(a₁) ∈ ℚ^{m+r}.  Then Q(w) = R(a₁) > 0 (z₀ is a solution at a₁), so w ≠ 0; pick a coordinate k₁ with
w_{k₁} ≠ 0 and two further distinct coordinates k₂, k₃ (there are at least three, polar rank ≥ 3), chosen so that j₀ ∈
{k₁, k₂, k₃}.  Let d ≥ 1 be a common denominator of w (W = d w integral) and M ≥ 1 a common denominator of the centre drift
C v along the line (V = M · C v integral).  Define φ(ξ) = ξ₀ w + (ξ₁/d) e_{k₂} + (ξ₂/d) e_{k₃} for ξ ∈ ℤ³.  At
ξ = e₁ + d x, φ(ξ) = w + (d x₀ w + x₁ e_{k₂} + x₂ e_{k₃}), and the bracket Y is integral.  The rational ternary form
G(ξ) = Q(φ(ξ)) is positive definite (Q is, and φ is injective: w has a non-zero k₁-coordinate, k₁ ∉ {k₂, k₃}).  A common
denominator L of the coefficients of G and of the line data A_q, B_q gives the integral symmetric positive definite
S = L·G, A' = L·A_q > 0, B' = L·B_q, with S[e₁] = L·Q(w) = L·R(a₁) and B'² − 4A'S[e₁] = L²(B_q² − 4A_q R(a₁)) ≠ 0.
Return map: if S[e₁ + dx] = A'(Mk)² + B'(Mk) + S[e₁], divide by L: Q(φ(e₁ + dx)) = R(a₁ + Mk·v) by the line formula.  The
centre at a = a₁ + Mk·v is c(a₁) + k V, so z = z₀ + k V + Y is an integer vector with z − c(a) = w + Y = φ(e₁ + dx); hence
Q(z − c(a)) = R(a), i.e. z is a solution at a.  Its j₀-coordinate is z₀,j₀ + k V_{j₀} + Y_{j₀}, and
φ(ξ)_{j₀} = (1/d)(p · ξ) with p = (W_{j₀}, [k₂ = j₀], [k₃ = j₀]); so α = z₀,j₀ − w_{j₀}, β = 1/d ≠ 0, γ = V_{j₀}.  Finally
p ≠ 0: if j₀ = k₁ then W_{j₀} = d w_{k₁} ≠ 0, otherwise one indicator is 1.  □

**Lemma 5.2 (two cosets that separate the output; `twoVisibleCosets`).** For S, d, p as in 5.1 there are a prime
ℓ ∤ 2d·|det S|·S[e₁] and ρ₁, ρ₂ ∈ ℤ³ with ρ₁ ≡ ρ₂ ≡ e₁ (mod d), ρ₁ ≡ e₁ (mod ℓ), S[ρ₂] ≡ S[e₁] (mod ℓ) and
p · ρ₁ ≢ p · ρ₂ (mod ℓ). Both finer cosets ρᵢ + dℓℤ³ lie in e₁ + dℤ³, and p · (point) takes different values on them modulo ℓ.

*Proof.* Write B(x, y) = xᵀSy.  Choose w ∈ ℤ³ with p · w ≠ 0 and B(e₁, w) ≠ 0: w = e₁ if p · e₁ ≠ 0 (B(e₁, e₁) = S[e₁] > 0);
otherwise p₀ = 0 and p_j ≠ 0 for some j ≠ 0, and w = e_j if B(e₁, e_j) ≠ 0, else w = e₁ + e_j.  Then S[w] > 0.  Put
β = B(e₁, w) and take a prime ℓ larger than 2d·|det S|·S[e₁]·S[w]·|2β (p · w)| (all factors non-zero; det S ≠ 0 by
definiteness).  In 𝔽_ℓ let c̄ = 2β / S[w] and lift it to c' = d·u with u ≡ c̄/d (mod ℓ), so c' ≡ 0 (mod d), c' ≡ c̄ (mod ℓ).
Put ρ₁ = e₁ and ρ₂ = e₁ − c' w (the reflection of e₁ in w, reduced modulo ℓ).  Then ρ₂ ≡ e₁ (mod d);
S[ρ₂] = S[e₁] − c'(2β − c' S[w]) ≡ S[e₁] (mod ℓ); and p · ρ₁ − p · ρ₂ = c' (p · w) ≢ 0 (mod ℓ) because c̄ ≠ 0 and ℓ ∤ p · w.  □

**Lemma 5.3 (simultaneous local conditions with controlled valuations; `localProgression`).** For these data, any integers A, B,
any finite set `bad` of primes and any M ≥ 1, there is J ≥ 1 with M | J such that for every k ∈ ℤ the integer
N_k = A(Jk)² + B(Jk) + S[e₁]
is primitively represented by both cosets ρ₁ + dℓℤ³ and ρ₂ + dℓℤ³ modulo every prime power (`LocalPrimRep`: for every prime p and
every e there is a point of the coset, not divisible by p in every coordinate, whose value is ≡ N_k mod pᵉ), and
v_q(N_k) = v_q(S[e₁]) for every q ∈ bad.

*Proof.* Fix i₀ with (S e₁)_{i₀} ≠ 0 (S e₁ ≠ 0 since S[e₁] > 0).  Put D = dℓ, R = 2d|det S|, K = 2|D · 2(S e₁)_{i₀}| + 1,
Q = ∏_{q ∈ bad} q^{|S[e₁]|+1} and J = M ℓ R^K Q; then J ≥ 1 and M | J.  Valuations: q^{|S[e₁]|+1} | J, so
N_k ≡ S[e₁] (mod q^{|S[e₁]|+1}); since v_q(S[e₁]) ≤ |S[e₁]|, v_q(N_k) = v_q(S[e₁]) for q ∈ bad.  Local primitive
representation of N_k by each coset ρᵢ + Dℤ³, at every prime p and precision e (`b3_one`), in three cases; in each, a point y
of the coset with y primitive at p, S[y] ≡ N_k to sufficient precision, and a line t ↦ y + tD e_i whose linear coefficient
D·2(S y)_i has p-valuation g, is lifted by Hensel's lemma (`b3_hensel`: constant term divisible by p^{2g+1}); the lifted point
stays ≡ y (mod p), hence primitive.
(A) p | R.  By CRT (ℓ ∤ R, ρᵢ ≡ e₁ (mod d)) pick y ∈ ρᵢ + Dℤ³ with y ≡ e₁ (mod R^K).  Then S[y] ≡ S[e₁] ≡ N_k (mod R^K)
(R^K | J), y ≡ e₁ is primitive, and along e_{i₀} the linear coefficient is ≡ D·2(S e₁)_{i₀} ≠ 0 (mod R^K), so its valuation g
is at most |D·2(S e₁)_{i₀}| and K ≥ 2g + 1.
(B) p = ℓ.  y = ρᵢ: S[ρᵢ] ≡ S[e₁] ≡ N_k (mod ℓ) (ℓ | J; for ρ₁ ≡ e₁ (mod ℓ), for ρ₂ by 5.2), and ℓ ∤ S[e₁] makes y primitive.
As ℓ ∤ det S some (S y)_i is an ℓ-unit.  Along y + t·dℓ e_i, S − N_k = ℓ·(d²ℓ S[e_i] t² + d·2(S y)_i t + c'), and the
bracket has a unit linear coefficient (ℓ ∤ 2d): Hensel with g = 0 from t₀ = −c'·(d·2(S y)_i)^{-1}.
(C) p ∤ 2Dℓ det S (all other primes).  Chevalley–Warning gives x_h primitive with S[x_h] ≡ 0 (mod p); some (S x_h)_j is a unit.
v₀ = e_j + (N_k − S[e_j])·(2(S x_h)_j)^{-1} x_h has S[v₀] ≡ N_k (mod p) and is primitive (its polar pairing with x_h is a
unit).  With γD ≡ 1 (mod p), y = ρᵢ + D·γ(v₀ − ρᵢ) lies in the coset and y ≡ v₀ (mod p); then Hensel with g = 0 along a unit
direction of S y.  □

**Lemma 5.4 (escape from the exceptional square classes; `squareClassEscapeProgression`).** Let A > 0, c > 0, B² − 4Ac ≠ 0,
forbid ≥ 1, and E a finite set of positive integers. There are a prime q with q ∤ forbid, q ∤ 2A(B² − 4Ac), q ∤ e for e ∈ E, and
k₁ ∈ ℤ, such that for every k ≡ k₁ (mod q²) the value N = Ak² + Bk + c is non-zero, v_q(N) = 1, and N ≠ e·s² for every e ∈ E and
s ∈ ℚ (v_q(N) = 1 is odd while q ∤ e).

*Proof.* Put F(k) = Ak² + Bk + c, Δ = B² − 4Ac, P = 2|A|·|Δ|·forbid·∏_{e∈E} e, T = |B| + 1 and H = 1 + BPT + AcP²T²
(H ≥ 2).  Let q be the least prime factor of H.  Since H ≡ 1 (mod P), q ∤ P, so q ∤ forbid, q ∤ 2AΔ and q ∤ e for e ∈ E.
At k₀ = cPT, F(k₀) = c·H ≡ 0 (mod q), and (2Ak₀ + B)² = Δ + 4A F(k₀) ≡ Δ ≢ 0, so k₀ is a simple root modulo q.  If
q² | F(k₀) replace k₀ by k₁ = k₀ + q: F(k₀ + q) = F(k₀) + q(2Ak₀ + B) + q²A ≢ 0 (mod q²).  So v_q(F(k₁)) = 1.  For
k ≡ k₁ (mod q²), F(k) ≡ F(k₁) (mod q²) (the difference is q²·j·(2Ak₁ + B + Aq²j)), hence v_q(F(k)) = 1: F(k) ≠ 0, and
F(k) = e s² with s ∈ ℚ is impossible for q ∤ e, since v_q(e s²) = 2 v_q(s) is even.  □

**Lemma 5.5 (return to one input; `ternaryCosetCollision_of_TCER` [C]).** Assume TCER. For S positive definite, d ≥ 1, p ≠ 0,
A > 0 and B with B² − 4A·S[e₁] ≠ 0, and M ≥ 1, there are k ∈ ℤ and x, x' ∈ ℤ³ with
  S[e₁ + dx] = S[e₁ + dx'] = A(Mk)² + B(Mk) + S[e₁]   and   p · (e₁ + dx) ≠ p · (e₁ + dx').
*Proof.* Lemma 5.2 gives ℓ, ρ₁, ρ₂. TCER, applied to each coset ρᵢ + dℓℤ³, gives bad primes badᵢ and exceptional classes Eᵢ; these
depend only on the coset. Lemma 5.3 with bad = bad₁ ∪ bad₂ gives J. Take the valuation bound b(q) = v_q(S[e₁]); TCER then gives
thresholds N₁, N₂. Lemma 5.4, applied to k ↦ N_k with forbid = 1 and E = E₁ ∪ E₂, gives a residue class of k modulo q² on which
N_k lies in no exceptional class. Since A > 0, N_k exceeds N₁ and N₂ for large k in that class. At such a k, N_k is locally
primitively represented by both cosets (5.3), has the prescribed bad valuations (5.3), and lies in no exceptional class (5.4).
TCER therefore represents N_k by a point of each coset. Both points lie in e₁ + dℤ³, and their values of p · (point) differ
modulo ℓ (5.2). M | J gives the form A(Mk)² + B(Mk) + S[e₁]. The quantifiers run in the order of TCER: coset, then bad primes and
exceptional classes, then valuation bound, then threshold, then k. □

**Assembly.** Lemma 5.1 turns the two points of 5.5, applied with its A', B' and M, into two integer solutions at the same input
a₁ + Mk·v. Their outputs j₀ differ, because β ≠ 0 and the γk terms agree. This contradicts output uniqueness, so R is constant.
No arithmetic statement beyond TCER is assumed. In ordinary mathematics TCER is the consequence on p. 5 of the published version of
Kane–Kim (Selecta Math. 32 (2026) art. 5), specialized to the TCER convention in paper Lemma A.8 (adapter:
`correspondence/TCER_ADAPTER_s58.md`). In Lean it remains an explicit hypothesis, not an axiom.

## 6. The scalar classification (s59; `ScalarRoots`, `ScalarClassification`, `SlopeStructure`)

**Families.**  For F : ℤⁿ → ℤ: (C) a common slope, F(a + Mt) = F(a) + B·t; (Q) F is one rational polynomial of total degree
≤ 2 on ℤⁿ (`GlobalQuadratic`; rational coefficients are needed, e.g. a(a − 1)/2); (H) parity-affine (`ParityAffineNF`):
integer p, q ∈ ℤⁿ, c, c' with p ≡ q (mod 2), p ≢ 0 (mod 2), c − c' odd, and 2F(a) = p·a + c when p·a + c is even,
2F(a) = q·a + c' otherwise.  The families overlap.

**Theorem 6.1** (`scalar_singleQuadratic_iff_of_TCER` [C]).  TCER ⇒ (F is SE₂ ⟺ C ∨ Q ∨ H).  The reverse direction holds
without TCER (`singleQuadratic_of_scalarFamilies`), and for Q and H without witnesses (`zeroWitness_of_*`).

*Proof of ⇐.*  C: the R47 compiler.  Q: clear denominators, P = N b − (N q)(a) with N ≥ 1.  H: P = (2b − p·a − c)(2b − q·a − c');
since (p − q)·a + (c − c') is odd, exactly one factor can vanish at an integer b, and it vanishes exactly at b = F(a).

*Proof of ⇒.*  Take a datum D defining F (m = 1).
(i) Q ≢ 0 and polar rank ≥ 2 (`commonSlope_of_TCER_of_two_le_polarRank`): the four branch theorems need only m > 0 —
isotropic ⇒ polar rank ≤ 2 gives a common slope, ≥ 3 is empty; semidefinite ⇒ TCER; quotient-anisotropic indefinite ⇒ global
affine with integer coefficients.  So F ∈ C.
(ii) Q ≡ 0: the linear branch gives a witness-free relation a y² + (β·x + d)y + (xᵀEx + φ·x + g) = 0 (`Rn`) whose graph is
exactly that of F.  (In ordinary terms: if a witness had a non-zero coefficient at some input, the kernel of the linear system
would move the output; so all witness coefficients vanish identically.)
(iii) Q ≢ 0, polar rank ≤ 1: rank 0 would make every vector radical and Q ≡ 0, so the rank is 1; the witness directions are
radical (`witnessDir_inRadicalQ`), the witnesses drop out (`noWitnessData_defines`), and again F is the graph of an `Rn`.
(iv) `rn_classify`: an `Rn` that is the graph of F gives Q or H.  If a = 0 this is the old global-quadratic theorem.  If a ≠ 0,
the discriminant (2aF(x) + β·x + d)² is an integer affine square (ℓ·x + s)² (`c21_affine_square`, integrality as in
`n_a_ne_zero_full`), so y is a root iff 2a·y ∈ {u(x), v(x)}, u, v = −(β·x + d) ± (ℓ·x + s) (`rn_two_roots`).  If 2a divides
u(x) then 2aF(x) = u(x) (the quotient is a root; uniqueness); likewise v; one of them always holds.  Domains
I_u = {x : 2a | u(x)}, I_v cover ℤⁿ.  If they meet at x₀, both divisibilities hold on x₀ + 2aℤⁿ, u = v there, hence u ≡ v
(`affine_eq_of_eq_on_coset`) and F = u/(2a) is affine (Q).  If one is empty, F is affine (Q).  Otherwise they are disjoint
non-empty cosets of K_u = {h : 2a | U·h} and K_v, covering ℤⁿ; by the two-coset lemma (`addSubgroup_two_coset_cover`:
k ∈ K \ H forces b ∈ K and 0 ∈ b + K; h ∈ H \ K forces b ∈ H and b ∈ b + K) K_u = K_v has index 2 and contains 2ℤⁿ, so
a | Uᵢ and a | Vᵢ.  Writing U = a p, V = a q and u(x₀) = a(p·x₀ + c), v(y₀) = a(q·y₀ + c'), the domains are
{p·x + c even} and {q·x + c' even}; exactly one holds at 0 and at each eᵢ, so c − c' is odd and pᵢ ≡ qᵢ; a proper
non-empty domain forces some pᵢ odd.  So F ∈ H.  □

**Theorem 6.2** (`singleQuadratic_iff_commonSlope_of_TCER_of_ne_one` [C]).  For m ≠ 1: SE₂ ⟺ C (m = 0 trivially; m ≥ 2 is R47).

**Theorem 6.3** (`singleQuadratic_padZero_iff_of_TCER` [C], `commonSlope_padZero_iff` [P]).  (F, 0) is SE₂ iff F has a common
slope, for every m; a ↦ (a², 0) is the instance F = a² (no common slope: (a + M)² − a² is not constant).

**Theorem 6.4** (`commonSlope_comp` [P]).  If f has (M, B) and g has (N, C) then g ∘ f has (MN, CB):
f(a + MNt) = f(a) + N(Bt) and g(y + N s) = g(y) + C s.  This is not closure of SE₂ under composition.

**Theorem 6.5** (`slopeEncoder_eval_scale`, `slopeUnknownQuad_eq_zero`, `commonSlope_posDef_presentation` [P]).  The R47 encoder
is t²·Q_u + t·L + P₀ when its unknowns (b, u, e) are scaled by t, with Q_u = (Σe)² + Σe² + Σᵢ(M uᵢ + Σ ρᵢ e_ρ)²
+ Σⱼ(M bⱼ − Σ δ_{ρj} e_ρ)² positive definite over ℚ (Σe² = 0 ⇒ e = 0, then M u = M b = 0).  A common-slope function therefore
has a presentation whose quadratic part in the unknowns is positive definite and whose witnesses are unique — this
presentation only; nothing is claimed about an arbitrary presentation.
