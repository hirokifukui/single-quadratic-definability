# Companion proof note — the sharp injective dimension theorem for SE₂

*This is the note §4 of the manuscript refers to.  Every statement here is a Lean
theorem in the artifact; the Lean name is given in the margin of each claim.  The note is written
so that the mathematics can be followed without reading Lean.*

---

## 1. What is proved

Let SE₂ be the class of relations on ℤᵏ definable by a **single** polynomial equation with integer
coefficients, of total degree at most two, with an unrestricted finite number of existentially
quantified integer unknowns.  A total function `f : ℤⁿ → ℤᵐ` is SE₂-definable when its graph is.

> **Theorem A.**  If `f : ℤⁿ → ℤᵐ` is SE₂-definable and injective, then `n ≤ m`.
> `singleQuadratic_injective_dimension_sharp`

> **Theorem B (the structural alternative).**  If a single quadratic equation defines a total
> function `f : ℤⁿ → ℤᵐ`, then either `f` has **linear growth** — there is `C` with
> `‖f(a)‖∞ ≤ C(1 + ‖a‖∞)` for all `a` — or `f` has a **weak vector coset normal form**: there are
> `M ≥ 1`, `ρ ∈ ℤⁿ` and rational polynomials `q₁,…,q_m` of total degree at most two with
> `f(ρ + Mt)_j = q_j(t)` for every `t ∈ ℤⁿ` and every `j`.
> `summit_of_defines`

> **Theorem C (sharpness).**  An injective SE₂-definable `ℤⁿ → ℤᵐ` exists **iff** `n ≤ m`.
> `singleQuadratic_sharp_iff`

Theorem A follows from Theorem B by a box count in the linear-growth branch and a symmetric-point
collision in the polynomial-coset branch (§3).  Theorem B is the work, and §4 is its proof.

What Theorem A improves is the bound `n ≤ 2m`, which is what the growth theorem alone gives: the
images of a box of side `N` lie in a box of side quadratic in `N`, so the count only yields
`n ≤ 2m`.  The gain comes from showing that the quadratic case is not generic — when the output
really does grow quadratically, it does so *polynomially on a coset*.  The sharp bound then comes
from two different arguments, not from the growth constant: in the linear-growth case a box count
(Lemma 3.1), and in the coset case a collision `f(ρ + Mv) = f(ρ − Mv)` for a nonzero `v` in the
kernel of the linear part (Lemma 3.2), which uses no count at all.

---

## 2. Setup: the shape of the equation

Fix a defining equation `P = 0` where `P` has integer coefficients, total degree at most two, and
its variables are split into the input block `a ∈ ℤⁿ`, the output block `b ∈ ℤᵐ` and the unknown
block `u ∈ ℤʳ`.  Write `z = (b, u)` for the output-and-unknown block.

Because the total degree is at most two, `P` splits, with no choices made:

    P(a, z)  =  Q(z)  +  ℓ_a(z)  +  q(a)                                    `eval_split`

where

* `Q` is an integer quadratic form in `z` **alone** — its type contains no `a` at all;
* `ℓ_a` is linear in `z` with coefficients affine in `a`;
* `q` is a polynomial of degree at most two in `a` alone.

Two definitions that the whole argument turns on.  `B(v,w)` denotes the **polar form** of `Q`,
i.e. `B(v,w) = Q(v+w) − Q(v) − Q(w)`; note `B(v,v) = 2Q(v)`, and in this note `B` *is* the polar
form, with no factor of two removed.  A vector `e` is **radical** if `B(e, ·) ≡ 0`.  Radical
vectors are isotropic: `2Q(e) = B(e,e) = 0`.

`Defines f` means: for all `a, b`, there is `u` with `P(a, b, u) = 0` **iff** `b = f(a)`.  It
packages totality and output-uniqueness at once.  Output-uniqueness is about the whole `m`-vector;
it says nothing about the unknowns, and the proof never uses uniqueness of unknowns.

**The polar map and the annihilator.**  Over ℚ, let `p : V → V*` be the polar map `p(x) = B(x, ·)`,
where `V` is the rational span of the output-and-unknown block.  Two facts are used repeatedly and
are worth isolating, because everything about centres rests on them.

* `ker p = rad Q`, by the definition of radical.  `mem_ker_polarMapQ`
* **`im p = Ann(rad Q)`**: the image of the polar map is exactly the annihilator of the radical.
  One inclusion is immediate (`p(x)` kills the radical by symmetry of `B`); the other is
  rank–nullity applied twice, over ℚ, with **no hypothesis on the form**.
  `range_polarMapQ_le`, `range_polarMapQ_eq_dualAnnihilator_ker`

The consequence is the criterion this note uses whenever it says "centre": **a centre at input `a`
exists** exactly when `ℓ_a` annihilates the radical.  This characterises existence, not a given
vector — for `Q(x) = x²` and `ℓ_a = 0` the condition holds, yet `c = 1` is not a centre (the only
centre is `0`).  No rational
complement of the radical is chosen anywhere, and none is needed.
`isCentre_iff_lin_annihilates_radical`, `exists_centre_of_lin_annihilates_radical`

---

## 3. The two closing lemmas: a box count and a collision

> **Lemma 3.1.**  If `f` has linear growth and is injective, then `n ≤ m`.
> `dim_le_of_linearGrowth_injective`

*Proof.*  Linear growth means `‖f(a)‖∞ ≤ C(1 + ‖a‖∞)`.  The box `‖a‖∞ ≤ N` holds `(2N+1)ⁿ` lattice
points; their images lie in the box of radius `C(1+N)`, which holds `(2C(1+N)+1)ᵐ` points;
injectivity gives `(2N+1)ⁿ ≤ (2C(1+N)+1)ᵐ` (`box_card_le`).  This is checked
at the single value `N = (2C+1)ᵐ` — no limits and no asymptotics are needed, and the exponent on
the left is `n` and on the right `m`. ∎

> **Lemma 3.2.**  If `f` has a weak vector coset normal form and `m < n`, then `f` is not
> injective.  `not_injective_of_weakVectorCosetNF`

*Proof.*  Restrict to the coset `ρ + Mℤⁿ`, which carries as many points as `ℤⁿ` does.  On it each
output coordinate is a rational polynomial of degree ≤ 2 in `t`, so on `‖t‖∞ ≤ N` the images lie
in a box of side `O(N²)`, and the count `(2N+1)ⁿ ≤ (κN² + 1)ᵐ` forces only `n ≤ 2m`.  Counting
does not give the sharp bound, and the note does not pretend otherwise.  The sharp step is a
collision, and here it is in full.

Write the restriction to the coset as `f(ρ + Mt) = (p₁(t), …, p_m(t))` with

    p_j = c_j + L_j + H_j,      L_j linear over ℚ,  H_j homogeneous quadratic over ℚ.

Suppose `m < n`.  The linear map `L = (L₁, …, L_m) : ℚⁿ → ℚᵐ` then has a nonzero kernel; clearing
denominators gives `v ∈ ℤⁿ \ {0}` with `L(v) = 0`.  Since each `H_j` is homogeneous of degree two,
`H_j(−v) = H_j(v)`, so

    p_j(v) − p_j(−v) = 2 L_j(v) = 0      for every j,

that is `f(ρ + Mv) = f(ρ − Mv)`.  But `ρ + Mv ≠ ρ − Mv`, because `M ≥ 1` and `v ≠ 0`.  So `f` is
not injective.  No hypothesis on the discriminant, on a common centre of the quadratic parts, or
on the number of unknowns enters.  `exists_collision_vector`, `not_injective_of_weakVectorCosetNF` ∎

Combining: **Theorem B ⇒ Theorem A**, `dim_le_of_summit`.

---

## 4. The proof of Theorem B

### 4.0 The branch split

Everything is decided by the behaviour of `Q` **over ℚ**.  Working over ℚ rather than ℤ is what
makes the split exhaustive; the integrality is recovered later, in 4.2, by clearing denominators.

> **Lemma 4.0.**  At least one of the following holds; the cases COVER but are not
> pairwise disjoint — if `Q ≡ 0` then case 1 and case 3(a) both hold.  What
> `branch_exhaustive` proves is the covering disjunction, and every later step uses only
> that.  `branch_exhaustive`
> 1. `Q ≡ 0` on ℚ.
> 2. Some `x` has `Q(x) = 0` and `x` is **not** radical.
> 3. Every isotropic vector is radical, and then one of
>    (a) `Q ≥ 0`, (b) `Q ≤ 0`, (c) `Q` takes both signs.

A warning that cost us a rebuild: the branch conditions must be stated on the **form** `Q` and its
polar `B`, never on the coefficient matrix.  The matrix is not symmetric and the form only sees its
symmetric part, so "the matrix is zero" and "`Q ≡ 0`" are different statements.

### 4.1 The branch `Q ≡ 0`

Here the equation is linear in `z`: `ℓ_a(z) + q(a) = 0`.

First, the unknowns drop out.  Write the equation at a fixed input `a` as
`Σⱼ cⱼ(a)·bⱼ + Σₖ dₖ(a)·uₖ + q(a) = 0`.  Suppose some `dₖ(a) ≠ 0`, take an integer solution `z₀`,
pick an output coordinate `j`, and set

    e  =  dₖ(a)·e_{bⱼ}  −  cⱼ(a)·e_{uₖ}.

The linear form evaluates to `0` on `e`, so `z₀` and `z₀ + e` are both solutions; but their `j`-th
output coordinates differ by `dₖ(a) ≠ 0`.  That contradicts output-uniqueness, so every witness
coefficient vanishes at every input.  The point to keep is that the kernel vector has to **move the
output** — a vector that moves only an unknown proves nothing, because two witnesses over the same
output are permitted.  `witnessCoeff_eq_zero`

What remains is `h(a)·b + q(a) = 0` with `m` output coordinates; if `m > 1` the output coefficient
form `ℤᵐ → ℤ` has a nonzero integer kernel and the same collision reappears, so `m ≤ 1`.
`m_le_one_of_linear`

* `m = 0`: nothing to prove; the coset normal form is vacuous.  `weakVectorCosetNF_of_m_zero`
* `m = 1`: the equation is `h(a)·b = −q(a)` with `h(a) = β·a + d` an **affine** form.  Totality and
  output-uniqueness give `h(a) ≠ 0` at every integer input and `h(a) ∣ q(a)` there — but `h` must
  **not** be assumed constant; `P(a,b) = (2a+1)(b−a)` is total and output-unique with the
  non-constant divisor `h(a) = 2a+1`.  Two cases.

  *`β = 0`.*  Then `h ≡ d ≠ 0` and `f(a) = −q(a)/d` is a rational polynomial of degree at most two
  on the whole lattice.

  *`β ≠ 0`.*  Choose a coordinate with `βᵢ = p ≠ 0`, write `t = aᵢ` and let `x` be the remaining
  inputs, so `h = p·t + h₀(x)` and `q = A·t² + q₁(x)·t + q₀(x)` with `A` constant and `h₀, q₁`
  affine in `x`.  Division without denominators gives the polynomial identity

      p²·q(t,x)  =  (p·A·t + p·q₁(x) − A·h₀(x))·h(t,x)
                    +  [ p²·q₀(x) − p·q₁(x)·h₀(x) + A·h₀(x)² ].

  The bracket does not depend on `t`.  Since `h(t,x)` divides `q(t,x)` at every integer `t`, it
  divides the bracket as well; and `|h(t,x)| → ∞` along `t`, so a fixed integer divisible by all of
  them is `0`.  Hence the bracket vanishes and

      f(t,x)  =  −(p·A·t + p·q₁(x) − A·h₀(x)) / p²

  is a rational **affine** function on the whole lattice.

  Either way the branch lands on a global rational polynomial of degree at most two — a coset normal
  form with `M = 1`.  `weakVectorCosetNF_of_linearBranch`

So this branch lands on the **right** disjunct.  It cannot land on the left: `b − a² = 0` is a
`Q ≡ 0` equation defining `f(a) = a²`, which has no linear bound.
`qZeroBranch_cannot_go_left`

### 4.2 The branch with a non-radical isotropic direction

This is the branch where the coset normal form has to be constructed rather than read off.

**Step 1 — a centre.**  Under output-uniqueness, `ℓ_a` kills every radical vector.
`zLinQ_radicalQ_eq_zero`  Over ℚ the image of the polar map is exactly the annihilator of the
radical, so `ℓ_a` is in the image: there is `c(a)` with `B(c(a), ·) = −ℓ_a`.  Solving the linear
system once, uniformly in `a`, gives a **centre family affine in `a`**:
`c(a) = c₀ + Σ aᵢ·cᵢ`.  `exists_affine_centre_of_all_inputs`

Completing the square at the centre turns the equation into

    Q(z − c(a))  =  R(a),        R of degree ≤ 2 in a.                      `completeSquare`

So every integer solution sits at "squared distance" exactly `R(a)` from the centre.

**Step 1b — the dichotomy.**  Entering this branch means *some* rational vector is isotropic and
not radical.  It does **not** mean that some *integer solution* has a non-radical off-centre part,
and the section of Step 2 needs the latter.  So split, and take both halves:

* *(a) every integer solution has `z − c(a) ∈ rad Q`.*  Then the output cannot see the off-centre
  part at all: `π(rad Q) = 0`, so `f(a) = π c(a)`, which is affine in `a`.  This half lands on the
  left disjunct with modulus `1` and needs no section.  `linearGrowth_of_offCentre_radical`,
  `affine_of_offCentre_radical`
* *(b) some integer solution `z₀` at some input `a₀` has a non-radical off-centre part.*  Only here
  is Step 2 available, and only here is it needed.

Stating (b) alone and "choosing" a non-radical `v₀` is a proof with (a) dropped.

**Step 2 — the section (case (b) only).**  Let `v₀ = z₀ − c(a₀)` be that non-radical off-centre
part, and let `e` be isotropic with `B(v₀, e) ≠ 0` — such an `e` exists by sliding the given
isotropic vector along a direction seen by both.
`exists_isotropic_nonorthogonal_of_nonradical`

Because `Q(e) = 0`, the line `v₀ + t·e` keeps `Q` affine in `t`:
`Q(v₀ + te) = Q(v₀) + t·B(v₀, e)`.  Choosing

    t(a) = (R(a) − R(a₀)) / B(v₀, e)

gives a **rational** solution at *every* input `a`:  `z(a) = c(a) + v₀ + t(a)·e`.
`exists_rational_solution_of_isotropic`

The denominator is `B(v₀, e)` — the polar form, not half of it.  Copying a convention in which the
bilinear form satisfies `polar = 2B` would insert a spurious factor of two and break the identity.

Each coordinate of `z(a)` is a rational polynomial of degree at most two in `a`: `c(a)` is affine,
`R(a)` is quadratic, `e` and `v₀` are constant.  `isQuadCoef_isoSection`

**Step 3 — clearing denominators.**  The section is rational, not integral.  Let `M ≥ 1` clear all
the denominators occurring in its coefficients; `M` is fixed once, from the finitely many
coefficients of the section, before `t` ranges over `ℤⁿ`.  On the coset `ρ + Mℤⁿ` — where `ρ` is the input of the
anchoring solution — the shifted polynomial has integer coefficients, because the shift identity

    q(ρ + M·t) = (q.shift ρ M)(t)                                            `eval_shift`

is an **exact identity**, not a congruence: the constant term is `q(ρ)` and the other coefficients
carry explicit factors of `M` and `M²`.  Packaging it as an identity rather than as "congruent mod
M" removes the integrality side-condition downstream.

**Step 4 — the section is the output.**  On that coset the section takes integer values and solves
the equation, so by **output-uniqueness** it *is* the output.  (Output-uniqueness is used
essentially elsewhere too: it kills the witness coefficients in §4.1, it gives the centre in Step 1,
and it is what the Pell collision of §4.5 contradicts.)
`weakVectorCosetNF_of_rational_section`, `weakVectorCosetNF_of_isotropic`

So this branch lands on the **right** disjunct.

### 4.3 The semidefinite branch `Q ≥ 0`

Here every isotropic vector is radical, and `Q` is non-negative on ℚ.

The centre of 4.2 Step 1 exists for the same reason, and completing the square gives
`Q(z − c(a)) = R(a)` with `R` quadratic in `a`.  Semidefiniteness gives a Cauchy–Schwarz
inequality for `B` on the quotient by the radical, and the output coordinates can be represented
by vectors `w_j` with `B(w_j, v) = v_j`.  `exists_polar_representative`

Then for a solution `z` with off-centre part `v`,

    |f(a)_j|  =  |B(w_j, v) + (centre term)|  ≤  2·√(Q(w_j)) · √(Q(v)) + |c(a)_j|
              =  2·√(Q(w_j)) · √(R(a)) + |c(a)_j|.

**The factor 2 is not decoration.**  In this note `B` is the polar form with no factor of two
removed (see the conventions above), so Cauchy–Schwarz for `B` reads `B(v,w)² ≤ 4·Q(v)·Q(w)`, i.e.
`|B(v,w)| ≤ 2·√(Q(v))·√(Q(w))`.  With coefficient `1` the inequality is FALSE: take `Q(x) = x²`,
`w = 1/2`, `v = 1`, where `B(w,v) = 1` while `√(Q(w))·√(Q(v)) = 1/2`.  The formal proof carries the
squared form with coefficient `4` and is correct.  `outCoord_sq_le`

Now the growth.  `R` is quadratic, so `R(a) ≤ C_R·(1 + ‖a‖∞)²` with `C_R` the sum of the absolute
values of its coefficients, hence `√(R(a)) ≤ √(C_R)·(1 + ‖a‖∞)`; and `c` is affine, so
`|c(a)_j| ≤ C_j·(1 + ‖a‖∞)`.  The right-hand side is therefore bounded by a linear function of
`‖a‖∞`.  What is claimed is this **upper bound**, not the identity "the square root of a quadratic
is linear", which is false as an identity.  `linearGrowth_of_semidefinite_defines`

Two traps were paid for here.  First, the analytic input has to be stated with a **rational**
constant: a single integer constant is unsatisfiable for sheared definite forms — `(x−2y)² + y²`
has `Q(2,1) = 1` but `‖(2,1)‖∞² = 4`, and the minimum ratio is `1/5`.  The hypothesis is therefore
`c·‖z‖∞² ≤ N·Q(z)` with **integers** `c ≥ 1`, `N ≥ 1` (`LatticeCoercive c N`), i.e. the rational
constant `c/N`.  Second, no square roots appear in the formal proof.  Multiplying the equation by
`N` and bounding coefficients gives, with `s = ‖z‖∞`,
`c·s² ≤ B·s + C` where `B = N·Λ·(1+‖a‖∞) ≥ 0`, `C = N·A·(1+‖a‖∞)²`, and `C ≤ K²` for
`K = (N·A+1)(1+‖a‖∞) ≥ 0` (`Λ`, `A` the coefficient sums).  The integer lemma used is: **for integers
with `c ≥ 1`, `s ≥ 0`, `B ≥ 0`, `K ≥ 0` and `C ≤ K²`, `c·s² ≤ B·s + C` implies `s ≤ B + K`.**
The formal proof uses these hypotheses.  The bound `c ≥ 1` cannot be weakened:
`c = 0, s = 2, B = 0, C = K = 1` violates the conclusion, and so does `c = 1/4` with the same
`s, B, C, K`.  `le_of_sq_le`, `supNorm_le_of_coercive`

So this branch lands on the **left** disjunct.

### 4.4 The negative-semidefinite branch `Q ≤ 0`

Negating the whole equation gives a graph with the same solution set and the opposite form:
`negGraph_eval`, `negGraph_defines`, `negGraph_zQuadQ`.  Apply 4.3 to it.  Four lines.
`linearGrowth_of_negSemidefinite_defines`

The content of the trap this control guards: "semidefinite" in ordinary usage covers both signs,
but the theorem of 4.3 knows only `Q ≥ 0`.  Reversing the *form* without reversing the *equation*
would change the solution set.

### 4.5 The quotient-anisotropic branch

`Q` takes both signs, and every isotropic vector is radical.

Suppose some integer solution has a **non-radical** off-centre part `v`.  Quotient-anisotropy gives
`Q(v) ≠ 0`.  Since `Q` takes both signs, one can find `u` with `Q(u)` of the sign opposite to
`Q(v)`, and then a vector `w` orthogonal to `v` with `Q(w)` of opposite sign such that **`v` and `w`
are not both invisible**: `π(v) ≠ 0` or `π(w) ≠ 0`, where `π` is the projection to the output
coordinates.  One cannot ask for `w` alone to be visible: for `Q(b,u) = b² − 2u²` and `v = (1,0)`
every `w` orthogonal to `v` has `π(w) = 0` (there `v` is the visible one).
`exists_visible_orthogonal`

On the rational plane spanned by `v, w`, the equation `Q(x) = R(a)` restricts to a binary form of
non-square discriminant: a **Pell conic**.  The non-squareness is not quoted from the literature;
it is proved here from quotient-anisotropy, and constructively: if `d = −Q(v)Q(w)` were `s²`, then
`e = s·v + Q(v)·w` satisfies `Q(e) = Q(v)(s² + Q(v)Q(w)) = 0` while `B(e, v) = 2sQ(v) ≠ 0`, so `e`
is isotropic and not radical — which is exactly what this branch forbids.
`not_isSquare_of_quotientAnisotropic`, `not_isSquare_pellDiscr`

Its integer points are permuted by the units of the
associated quadratic order, and one can choose a nontrivial positive unit congruent to 1 modulo any
prescribed `N` — proved by pigeonhole in the finite ring `ZMod N × ZMod N`, with no continued
fractions and no fundamental unit.  `exists_pell_unit_congr`

**The return to the original lattice, written out.**  The input `a₀` is **fixed** throughout; what
moves is `z`, the output and the witnesses together, never the input.  (Moving the witnesses alone
could not produce two different outputs.)  Put `A = h·Q(v)` and `B_w = h·Q(w)` with `h ≥ 1`
clearing denominators, so `Δ = −A·B_w > 0`, and let `X² − Δ·Y² = 1` be the unit of the previous
paragraph, chosen with `X ≡ 1` and `Y ≡ 0` modulo the `N` that clears the denominators of `v` and
`w`.  Then

    z±  =  c + X·v ± A·Y·w  =  z₀ + (X − 1)·v ± A·Y·w

is **integral** — the congruence, not the mere existence of a rational point, is what puts it back
on the lattice — and, by `B(v, w) = 0`,

    Q(X·v ± A·Y·w)  =  Q(v)·(X² − Δ·Y²)  =  Q(v),

so `z₊`, `z₋` and `z₀` are all solutions at the same input `a₀`.  Their outputs cannot all agree:
if `π w ≠ 0` then `z₊` and `z₋` differ in the output by `2·A·Y·π w ≠ 0`; if `π w = 0` then `π v ≠ 0`
and `z₊` differs from `z₀` by `(X − 1)·π v ≠ 0`.  Either way output-uniqueness fails.
`pell_two_step_obstruction` carries the same obstruction in the formal proof through the
determinant `2S₁(1 − T₁) ≠ 0` of the two-step displacement.  Contradiction.
`pell_branch_contradiction`

Hence **every** off-centre part is radical, so the output is the centre's output, which is affine
in `a`.  `linearGrowth_of_offCentre_radical`

So this branch lands on the **left** disjunct.

### 4.5b The boundaries `n = 0` and `m = 0`

Neither boundary is a degenerate case to be waved through, and both are in the Lean.

* **`m = 0`.**  The output vector is empty, so output-uniqueness holds vacuously
  (`outputUnique_of_m_zero`) and the coset normal form holds with the empty family of
  polynomials (`weakVectorCosetNF_of_m_zero`).  The dimension conclusion `n ≤ 0` is **not** a
  consequence of `m = 0` alone: an empty output constrains nothing about the input dimension, and
  the constant map `ℤⁿ → ℤ⁰` exists for every `n`.  `n ≤ 0` is the conclusion of the sharpness
  statement, whose hypothesis includes **injectivity**; with `m = 0` an injective `ℤⁿ → ℤ⁰` forces
  `n = 0` because the domain must be a single point.  It is the injectivity hypothesis, not the
  boundary convention, that supplies the bound.
* **`n = 0`.**  The input space is a single point, so every function on it is constant and hence
  globally a polynomial of degree ≤ 2 (`globalQuadratic_of_zero`).  The dimension conclusion
  `0 ≤ m` holds because `m` is a natural number; nothing about the map is used.
* **Existence at the boundary.**  The sufficiency direction of the sharpness statement is
  zero-padding `a ↦ (a₁, …, a_n, 0, …, 0)`, whose graph is defined by a single quadratic equation
  with **no unknowns**; it covers `n = 0` and `m = 0` with no separate construction.
  `exists_graph_injective_pad`

### 4.6 Assembly

Four of the five landings need no branch data beyond what `branch_exhaustive` supplies; the
isotropic and Pell branches build their own centre family and their own visible directions inside.
`summit_of_isotropicBranch`, `summit_of_quotientAnisotropicBranch`, `summit_of_defines`

---

## 5. Sharpness, and the coding arity

For `n ≤ m`, zero-padding is SE₂-definable with **no unknowns**: `Σ_j (b_j − pad(a)_j)² = 0` is a
single equation of total degree two, and it is total, output-unique and injective.
`pad_singleQuadratic`, `pad_injective`, `exists_graph_injective_pad`

With Theorem A this gives Theorem C, the `iff`, and hence sharpness at every pair `n ≤ m` — not
only on the diagonal.  `singleQuadratic_sharp_iff`

At `m = 1`, Theorem A gives `n ≤ 1`, so the one-sorted coding arity is exactly one:
`atomGraphZZ_le_one`, `not_atomGraphZZ_two`, `atomGraphZZ_capacity_eq_one`.

**This is a ℤ statement and does not transfer to ℕ.**  Over ℕ-inputs the coding arity at degree two
is 2, witnessed by the Cantor pairing.  Both facts hold simultaneously — `AtomGraphZ 2 2` and
`¬ AtomGraphZZ 2 2` — and that is itself a theorem: `natInput_intInput_separation_at_two`.  So the conclusion does not transfer to ℕ-inputs; this note does not
identify a single step of §4 that fails there.  In particular the Pell argument of §4.5 does not
"leave the domain": it keeps the input `a₀` fixed and moves only the unknowns, which range over ℤ in
both semantics.

---

## 6. What the proof does **not** use

This section is the hidden-hypothesis audit.  The claim is not "we did not mean to use them" but
"they do not appear in the type", which is checked by printing the full statements.

`singleQuadratic_injective_dimension_sharp` and `summit_of_defines` have, beyond `Defines f` and
(for the former) injectivity, **no** hypotheses.  In particular:

| not used | where one might have expected it |
|---|---|
| nondegeneracy of `Q` | 4.2, 4.3 — both are stated without it |
| a bound on the number of unknowns `r` | everywhere; `r` is arbitrary and appears in no bound |
| `0 < m` | it is a *case*, not a hypothesis; `m = 0` is handled |
| a coercivity certificate | 4.3 constructs its constant |
| a normal form assumed in advance | 4.2 constructs one; it is a conclusion, not an input |
| uniqueness of the unknowns | never — two witnesses over the same output are permitted. Output-uniqueness, by contrast, is used throughout: it kills the witness coefficients in 4.1, it forces the centre in 4.2 Step 1, it identifies the section with `f` in 4.2 Step 4, and it is the contradiction in the Pell branch 4.5 |
| any field or characteristic hypothesis | the ℚ layer is a proof device; the statements are over ℤ |
| a discriminant hypothesis | 4.5 replaces it with the Pell argument |

Axiom footprint: `[propext, Classical.choice, Quot.sound]` — the three standard axioms — for every
theorem named in this note.  Several branch capstones use `Classical.choice` through `choose` and
`by_cases`; the proofs are therefore not constructive, and this is disclosed rather than hidden.
No `sorry`, no `native_decide`, no added axiom anywhere in the development.

There are two assemblies of the same branch split: one closes each branch at `n ≤ m` directly,
the other closes each branch at a disjunct of Theorem B and then applies §3 once — the count for
linear growth, the collision for the coset normal form.  They agree, but they are **not**
independent proofs: both rest on `branch_exhaustive` and on the same per-branch leaves of §4.
`dim_le_of_defines`, `dim_le_of_defines_via_summit`

---

## 7. Attribution

The case `n = 2`, `m = 1`, no unknowns, with the defined function **itself a polynomial**, is
classical: Lew and Rosenberg prove that no quadratic storing function exists on ℤ²
[LR78a, Theorem 5.3(2)].  Their proof is three lines and uses only integer-valuedness, and its
method is the collision of §3: with linear part `L(x,y) = a₁₀x + a₀₁y`, the vector
`v = (2a₀₁, −2a₁₀)` lies in `ker L`, and `f(v) = f(−v)` because the quadratic part is even (if
`L = 0` then `f(x,y) = f(−x,−y)` outright).  So at `(n, m, r) = (2, 1, 0)` neither the result nor the
`±`-kernel method is new here.  The proof carries no density and no discriminant hypothesis, although both their abstract and the review in [LR78b]
describe it as if it did.  The restriction of the same question to the lattice points of an affine
convex cone, under a nonzero-discriminant hypothesis, is [Gj21, Theorem 2].

Neither reaches Theorem A even at `n = 2, m = 1`, for two reasons.  **Unknowns**: neither paper
admits existential quantifiers.  **Non-polynomial outputs**: a function with SE₂-definable graph
need not be a polynomial.  The equation

    4b² − (4a+2)b + (a² + a) = 0,   equivalently   (2b − a)(2b − a − 1) = 0,

is total and output-unique over ℤ — exactly one of `2b = a`, `2b = a+1` is solvable, by parity —
and defines `a ↦ ⌈a/2⌉`.  What is **formalised** is that this function is not given by a rational
polynomial of degree at most two (`parity_not_quadratic`); that is the statement the dichotomy
needs.  That it is not a polynomial of any degree is true and elementary — a polynomial agreeing
with `⌈a/2⌉` on ℤ would have to agree with the two affine branches on two infinite sets, and the
difference of the two branches has finitely many zeros — but it is a remark of ordinary
mathematics here, not a Lean theorem.  `parity_exists_unique`, `parity_not_quadratic`

[DLS64]'s square-values corollary — a polynomial that takes `k`-th power values on an integer in
every arithmetic progression is a `k`-th power identically — is cited as **background** and is
**not used** by §4.5: the non-squareness there is proved internally from quotient-anisotropy with
an explicit forbidden vector (`not_isSquare_pellDiscr`).  Erratum E-22-8.  [DLS66] is a different
theorem (parametric solvability) and is cited only for the pointer it gives to [DLS64].

The mixed-semantics value 2 is Fueter–Pólya's classification of quadratic packing functions on ℕ²
[FP23] in its modern form; it is the reason §5 insists the two semantics be kept apart.

---

## 8. Lean anchors

Every claim above is a theorem in the artifact.  The full axiom report is
`certificates/FinalAxiomReport_current.log` together with the ResearchUpgrade report produced by
`scripts/ResearchUpgradeAxiomReport.lean` (`logs/ru_axioms.log` in the clean-room record).  Names used in this note, in order of appearance:

`eval_split`, `dim_le_of_linearGrowth_injective`, `not_injective_of_weakVectorCosetNF`,
`dim_le_of_summit`, `branch_exhaustive`, `witnessCoeff_eq_zero`, `m_le_one_of_linear`,
`weakVectorCosetNF_of_m_zero`, `weakVectorCosetNF_of_linearBranch`, `qZeroBranch_cannot_go_left`,
`zLinQ_radicalQ_eq_zero`, `exists_affine_centre_of_all_inputs`, `completeSquare`,
`exists_isotropic_nonorthogonal_of_nonradical`, `exists_rational_solution_of_isotropic`,
`isQuadCoef_isoSection`, `eval_shift`, `weakVectorCosetNF_of_rational_section`,
`weakVectorCosetNF_of_isotropic`, `exists_polar_representative`,
`linearGrowth_of_semidefinite_defines`, `le_of_sq_le`, `negGraph_eval`, `negGraph_defines`,
`negGraph_zQuadQ`, `linearGrowth_of_negSemidefinite_defines`, `exists_visible_orthogonal`,
`exists_pell_unit_congr`, `pell_two_step_obstruction`, `pell_branch_contradiction`,
`linearGrowth_of_offCentre_radical`, `summit_of_isotropicBranch`,
`summit_of_quotientAnisotropicBranch`, `summit_of_defines`, `pad_singleQuadratic`,
`pad_injective`, `exists_graph_injective_pad`, `singleQuadratic_sharp_iff`, `atomGraphZZ_le_one`,
`not_atomGraphZZ_two`, `atomGraphZZ_capacity_eq_one`, `natInput_intInput_separation_at_two`,
`dim_le_of_defines`, `dim_le_of_defines_via_summit`, `parity_exists_unique`,
`parity_not_quadratic`, `singleQuadratic_injective_dimension_sharp`.

---

## 9. Status of this draft

Written in s48, after the ruling of 2026-09-13.  **Not sealed, not posted.**  Two items in it are
stated but not formalised, and are flagged here rather than in a footnote:

Revised in s51.  Both items flagged in the s48 draft are now closed, and one of them was a
mis-attribution rather than a gap.

1. §3 Lemma 3.2's sharp step is now written out in full above, in the same form as the
   corresponding paragraph of the paper.  `exists_collision_vector`,
   `not_injective_of_weakVectorCosetNF`
2. **The square-values lemma of [DLS64] is NOT used.**  The s48 draft said §4.5 depended on it;
   that was wrong.  A search of the whole Lean source for `Davenport`, `DLS`, `square_values`
   returns nothing, and §4.5's non-squareness is proved internally from quotient-anisotropy with
   an explicit forbidden vector (`not_isSquare_pellDiscr`).  [DLS64] is retained in the paper as
   background on square values of quadratic polynomials, and is cited as such.  Recorded as
   erratum E-22-8.

One further note on the r41 mathematics, so that this text is not read as more than it is: §4.2
and §4.5 describe the landings as of r40.  (Both fallbacks named below close through one shared leaf,
`fullVectorCosetNF_of_isotropic_fallback`.)  Since then the two fallbacks in those branches — the
case where every off-centre part is radical — have been shown to carry an explicit affine normal
form with modulus 1, so they land on the RIGHT disjunct as well as the left.  The branch logic of
this note is unaffected; the conclusion in those cases is simply stronger than stated here.
`affine_of_offCentre_radical`, `fullVectorCosetNF_of_offCentre_radical`

Revised in s53: §10 added (unknown compression, R41-C2; the positive definite reduction, R41-C3).
Sections 1–9 are unchanged.

---

## 10. Unknown compression and the positive definite reduction (added in s53)

This section records two results that sit beside Theorem B rather than inside it.  Throughout,
`Defines f` holds, `m ≥ 1`, and `Q` is not the zero form on integer vectors.  `B` is the polar form
of §2 (no factor of two removed), `V = ℚ^(m+r)`, and

    d  =  rank B  =  dim V − dim rad Q.

This is the rank of the polar form, not of the (non-symmetric) coefficient matrix of `P`.

### 10.1 `m ≤ d ≤ m + r`

By §4 the output coordinates of every radical vector vanish (`outCoordQ_radicalQ_eq_zero`), so
`rad Q` lies in the kernel of the projection `π : V → ℚᵐ` onto the output block.  That kernel has
dimension `r`, hence `m + r − d = dim rad Q ≤ r`.  `m_le_polarRank`, `polarRank_le`

### 10.2 The radical unknown lattice

Let `L = {u ∈ ℤʳ : (0, u) ∈ rad Q}`.  It is a subgroup of `ℤʳ`, and it is **saturated**: if
`c·u ∈ L` with `c ≠ 0` then `u ∈ L`, because `rad Q` is a ℚ-subspace.  `witRadLattice_saturated`

Take a Smith normal form of `L ⊆ ℤʳ`: a basis `e₁, …, e_r` of `ℤʳ`, an injection `σ` of
`{1, …, k}` into the indices, and nonzero integers `α_i` such that the vectors `α_i e_σ(i)` form a
basis of `L`.  Saturation puts each `e_σ(i)` itself in `L` (`snf_mem`), so the `e_σ(i)` span `L`
over ℤ (`snf_span`); equivalently each `α_i` is a unit (`smith_isUnit_of_saturated`).  Clearing
denominators from a rational basis of `rad Q` would give a sublattice of finite index in `L`, not
`L`; the saturation step is what makes the change of basis below a bijection of `ℤʳ`.

### 10.3 `k = m + r − d`

The vectors `(0, e_σ(i))` span `rad Q` over ℚ.  Each lies in `rad Q`.  Conversely, for `x ∈ rad Q`
the output block of `x` is zero (10.1); clearing denominators gives `N·x = (0, u)` with `N ≥ 1` and
`u ∈ L`, and `u` is an integer combination of the `e_σ(i)`.  The vectors are ℚ-independent: a
rational relation, multiplied by a common denominator, is an integer relation among members of a
basis of `ℤʳ`.  Hence `dim rad Q = k` and `d + k = m + r`.
`snfSpanQ_injective`, `range_snfSpanQ`, `polarRank_add_snfRank`

### 10.4 The change of unknown coordinates

Order the basis so that the `r − k = d − m` vectors `e_j` with `j` outside the image of `σ` come
first and the `m + r − d` vectors `e_σ(i)` come last, and let

    U : ℤ^(d−m) × ℤ^(m+r−d) → ℤʳ,    U(v, w) = Σ v_j e′_j + Σ w_i e″_i .

`U` is a ℤ-linear bijection (it is a change of basis), it acts on the unknown block only, and
`U(0, w) ∈ L`.  For `u′ ∈ L` the vector `x = (0, u′)` is radical, so
`Q(y + x) = Q(y) + B(y, x) + Q(x) = Q(y)` (with `2Q(x) = B(x, x) = 0`), and `ℓ_a(x) = 0` by
output uniqueness (§4.1, `zLinQ_radicalQ_eq_zero`).  Therefore `P(a, b, u + u′) = P(a, b, u)`
(`eval_add_radWit`), and

    P(a, b, U(v, w))  =  P(a, b, U(v, 0))      for all a, b, v, w.        `exists_witnessCompiler`

### 10.5 The compiled equation

Put `P_red(a, b, v) = P(a, b, U(v, 0))`.  This is a linear substitution of variables, so `P_red`
has integer coefficients and total degree at most two.  `IntQuad.pull`, `IntQuad.eval_pull`,
`compiledData_totalDegree_le_two`

Since `U` is a bijection of `ℤʳ`,

    ∃u P(a,b,u) = 0   ⟺   ∃(v,w) P(a,b,U(v,w)) = 0   ⟺   ∃v P_red(a,b,v) = 0.

Inputs and outputs are not touched, so `P_red` has the same graph and defines the same `f`, with
`d − m` unknowns.  `compiledData_graph_iff`, `compiledData_defines`, `rankExcess_compiler`

`d − m` is the number of unknowns of **this** presentation, not the least number of unknowns with
which the graph can be defined.  In `(b − a)² + (u₁ + u₂)² = 0` one has `m = 1`, `r = 2`, `d = 2`;
the change `u₁ = v + w`, `u₂ = −w` (determinant `−1`) gives `(b − a)² + v² = 0`, while `b − a = 0`
defines the same graph with no unknown at all.
`exD_polarRank`, `exD_graph_iff_oneWit`, `sameGraph_three_witnessCounts`

### 10.6 The compiled form has zero radical

Choose `U` as above and read the extra fact the Smith basis gives: every `u ∈ L` is `U(0, w)` for
some `w`, since the coordinates of `u` along the `e′_j` vanish.  `exists_exactWitnessCompiler`

Let `ψ(b, v) = (b, U(v, 0))`, a ℤ-linear map.  The quadratic part of any such equation is read off
three evaluations at input `0`,

    2·Q(z)  =  E(2z) − 2·E(z) + E(0),      E(z) = P(0, z),

and `P_red(0, z) = P(0, ψ z)`; hence `Q_red = Q ∘ ψ` and `B_red(z, z′) = B(ψ z, ψ z′)`.
`two_zQuad_eq`, `compiled_zQuad`, `compiled_zPolar`

Let `z` be an integer vector with `B_red(z, ·) = 0`.  Every integer `x = (x_out, x_unk)` splits as
`x = ψ(y) + (0, ℓ)`, where `(s, t) = U⁻¹(x_unk)`, `y = (x_out, s)` and `ℓ = U(0, t) ∈ L`.  Then
`B(ψ z, x) = B_red(z, y) + B(ψ z, (0, ℓ)) = 0 + 0`.  Orthogonality to all integer vectors gives
orthogonality to all rational ones (`inRadicalQ_of_int`), so `ψ z ∈ rad Q`.  By 10.1 the output
block of `z` is zero, so `ψ z = (0, U(v, 0))` with `U(v, 0) ∈ L`; by the choice of `U`,
`U(v, 0) = U(0, w)` for some `w`, and injectivity of `U` forces `v = 0`.  Thus `z = 0`
(`compiled_intRadical_eq_zero`).  A rational radical vector scales to an integer one, so `B_red` is
nondegenerate over ℚ (`compiledData_nondegQ`), and its rank is `m + (d − m) = d`
(`compiledData_polarRank`).

### 10.7 Semidefinite compiles to definite

If `Q ≥ 0` on `V`, then `Q_red ≥ 0`: for rational `u`, choose `N ≥ 1` with `N·u` integral; then
`N²·Q_red(u) = Q(ψ(N·u)) ≥ 0`.  On a semidefinite form an isotropic vector is radical
(`polar_eq_zero_of_zQuadQ_eq_zero`), so `Q_red(u) = 0` forces `u ∈ rad Q_red = 0`.  Hence
`Q_red(u) > 0` for every nonzero `u`.  `compiledData_posDef`, `definite_reduction`

### 10.8 The reduction theorem

Let `DefiniteWeakNF` be the statement: every datum with `m ≥ 1` and positive definite form that
defines `f` gives `f` a weak vector coset normal form.

* **PROVED.**  `SemidefiniteWeakNF ⟺ DefiniteWeakNF`.  Forward: a definite form is semidefinite,
  and it is nonzero on the integer vector with one output coordinate equal to `1`.  Backward:
  10.7, applied to the given datum.  `semidefiniteWeakNF_iff_definiteWeakNF`
* **PROVED.**  With r41's `generalWeakNF_iff_semidefiniteWeakNF`:
  `GeneralWeakNF ⟺ DefiniteWeakNF`.  `generalWeakNF_iff_definiteWeakNF`
* **OPEN.**  `DefiniteWeakNF` itself.  Removing the degeneracy does not solve the integer
  representation problem of the definite case.
* **PROVED in §11 (s54).**  The first arithmetic residue: one output, one unknown, any `n`,
  positive definite (`DefiniteWeakNF_oneOut_oneWit`; `definiteWeakNF_oneOut_oneWit_holds`), and more
  generally every nonzero semidefinite datum of polar rank at most two.  Nothing in this section is
  conditional on it.
* **Not reduced here.**  The full-residue normal form.

The control of 10.5 is semidefinite and compiles to a positive definite datum of rank 2.
`exD_semidefinite`, `exD_definite_reduction`

---

## 11. Polar rank at most two, and the four-square family

Everything in this section is std-3.

### 11.1 Square values force a square

Let `T` be a rational quadratic form in `n` variables with `T(v)` a rational square for every
`v ∈ ℤⁿ`.  Clear denominators: `A = N²T` has integer entries, and `A(v)` is an integer that is a
rational square, hence an integer square.  `c21_affine_square` gives `A(v) = (ℓ·v + s)²` on ℤⁿ;
`v = 0` gives `s = 0`.  So `T(v) = (h·v)²` with `h = ℓ/N` on ℤⁿ, and on ℚⁿ by homogeneity (write
`x = y/d` with `y` integral).  A test on basis vectors alone would not suffice: `x₁² + x₂²`.
`square_values_rigidity`

### 11.2 One discriminant for all directions

Suppose `c + 2ℓ(x) + H(x)` is a rational value of `X² + D·Y²` (`D > 0`) at every `x ∈ ℤⁿ`.  Fix
`v ∈ ℤⁿ`; on the line `t ↦ tv` the polynomial is `H(v)t² + 2ℓ(v)t + c`.  If `H(v) ≠ 0`, its
discriminant is `−D` times a rational square (`rat_discriminant_of_total'`), i.e.
`(c·H(v) − ℓ(v)²)/D` is a square.  If `H(v) = 0`, a non-constant linear polynomial cannot be a norm
at every integer (`not_total_of_linear`), so `ℓ(v) = 0` and the quotient is `0`.
`direction_discriminant_square`

### 11.3 The section through a prescribed representation

Let `c = r₀² + D·s₀² > 0`.  By 11.2 and 11.1, `(c·H − ℓℓᵀ)/D = h²` for one rational linear form
`h` (`discMatrix`, `discMatrix_form`), i.e. `c·H(x) − ℓ(x)² = D·h(x)²`.  Hence
`c·(c + 2ℓ(x) + H(x)) = (c + ℓ(x))² + D·h(x)²`, and Brahmagupta's identity gives

    c + 2ℓ(x) + H(x) = r(x)² + D·s(x)²,
    r(x) = r₀ + (r₀ℓ(x) − D s₀ h(x))/c,   s(x) = s₀ + (s₀ℓ(x) + r₀ h(x))/c,

identically on ℚⁿ, with `(r(0), s(0)) = (r₀, s₀)` exactly.  `norm_identity`, `norm_section`

### 11.4 Two output/unknown coordinates, positive definite

Let the form `Q` be positive definite on `z` with `m + r = 2` (`OutWit m r ≃ Fin 2`).  With
`α = Q(e₁) > 0`, `b` the cross coefficient and `γ = Q(e₂)`, `Δ' = 4αγ − b² > 0`, and
`Q(w) = α((w₁ + βw₂)² + Δw₂²)` with `β = b/(2α)`, `Δ = Δ'/(4α²)` (`binDiag`).  Cramer's rule gives
a rational affine centre `c(a)` (`binCentre`, `centre_isCentre`), and the residual
`R(a) = Q(c(a)) − q(a)` is an explicit rational quadratic form in `a` (`residualForm`,
`residual_eq`).  Every integer solution satisfies `Q(z − c(a)) = R(a)` (`offCentre_norm`), and
conversely an integer `z` with that norm is a solution (`solZ_of_norm`).  `binary_compiler_gen`

If `R` vanishes at every integer input, positive definiteness forces `z = c(a)` and `f` is affine
(`M = 1`).  Otherwise pick `a₀` with `R(a₀) ≠ 0` and an integer solution `z₀` at `a₀`; put
`w₀ = z₀ − c(a₀)`, `r₀ = w₀₁ + βw₀₂`, `s₀ = w₀₂`, so `R(a₀)/α = r₀² + Δs₀² > 0`.  Totality makes
`R(a₀ + x)/α` a rational norm at every integer `x` (read off the solution there), so 11.3 applies
to the Taylor expansion at `a₀` (`QuadForm.translate`).  The rational family
`z(x) = c(a₀ + x) + (r(x) − β s(x), s(x))` equals `z₀ + G·x` with a rational matrix `G`, solves the
equation for every `x`, and passes through `z₀` at `x = 0`.  A common denominator `M` of `G`
(`exists_common_den`) makes `z(Mt)` integral; output-uniqueness identifies its output coordinates
with `f(a₀ + Mt)`.  `weakVectorCosetNF_of_binary`

No class-number argument and no uniqueness of the unknowns is used.  Instances:
`definiteWeakNF_oneOut_oneWit_holds` (`(m, r) = (1, 1)`, every `n`) and
`definiteWeakNF_twoOut_zeroWit_holds` (`(2, 0)`); `definite_binary_compiler` is the `(1, 1)` form of
the compiler.

### 11.5 Polar rank at most two

Let `Q ≠ 0` be semidefinite of either sign, `m ≥ 1`, polar rank `d ≤ 2`.  A negative semidefinite
datum is negated (`negGraph`, whose polar rank is the same: `negGraph_polarRank`).  §10 compiles a
positive semidefinite datum to a positive definite one with `m` outputs and `d − m` unknowns
(`definite_reduction`, `m_le_polarRank`), so `m + (d − m) = d ≤ 2`.  If `d = 1`, the compiled datum
has one output and no unknown, and the full vector coset normal form is known
(`fullVectorCosetNF_of_defines`); if `d = 2`, 11.4 applies.  `weakNF_of_small`,
`lowRankSemidefiniteWeakNF_holds`

Still open in general: the positive definite case of polar rank at least three (`DefiniteWeakNF`),
and a full-residue normal form beyond rank one.  Special families are settled — for instance the
four-square family (§11.6).

### 11.6 The four-square family: a finite criterion

For `Family n m` (`m ≥ 1`) whose residual is carried by an integer polynomial `P` of degree at most
two, total ∧ output-unique already forces `P` constant (`R_const`), and constancy is the finite
coefficient condition `l = 0 ∧ Q + Qᵀ = 0` (`IntQuad.eval_eq_c_iff`; not "every entry of `Q` is
zero").  Writing `lin(a) = k·q + η` coordinatewise, `b ↦ b − q` is a bijection between the box at
`a` and the box `S_η` of the residue (`shift_existsUnique`), and `lin(a) mod k` depends only on
`a mod k` (`resid_rep`).  Hence

    total ∧ OU  ⟺  l = 0 ∧ Q + Qᵀ = 0 ∧ for each of the kⁿ representatives ρ, #S_{resid ρ} = 1,

with no quantifier over integer inputs left (`total_and_outputUnique_iff_finite`; `n = 0` included).
Each `S_η` lies in an explicit finite box (`mem_boxFinset_of_le`, `existsUnique_iff_card`).

Coordinate by coordinate, with `δ = min(η, k − η)`: the nearest multiple has error `δ²`, the other
neighbour `(k − δ)²`, and every other integer at least that (`nearest_err`, `other_err`,
`other_le_err`).  Summing, the nearest point has `d_η = Σδⱼ²`, every other point has at least
`d_η + k(k − 2δⱼ)` for some `j`, and changing the minimising coordinate attains
`d_η + g_η` with `g_η = min_j k(k − 2δⱼ)` (`far_of_ne`, `second_point`).  So

    #S_η = 1  ⟺  d_η ≤ R0 < d_η + g_η,

equal-distance points counted separately (`existsUnique_iff_gap`); the unique point is the
coordinatewise nearest one (`nearest_mem`), which reads off
`f(a)ⱼ = ⌊linⱼ(a)/k⌋ + [2(linⱼ(a) mod k) ≥ k]` (`graph_iff_table`).  If every residue is reached,
the criterion is `k` odd, `k = 2h + 1`, and `m·h² ≤ R0 < (h + 1)²` (`full_residue_iff`,
`total_and_outputUnique_iff_of_surjective`); `k = 3, m = 3, R0 = 3` passes, `k = 3, m = 4` has no
`R0`, `k = 5, m = 2, R0 = 8` passes.

Control: `k = 2`, `R(a) = a(a − 1)`.  The representatives `a = 0, 1` each have exactly one output,
yet `a = 3` has three, and `R` is not constant — checking representatives before using constancy is
wrong (`ExNeg_representatives`, `ExNeg_not_outputUnique`, `ExNeg_residual_not_const`).  The s52
example passes through the finite criterion (`Ex_total_outputUnique_via_finite`).

Not claimed: a decision procedure for general SE₂, a complexity bound, or anything for a residual
not carried by a degree-≤2 integer polynomial.

### 11.7 Three interface statements

* **Rank one without auxiliary data.**  If `polarRank = 1`, the polar image is spanned by
  `B(w₀, ·)` for some `w₀`, so every `x` differs from a multiple of `w₀` by a radical vector; a
  base solution comes from totality.  These are exactly the extra hypotheses of
  `fullVectorCosetNF_of_polarRankOne`.  `fullVectorCosetNF_of_polarRank_eq_one`
* **The solution side of the binary compiler.**  For `(n, 1, 1)` positive definite, an integer `z`
  solves the equation at `a` if and only if `z − c(a) = (x − βy, y)` for rational `x, y` with
  `R(a) = α(x² + Δy²)`.  `definite_binary_compiler_solutions`
* **No outputs.**  With `m = 0` the weak normal form holds vacuously, so the low-rank statement
  holds without `0 < m`.  `weakVectorCosetNF_of_no_outputs`, `lowRankSemidefiniteWeakNF_allM_holds`

## 12. Constant residual and doubled-centre reflection, in any rank

Everything in this section is std-3.  Throughout, `P(a, z) = Q(z) + ℓ_a(z) + q(a)` with
`z = (b, u)`, and an affine centre `c(a) = c0 + C a` is given as data: `c(a)` is a centre at every
integer input, so that `P(a, z) = Q(z − c(a)) − R(a)` over ℚ (§10, `completeSquare`).  No sign, rank
or nondegeneracy hypothesis on `Q` is used anywhere in this section, and nothing here produces
the centre for a general datum.  `centreAt`

### 12.1 Constant residual: integer transport

> **Proposition 12.1.**  If `R(a) = R0` for every integer `a`, there are `M ≥ 1` and an integer
> matrix `G = M·C` with `P(a + Mt, z + Gt) = P(a, z)` for all integer `a, z, t`.  For every `a, t`
> the map `z ↦ z + Gt` is a bijection from the integer solutions at `a` to those at `a + Mt`, with
> inverse `z ↦ z − Gt`.  `constResidual_transport`, `constResidual_solEquiv`

*Proof.*  Take `M` a common denominator of the entries of `C` (the constant term `c0` need not be
integral).  Then `c(a + Mt) = c(a) + Gt`, so `(z + Gt) − c(a + Mt) = z − c(a)`, and the residual is
the same constant on both sides.  Both sides of the completed square therefore agree; the inverse
is the same identity at `z − Gt`. ∎

The number of witnesses plays no role: in the control `b² + (u − v)² = 0` (centre 0, residual 0,
`f = 0`) every input has infinitely many witnesses.  `ctlB1_hyp`, `ctlB1_defines`,
`ctlB1_witnesses_infinite`

### 12.2 Constant residual: one modulus and one slope on every class

> **Proposition 12.2.**  Under 12.1 and `Defines f`, `f(a + Mt) = f(a) + π(Gt)` for all integer
> `a, t`; in particular `f` has a full vector coset normal form with one modulus and one integer
> slope.  `constResidual_translate`, `constResidual_commonSlopeIntNF`,
> `constResidual_fullVectorCosetNF`

*Proof.*  Take the solution `z = (f(a), u)` given by totality and move it by 12.1; its output part
is a solution output at `a + Mt`, hence equals `f(a + Mt)` by output-uniqueness. ∎

> **Lemma 12.3.**  If `f(a + Mt) = f(a) + M·A t` and `f(a + M't) = f(a) + M'·A' t` for all `a, t`,
> with `M, M' ≥ 1` and rational matrices `A, A'`, then `A = A'`.  `affineSlope_unique`

*Proof.*  Compare both laws at the step `MM' eᵢ` from `a = 0`: `MM' A eᵢ = MM' A' eᵢ`. ∎

The four-square family is an instance: its compiled datum has the explicit centre
`c(a) = (lin(a)/k, 0)`, and the residual along it is `R(a)`, which is constant by `R_const` — the
constancy is derived, not assumed.  `familyData_constResidualCentre`

The rank-one control `N4Control` (R41-D3) has slope `+1` on even inputs and `−3` on odd ones.  This
does not contradict 12.3: its residual `(4a − 1)²/4` is not constant, so 12.2 does not apply, and
12.3 compares two laws of the displayed form on all of `ℤⁿ`, which that example does not have.

### 12.3 Reflection in a doubled centre

> **Proposition 12.4.**  Fix `a` and suppose the whole vector `2c(a)` is an integer vector `h`.
> Then `h − z` is an integer solution whenever `z` is; under output-uniqueness `πz = πc(a)` for
> every integer solution `z`; under `Defines f`, `f(a) = πc(a)`.  `centreReflect_solZ`,
> `centreReflect_output`, `centreReflect_value`

*Proof.*  `(h − z) − c(a) = −(z − c(a))` and `Q(−w) = Q(w)`, so `h − z` solves the same equation.
Output-uniqueness gives `πz = π(h − z) = 2πc(a) − πz`. ∎

The witnesses of `z` and `h − z` may differ; only the outputs are compared.  The hypothesis is on
all coordinates of `2c(a)`: integrality of its output part alone is not enough for this argument.

> **Proposition 12.5.**  Let `N ≥ 1` be a common denominator of `2c0` and `2C`, and `H0 = 2N c0`,
> `H = 2N C`.  Some integer input has an integral doubled centre if and only if some
> `ρ ∈ {0, …, N − 1}ⁿ` satisfies `H0 + Hρ ≡ 0 (mod N)`.  If one input `a0` has an integral doubled
> centre, so does every point of a coset `a0 + Mℤⁿ`, and then `f` is an integer affine map on that
> coset.  `centreReflect_finite_iff`, `centreReflect_coset`,
> `centreReflect_weakIntAffineCosetNF`, `centreReflect_weakVectorCosetNF`

*Proof.*  `2c(a) = (H0 + Ha)/N`, so integrality is `N | H0 + Ha`, which depends only on
`a mod N`.  For the coset, take `M` clearing the denominators of `2C`.  On the coset,
12.4 gives `f(a0 + Mt) = πc(a0) + M·πC t`; the constant and the slope are integers because they
are differences of values of `f`. ∎

The criterion is sufficient, not necessary: in `N4Control` the doubled centre `(1 − 2a)/2` is
never integral, yet `f` has a full normal form with modulus 2.  `D3_double_centre_not_integral`

## 13. Positive definite shells and a finite criterion for constant residual

Everything in this section is std-3.  The setting is §12's (an affine centre `c(a) = c0 + C a` as
data), with the output/witness form `Q` positive definite where stated.

### 13.1 The doubled-centre coset with the common denominator

If `N ≥ 1` makes `2N·C` integral — the `N` of Proposition 12.5 does — and `2c(a0)` is an integer
vector `h`, then `2c(a0 + Nt) = h + (2N·C) t` is an integer vector for every integer `t`.
`centreReflect_coset_mod`

### 13.2 An explicit box for a positive definite shell

> **Lemma 13.1.**  If `Q` is positive definite, there is a rational `h ≥ 0` with
> `yₖ² ≤ h·Q(y)` for every rational vector `y` and every coordinate `k`.  `definite_coord_sq_le`

*Proof.*  Positive definiteness makes the radical zero, so each coordinate functional `y ↦ yₖ` is
`B(wₖ, ·)` for some `wₖ` (`exists_polar_rep`).  Cauchy–Schwarz for the polar form gives
`yₖ² = B(wₖ, y)² ≤ 4·Q(wₖ)·Q(y)`; take `h = Σₖ 4·Q(wₖ)`. ∎

No eigenvalue and no square root is used.  With this `h`, a lattice point on the shell
`Q(y) = T` has `|yₖ| ≤ ⌈h·max(T, 0)⌉ + 1`, so the shell is exactly the filtered box of that
radius; for `T < 0` the shell is empty and for `T = 0` it is `{0}`.  The bound needs `h ≥ 0`: for
the indefinite `Q(y) = −y²` the inequality holds with `h = −1`, and `y = 5` lies on the shell
`T = −25` outside the box of radius 1.  `definiteShell_neg`, `definiteShell_zero`,
`definiteShell_bound`, `mem_shellFinset`

### 13.3 Shell and solutions

> **Proposition 13.2.**  Let the residual be a constant `R0`, and let `M ≥ 1` clear the
> denominators of `c0` and of `C`, with `e0 = M c0` and `E = M C`.  For every integer `a`, the map
> `z ↦ y = Mz − (e0 + E a)` is a bijection from the integer solutions at `a` to the lattice points
> with `Q(y) = M²R0` and `y ≡ −(e0 + E a) (mod M)`; its inverse is `y ↦ (y + e0 + E a)/M`.  The
> congruence depends on `a` only modulo `M`.  `shellEquiv`, `shellResidue_mod`

*Proof.*  `Mz − (e0 + E a) = M(z − c(a))`, so `Q(y) = M²·Q(z − c(a)) = M²R0` exactly when `z` is a
solution.  The congruence says that `(y + e0 + E a)/M` is an integer vector, and the two maps are
inverse to each other.  Replacing `a` by `a + Mt` adds `M·Et` to the congruence. ∎

No sign hypothesis is used in 13.2.

### 13.4 The finite criterion

> **Theorem 13.3.**  If moreover `Q` is positive definite, then, with `B` the box radius of 13.2,
> the graph is total and output-unique if and only if, for each of the finitely many residues
> `ρ ∈ {0, …, M − 1}ⁿ`, the set of output parts of the lattice points of the residue shell
> `{y : ‖y‖∞ ≤ B, Q(y) = M²R0, y ≡ −(e0 + Eρ) (mod M)}` has exactly one element.  In that case
> the one element for `ρ = a mod M` is `M·f(a) − π(e0 + E a)`.
> `total_outputUnique_iff_shellImage`, `shellImage_eq_value`

*Proof.*  By 13.2 the solutions at `a` are the points of the residue shell of `a mod M`, moved by
an injective affine map whose output part is `πz ↦ M·πz − π(e0 + E a)`.  A nonempty output image
is totality at `a`; an output image with one element is output-uniqueness at `a`. ∎

The recovered value agrees with 12.2: along `a + Mt` the point `M f(a) − π(e0 + E a)` does not move,
since `M f(a + Mt) = M f(a) + π(M·E t)` and `π(e0 + E(a + Mt)) = π(e0 + E a) + π(M·E t)`.

The criterion asks for one OUTPUT value, not for one point: several witnesses are allowed.  If
`R0 < 0` there is no solution at any input, so the graph is not total.
`not_total_of_negResidual`

### 13.5 A rank-three example with a cross term

`(3b − a)² + (u + b)² + v² = 1`, one input, one output, two witnesses.  The form
`9b² + (u + b)² + v²` is positive definite of polar rank 3, the centre is `(a/3, −a/3, 0)`, and the
residual is 1.  It defines `f(a) = ⌊(a + 1)/3⌋`, and `f(a + 3t) = f(a) + t`.  At `a = 0` the
solutions are `(0, ±1, 0)` and `(0, 0, ±1)` — four of them — so witnesses are not unique.
With `M = 3` and box radius 4, each residue shell has a one-point output image, while the residue
shell of `0` has four points: a test asking for one point per residue shell rejects this total,
output-unique graph.  `ctlC4_eval`, `ctlC4_posDef`, `ctlC4_polarRank`, `ctlC4_centre_residual`,
`ctlC4_defines`, `ctlC4_translate`, `ctlC4_solutions_zero`, `ctlC4_not_witnessUnique`,
`ctlC4_shellImage`, `ctlC4_residueShell_zero_card`

## 14. Integer affine sections

Everything in this section is std-3.  A map `f` has a weak integer affine coset normal form when,
for some `M ≥ 1` and `ρ`, `f(ρ + Mt) = b0 + Bt` for all integer `t` with an integer vector `b0` and
an integer matrix `B`.

### 14.1 Two bridges

> **Lemma 14.1.**  (a) If `f(ρ + Mt) = c + Lt` for all integer `t`, with rational `c` and `L`, then
> `c = f(ρ)` and `L eᵢ = f(ρ + M eᵢ) − f(ρ)`, so both are integral.  (b) If `Defines f` and
> `z0 + Gt` is an integer solution at `a0 + Mt` for every `t` (with `G` integral), then
> `f(a0 + Mt) = π z0 + (πG) t`.  `weakIntAffine_of_affineCoset`, `weakIntAffine_of_section`

> **Lemma 14.2.**  A rational quadratic polynomial `q` with `|q(x)| ≤ K(1 + Σ|xᵢ|)` on the integer
> lattice has zero quadratic form: `xᵀ Q x = 0` for every rational `x`.
> `quadForm_zero_of_linearGrowth`

*Proof.*  On the line `t ↦ tv` (`v` integral, `t ∈ ℕ`) the value is `c + Bt + At²` with
`A = vᵀQv`.  If `A ≠ 0`, take `T ≥ 1` with `|A|·T ≥ K + KS + |B| + |c| + 1`, `S = Σ|vᵢ|`; then
`|A|T² > (K + KS + |B| + |c|)T ≥ K(1 + TS) + |B|T + |c|`, against the bound.  So `A = 0` on the
lattice, and on rational points after clearing denominators. ∎

The conclusion is about the form, not the matrix: a nonsymmetric `Q` with `Q + Qᵀ = 0` also
qualifies.  With Lemma 14.1(a), a weak coset normal form of a map of linear growth is a weak
integer affine coset normal form.  `weakIntAffine_of_weakNF_linearGrowth`

### 14.2 The binary case through a given solution

> **Proposition 14.3.**  Positive definite in two output/unknown coordinates and total.  For a
> given input `a0`, a given integer solution `z0` there, and positive residual at `a0`, there are
> `M ≥ 1` and an integer matrix `G` with `z0 + Gt` an integer solution at `a0 + Mt` for every
> integer `t`.  `binary_baseSection`

*Proof.*  This is the construction of §11.4 with the base point fixed.  Positive definiteness
makes the centre unique, so the residual at `a0` is the value `R(a0) > 0` of the compiled
residual; the off-centre vector of `z0` gives the representation `(r0, s0)`, and
the section of §11.3 passes through it.  Clearing the denominators of its slope gives
`M` and `G`; the family is `z0` at `t = 0`. ∎

Output-uniqueness is not used here; it enters only in Lemma 14.1(b).  The branch in which the
residual vanishes at every integer input is separate: then every solution is the centre, so the
centre is integral at every input and is itself an integer affine family of solutions on all of
`ℤⁿ`.  A single input with zero residual does not put the datum in this branch.
`zeroResidual_section`, `weakIntAffineCosetNF_of_binary`

### 14.3 Low rank

> **Theorem 14.4.**  Under the hypotheses of Proposition A.2 (a nonzero semidefinite form of
> polar rank at most two, either sign), `f` has a weak integer affine coset normal form.
> `lowRankSemidefiniteIntAffineNF_holds`

*Proof.*  For `m = 0` there is nothing to prove.  Otherwise the weak normal form holds (§11.5),
and a semidefinite graph has linear growth (§4.3, after a change of sign if needed); Lemma 14.2
and Lemma 14.1(a) conclude. ∎

This route does not pass through 14.3 for polar rank two; 14.3 gives the binary case separately,
through a prescribed solution.  No full-residue form is claimed.

### 14.4 Two more controls for the finite criterion

With no input (`n = 0`), `9b² + (u + b)² + v² = 1` defines `f = 0`; the single residue passes the
criterion of §13.4 at `M = 1`, and its residue shell has four points.  With residual `−1`
(`9b² + (u + b)² + v² + 1 = 0`) every residue shell is empty and the graph is not total.
`ctlN0_centre_residual`, `ctlN0_posDef`, `ctlN0_defines`, `ctlN0_shellImage`,
`ctlN0_residueShell_card`, `ctlNeg_centre_residual`, `ctlNeg_residueShell_empty`,
`ctlNeg_not_total`

## 15. What totality alone cannot do, and what output-uniqueness adds

Everything in this section is std-3 unless a hypothesis is named.

### 15.1 Rank three: no affine section from totality

`b² + u² + v² = 1 + 8(a₁² + a₂² + a₃² + a₄²)`, four inputs, one output, two unknowns.  The right
side is `≡ 1 (mod 8)`, hence not of the form `4ᵏ(8l + 7)`, so by the three-square theorem of
Legendre and Gauss every integer input has an integer solution.  This theorem is not available
in Lean at the pin used here; the formal statement takes it as a HYPOTHESIS for `N ≡ 1 (mod 8)`,
and no axiom is added.  `d1_total_of_threeSquares`, `ctlD1_total_of_threeSquares`

> **Proposition 15.1.**  No rational affine family `p + Lt` solves the equation along a full
> lattice coset `ρ + Mℤ⁴` (`M ≥ 1`).  `d1_no_affine_section`

*Proof.*  If it did, the function `t ↦ ‖p + Lt‖² − 1 − 8‖ρ + Mt‖²` would vanish on `ℤ⁴`; its
second difference in the directions `eᵢ, eⱼ` gives `LᵀL = 8M²·I₄`.  The left side has rank at most
three (it factors through `ℚ³`), the right side has rank four. ∎

At `a = 0` the outputs `−1, 0, 1` all occur, so output-uniqueness fails: the example refutes the
strategy "totality gives a norm section", not any normal form.  `d1_outputs_zero`,
`ctlD1_not_outputUnique`

The same argument in rank four is unconditional: `z₁² + z₂² + z₃² + z₄² = 1 + a₁² + … + a₅²` is
total by the four-square theorem (in Lean), and `LᵀL = M²·I₅` is impossible for a `4 × 5` matrix.
`d1r4_total`, `d1r4_no_affine_section`, `ctlD1r4_total`, `ctlD1r4_not_outputUnique`

Degree-two sections are not treated here.

### 15.2 Isometries: where output-uniqueness enters

> **Lemma 15.2.**  Let `c` be a centre at `a` and `T` a rational matrix with `Q(Tw) = Q(w)`.  If
> `z` is an integer solution and `z' = c + T(z − c)` is an INTEGER vector, then `z'` is a solution,
> and output-uniqueness gives `π(T − I)(z − c) = 0`.  With `N` clearing `c` and `T`,
> `z'` is integral if and only if `N²` divides `N·(Nc) + N·(NT)z − (NT)(Nc)` coordinatewise.
> `isometry_solZ`, `isometry_output_zero`, `isometry_integral_iff`

*Proof.*  `Q(z' − c) − R = Q(T(z − c)) − R = Q(z − c) − R = 0`.  The outputs of `z` and `z'` agree,
and `z' − z = (T − I)(z − c)`.  Multiplying `c + T(z − c)` by `N²` gives the displayed integer
vector. ∎

A rational isometry alone does not return to the lattice.  In `(2b − 2a)² + (3u − 1)² + v² = 1`
(centre `(a, 1/3, 0)`, residual 1, `f(a) = a`) the witness flip `diag(1, −1, 1)` sends the integer
solution `(a, 0, 0)` to `(a, 2/3, 0)`.  `ctlD4_T2_not_integral`

### 15.3 Finite symmetry certificates

> **Theorem 15.3.**  Suppose finitely many integer matrices `Tᵢ` preserve `Q`; on a coset
> `ρ + Mℤⁿ` the vectors `(I − Tᵢ)c(ρ)` and the matrices `M(I − Tᵢ)C` are integral; and rational
> matrices `Aᵢ` satisfy `π = Σᵢ Aᵢ π(Tᵢ − I)`.  If `f` is defined by the datum, then on the coset
> `f(a) = πc(a)`, and `f` has a weak integer affine coset normal form.
> `symmetry_certificate_NF`, `affineIntegral_coset`

*Proof.*  On the coset `(I − Tᵢ)c(a)` is integral, so `z' = Tᵢz + (I − Tᵢ)c(a)` is an integer
vector for every integer solution `z`; Lemma 15.2 gives `π(Tᵢ − I)(z − c(a)) = 0` for each `i`,
and the certificate gives `π(z − c(a)) = 0`.  So `f(a) = πc(a)`, which is affine on the coset;
Lemma 14.1(a) makes it integral. ∎

All hypotheses are finite checks, and the normal form is not among them.  For `T = −I`,
`(I − T)x = 2x` and `π = (−½)·π(T − I)`, which is the doubled-centre condition of §12.3.
`negIdentity_shift`, `negIdentity_certificate`

In the example above the doubled centre is never integral, so §12.3 does not apply, but the output
flip `diag(−1, 1, 1)` passes the certificate with `M = 1`, `ρ = 0`, `A = −½`, and forces
`f(a) = a`.  `ctlD4_not_reflectable`, `ctlD4_T1_isometry`, `ctlD4_certificate_NF`.  The residual of
this example is constant, so it does not bear on the open case below.  A checker of the four finite
conditions (exact rational arithmetic) accompanies the artifact.

### 15.4 The remaining case

Let the obstruction case be: `Q` positive definite, at least one output, polar rank at least three,
and — along the (unique) affine centre — a residual that is not constant and a doubled centre that
is integral at no input.

> **Theorem 15.4.**  The weak normal form holds for every single-equation graph if and only if it
> holds in the obstruction case.  `generalWeakNF_iff_residualReflectionObstructionNF`

*Proof.*  One direction is a specialisation.  For the other, the general case reduces to the
positive definite one with at least one output (§10.8).  A positive definite datum has an affine
centre (`definite_exists_centreAt`).  Polar rank at most two is §11.5; a constant residual is
§12.2; a reflectable input is §12.3; what remains is the obstruction case. ∎

Dependencies: §10.8 → {§11.5, §12.2, §12.3, obstruction case}.  The obstruction case itself is
open; this theorem locates it and does not decide it.

## 16. Two completions

Everything in this section is std-3.

**The low-rank theorem through the binary section.**  Theorem 14.4 also follows along the route of
§14.2: after the change of sign and the compilation of §11.5, a positive definite datum with two
output/unknown coordinates has a weak integer affine coset normal form by Proposition 14.3 and
Lemma 14.1(b), and one with a single coordinate by the full normal form of §11.5 together with
Lemma 14.2.  `weakIntAffine_of_small`, `lowRankSemidefiniteIntAffineNF_holds_viaBinary`

**No section of degree two in §15.1.**  Suppose `p + Lt + (tᵀH₁t, tᵀH₂t, tᵀH₃t)` solved the equation
of §15.1 along `ρ + Mℤ⁴`.  Fix `t` and restrict to `s ↦ s·t`: the left side is a polynomial of degree
at most four in `s` with leading coefficient `Σₖ (tᵀHₖt)²`, the right side has degree two.  The
fourth difference at `s = 0, …, 4` gives `Σₖ (tᵀHₖt)² = 0`, so every `tᵀHₖt` vanishes, the family is
affine on the lattice, and Proposition 15.1 applies.  `d1_no_quadratic_section`

## 17. Totality of a one-variable rational norm family

Everything in this section is std-3.  The witnesses are rational; nothing here decides integer SE₂ graphs in general, and no complexity bound is claimed.

> **Proposition 17.1.**  Let `A ≠ 0`, `B`, `C` be rational and `D > 0`.  Then `At² + Bt + C` is a value of
> `x² + Dz²` (rational `x, z`) at every integer `t` if and only if `B² − 4AC = −Dh²` for some rational `h`
> and `A` itself is a value of `x² + Dz²`.  `norm_totality_iff`

*Proof.*  If the family is total, Lemma A.3 gives the discriminant condition; then
`4A·P(t) = (2At + B)² + Dh²` for every `t`, and at a `t` with `P(t) ≠ 0` (one of `0, 1, 2`) the quotient of
two nonzero values of `x² + Dz²` is again such a value, so `A` is one.  Conversely, with
`A = a₀² + Db₀²`, the affine functions `((2At + B)a₀ + Dhb₀)/(2A)` and `(ha₀ − (2At + B)b₀)/(2A)` represent
`P(t)` by Brahmagupta's identity. ∎

Each side of the equivalence is finitely certified: a section; a prime `p` with `(−D/p) = −1` dividing
some `P(t)` exactly once (the proof of Lemma A.3); or a place at which the Hilbert symbol `(A, −D)` is
`−1`.  The artifact's checkers (`certificates/own_s55/`) produce and verify these certificates.
