/-
  CosetShift.lean — Gate-20 Packet 3, task T12.

  From a rational degree-≤2 section to an INTEGRAL coset normal form.  The mechanism is the one
  the reviewer gives in §4.3: a rational polynomial that is integral at `ρ` stays integral on the
  coset `ρ + M ℤⁿ` once `M` clears the denominators, because `g ∈ ℤ[a] ⇒ g(ρ + Mt) ≡ g(ρ) mod M`.
  Here it is packaged as an exact identity — the shifted polynomial — so no congruence reasoning
  is needed downstream:

      q.eval (ρ + M·t) = (q.shift ρ M).eval t        (identically, over ℚ)

  and `q.shift ρ M` has constant term `q.eval ρ`, linear part scaled by `M` and quadratic part by
  `M²`.  Integrality of the shifted coefficients is then a hypothesis that a CAS can discharge for
  a concrete section (`eval_shift_int`), and the whole thing collapses to `WeakVectorCosetNF`
  (`weakVectorCosetNF_of_coset`) — the second disjunct of the II-D summit.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.RadicalDrift

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadForm

variable {n : ℕ}

/-- The pure quadratic part. -/
def qq (q : QuadForm n) (x : Fin n → ℚ) : ℚ := ∑ i, ∑ j, x i * (q.Q i j * x j)

/-- Its polar form. -/
def qpolar (q : QuadForm n) (x y : Fin n → ℚ) : ℚ :=
  ∑ i, ∑ j, (x i * (q.Q i j * y j) + y i * (q.Q i j * x j))

theorem eval_eq (q : QuadForm n) (x : Fin n → ℚ) :
    q.eval x = q.c + (∑ i, q.l i * x i) + q.qq x := by
  simp only [QuadForm.eval, qq, dotProduct, Matrix.mulVec, Finset.mul_sum]

theorem qq_add (q : QuadForm n) (x y : Fin n → ℚ) :
    q.qq (x + y) = q.qq x + q.qpolar x y + q.qq y := by
  simp only [qq, qpolar, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem qq_smul (q : QuadForm n) (c : ℚ) (x : Fin n → ℚ) : q.qq (c • x) = c ^ 2 * q.qq x := by
  simp only [qq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem qpolar_smul_right (q : QuadForm n) (c : ℚ) (x y : Fin n → ℚ) :
    q.qpolar x (c • y) = c * q.qpolar x y := by
  simp only [qpolar, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- The polar form, written with the shifted variable outside. -/
theorem qpolar_eq_sum (q : QuadForm n) (x y : Fin n → ℚ) :
    q.qpolar x y = ∑ i, (∑ j, (q.Q j i + q.Q i j) * x j) * y i := by
  have h1 : (∑ i, ∑ j, x i * (q.Q i j * y j)) = ∑ i, (∑ j, q.Q j i * x j) * y i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have h2 : (∑ i, ∑ j, y i * (q.Q i j * x j)) = ∑ i, (∑ j, q.Q i j * x j) * y i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  simp only [qpolar, Finset.sum_add_distrib, h1, h2]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← add_mul, ← Finset.sum_add_distrib]
  refine congrArg (fun s => s * y i) ?_
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **T12 (the shift).**  The polynomial read on the coset `ρ + M ℤⁿ`, as a polynomial in the
coset parameter.  Constant term `q.eval ρ`, linear part scaled by `M`, quadratic part by `M²`. -/
def shift (q : QuadForm n) (ρ : Fin n → ℤ) (M : ℤ) : QuadForm n where
  c := q.eval (castQ ρ)
  l := fun i => (M : ℚ) * (q.l i + ∑ j, (q.Q j i + q.Q i j) * castQ ρ j)
  Q := fun i j => (M : ℚ) ^ 2 * q.Q i j

theorem castQ_add_smul (ρ t : Fin n → ℤ) (M : ℤ) :
    castQ (ρ + M • t) = castQ ρ + (M : ℚ) • castQ t := by
  funext i
  simp only [castQ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **T12.**  `q.eval (ρ + M·t) = (q.shift ρ M).eval t`, identically. -/
theorem eval_shift (q : QuadForm n) (ρ : Fin n → ℤ) (M : ℤ) (t : Fin n → ℤ) :
    q.eval (castQ (ρ + M • t)) = (q.shift ρ M).eval (castQ t) := by
  rw [castQ_add_smul, q.eval_eq, (q.shift ρ M).eval_eq, q.qq_add, q.qpolar_smul_right,
    q.qq_smul, q.qpolar_eq_sum]
  have e1 : (∑ i, q.l i * (castQ ρ + (M : ℚ) • castQ t) i)
      = (∑ i, q.l i * castQ ρ i) + (M : ℚ) * ∑ i, q.l i * castQ t i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e2 : (q.shift ρ M).qq (castQ t) = (M : ℚ) ^ 2 * q.qq (castQ t) := by
    simp only [qq, shift]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have e3 : (∑ i, (q.shift ρ M).l i * castQ t i)
      = (M : ℚ) * ∑ i, (∑ j, (q.Q j i + q.Q i j) * castQ ρ j) * castQ t i
        + (M : ℚ) * ∑ i, q.l i * castQ t i := by
    simp only [shift]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have e4 : (q.shift ρ M).c = q.eval (castQ ρ) := rfl
  rw [e1, e2, e3, e4, q.eval_eq]
  ring

end QuadForm

/-- **T12, the payoff.**  If `f` agrees with rational degree-≤2 polynomials on ONE full lattice
coset `ρ + M ℤⁿ`, then `f` has a weak vector coset normal form — the second disjunct of the II-D
summit.  No congruence bookkeeping is needed: `eval_shift` is an identity. -/
theorem weakVectorCosetNF_of_coset {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} {M : ℕ}
    (hM : 1 ≤ M) {ρ : Fin n → ℤ} {q : Fin m → QuadForm n}
    (h : ∀ (t : Fin n → ℤ) (j : Fin m),
        (f (ρ + (M : ℤ) • t) j : ℚ) = (q j).eval (castQ (ρ + (M : ℤ) • t))) :
    WeakVectorCosetNF f :=
  ⟨M, ρ, fun j => (q j).shift ρ (M : ℤ), hM, fun t j => by
    rw [h t j, QuadForm.eval_shift]⟩

/-- **The integral reading of the shift.**  If `M` clears the denominators of the shifted linear
and quadratic parts and the value at `ρ` is an integer, then the polynomial takes an explicitly
INTEGER value at every point of the coset.  This is the reviewer's §4.3 conclusion, obtained from
the identity rather than from a congruence. -/
theorem QuadForm.eval_shift_int {n : ℕ} (q : QuadForm n) (ρ : Fin n → ℤ) (M : ℤ)
    {cz : ℤ} {lz : Fin n → ℤ} {Qz : Matrix (Fin n) (Fin n) ℤ}
    (hc : q.eval (castQ ρ) = (cz : ℚ))
    (hl : ∀ i, (q.shift ρ M).l i = (lz i : ℚ))
    (hQ : ∀ i j, (q.shift ρ M).Q i j = (Qz i j : ℚ))
    (t : Fin n → ℤ) :
    q.eval (castQ (ρ + M • t))
      = ((cz + (∑ i, lz i * t i) + ∑ i, ∑ j, t i * (Qz i j * t j) : ℤ) : ℚ) := by
  rw [q.eval_shift ρ M t, QuadForm.eval_eq]
  have hcc : (q.shift ρ M).c = (cz : ℚ) := by
    show q.eval (castQ ρ) = (cz : ℚ)
    exact hc
  simp only [QuadForm.qq, hcc, hl, hQ, castQ]
  push_cast
  ring

/-- **The bridge (Packet 3 joint).**  A rational degree-≤2 section that takes INTEGER values on a
coset and solves the equation there gives `f` a weak vector coset normal form.  Output uniqueness
enters here and only here: it is what turns "the section solves the equation" into "the section IS
the output".  With this, the remaining obligation of the isotropic branch is purely the CONSTRUCTION
of such a section (centre affine in `a`, denominators cleared) — no further reasoning about
uniqueness or about the graph is needed. -/
theorem weakVectorCosetNF_of_rational_section {n m r : ℕ} {D : QuadraticGraphData n m r}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    {M : ℕ} (hM : 1 ≤ M) {ρ : Fin n → ℤ}
    (q : OutWit m r → QuadForm n)
    (zint : (Fin n → ℤ) → (OutWit m r → ℤ))
    (hmatch : ∀ (t : Fin n → ℤ) (k : OutWit m r),
        ((zint t k : ℤ) : ℚ) = (q k).eval (castQ (ρ + (M : ℤ) • t)))
    (hsol : ∀ t : Fin n → ℤ, D.SolZ (ρ + (M : ℤ) • t) (zint t)) :
    WeakVectorCosetNF f := by
  refine weakVectorCosetNF_of_coset (M := M) hM (ρ := ρ) (q := fun j => q (Sum.inl j)) ?_
  intro t j
  have hgraph : D.Graph (ρ + (M : ℤ) • t) (outProj (zint t)) := D.graph_of_solZ (hsol t)
  have hfeq : outProj (zint t) = f (ρ + (M : ℤ) • t) := (hf _ _).1 hgraph
  have : (f (ρ + (M : ℤ) • t) j : ℚ) = ((zint t (Sum.inl j) : ℤ) : ℚ) := by
    rw [← hfeq]; rfl
  rw [this, hmatch t (Sum.inl j)]


/-- POSITIVE control: a globally quadratic vector function has a coset normal form with `M = 1`
(so the hypothesis of `weakVectorCosetNF_of_coset` is satisfiable). -/
theorem weakVectorCosetNF_of_global {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    {q : Fin m → QuadForm n} (h : ∀ x j, (f x j : ℚ) = (q j).eval (castQ x)) :
    WeakVectorCosetNF f :=
  weakVectorCosetNF_of_coset (M := 1) (le_refl 1) (ρ := 0) (q := q)
    (fun t j => h _ j)

end DiophCompression.ResearchUpgrade
