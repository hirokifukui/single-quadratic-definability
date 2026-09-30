/-
  C1 (R40-C1) — the residual bound for the four-square witness family.

      P(a,b,u) = Σ_j (k b_j − ℓ_j(a))² + Σ_{i<4} u_i² − R(a),   ℓ(a) = c + B a

  with totality and output uniqueness (witness uniqueness NOT assumed).  Conclusion:

      0 ≤ R(a) < m k².

  Two remarks on scope, against the review's statement:
  * C1 needs NO hypothesis on R.  The reviewer states the family with `deg R ≤ 2`; the degree
    only enters at C2 (a bounded quadratic is constant).  R is an arbitrary function here, so
    the bound is proved once and C2 may add the degree hypothesis on top.
  * `m ≥ 1` is used exactly once, to move one output coordinate.  Nothing is a finite search.

  s51.  Ordinary-mathematics proof re-derived by hand before formalising (disposition §3 H-22-7).
-/
import ResearchUpgrade.AffineNormalForm

namespace DiophCompression.ResearchUpgrade.FourSquareSlack

open Finset Matrix

/-- Lagrange's four-square theorem in the shape this family needs: every non-negative integer is
a sum of four integer squares.  `Nat.sum_four_squares` is the mathlib statement. -/
theorem exists_four_squares {N : ℤ} (hN : 0 ≤ N) :
    ∃ u : Fin 4 → ℤ, ∑ i, (u i) ^ 2 = N := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares N.toNat
  refine ⟨![(a : ℤ), (b : ℤ), (c : ℤ), (d : ℤ)], ?_⟩
  have hc : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 = (N.toNat : ℤ) := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℤ)) h
  have hsum : ∑ i, (![(a : ℤ), (b : ℤ), (c : ℤ), (d : ℤ)] i) ^ 2
      = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by
    simp [Fin.sum_univ_four]
  rw [hsum, hc, Int.toNat_of_nonneg hN]

/-- The family: one equation, `m` outputs, four free witnesses, modulus `k`. -/
structure Family (n m : ℕ) where
  k : ℤ
  hk : 1 ≤ k
  c : Fin m → ℤ
  B : Fin m → Fin n → ℤ
  R : (Fin n → ℤ) → ℤ

namespace Family

variable {n m : ℕ} (F : Family n m)

/-- `ℓ_j(a) = c_j + (B a)_j`. -/
def lin (a : Fin n → ℤ) (j : Fin m) : ℤ := F.c j + ∑ i, F.B j i * a i

/-- `P(a,b,u) = 0`. -/
def Sol (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin 4 → ℤ) : Prop :=
  (∑ j, (F.k * b j - F.lin a j) ^ 2) + (∑ i, (u i) ^ 2) = F.R a

def Graph (a : Fin n → ℤ) (b : Fin m → ℤ) : Prop := ∃ u, F.Sol a b u

def Total : Prop := ∀ a : Fin n → ℤ, ∃ b, F.Graph a b

/-- Output uniqueness.  The witnesses are NOT required to be unique. -/
def OutputUnique : Prop := ∀ (a : Fin n → ℤ) (b b' : Fin m → ℤ), F.Graph a b → F.Graph a b' → b = b'

theorem k_pos : 0 < F.k := lt_of_lt_of_le zero_lt_one F.hk

/-- Totality forces `R ≥ 0`: it is a sum of squares. -/
theorem R_nonneg (hT : F.Total) (a : Fin n → ℤ) : 0 ≤ F.R a := by
  obtain ⟨b, u, hu⟩ := hT a
  rw [← hu]
  have h1 : (0 : ℤ) ≤ ∑ j, (F.k * b j - F.lin a j) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have h2 : (0 : ℤ) ≤ ∑ i, (u i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

/-- If every coordinate of the squared error is at most `k²`, the whole error is at most `m k²`. -/
theorem sum_le_of_termwise {a : Fin n → ℤ} {b : Fin m → ℤ}
    (h : ∀ j, (F.k * b j - F.lin a j) ^ 2 ≤ F.k ^ 2) :
    (∑ j, (F.k * b j - F.lin a j) ^ 2) ≤ (m : ℤ) * F.k ^ 2 := by
  calc (∑ j, (F.k * b j - F.lin a j) ^ 2) ≤ ∑ _j : Fin m, F.k ^ 2 :=
        Finset.sum_le_sum fun j _ => h j
    _ = (m : ℤ) * F.k ^ 2 := by simp [Finset.sum_const, Finset.card_univ]

/-- **C1.**  With `m ≥ 1`, totality and output uniqueness force the residual to be bounded by
`m k²` — not by a search, but because otherwise two different outputs are both realisable. -/
theorem R_lt (hm : 0 < m) (hT : F.Total) (hU : F.OutputUnique) (a : Fin n → ℤ) :
    F.R a < (m : ℤ) * F.k ^ 2 := by
  by_contra hcon
  push_neg at hcon        -- (m : ℤ) * F.k ^ 2 ≤ F.R a
  have hk0 : 0 < F.k := F.k_pos
  have hkne : F.k ≠ 0 := ne_of_gt hk0
  -- Euclid division of each ℓ_j(a) by k
  set q : Fin m → ℤ := fun j => F.lin a j / F.k with hq
  set r : Fin m → ℤ := fun j => F.lin a j % F.k with hr
  have hr0 : ∀ j, 0 ≤ r j := fun j => Int.emod_nonneg _ hkne
  have hrk : ∀ j, r j < F.k := fun j => Int.emod_lt_of_pos _ hk0
  have hdiv : ∀ j, F.k * q j = F.lin a j - r j := by
    intro j
    have := Int.mul_ediv_add_emod (F.lin a j) F.k
    simp only [hq, hr]
    linarith [this]
  -- the base output q: every coordinate error is -r j
  have hbase : ∀ j, (F.k * q j - F.lin a j) ^ 2 ≤ F.k ^ 2 := by
    intro j
    have h1 : F.k * q j - F.lin a j = -(r j) := by rw [hdiv j]; ring
    rw [h1]
    have := hr0 j; have := hrk j
    nlinarith [hr0 j, hrk j, hk0]
  -- the moved output: q + e_{j₀}
  set j₀ : Fin m := ⟨0, hm⟩ with hj₀
  set b₁ : Fin m → ℤ := Function.update q j₀ (q j₀ + 1) with hb₁
  have hmove : ∀ j, (F.k * b₁ j - F.lin a j) ^ 2 ≤ F.k ^ 2 := by
    intro j
    by_cases hj : j = j₀
    · have hval : b₁ j = q j + 1 := by rw [hj]; simp [hb₁]
      have h1 : F.k * b₁ j - F.lin a j = F.k - r j := by
        rw [hval]; have := hdiv j; linarith [this]
      rw [h1]
      nlinarith [hr0 j, hrk j, hk0]
    · have hval : b₁ j = q j := by simp [hb₁, hj]
      rw [hval]
      exact hbase j
  -- both residuals are non-negative, so four squares fill them
  have hres0 : 0 ≤ F.R a - ∑ j, (F.k * q j - F.lin a j) ^ 2 := by
    have := F.sum_le_of_termwise hbase; linarith
  have hres1 : 0 ≤ F.R a - ∑ j, (F.k * b₁ j - F.lin a j) ^ 2 := by
    have := F.sum_le_of_termwise hmove; linarith
  obtain ⟨u₀, hu₀⟩ := exists_four_squares hres0
  obtain ⟨u₁, hu₁⟩ := exists_four_squares hres1
  have hg0 : F.Graph a q := ⟨u₀, by simp only [Sol]; linarith [hu₀]⟩
  have hg1 : F.Graph a b₁ := ⟨u₁, by simp only [Sol]; linarith [hu₁]⟩
  have heq : q = b₁ := hU a q b₁ hg0 hg1
  have : q j₀ = q j₀ + 1 := by
    have := congrFun heq j₀
    simpa [hb₁] using this
  omega

/-- **C1, packaged.**  `0 ≤ R(a) < m k²` at every input. -/
theorem residual_bounded (hm : 0 < m) (hT : F.Total) (hU : F.OutputUnique) (a : Fin n → ℤ) :
    0 ≤ F.R a ∧ F.R a < (m : ℤ) * F.k ^ 2 :=
  ⟨F.R_nonneg hT a, F.R_lt hm hT hU a⟩

/-- NEGATIVE control for `m ≥ 1`: with no output coordinate the bound is false.  `m = 0` makes
the squared-error sum empty, so `R(a) = Σ u_i²` may be any non-negative value — take `R(a) = a₀²`
on `n = 1`, which is total and (vacuously) output-unique but unbounded. -/
theorem m_zero_counterexample :
    ∃ F : Family 1 0, F.Total ∧ F.OutputUnique ∧ ¬ ∀ a, F.R a < (0 : ℤ) * F.k ^ 2 := by
  refine ⟨⟨1, le_refl 1, fun j => j.elim0, fun j => j.elim0, fun a => (a 0) ^ 2⟩, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨u, hu⟩ := exists_four_squares (N := (a 0) ^ 2) (sq_nonneg _)
    refine ⟨fun j => j.elim0, u, ?_⟩
    simp only [Family.Sol, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    exact hu
  · intro a b b' _ _
    funext j
    exact j.elim0
  · intro h
    have := h (fun _ => 1)
    norm_num at this




end Family

/-! ### C2 — a uniformly bounded integer quadratic is constant

The reviewer's step (2).  Stated for `IntQuad`, the project's own faithful degree-≤2 carrier, so
that `isQuadRep_of_totalDegree_le_two` (the existing forward compiler) carries it to any
`MvPolynomial` of total degree ≤ 2.  No coordinate-by-coordinate argument is needed: the line
through `x` already kills both coefficients at once.
-/

/-- A bounded integer quadratic in ONE variable has zero linear and zero quadratic coefficient.
Two-point trick: `f(T) + f(−T) = 2γ + 2αT²` and `f(T) − f(−T) = 2βT`, read at `T = C + 1`.
No limit, no analysis, no finite search. -/
theorem line_coeffs_zero {α β γ C : ℤ} (h : ∀ t : ℤ, |γ + β * t + α * t ^ 2| ≤ C) :
    α = 0 ∧ β = 0 := by
  have h0 : |γ| ≤ C := by simpa using h 0
  have hC : 0 ≤ C := le_trans (abs_nonneg γ) h0
  rw [abs_le] at h0
  set T : ℤ := C + 1 with hTdef
  have hT1 : 1 ≤ T := by omega
  have hp := h T
  have hn := h (-T)
  rw [show γ + β * (-T) + α * (-T) ^ 2 = γ - β * T + α * T ^ 2 from by ring] at hn
  rw [abs_le] at hp hn
  constructor
  · rcases lt_trichotomy α 0 with hneg | hzero | hpos
    · exfalso
      have hα : α ≤ -1 := by omega
      nlinarith [hp.1, hp.2, hn.1, hn.2, h0.1, h0.2, hT1]
    · exact hzero
    · exfalso
      have hα : 1 ≤ α := by omega
      nlinarith [hp.1, hp.2, hn.1, hn.2, h0.1, h0.2, hT1]
  · rcases lt_trichotomy β 0 with hneg | hzero | hpos
    · exfalso
      have hβ : β ≤ -1 := by omega
      nlinarith [hp.1, hp.2, hn.1, hn.2, h0.1, h0.2, hT1]
    · exact hzero
    · exfalso
      have hβ : 1 ≤ β := by omega
      nlinarith [hp.1, hp.2, hn.1, hn.2, h0.1, h0.2, hT1]

open DiophCompression.ResearchUpgrade in
/-- Restriction to the line `t ↦ t • v` is an honest quadratic in `t`. -/
theorem eval_smul {n : ℕ} (P : IntQuad (Fin n)) (v : Fin n → ℤ) (t : ℤ) :
    P.eval (t • v) = P.c + (P.l ⬝ᵥ v) * t + (v ⬝ᵥ (P.Q *ᵥ v)) * t ^ 2 := by
  simp only [IntQuad.eval, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

open DiophCompression.ResearchUpgrade in
/-- **C2.**  An integer polynomial of total degree ≤ 2 that is bounded on ALL of `ℤⁿ` is constant.
`n = 0` is included (the input space is a point).  Note what is NOT concluded: the matrix `Q` is
not asserted to be zero — its skew part contributes nothing to `eval`, so the conclusion is about
the form, not the matrix. -/
theorem const_of_bounded {n : ℕ} (P : IntQuad (Fin n)) {C : ℤ}
    (h : ∀ x : Fin n → ℤ, |P.eval x| ≤ C) (x : Fin n → ℤ) : P.eval x = P.c := by
  have hline : ∀ t : ℤ, |P.c + (P.l ⬝ᵥ x) * t + (x ⬝ᵥ (P.Q *ᵥ x)) * t ^ 2| ≤ C := by
    intro t
    rw [← eval_smul P x t]
    exact h _
  obtain ⟨hq, hl⟩ := line_coeffs_zero hline
  have h1 : P.eval x = P.c + (P.l ⬝ᵥ x) * 1 + (x ⬝ᵥ (P.Q *ᵥ x)) * 1 ^ 2 := by
    rw [← eval_smul P x 1]
    simp
  rw [h1, hq, hl]
  ring

namespace Family

variable {n m : ℕ} (F : Family n m)

open DiophCompression.ResearchUpgrade in
/-- **C1 + C2.**  If the residual is carried by a degree-≤2 integer polynomial, it is constant. -/
theorem R_const (hm : 0 < m) (hT : F.Total) (hU : F.OutputUnique)
    {P : IntQuad (Fin n)} (hR : ∀ a, F.R a = P.eval a) (a : Fin n → ℤ) :
    F.R a = F.R 0 := by
  have hk2 : (0 : ℤ) ≤ (m : ℤ) * F.k ^ 2 := by positivity
  have hb : ∀ x : Fin n → ℤ, |P.eval x| ≤ (m : ℤ) * F.k ^ 2 := by
    intro x
    obtain ⟨hlo, hhi⟩ := F.residual_bounded hm hT hU x
    rw [← hR x, abs_le]
    exact ⟨by linarith, by linarith⟩
  rw [hR a, hR 0, const_of_bounded P hb a, const_of_bounded P hb 0]

end Family


/-! ### C3 — translation covariance, and the full-residue vector normal form

With `R` constant the SAME witness `u` solves the equation at `(a + k t, b + B t)`: the squared
error is unchanged coordinate by coordinate, because `ℓ(a + k t) = ℓ(a) + k B t` cancels the
`k B t` added to the output.  Output uniqueness then turns that into an identity for `f`.
The modulus is `k`, and it depends on neither `ρ` nor `t`; no per-input denominator is promoted
to a uniform one, and no ray or one-sided cone is involved.
-/

namespace Family

variable {n m : ℕ} (F : Family n m)

theorem lin_translate (a t : Fin n → ℤ) (j : Fin m) :
    F.lin (a + F.k • t) j = F.lin a j + F.k * ∑ i, F.B j i * t i := by
  have hterm : ∀ i, F.B j i * ((a + F.k • t) i) = F.B j i * a i + F.k * (F.B j i * t i) := by
    intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [lin, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib]
  ring

/-- The same witness solves the translated equation. -/
theorem graph_translate (hconst : ∀ a, F.R a = F.R 0)
    {a : Fin n → ℤ} {b : Fin m → ℤ} (h : F.Graph a b) (t : Fin n → ℤ) :
    F.Graph (a + F.k • t) (fun j => b j + ∑ i, F.B j i * t i) := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_⟩
  have hterm : ∀ j : Fin m,
      (F.k * (b j + ∑ i, F.B j i * t i) - F.lin (a + F.k • t) j) ^ 2
        = (F.k * b j - F.lin a j) ^ 2 := by
    intro j
    rw [F.lin_translate a t j]
    ring
  simp only [Sol] at hu ⊢
  rw [Finset.sum_congr rfl fun j _ => hterm j, hconst (a + F.k • t), ← hconst a]
  exact hu

/-- **C3, the covariance.**  `f(a + k t) = f(a) + B t` at every input and every step. -/
theorem output_translate (hU : F.OutputUnique) (hconst : ∀ a, F.R a = F.R 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : ∀ a, F.Graph a (f a)) (a t : Fin n → ℤ) :
    f (a + F.k • t) = fun j => f a j + ∑ i, F.B j i * t i :=
  hU (a + F.k • t) _ _ (hf (a + F.k • t)) (F.graph_translate hconst (hf a) t)

/-- **C3, the normal form.**  `f` is affine on EVERY residue class modulo `k`, in the vocabulary
of B1.  The quadratic part of each `QuadForm` is literally `0`: the conclusion is affine, not
merely degree ≤ 2. -/
theorem fullVectorCosetNF_of_constant_residual (hU : F.OutputUnique)
    (hconst : ∀ a, F.R a = F.R 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : ∀ a, F.Graph a (f a)) :
    FullVectorCosetNF f := by
  have hk : ((F.k.toNat : ℤ)) = F.k := Int.toNat_of_nonneg (by have := F.hk; omega)
  refine ⟨F.k.toNat, by have := F.hk; omega, fun ρ => ?_⟩
  refine ⟨fun j => ⟨(f ρ j : ℚ), fun i => (F.B j i : ℚ), 0⟩, ?_⟩
  intro t j
  rw [hk, F.output_translate hU hconst hf ρ t]
  simp only [QuadForm.eval, castQ, Matrix.zero_mulVec, add_zero, dotProduct]
  push_cast
  simp

/-- **C1 + C2 + C3.**  For a degree-≤2 residual the whole chain closes: bounded, hence constant,
hence affine on every class modulo `k`. -/
theorem fullVectorCosetNF_of_intQuad_residual (hm : 0 < m) (hT : F.Total) (hU : F.OutputUnique)
    {P : IntQuad (Fin n)} (hR : ∀ a, F.R a = P.eval a)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : ∀ a, F.Graph a (f a)) :
    FullVectorCosetNF f :=
  F.fullVectorCosetNF_of_constant_residual hU (F.R_const hm hT hU hR) hf

end Family


/-! ### The non-vacuity control for Packet C

`n = m = 1`, `k = 3`, `ℓ(a) = a`, `R ≡ 1`:

    (3b − a)² + u₁² + u₂² + u₃² + u₄² = 1,      f(a) = ⌊(a+1)/3⌋.

`3b − a ≡ −a (mod 3)`, so of the three admissible values `{−1,0,1}` exactly one fits each residue
class; the leftover `1 − (3b−a)²` is `0` or `1` and is filled by four squares.  The function is
affine on each class modulo 3 and is NOT a single rational polynomial on ℤ, and at `a ≡ 0 (mod 3)`
the same output carries several witnesses — so output uniqueness is genuinely weaker than witness
uniqueness here.  The proof is by residues, not by a finite window.
-/

/-- `x² ≤ 1` on ℤ is the interval `−1 ≤ x ≤ 1`. -/
theorem sq_le_one_iff (x : ℤ) : x ^ 2 ≤ 1 ↔ -1 ≤ x ∧ x ≤ 1 := by
  constructor
  · intro h; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; nlinarith

/-- The control family. -/
def Ex : Family 1 1 := ⟨3, by norm_num, fun _ => 0, fun _ _ => 1, fun _ => 1⟩

theorem Ex_sol_iff (a b : Fin 1 → ℤ) (u : Fin 4 → ℤ) :
    Ex.Sol a b u ↔ (3 * b 0 - a 0) ^ 2 + ∑ i, (u i) ^ 2 = 1 := by
  simp [Family.Sol, Family.lin, Ex, Fin.sum_univ_one]

theorem Ex_total : Ex.Total := by
  intro a
  refine ⟨fun _ => (a 0 + 1) / 3, ?_⟩
  have hrange : -1 ≤ 3 * ((a 0 + 1) / 3) - a 0 ∧ 3 * ((a 0 + 1) / 3) - a 0 ≤ 1 := by omega
  have hsq : (3 * ((a 0 + 1) / 3) - a 0) ^ 2 ≤ 1 := (sq_le_one_iff _).mpr hrange
  obtain ⟨u, hu⟩ := exists_four_squares (N := 1 - (3 * ((a 0 + 1) / 3) - a 0) ^ 2) (by linarith)
  exact ⟨u, (Ex_sol_iff a _ u).mpr (by linarith)⟩

theorem Ex_outputUnique : Ex.OutputUnique := by
  rintro a b b' ⟨u, hu⟩ ⟨u', hu'⟩
  rw [Ex_sol_iff] at hu hu'
  have h1 : (0 : ℤ) ≤ ∑ i, (u i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1' : (0 : ℤ) ≤ ∑ i, (u' i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hb := (sq_le_one_iff (3 * b 0 - a 0)).mp (by linarith)
  have hb' := (sq_le_one_iff (3 * b' 0 - a 0)).mp (by linarith)
  have : b 0 = b' 0 := by omega
  funext j
  fin_cases j
  exact this

theorem Ex_value (a b : Fin 1 → ℤ) : Ex.Graph a b ↔ b 0 = (a 0 + 1) / 3 := by
  constructor
  · rintro ⟨u, hu⟩
    rw [Ex_sol_iff] at hu
    have h1 : (0 : ℤ) ≤ ∑ i, (u i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hb := (sq_le_one_iff (3 * b 0 - a 0)).mp (by linarith)
    omega
  · intro hb
    have hrange : -1 ≤ 3 * b 0 - a 0 ∧ 3 * b 0 - a 0 ≤ 1 := by omega
    have hsq : (3 * b 0 - a 0) ^ 2 ≤ 1 := (sq_le_one_iff _).mpr hrange
    obtain ⟨u, hu⟩ := exists_four_squares (N := 1 - (3 * b 0 - a 0) ^ 2) (by linarith)
    exact ⟨u, (Ex_sol_iff a b u).mpr (by linarith)⟩

theorem Ex_witness_not_unique :
    ∃ (a b : Fin 1 → ℤ) (u u' : Fin 4 → ℤ), u ≠ u' ∧ Ex.Sol a b u ∧ Ex.Sol a b u' := by
  refine ⟨fun _ => 0, fun _ => 0, ![1, 0, 0, 0], ![0, 1, 0, 0], ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · rw [Ex_sol_iff]; simp [Fin.sum_univ_four]
  · rw [Ex_sol_iff]; simp [Fin.sum_univ_four]

/-- The control is not a single rational polynomial of degree ≤ 2 on ℤ: the values at
`a = 0,1,2,3` are `0,0,1,1`, and no rational quadratic does that. -/
theorem Ex_not_global_quadratic :
    ¬ ∃ c₀ c₁ c₂ : ℚ, ∀ a : ℤ, (((a + 1) / 3 : ℤ) : ℚ) = c₀ + c₁ * (a : ℚ) + c₂ * (a : ℚ) ^ 2 := by
  rintro ⟨c₀, c₁, c₂, h⟩
  have e0 := h 0
  have e1 := h 1
  have e2 := h 2
  have e3 := h 3
  norm_num at e0 e1 e2 e3
  linarith

/-- The control satisfies the C3 conclusion: affine on every class modulo 3. -/
theorem Ex_fullVectorCosetNF :
    FullVectorCosetNF (fun a : Fin 1 → ℤ => fun _ : Fin 1 => (a 0 + 1) / 3) :=
  Ex.fullVectorCosetNF_of_constant_residual Ex_outputUnique (fun _ => rfl)
    (fun a => (Ex_value a _).mpr rfl)

end DiophCompression.ResearchUpgrade.FourSquareSlack
