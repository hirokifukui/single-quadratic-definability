/-
  NInputNoWitness.lean — Gate-18 research program, Packet c1_ninput.
  "No witness, n inputs": the relation
    `P(x,y) = a y² + (β·x + d) y + (xᵀEx + φ·x + g) = 0`   (x ∈ ℤⁿ, y ∈ ℤ)
  with a unique output `y` for every input `x` (RelTotal + RelUnique) makes the output
  function `fn` land in the full-residue coset normal form (`FullCosetNF`), hence the weak
  scalar coset form — the `r = 0` conjecture for ALL n (docs/C3_RESEARCH_MEMO_s45.md §1).

  Engine: the discriminant `Δ(x) = (β·x+d)² − 4a(xᵀEx+φ·x+g)` is a perfect square at every
  `x` (its integer square root is `2a·f(x) + (β·x+d)`), so by the multi-input rigidity
  `c21_affine_square` it is an affine square `Δ(x) = (ℓ·x+s)²` over ℚ; here `ℓ, s` are in fact
  integers (their square-roots at integer points are integers), so the two branches
  `y± = (−(β·x+d) ± (ℓ·x+s))/(2a)` are affine with denominator dividing `2a`, and on each coset
  `ρ + 2|a|·ℤⁿ` uniqueness selects one branch — a QuadForm of degree 1 per coset.

  The degenerate branch `a = 0` gives a single global quadratic: for `β = 0` the output is the
  rational quadratic `−(xᵀEx+φ·x+g)/d`; for `β ≠ 0` the quadratic form `T(x)` obstructing
  affinity is divisible by `β·x+d` at every point yet homogeneous of degree 2, forcing `T ≡ 0`
  (an arbitrarily large integer cannot divide a fixed nonzero one), so the output is affine.

  Baseline (mpup-lean r39) is read-only; nothing here is imported by the baseline.
  Contains no proof holes and introduces no new axioms (std-3 only; see certificates/AxiomReport_c1n.log).
-/
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import ResearchUpgrade.C2Partial
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.SmallLeaves

namespace DiophCompression.ResearchUpgrade

open Matrix

/-- The defining polynomial of a C1 family with `n` inputs. -/
def Pn {n : ℕ} (a : ℤ) (β : Fin n → ℤ) (d : ℤ) (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ)
    (g : ℤ) (x : Fin n → ℤ) (y : ℤ) : ℤ :=
  a * y ^ 2 + (β ⬝ᵥ x + d) * y + (x ⬝ᵥ (E *ᵥ x) + φ ⬝ᵥ x + g)

/-- The `n`-input relation `Pn = 0`. -/
def Rn {n : ℕ} (a : ℤ) (β : Fin n → ℤ) (d : ℤ) (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ)
    (g : ℤ) (x : Fin n → ℤ) (y : ℤ) : Prop := Pn a β d E φ g x y = 0

/-- The choice-extracted unique output of a total relation. -/
noncomputable def fn {n : ℕ} (a : ℤ) (β : Fin n → ℤ) (d : ℤ) (E : Matrix (Fin n) (Fin n) ℤ)
    (φ : Fin n → ℤ) (g : ℤ) (hT : RelTotal (Rn a β d E φ g)) : (Fin n → ℤ) → ℤ :=
  fun x => Classical.choose (hT x)

/-! ### The discriminant as a `deltaQ`. -/

/-- The discriminant `Δ(x) = (β·x+d)² − 4a(xᵀEx+φ·x+g)` written as a `deltaQ` with matrix
`ββᵀ − 4aE`, vector `2dβ − 4aφ`, constant `d² − 4ag`. -/
theorem deltaQ_disc {n : ℕ} (a : ℤ) (β : Fin n → ℤ) (d : ℤ) (E : Matrix (Fin n) (Fin n) ℤ)
    (φ : Fin n → ℤ) (g : ℤ) (x : Fin n → ℤ) :
    deltaQ (vecMulVec β β - (4 * a) • E) ((2 * d) • β - (4 * a) • φ) (d ^ 2 - 4 * a * g) x
      = (β ⬝ᵥ x + d) ^ 2 - 4 * a * (x ⬝ᵥ (E *ᵥ x) + φ ⬝ᵥ x + g) := by
  have hquad : x ⬝ᵥ ((vecMulVec β β - (4 * a) • E) *ᵥ x)
      = (β ⬝ᵥ x) * (β ⬝ᵥ x) - 4 * a * (x ⬝ᵥ (E *ᵥ x)) := by
    rw [sub_mulVec, dotProduct_sub]
    congr 1
    · simp only [dotProduct, Matrix.mulVec, vecMulVec_apply]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      ring
    · rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hlin : ((2 * d) • β - (4 * a) • φ) ⬝ᵥ x = 2 * d * (β ⬝ᵥ x) - 4 * a * (φ ⬝ᵥ x) := by
    rw [sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  simp only [deltaQ, hquad, hlin]
  ring

/-- Casting an integer dot product: `castQ v ⬝ᵥ castQ x = ↑(v ⬝ᵥ x)`. -/
theorem castQ_dot {n : ℕ} (v x : Fin n → ℤ) : castQ v ⬝ᵥ castQ x = ((v ⬝ᵥ x : ℤ) : ℚ) := by
  simp only [dotProduct, castQ, Int.cast_sum]
  apply Finset.sum_congr rfl; intro i _; push_cast; ring

/-- Casting an integer quadratic form. -/
theorem castQ_quad {n : ℕ} (E : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    castQ x ⬝ᵥ ((E.map (fun z : ℤ => (z : ℚ))) *ᵥ castQ x) = ((x ⬝ᵥ (E *ᵥ x) : ℤ) : ℚ) := by
  simp only [dotProduct, Matrix.mulVec, castQ, Matrix.map_apply, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/-! ### Theorem 1 — the generic branch `a ≠ 0` gives the full-residue coset normal form. -/

theorem n_a_ne_zero_full {n : ℕ} (a : ℤ) (β : Fin n → ℤ) (d : ℤ) (E : Matrix (Fin n) (Fin n) ℤ)
    (φ : Fin n → ℤ) (g : ℤ) (hT : RelTotal (Rn a β d E φ g)) (hU : RelUnique (Rn a β d E φ g))
    (ha : a ≠ 0) : FullCosetNF (fn a β d E φ g hT) := by
  set gfun : (Fin n → ℤ) → ℤ := fun x => Classical.choose (hT x) with hgfun
  have hspec : ∀ x : Fin n → ℤ,
      a * gfun x ^ 2 + (β ⬝ᵥ x + d) * gfun x + (x ⬝ᵥ (E *ᵥ x) + φ ⬝ᵥ x + g) = 0 := by
    intro x; have h := Classical.choose_spec (hT x); simpa [Rn, Pn, hgfun] using h
  -- The discriminant matrix / vector / constant.
  set Am : Matrix (Fin n) (Fin n) ℤ := vecMulVec β β - (4 * a) • E with hAm
  set bv : Fin n → ℤ := (2 * d) • β - (4 * a) • φ with hbv
  set cv : ℤ := d ^ 2 - 4 * a * g with hcv
  -- `w x := 2a·f(x) + (β·x+d)` is an integer square root of `Δ(x)`.
  have hw : ∀ x : Fin n → ℤ, (2 * a * gfun x + (β ⬝ᵥ x + d)) ^ 2 = deltaQ Am bv cv x := by
    intro x; rw [hAm, hbv, hcv, deltaQ_disc]; linear_combination (4 * a) * hspec x
  have hdisc : ∀ x : Fin n → ℤ, IsSquare (deltaQ Am bv cv x) :=
    fun x => ⟨2 * a * gfun x + (β ⬝ᵥ x + d), by rw [← hw x]; ring⟩
  obtain ⟨ℓ, s, hℓs⟩ := c21_affine_square Am bv cv hdisc
  -- The affine ℚ-form is integer-valued at every integer point.
  have hFint : ∀ x : Fin n → ℤ, ∃ z : ℤ, (z : ℚ) = ℓ ⬝ᵥ castQ x + s := by
    intro x
    have hEq : (ℓ ⬝ᵥ castQ x + s) ^ 2 = ((2 * a * gfun x + (β ⬝ᵥ x + d) : ℤ) : ℚ) ^ 2 := by
      rw [← hℓs x, ← hw x]; push_cast; ring
    have hfac : (ℓ ⬝ᵥ castQ x + s - ((2 * a * gfun x + (β ⬝ᵥ x + d) : ℤ) : ℚ))
        * (ℓ ⬝ᵥ castQ x + s + ((2 * a * gfun x + (β ⬝ᵥ x + d) : ℤ) : ℚ)) = 0 := by
      linear_combination hEq
    rcases mul_eq_zero.1 hfac with h | h
    · exact ⟨2 * a * gfun x + (β ⬝ᵥ x + d), by linarith [sub_eq_zero.1 h]⟩
    · refine ⟨-(2 * a * gfun x + (β ⬝ᵥ x + d)), ?_⟩; push_cast at h ⊢; linarith [h]
  -- Extract integer `s'` and integer vector `ℓ'`.
  obtain ⟨s', hs'0⟩ := hFint 0
  have hs' : (s' : ℚ) = s := by
    rw [hs'0]; have : ℓ ⬝ᵥ castQ (0 : Fin n → ℤ) = 0 := by simp [castQ, dotProduct]
    rw [this, zero_add]
  have hli : ∀ i, ∃ z : ℤ, (z : ℚ) = ℓ i := by
    intro i
    obtain ⟨z, hz⟩ := hFint (Pi.single i 1)
    refine ⟨z - s', ?_⟩
    have hdot : ℓ ⬝ᵥ castQ (Pi.single i (1 : ℤ)) = ℓ i := by
      have : castQ (Pi.single i (1 : ℤ)) = Pi.single i (1 : ℚ) := by
        funext j; simp [castQ, Pi.single_apply]
      rw [this, dotProduct_single, mul_one]
    rw [hdot] at hz
    push_cast; rw [hz, hs']; ring
  choose ℓ' hℓ' using hli
  have hℚcast : ∀ x : Fin n → ℤ, ((ℓ' ⬝ᵥ x : ℤ) : ℚ) = ℓ ⬝ᵥ castQ x := by
    intro x
    simp only [dotProduct, castQ, Int.cast_sum]
    apply Finset.sum_congr rfl; intro i _; rw [← hℓ' i]; push_cast; ring
  -- The integer affine-square identity `Δ(x) = (ℓ'·x + s')²`.
  have hΔ : ∀ x : Fin n → ℤ, deltaQ Am bv cv x = (ℓ' ⬝ᵥ x + s') ^ 2 := by
    intro x
    have hq : ((deltaQ Am bv cv x : ℤ) : ℚ) = (((ℓ' ⬝ᵥ x + s') ^ 2 : ℤ) : ℚ) := by
      rw [hℓs x, ← hℚcast x, ← hs']; push_cast; ring
    exact_mod_cast hq
  -- The discriminant identity `(β·x+d)² − 4a·Q(x) = (ℓ'·x+s')²`.
  have hDsc : ∀ x : Fin n → ℤ,
      (β ⬝ᵥ x + d) ^ 2 - 4 * a * (x ⬝ᵥ (E *ᵥ x) + φ ⬝ᵥ x + g) = (ℓ' ⬝ᵥ x + s') ^ 2 := by
    intro x; rw [← deltaQ_disc a β d E φ g x, ← hAm, ← hbv, ← hcv]; exact hΔ x
  -- The `±` branch fact.
  have hsplit : ∀ x : Fin n → ℤ, 2 * a * gfun x + (β ⬝ᵥ x + d) = ℓ' ⬝ᵥ x + s'
      ∨ 2 * a * gfun x + (β ⬝ᵥ x + d) = -(ℓ' ⬝ᵥ x + s') := by
    intro x
    have hsq : (2 * a * gfun x + (β ⬝ᵥ x + d)) ^ 2 = (ℓ' ⬝ᵥ x + s') ^ 2 := by
      rw [hw x, hΔ x]
    have hfac : (2 * a * gfun x + (β ⬝ᵥ x + d) - (ℓ' ⬝ᵥ x + s'))
        * (2 * a * gfun x + (β ⬝ᵥ x + d) + (ℓ' ⬝ᵥ x + s')) = 0 := by linear_combination hsq
    rcases mul_eq_zero.1 hfac with h | h
    · left; linarith
    · right; linarith
  -- The modulus `M = 2|a|`.
  set M : ℕ := 2 * a.natAbs with hMdef
  have hMcast : (M : ℤ) = 2 * |a| := by rw [hMdef]; push_cast; rw [Int.abs_eq_natAbs]
  have hMdvd : (2 * a) ∣ (M : ℤ) := by
    rw [hMcast]; exact mul_dvd_mul_left 2 ((dvd_abs a a).mpr (dvd_refl a))
  have h2a : (2 * a : ℤ) ≠ 0 := by intro hh; apply ha; linarith
  refine ⟨M, ?_, fun ρ => ?_⟩
  · have : a.natAbs ≠ 0 := Int.natAbs_ne_zero.2 ha
    rw [hMdef]; omega
  · -- Pick the branch `ε ∈ {±1}` realised by `f(ρ)`.
    obtain ⟨ε, hε2, hεℓ⟩ : ∃ ε : ℤ, ε ^ 2 = 1
        ∧ 2 * a * gfun ρ + (β ⬝ᵥ ρ + d) = ε * (ℓ' ⬝ᵥ ρ + s') := by
      rcases hsplit ρ with h | h
      · exact ⟨1, by norm_num, by rw [one_mul]; exact h⟩
      · exact ⟨-1, by norm_num, by rw [neg_one_mul]; exact h⟩
    -- The integer direction vector `wv := -β + ε • ℓ'`.
    set wv : Fin n → ℤ := -β + ε • ℓ' with hwvdef
    have hwt : ∀ u : Fin n → ℤ, wv ⬝ᵥ u = -(β ⬝ᵥ u) + ε * (ℓ' ⬝ᵥ u) := by
      intro u; rw [hwvdef, add_dotProduct, neg_dotProduct, smul_dotProduct, smul_eq_mul]
    -- On the whole coset `ρ + Mℤⁿ` the output follows the `ε`-branch (uniqueness).
    have hval : ∀ τ : Fin n → ℤ, 2 * a * gfun (ρ + (M : ℤ) • τ)
        = (-(β ⬝ᵥ ρ + d) + ε * (ℓ' ⬝ᵥ ρ + s')) + (M : ℤ) * (wv ⬝ᵥ τ) := by
      intro τ
      set x : Fin n → ℤ := ρ + (M : ℤ) • τ with hx
      have hβx : β ⬝ᵥ x = β ⬝ᵥ ρ + (M : ℤ) * (β ⬝ᵥ τ) := by
        rw [hx, dotProduct_add, dotProduct_smul, smul_eq_mul]
      have hℓx : ℓ' ⬝ᵥ x = ℓ' ⬝ᵥ ρ + (M : ℤ) * (ℓ' ⬝ᵥ τ) := by
        rw [hx, dotProduct_add, dotProduct_smul, smul_eq_mul]
      -- The `ε`-branch value is `2a`-divisible on the coset.
      have hV0 : (2 * a) ∣ (-(β ⬝ᵥ ρ + d) + ε * (ℓ' ⬝ᵥ ρ + s')) :=
        ⟨gfun ρ, by linear_combination -hεℓ⟩
      have hstep : (2 * a) ∣ ((M : ℤ) * (wv ⬝ᵥ τ)) :=
        dvd_mul_of_dvd_left hMdvd _
      have hVdvd : (2 * a) ∣ (-(β ⬝ᵥ x + d) + ε * (ℓ' ⬝ᵥ x + s')) := by
        have heq : -(β ⬝ᵥ x + d) + ε * (ℓ' ⬝ᵥ x + s')
            = (-(β ⬝ᵥ ρ + d) + ε * (ℓ' ⬝ᵥ ρ + s')) + (M : ℤ) * (wv ⬝ᵥ τ) := by
          rw [hβx, hℓx, hwt]; ring
        rw [heq]; exact dvd_add hV0 hstep
      obtain ⟨k, hk⟩ := hVdvd
      have hyc : 2 * a * k = -(β ⬝ᵥ x + d) + ε * (ℓ' ⬝ᵥ x + s') := by linear_combination -hk
      have hRk : a * k ^ 2 + (β ⬝ᵥ x + d) * k + (x ⬝ᵥ (E *ᵥ x) + φ ⬝ᵥ x + g) = 0 := by
        have h4 : (4 * a) * (a * k ^ 2 + (β ⬝ᵥ x + d) * k + (x ⬝ᵥ (E *ᵥ x) + φ ⬝ᵥ x + g)) = 0 := by
          have hbranch : 2 * a * k + (β ⬝ᵥ x + d) = ε * (ℓ' ⬝ᵥ x + s') := by linear_combination hyc
          have hd := hDsc x
          linear_combination (2 * a * k + (β ⬝ᵥ x + d) + ε * (ℓ' ⬝ᵥ x + s')) * hbranch
            + (ℓ' ⬝ᵥ x + s') ^ 2 * hε2 - hd
        rcases mul_eq_zero.1 h4 with hh | hh
        · exact absurd hh (by intro hz; apply ha; linarith)
        · exact hh
      have hRgn : Rn a β d E φ g x (gfun x) := hspec x
      have hRkR : Rn a β d E φ g x k := by simp only [Rn, Pn]; linear_combination hRk
      have hgn : gfun x = k := hU x (gfun x) k hRgn hRkR
      rw [hgn, hyc, hβx, hℓx, hwt]; ring
    -- Assemble the affine `QuadForm` for this coset.
    have h2aQ : ((2 * a : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h2a
    refine ⟨⟨((-(β ⬝ᵥ ρ + d) + ε * (ℓ' ⬝ᵥ ρ + s') : ℤ) : ℚ) / ((2 * a : ℤ) : ℚ),
             fun i => ((wv i * (M : ℤ) : ℤ) : ℚ) / ((2 * a : ℤ) : ℚ),
             fun _ _ => 0⟩, fun t => ?_⟩
    show ((gfun (ρ + (M : ℤ) • t) : ℤ) : ℚ) = _
    -- The linear part evaluates to `(wv·t · M)/(2a)`.
    have hlx : (fun i => ((wv i * (M : ℤ) : ℤ) : ℚ) / ((2 * a : ℤ) : ℚ)) ⬝ᵥ castQ t
        = (((wv ⬝ᵥ t) * (M : ℤ) : ℤ) : ℚ) / ((2 * a : ℤ) : ℚ) := by
      have hcast : (((wv ⬝ᵥ t) * (M : ℤ) : ℤ) : ℚ)
          = ∑ i, ((wv i * (M : ℤ) : ℤ) : ℚ) * (t i : ℚ) := by
        rw [dotProduct, Finset.sum_mul, Int.cast_sum]
        apply Finset.sum_congr rfl; intro i _; push_cast; ring
      rw [hcast, Finset.sum_div]
      simp only [dotProduct, castQ]
      apply Finset.sum_congr rfl; intro i _; ring
    simp only [QuadForm.eval]
    rw [show (castQ t ⬝ᵥ ((fun _ _ => (0 : ℚ)) *ᵥ castQ t)) = 0 by
      simp [dotProduct, Matrix.mulVec], add_zero, hlx, ← add_div, eq_div_iff h2aQ]
    have hgQ : ((2 * a : ℤ) : ℚ) * ((gfun (ρ + (M : ℤ) • t) : ℤ) : ℚ)
        = ((-(β ⬝ᵥ ρ + d) + ε * (ℓ' ⬝ᵥ ρ + s') + (M : ℤ) * (wv ⬝ᵥ t) : ℤ) : ℚ) := by
      exact_mod_cast hval t
    push_cast at hgQ ⊢
    linear_combination hgQ

/-! ### Theorem 2 — the degenerate branch `a = 0` gives a single global quadratic. -/

theorem n_a_zero_global {n : ℕ} (a : ℤ) (β : Fin n → ℤ) (d : ℤ) (E : Matrix (Fin n) (Fin n) ℤ)
    (φ : Fin n → ℤ) (g : ℤ) (hT : RelTotal (Rn a β d E φ g)) (hU : RelUnique (Rn a β d E φ g))
    (ha : a = 0) : GlobalQuadratic (fn a β d E φ g hT) := by
  subst ha
  set gfun : (Fin n → ℤ) → ℤ := fun x => Classical.choose (hT x) with hgfun
  have hspec : ∀ x : Fin n → ℤ, (β ⬝ᵥ x + d) * gfun x + (x ⬝ᵥ (E *ᵥ x) + φ ⬝ᵥ x + g) = 0 := by
    intro x
    have h := Classical.choose_spec (hT x)
    have h' : (0 : ℤ) * gfun x ^ 2 + (β ⬝ᵥ x + d) * gfun x + (x ⬝ᵥ (E *ᵥ x) + φ ⬝ᵥ x + g) = 0 := by
      simpa [Rn, Pn, hgfun] using h
    linarith [h']
  -- `β·x + d ≠ 0` for every `x` (uniqueness).
  have hbd : ∀ x : Fin n → ℤ, β ⬝ᵥ x + d ≠ 0 := by
    intro x hbd0
    have hc : x ⬝ᵥ (E *ᵥ x) + φ ⬝ᵥ x + g = 0 := by
      have := hspec x; rw [hbd0] at this; simpa using this
    have r0 : Rn 0 β d E φ g x 0 := by simp only [Rn, Pn]; linear_combination hc
    have r1 : Rn 0 β d E φ g x 1 := by simp only [Rn, Pn]; linear_combination hbd0 + hc
    exact absurd (hU x 0 1 r0 r1) (by norm_num)
  rcases eq_or_ne β 0 with hβ0 | hβ0
  · -- Sub-case `β = 0`: `f(x) = −(xᵀEx+φ·x+g)/d` (a rational quadratic).
    have hd0 : d ≠ 0 := by have h := hbd 0; simpa using h
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
    refine ⟨⟨-(g : ℚ) / d, (-(d : ℚ)⁻¹) • castQ φ,
             (-(d : ℚ)⁻¹) • E.map (fun z : ℤ => (z : ℚ))⟩, fun x => ?_⟩
    have hs : d * gfun x + (x ⬝ᵥ (E *ᵥ x) + φ ⬝ᵥ x + g) = 0 := by
      have := hspec x; rw [hβ0] at this; simpa using this
    have hsQ : (d : ℚ) * (gfun x : ℚ)
        + (((x ⬝ᵥ (E *ᵥ x) : ℤ) : ℚ) + ((φ ⬝ᵥ x : ℤ) : ℚ) + (g : ℚ)) = 0 := by
      exact_mod_cast hs
    show ((gfun x : ℤ) : ℚ) = _
    rw [show ((gfun x : ℤ) : ℚ)
        = -(((x ⬝ᵥ (E *ᵥ x) : ℤ) : ℚ) + ((φ ⬝ᵥ x : ℤ) : ℚ) + (g : ℚ)) / (d : ℚ) from by
      rw [eq_div_iff hdQ]; linear_combination hsQ]
    simp only [QuadForm.eval, smul_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      castQ_quad, castQ_dot]
    field_simp
    ring
  · -- Sub-case `β ≠ 0`: `f` is affine, `d² f(x) = ũ·x + w̃` with `ũ = gβ − dφ`, `w̃ = −dg`.
    set uc : Fin n → ℤ := g • β - d • φ with huc
    set wc : ℤ := -(d * g) with hwc
    set Mm : Matrix (Fin n) (Fin n) ℤ := vecMulVec β uc + (d ^ 2) • E with hMm
    have hd0 : d ≠ 0 := by have h := hbd 0; simpa using h
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
    have hucdot : ∀ x : Fin n → ℤ, uc ⬝ᵥ x = g * (β ⬝ᵥ x) - d * (φ ⬝ᵥ x) := by
      intro x; rw [huc, sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    -- `Tf x := deltaQ Mm 0 0 x` is the pure quadratic form `(β·x)(ũ·x) + d²(xᵀEx)`.
    set Tf : (Fin n → ℤ) → ℤ := deltaQ Mm 0 0 with hTf
    have hTval : ∀ x : Fin n → ℤ, Tf x = (β ⬝ᵥ x) * (uc ⬝ᵥ x) + d ^ 2 * (x ⬝ᵥ (E *ᵥ x)) := by
      intro x
      have hq : x ⬝ᵥ (Mm *ᵥ x) = (β ⬝ᵥ x) * (uc ⬝ᵥ x) + d ^ 2 * (x ⬝ᵥ (E *ᵥ x)) := by
        rw [hMm, add_mulVec, dotProduct_add]
        congr 1
        · simp only [dotProduct, Matrix.mulVec, vecMulVec_apply]
          rw [Finset.sum_mul_sum]
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _
          ring
        · rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
      rw [hTf]; simp only [deltaQ, zero_dotProduct, add_zero]; exact hq
    -- The cancellation identity: `(β·x+d)(ũ·x+w̃) + d²·Q(x) = Tf x`.
    have hWANT : ∀ x : Fin n → ℤ,
        (β ⬝ᵥ x + d) * (uc ⬝ᵥ x + wc) + d ^ 2 * (x ⬝ᵥ (E *ᵥ x) + φ ⬝ᵥ x + g) = Tf x := by
      intro x; rw [hTval x, hucdot x, hwc]; ring
    -- `Tf x` is divisible by `β·x+d`, with cofactor `(ũ·x+w̃) − d²·f(x)`.
    have hdvdT : ∀ x : Fin n → ℤ, Tf x = (β ⬝ᵥ x + d) * ((uc ⬝ᵥ x + wc) - d ^ 2 * gfun x) := by
      intro x; rw [← hWANT x]; linear_combination (d ^ 2) * hspec x
    -- `Tf` is homogeneous of degree 2.
    have hThom : ∀ (k : ℤ) (x : Fin n → ℤ), Tf (k • x) = k ^ 2 * Tf x := by
      intro k x
      rw [hTval, hTval,
        show β ⬝ᵥ (k • x) = k * (β ⬝ᵥ x) by rw [dotProduct_smul, smul_eq_mul],
        show uc ⬝ᵥ (k • x) = k * (uc ⬝ᵥ x) by rw [dotProduct_smul, smul_eq_mul],
        show (k • x) ⬝ᵥ (E *ᵥ (k • x)) = k * (k * (x ⬝ᵥ (E *ᵥ x))) by
          rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]]
      ring
    -- If `β·x ≠ 0` then `Tf x = 0`.
    have hTne : ∀ x : Fin n → ℤ, β ⬝ᵥ x ≠ 0 → Tf x = 0 := by
      intro x hp
      by_contra hTx
      set p : ℤ := β ⬝ᵥ x with hp'
      set m : ℕ := (|Tf x| + |d|).toNat + 1 with hm
      set k : ℤ := 1 + d ^ 2 * (m : ℤ) with hk
      have hcop_dk : IsCoprime d k := by
        rw [hk, show d ^ 2 * (m : ℤ) = d * (d * (m : ℤ)) by ring, IsCoprime.add_mul_left_right_iff]
        exact isCoprime_one_right
      have hcop : IsCoprime (k * p + d) (k ^ 2) := by
        have h1 : IsCoprime (k * p + d) k := by
          rw [show k * p + d = d + p * k by ring]
          exact hcop_dk.add_mul_right_left p
        exact h1.pow_right
      have hdvd1 : (k * p + d) ∣ k ^ 2 * Tf x := by
        have hkx : β ⬝ᵥ (k • x) = k * p := by rw [dotProduct_smul, smul_eq_mul, hp']
        have hh := hdvdT (k • x)
        rw [hkx, hThom] at hh
        exact ⟨(uc ⬝ᵥ (k • x) + wc) - d ^ 2 * gfun (k • x), hh⟩
      have hdvd2 : (k * p + d) ∣ Tf x := hcop.dvd_of_dvd_mul_left hdvd1
      -- but `|k*p+d| > |Tf x|`, contradiction.
      have habs_pos : (0 : ℤ) < |Tf x| := abs_pos.2 hTx
      have hd1 : (1 : ℤ) ≤ |d| := Int.one_le_abs hd0
      have hp1 : (1 : ℤ) ≤ |p| := Int.one_le_abs hp
      have hd2 : (1 : ℤ) ≤ d ^ 2 := by nlinarith [hd1, sq_abs d]
      have hmval : (m : ℤ) = |Tf x| + |d| + 1 := by
        rw [hm]; push_cast; rw [Int.toNat_of_nonneg (by positivity)]
      have hkpos : (0 : ℤ) < k := by
        rw [hk]; nlinarith [hd2, hmval, Int.ofNat_nonneg m, habs_pos, hd1]
      have hkge : |Tf x| + |d| + 1 ≤ k := by
        rw [hk]; nlinarith [hd2, hmval, Int.ofNat_nonneg m]
      have hbig : |Tf x| < |k * p + d| := by
        have htri : |k * p| ≤ |k * p + d| + |d| := by
          have := abs_add_le (k * p + d) (-d); simpa using this
        have hkp : |k * p| = k * |p| := by rw [abs_mul, abs_of_pos hkpos]
        nlinarith [htri, hkp, hkge, hp1, hkpos, hd1, habs_pos]
      have hle : |k * p + d| ≤ |Tf x| :=
        Int.le_of_dvd habs_pos ((abs_dvd _ _).2 ((dvd_abs _ _).2 hdvd2))
      linarith [hbig, hle]
    -- `Tf ≡ 0` on all of ℤⁿ.
    have hTgen : ∀ x : Fin n → ℤ, Tf x = 0 := by
      intro x
      by_cases hbx : β ⬝ᵥ x = 0
      · obtain ⟨i, hi⟩ : ∃ i, β i ≠ 0 := by
          by_contra h; push_neg at h; exact hβ0 (funext h)
        set y : Fin n → ℤ := Pi.single i 1 with hy
        have hby : β ⬝ᵥ y ≠ 0 := by rw [hy, dotProduct_single, mul_one]; exact hi
        have hline : ∀ t : ℤ, Tf (x + t • y)
            = (y ⬝ᵥ (Mm *ᵥ y)) * t ^ 2
              + (x ⬝ᵥ (Mm *ᵥ y) + y ⬝ᵥ (Mm *ᵥ x)) * t + Tf x := by
          intro t
          have h := deltaQ_line Mm 0 0 x y t
          rw [hTf]; simp only [zero_dotProduct, add_zero] at h ⊢; exact h
        have hzero : ∀ t : ℤ, t ≠ 0 →
            (y ⬝ᵥ (Mm *ᵥ y)) * t ^ 2 + (x ⬝ᵥ (Mm *ᵥ y) + y ⬝ᵥ (Mm *ᵥ x)) * t + Tf x = 0 := by
          intro t ht
          rw [← hline t]
          apply hTne
          rw [dotProduct_add, dotProduct_smul, hbx, smul_eq_mul, zero_add]
          exact mul_ne_zero ht hby
        obtain ⟨_, _, hR⟩ := quad_three_roots (hzero 1 (by norm_num)) (hzero 2 (by norm_num))
          (hzero 3 (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
        exact hR
      · exact hTne x hbx
    -- Hence `d²·f(x) = ũ·x + w̃`.
    have hglin : ∀ x : Fin n → ℤ, d ^ 2 * gfun x = uc ⬝ᵥ x + wc := by
      intro x
      have h0 : (β ⬝ᵥ x + d) * ((uc ⬝ᵥ x + wc) - d ^ 2 * gfun x) = 0 := by
        rw [← hdvdT x]; exact hTgen x
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h (hbd x)
      · linarith
    -- Package the affine QuadForm.
    refine ⟨⟨(wc : ℚ) / (d : ℚ) ^ 2, (((d : ℚ) ^ 2)⁻¹) • castQ uc, 0⟩, fun x => ?_⟩
    have hglinQ : (d : ℚ) ^ 2 * (gfun x : ℚ) = ((uc ⬝ᵥ x : ℤ) : ℚ) + (wc : ℚ) := by
      have := hglin x; exact_mod_cast this
    have hd2Q : ((d : ℚ) ^ 2) ≠ 0 := pow_ne_zero 2 hdQ
    show ((gfun x : ℤ) : ℚ) = _
    rw [show ((gfun x : ℤ) : ℚ) = (((uc ⬝ᵥ x : ℤ) : ℚ) + (wc : ℚ)) / (d : ℚ) ^ 2 from by
      rw [eq_div_iff hd2Q]; linear_combination hglinQ]
    simp only [QuadForm.eval, smul_dotProduct, smul_eq_mul, castQ_dot, Matrix.zero_mulVec,
      dotProduct_zero, add_zero]
    field_simp
    ring

/-! ### Theorem 3 — combine, and the `GlobalQuadratic ⇒ FullCosetNF` bridge (all n). -/

/-- A single global quadratic in `n` variables also has the full-residue coset form (`M = 1`):
each coset uses the translated polynomial `q.translate (castQ ρ)`. -/
theorem globalQuadratic_imp_fullCoset {n : ℕ} {F : (Fin n → ℤ) → ℤ} (h : GlobalQuadratic F) :
    FullCosetNF F := by
  obtain ⟨q, hq⟩ := h
  refine ⟨1, le_refl 1, fun ρ => ⟨q.translate (castQ ρ), fun t => ?_⟩⟩
  rw [show ((1 : ℕ) : ℤ) • t = t by rw [Nat.cast_one, one_smul], hq (ρ + t), castQ_add,
    QuadForm.eval_translate]

/-- **Main c1_ninput deliverable.** The output of a total, unique `n`-input C1 relation has the
full-residue coset normal form — the `r = 0` conjecture for all `n`. -/
theorem nInputNoWitness_full {n : ℕ} (a : ℤ) (β : Fin n → ℤ) (d : ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ) (hT : RelTotal (Rn a β d E φ g))
    (hU : RelUnique (Rn a β d E φ g)) : FullCosetNF (fn a β d E φ g hT) := by
  rcases eq_or_ne a 0 with ha | ha
  · exact globalQuadratic_imp_fullCoset (n_a_zero_global a β d E φ g hT hU ha)
  · exact n_a_ne_zero_full a β d E φ g hT hU ha

/-- **Main c1_ninput deliverable (weak form).** Corollary of the full-residue form. -/
theorem nInputNoWitness_weak {n : ℕ} (a : ℤ) (β : Fin n → ℤ) (d : ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) (φ : Fin n → ℤ) (g : ℤ) (hT : RelTotal (Rn a β d E φ g))
    (hU : RelUnique (Rn a β d E φ g)) : WeakScalarCosetNF (fn a β d E φ g hT) :=
  WeakScalarCosetNF.of_full (nInputNoWitness_full a β d E φ g hT hU)

/-! ### Controls (n = 2). -/

/-- `⌈(x₁+x₂)/2⌉` control (Full NF, `M = 2`): `P` factors as `(2y−x₁−x₂)(2y−x₁−x₂−1)`, the double
line whose integer root is `⌈(x₁+x₂)/2⌉`. -/
example (x : Fin 2 → ℤ) (y : ℤ) :
    Pn 4 ![-4, -4] (-2) !![1, 1; 1, 1] ![1, 1] 0 x y
      = (2 * y - x 0 - x 1) * (2 * y - x 0 - x 1 - 1) := by
  simp only [Pn, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.head_fin_const]
  ring

/-- `y = x₁·x₂` control (the `a = 0`, `β = 0` global branch): `R` is exactly `y = x₁ x₂`. -/
example (x : Fin 2 → ℤ) (y : ℤ) :
    Rn 0 (0 : Fin 2 → ℤ) 1 !![0, -1; 0, 0] (0 : Fin 2 → ℤ) 0 x y ↔ y = x 0 * x 1 := by
  simp only [Rn, Pn, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  constructor <;> intro h <;> linear_combination h

end DiophCompression.ResearchUpgrade
