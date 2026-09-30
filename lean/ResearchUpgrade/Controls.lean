/-
  D1 (R40-D1) — the controls that fix what NF reasoning may NOT assume.

  Each entry says what it refutes and what it does NOT refute.  Nothing here is a random search;
  the collisions already proved elsewhere are not re-searched.

  | control                        | refutes                                   | does NOT refute |
  |--------------------------------|-------------------------------------------|-----------------|
  | `sqrt2Floor` (this file)       | `LinearGrowth → WeakScalarCosetNF`        | anything about SE₂-definability — `⌊√2 x⌋` is NOT claimed to be SE₂-definable |
  | `ceilHalf1_not_global` (r40)   | `FullCosetNF → GlobalQuadratic`           | the coset form itself, which holds with `M = 2` |
  | `tri1_global` (r40)            | "integer values force integer coefficients" | the degree bound |
  | `sq1_global` (r40)             | nothing — positive control, non-vacuity    | — |
  | `Ex_witness_not_unique` (C)    | "output uniqueness ⇒ witness uniqueness"  | output uniqueness, which holds there |
  | `m_zero_counterexample` (C1)   | the residual bound at `m = 0`             | the bound for `m ≥ 1` |

  The `t² + 7` reading belongs to the same list: representability of every input value by a
  four-square expression does NOT give a rational polynomial section, because that family has no
  output uniqueness.  A counterexample candidate for a general NF is only admissible if it carries
  BOTH totality on the infinite domain and output uniqueness.

  RESIDUAL, recorded with its type rather than solved: for a one-witness, `n`-input family, the
  uniformisation of a per-class modulus into a single line modulus
      `∀ ρ, ∃ M_ρ, …`   ⟶   `∃ M, ∀ ρ, …`
  is not established.  D1 is not conditional on it.

  s51.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination
import ResearchUpgrade.CosetNormalForm

namespace DiophCompression.ResearchUpgrade.Controls

open Matrix

/-- If `|x| · N ≤ c` for every natural `N`, then `x = 0`.  The Archimedean step, isolated. -/
theorem eq_zero_of_abs_mul_nat_bounded {x c : ℝ} (h : ∀ N : ℕ, |x| * (N : ℝ) ≤ c) : x = 0 := by
  by_contra hx
  have hpos : 0 < |x| := abs_pos.mpr hx
  obtain ⟨N, hN⟩ := exists_nat_gt (c / |x|)
  have hle := h N
  rw [div_lt_iff₀ hpos] at hN
  nlinarith

/-- A REAL quadratic that is bounded on all of ℤ has zero linear and zero quadratic coefficient.
The integer version (`line_coeffs_zero`, Packet C) needs `|α| ≥ 1`; here the Archimedean property
replaces it. -/
theorem real_line_coeffs_zero {α β γ C : ℝ}
    (h : ∀ t : ℤ, |γ + β * (t : ℝ) + α * (t : ℝ) ^ 2| ≤ C) : α = 0 ∧ β = 0 := by
  have h0 : |γ| ≤ C := by simpa using h 0
  have hC : 0 ≤ C := le_trans (abs_nonneg γ) h0
  rw [abs_le] at h0
  -- the two-point identities
  have key : ∀ T : ℤ, |α| * (T : ℝ) ^ 2 ≤ 2 * C ∧ |β| * (T : ℝ) ≤ 2 * C ∨ (T : ℝ) < 0 := by
    intro T
    by_cases hT : (0 : ℝ) ≤ (T : ℝ)
    · left
      have hp := h T
      have hn := h (-T)
      have hcast : ((-T : ℤ) : ℝ) = -(T : ℝ) := by push_cast; ring
      rw [hcast, show γ + β * -(T : ℝ) + α * (-(T : ℝ)) ^ 2
            = γ - β * (T : ℝ) + α * (T : ℝ) ^ 2 from by ring] at hn
      rw [abs_le] at hp hn
      constructor
      · rcases abs_cases α with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> nlinarith [sq_nonneg (T : ℝ)]
      · rcases abs_cases β with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> nlinarith
    · right; linarith [not_le.mp hT]
  have hα : α = 0 := by
    refine eq_zero_of_abs_mul_nat_bounded (c := 2 * C) fun N => ?_
    rcases key (N : ℤ) with ⟨h1, _⟩ | h2
    · have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hsq : (N : ℝ) ≤ ((N : ℤ) : ℝ) ^ 2 ∨ (N : ℝ) = 0 := by
        rcases Nat.eq_zero_or_pos N with h | h
        · right; simp [h]
        · left
          have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
          push_cast
          nlinarith
      rcases hsq with hs | hs
      · have : |α| * (N : ℝ) ≤ |α| * ((N : ℤ) : ℝ) ^ 2 := by
          have := abs_nonneg α; nlinarith
        linarith
      · rw [hs, mul_zero]; linarith
    · exfalso
      have hnn : (0 : ℝ) ≤ ((N : ℤ) : ℝ) := by push_cast; positivity
      linarith
  have hβ : β = 0 := by
    refine eq_zero_of_abs_mul_nat_bounded (c := 2 * C) fun N => ?_
    rcases key (N : ℤ) with ⟨_, h1⟩ | h2
    · push_cast at h1 ⊢; linarith
    · exfalso
      have hnn : (0 : ℝ) ≤ ((N : ℤ) : ℝ) := by push_cast; positivity
      linarith
  exact ⟨hα, hβ⟩

/-- `x ↦ ⌊√2 · x⌋`. -/
noncomputable def sqrt2Floor : (Fin 1 → ℤ) → ℤ := fun x => ⌊(x 0 : ℝ) * Real.sqrt 2⌋

/-- The growth side: `|⌊√2 x⌋| ≤ 2|x| + 1`.  This is the linear-growth content of the control. -/
theorem sqrt2Floor_bound (x : Fin 1 → ℤ) : |sqrt2Floor x| ≤ 2 * |x 0| + 1 := by
  have hs : Real.sqrt 2 ≤ 2 := by
    have : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    calc Real.sqrt 2 ≤ Real.sqrt 4 := this
      _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hfl : (⌊(x 0 : ℝ) * Real.sqrt 2⌋ : ℝ) ≤ (x 0 : ℝ) * Real.sqrt 2 := Int.floor_le _
  have hfl' : (x 0 : ℝ) * Real.sqrt 2 < (⌊(x 0 : ℝ) * Real.sqrt 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have habs : |(x 0 : ℝ) * Real.sqrt 2| ≤ 2 * |(x 0 : ℝ)| := by
    rw [abs_mul, abs_of_nonneg hs0]
    nlinarith [abs_nonneg ((x 0 : ℝ))]
  rw [abs_le] at habs
  have : |(⌊(x 0 : ℝ) * Real.sqrt 2⌋ : ℝ)| ≤ 2 * |(x 0 : ℝ)| + 1 := by
    rw [abs_le]; constructor <;> linarith
  have hcast : ((2 * |x 0| + 1 : ℤ) : ℝ) = 2 * |(x 0 : ℝ)| + 1 := by push_cast; simp
  rw [show |sqrt2Floor x| = |⌊(x 0 : ℝ) * Real.sqrt 2⌋| from rfl]
  have := this
  rw [← Int.cast_abs] at this
  exact_mod_cast this.trans_eq hcast.symm

/-- **D1, the headline control.**  `⌊√2 x⌋` has linear growth but has NO weak coset normal form:
on no full lattice coset `ρ + M ℤ` does it agree with a rational polynomial of degree ≤ 2.
So `LinearGrowth → WeakNF` is FALSE, and B2 must not use it.

What this does NOT claim: that `⌊√2 x⌋` is SE₂-definable.  It is a control on the implication
between the two normal-form predicates, not an instance of the theory. -/
theorem sqrt2Floor_not_weakScalarCosetNF : ¬ WeakScalarCosetNF sqrt2Floor := by
  rintro ⟨M, ρ, q, hM, h⟩
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hM
  -- read the hypothesis along the diagonal of `Fin 1`
  have hval : ∀ t : ℤ,
      ((⌊((ρ 0 + (M : ℤ) * t : ℤ) : ℝ) * Real.sqrt 2⌋ : ℤ) : ℚ)
        = q.c + q.l 0 * (t : ℚ) + q.Q 0 0 * (t : ℚ) ^ 2 := by
    intro t
    have := h (fun _ => t)
    simpa [sqrt2Floor, QuadForm.eval, castQ, dotProduct, Fin.sum_univ_one, Matrix.mulVec,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm, mul_assoc, mul_left_comm, sq] using this
  -- transport to ℝ and subtract the true line
  have hreal : ∀ t : ℤ,
      |((q.c : ℝ) - (ρ 0 : ℝ) * Real.sqrt 2)
        + ((q.l 0 : ℝ) - (M : ℝ) * Real.sqrt 2) * (t : ℝ)
        + (q.Q 0 0 : ℝ) * (t : ℝ) ^ 2| ≤ 1 := by
    intro t
    have hq := hval t
    have hq' : ((⌊((ρ 0 + (M : ℤ) * t : ℤ) : ℝ) * Real.sqrt 2⌋ : ℤ) : ℝ)
        = (q.c : ℝ) + (q.l 0 : ℝ) * (t : ℝ) + (q.Q 0 0 : ℝ) * (t : ℝ) ^ 2 := by
      exact_mod_cast congrArg (fun z : ℚ => (z : ℝ)) hq
    have hfl := Int.floor_le (((ρ 0 + (M : ℤ) * t : ℤ) : ℝ) * Real.sqrt 2)
    have hfl' := Int.lt_floor_add_one (((ρ 0 + (M : ℤ) * t : ℤ) : ℝ) * Real.sqrt 2)
    have hexp : (((ρ 0 + (M : ℤ) * t : ℤ) : ℝ)) * Real.sqrt 2
        = (ρ 0 : ℝ) * Real.sqrt 2 + ((M : ℝ) * Real.sqrt 2) * (t : ℝ) := by
      push_cast; ring
    rw [hq'] at hfl hfl'
    rw [hexp] at hfl hfl'
    rw [abs_le]
    constructor <;> nlinarith
  obtain ⟨hquad, hlin⟩ := real_line_coeffs_zero hreal
  -- the linear coefficient forces √2 to be rational
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hM0
  have hsqrt : ((q.l 0 / (M : ℚ) : ℚ) : ℝ) = Real.sqrt 2 := by
    push_cast
    rw [div_eq_iff hMne]
    linear_combination hlin
  exact irrational_sqrt_two ⟨q.l 0 / (M : ℚ), hsqrt⟩

end DiophCompression.ResearchUpgrade.Controls
