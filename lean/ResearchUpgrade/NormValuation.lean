/-
  NormValuation.lean — Gate-20 Packet N2, task N2.1.

  The inert-prime obstruction for rational norms of the definite form `x² + D y²`.

  Reviewer's §3: if `p` is odd, `D` is a `p`-unit and `(−D/p) = −1`, then `v_p(r² + D s²)` is
  EVEN for every rational `r, s` with `r² + D s² ≠ 0`.  What the pipeline (N2.2) consumes is the
  contrapositive at valuation exactly one, so that is what is proved here, by infinite descent on
  the common denominator — no `padicValRat` arithmetic is needed, and denominators are handled in
  full (reviewer regression control #12).  DEVIATION, recorded: the general even-valuation
  statement is not formalised; `not_norm_rat_of_val_one` is its valuation-one instance, which is
  what N2.2 uses.  The `p`-unit hypothesis on `D` is not needed separately: it follows from
  `¬ IsSquare (−D : ZMod p)` (if `p ∣ D` then `−D = 0 = 0²`).

  * `inert_dvd_both`          — `p ∣ a² + D b² → p ∣ a ∧ p ∣ b`   (the ZMod-p core).
  * `no_norm_descent`         — no integer solution of `N c² = a² + D b²` with `c ≠ 0`.
  * `not_norm_rat_of_val_one` — hence `N` is not `r² + D s²` for any rationals `r, s`.
  * `control_inert_hypothesis_needed` — at `D = 1`, `p = 5` the hypothesis fails and so does the
                                conclusion (`5 = 1² + 2²`): the hypothesis is load-bearing.
  * `smoke_three_not_norm`    — positive instance: `3` is not a sum of two rational squares.

  Claim tags: all [P] (std-3).  Baseline (mpup-lean r39) read-only.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Fintype.Parity
import Mathlib.Data.Int.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Prime

namespace DiophCompression.ResearchUpgrade

/-! ## The ZMod-p core -/

/-- If `−D` is not a square mod the prime `p`, then `p ∣ a² + D b²` forces `p ∣ a` and `p ∣ b`. -/
theorem inert_dvd_both (p : ℕ) (hp : p.Prime) (D a b : ℤ)
    (hns : ¬ IsSquare (-(D : ZMod p)))
    (h : (p : ℤ) ∣ a ^ 2 + D * b ^ 2) :
    (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b := by
  haveI := Fact.mk hp
  have h0 : ((a : ZMod p) ^ 2 + (D : ZMod p) * (b : ZMod p) ^ 2) = 0 := by
    have hcast := (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 + D * b ^ 2) p).mpr h
    push_cast at hcast
    exact hcast
  have hb : (b : ZMod p) = 0 := by
    by_contra hb
    exact hns ⟨(a : ZMod p) / (b : ZMod p), by field_simp; linear_combination -h0⟩
  have ha : (a : ZMod p) = 0 := by
    rw [hb] at h0
    have h2 : (a : ZMod p) ^ 2 = 0 := by linear_combination h0
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha,
    (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb⟩

/-! ## Descent on the denominator -/

/-- Infinite descent on `|c|`: if `v_p(N) = 1` exactly and `−D` is not a square mod `p`, then
`N c² = a² + D b²` has no integer solution with `c ≠ 0`. -/
theorem no_norm_descent (p : ℕ) (hp : p.Prime) (D : ℤ)
    (hns : ¬ IsSquare (-(D : ZMod p))) (N : ℤ)
    (h1 : (p : ℤ) ∣ N) (h2 : ¬ ((p : ℤ) ^ 2 ∣ N)) :
    ∀ n : ℕ, ∀ a b c : ℤ, c.natAbs = n → c ≠ 0 → N * c ^ 2 = a ^ 2 + D * b ^ 2 → False := by
  haveI := Fact.mk hp
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c hcn hc0 heq
    obtain ⟨N₁, hN₁⟩ := h1
    have hdvd : (p : ℤ) ∣ a ^ 2 + D * b ^ 2 := ⟨N₁ * c ^ 2, by rw [← heq, hN₁]; ring⟩
    obtain ⟨ha, hb⟩ := inert_dvd_both p hp D a b hns hdvd
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    have heq2 : (p : ℤ) * (N₁ * c ^ 2) = (p : ℤ) * ((p : ℤ) * (a' ^ 2 + D * b' ^ 2)) := by
      calc (p : ℤ) * (N₁ * c ^ 2) = N * c ^ 2 := by rw [hN₁]; ring
        _ = a ^ 2 + D * b ^ 2 := heq
        _ = (p : ℤ) * ((p : ℤ) * (a' ^ 2 + D * b' ^ 2)) := by rw [ha', hb']; ring
    have heq3 : N₁ * c ^ 2 = (p : ℤ) * (a' ^ 2 + D * b' ^ 2) := mul_left_cancel₀ hp0 heq2
    by_cases hpc : (p : ℤ) ∣ c
    · obtain ⟨c', hc'⟩ := hpc
      have hc'0 : c' ≠ 0 := by
        intro hzero; rw [hzero, mul_zero] at hc'; exact hc0 hc'
      have hsmall : c'.natAbs < n := by
        subst hcn
        have hpa : (p : ℤ).natAbs = p := Int.natAbs_natCast p
        have h2p : 2 ≤ p := hp.two_le
        have hc'pos : 1 ≤ c'.natAbs :=
          Nat.one_le_iff_ne_zero.mpr (by simpa [Int.natAbs_eq_zero] using hc'0)
        rw [hc', Int.natAbs_mul, hpa]
        nlinarith
      have hkey : N * c' ^ 2 = a' ^ 2 + D * b' ^ 2 := by
        have hstep : (p : ℤ) * ((p : ℤ) * (N * c' ^ 2))
            = (p : ℤ) * ((p : ℤ) * (a' ^ 2 + D * b' ^ 2)) := by
          calc (p : ℤ) * ((p : ℤ) * (N * c' ^ 2)) = N * ((p : ℤ) * c') ^ 2 := by ring
            _ = N * c ^ 2 := by rw [← hc']
            _ = a ^ 2 + D * b ^ 2 := heq
            _ = (p : ℤ) * ((p : ℤ) * (a' ^ 2 + D * b' ^ 2)) := by rw [ha', hb']; ring
        exact mul_left_cancel₀ hp0 (mul_left_cancel₀ hp0 hstep)
      exact ih c'.natAbs hsmall a' b' c' rfl hc'0 hkey
    · have hz : ((N₁ * c ^ 2 : ℤ) : ZMod p) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact ⟨a' ^ 2 + D * b' ^ 2, heq3⟩
      push_cast at hz
      rcases mul_eq_zero.mp hz with hz1 | hz2
      · have hpN₁ : (p : ℤ) ∣ N₁ := (ZMod.intCast_zmod_eq_zero_iff_dvd N₁ p).mp hz1
        obtain ⟨N₂, hN₂⟩ := hpN₁
        exact h2 ⟨N₂, by rw [hN₁, hN₂]; ring⟩
      · have hc : ((c : ZMod p)) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz2
        exact hpc ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp hc)

/-- `N` with `v_p(N) = 1` exactly is not represented by `x² + D y²` over ℚ. -/
theorem not_norm_rat_of_val_one (p : ℕ) (hp : p.Prime) (D : ℤ)
    (hns : ¬ IsSquare (-(D : ZMod p))) (N : ℤ)
    (h1 : (p : ℤ) ∣ N) (h2 : ¬ ((p : ℤ) ^ 2 ∣ N)) :
    ¬ ∃ r s : ℚ, (N : ℚ) = r ^ 2 + (D : ℚ) * s ^ 2 := by
  rintro ⟨r, s, hrs⟩
  have hrdQ : ((r.den : ℚ)) ≠ 0 := by exact_mod_cast (Rat.den_pos r).ne'
  have hsdQ : ((s.den : ℚ)) ≠ 0 := by exact_mod_cast (Rat.den_pos s).ne'
  have hrdZ : ((r.den : ℤ)) ≠ 0 := by exact_mod_cast (Rat.den_pos r).ne'
  have hsdZ : ((s.den : ℤ)) ≠ 0 := by exact_mod_cast (Rat.den_pos s).ne'
  have hrn : (r.num : ℚ) = r * (r.den : ℚ) := by
    have h := Rat.num_div_den r
    field_simp at h
    linear_combination h
  have hsn : (s.num : ℚ) = s * (s.den : ℚ) := by
    have h := Rat.num_div_den s
    field_simp at h
    linear_combination h
  have hQ : ((N * ((r.den : ℤ) * (s.den : ℤ)) ^ 2 : ℤ) : ℚ)
      = (((r.num * (s.den : ℤ)) ^ 2 + D * (s.num * (r.den : ℤ)) ^ 2 : ℤ) : ℚ) := by
    push_cast
    rw [hrn, hsn, hrs]
    ring
  exact no_norm_descent p hp D hns N h1 h2
    (((r.den : ℤ) * (s.den : ℤ))).natAbs (r.num * (s.den : ℤ)) (s.num * (r.den : ℤ))
    ((r.den : ℤ) * (s.den : ℤ)) rfl (mul_ne_zero hrdZ hsdZ) (by exact_mod_cast hQ)

/-! ## Controls -/

/-- The inert hypothesis is load-bearing: at `D = 1`, `p = 5`, `−1` IS a square mod `5`, and
`5 = 1² + 1·2²` with `v₅(5) = 1`.  A proof that dropped the hypothesis would contradict this. -/
theorem control_inert_hypothesis_needed :
    IsSquare (-(1 : ZMod 5)) ∧ ((5 : ℚ) = (1 : ℚ) ^ 2 + (1 : ℚ) * (2 : ℚ) ^ 2) :=
  ⟨⟨2, by decide⟩, by norm_num⟩

/-- Positive instance: `3` is not a sum of two rational squares. -/
theorem smoke_three_not_norm :
    ¬ ∃ r s : ℚ, ((3 : ℤ) : ℚ) = r ^ 2 + ((1 : ℤ) : ℚ) * s ^ 2 := by
  have hnd : ¬ ((3 : ℤ) ^ 2 ∣ (3 : ℤ)) := by
    rintro ⟨k, hk⟩
    have h9 : (3 : ℤ) = 9 * k := by linear_combination hk
    omega
  exact not_norm_rat_of_val_one 3 (by norm_num) 1 (by decide) 3 ⟨1, by ring⟩ hnd

end DiophCompression.ResearchUpgrade
