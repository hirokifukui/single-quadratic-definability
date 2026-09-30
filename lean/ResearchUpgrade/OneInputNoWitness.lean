/-
  OneInputNoWitness.lean — Gate-18 research program, Packet C1.
  "No witness, one input": the relation `P(x,y) = a y² + (b x + d) y + (e x² + f x + g) = 0`
  with a unique output `y` for every input `x` (RelTotal + RelUnique) makes the output
  function `f` land in the full-residue coset normal form (`FullCosetNF`), hence the weak
  scalar coset form.  The engine is the RIGIDITY LEMMA (C1-1): a degree-≤2 integer polynomial
  whose values at all integers are perfect squares is the square of an integer linear form.
  See docs/C_LINE_MEMO_s44.md §C1.
-/
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Int.Star
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.Ring.RingNF
import ResearchUpgrade.CosetNormalForm

namespace DiophCompression.ResearchUpgrade

open Finset

/-- The defining polynomial of a C1 family. -/
def P1 (a b d e f g : ℤ) (x y : ℤ) : ℤ :=
  a * y ^ 2 + (b * x + d) * y + (e * x ^ 2 + f * x + g)

/-- The C1 relation `P1 = 0`. -/
def R1 (a b d e f g : ℤ) (x y : ℤ) : Prop := P1 a b d e f g x y = 0

/-- The output function packaged for the `CosetNormalForm` predicates: `x ↦ f (x 0)`, where
`f` is the (choice-extracted) unique output of a total relation. -/
noncomputable def f1 (a b d e f g : ℤ) (hT : RelTotal (R1 a b d e f g)) : (Fin 1 → ℤ) → ℤ :=
  fun x => Classical.choose (hT (x 0))

/-! ### An algebraic helper: a quadratic with three distinct roots is the zero quadratic. -/

theorem quad_three_roots {p q r x₁ x₂ x₃ : ℤ}
    (h₁ : p * x₁ ^ 2 + q * x₁ + r = 0) (h₂ : p * x₂ ^ 2 + q * x₂ + r = 0)
    (h₃ : p * x₃ ^ 2 + q * x₃ + r = 0) (d12 : x₁ ≠ x₂) (d13 : x₁ ≠ x₃) (d23 : x₂ ≠ x₃) :
    p = 0 ∧ q = 0 ∧ r = 0 := by
  have e12 : p * (x₁ + x₂) + q = 0 := by
    have hmul : (x₁ - x₂) * (p * (x₁ + x₂) + q) = 0 := by linear_combination h₁ - h₂
    rcases mul_eq_zero.1 hmul with h | h
    · exact absurd (sub_eq_zero.1 h) d12
    · exact h
  have e23 : p * (x₂ + x₃) + q = 0 := by
    have hmul : (x₂ - x₃) * (p * (x₂ + x₃) + q) = 0 := by linear_combination h₂ - h₃
    rcases mul_eq_zero.1 hmul with h | h
    · exact absurd (sub_eq_zero.1 h) d23
    · exact h
  have hp : p = 0 := by
    have hmul : (x₁ - x₃) * p = 0 := by linear_combination e12 - e23
    rcases mul_eq_zero.1 hmul with h | h
    · exact absurd (sub_eq_zero.1 h) d13
    · exact h
  have hq : q = 0 := by have := e12; rw [hp] at this; simpa using this
  refine ⟨hp, hq, ?_⟩
  have := h₁; rw [hp, hq] at this; simpa using this

/-! ### Theorem 1 — the rigidity lemma. -/

/-- **Rigidity (core form).** A degree-≤2 integer polynomial that is a perfect square at every
integer is the square of an integer linear form. -/
theorem rigidity_core (A B C : ℤ) (h : ∀ x : ℤ, IsSquare (A * x ^ 2 + B * x + C)) :
    ∃ r s : ℤ, ∀ x : ℤ, A * x ^ 2 + B * x + C = (r * x + s) ^ 2 := by
  -- Values are nonnegative (they are squares).
  have hnn : ∀ x : ℤ, 0 ≤ A * x ^ 2 + B * x + C := by
    intro x; obtain ⟨t, ht⟩ := h x; rw [ht]; exact mul_self_nonneg t
  rcases eq_or_ne A 0 with hA0 | hA0
  · -- Case A = 0.
    subst hA0
    have hB0 : B = 0 := by
      by_contra hB
      rcases lt_trichotomy B 0 with hB' | hB' | hB'
      · have h1 := hnn (|C| + 1)
        nlinarith [h1, le_abs_self C, abs_nonneg C]
      · exact hB hB'
      · have h1 := hnn (-(|C| + 1))
        nlinarith [h1, le_abs_self C, abs_nonneg C]
    subst hB0
    obtain ⟨t, ht⟩ := h 0
    have hC : C = t * t := by simpa using ht
    exact ⟨0, |t|, fun x => by rw [hC]; rw [show |t| = |t| from rfl]; nlinarith [sq_abs t]⟩
  · -- Case A ≠ 0.  First A > 0.
    have hApos : 0 < A := by
      rcases lt_trichotomy A 0 with hA' | hA' | hA'
      · exfalso
        have h1 := hnn (|C| + |B| + 1)
        have h2 := hnn (-(|C| + |B| + 1))
        nlinarith [h1, h2, le_abs_self C, le_abs_self B, neg_abs_le C, neg_abs_le B,
          abs_nonneg C, abs_nonneg B]
      · exact absurd hA' hA0
      · exact hA'
    have hA1 : 1 ≤ A := hApos
    -- Nonnegative square roots `m x` with `(m x)² = Δ(x)`.
    have key : ∀ x : ℤ, ∃ mx : ℤ, 0 ≤ mx ∧ mx ^ 2 = A * x ^ 2 + B * x + C := by
      intro x; obtain ⟨t, ht⟩ := h x
      exact ⟨|t|, abs_nonneg _, by rw [sq_abs, ht]; ring⟩
    choose m hmnn hm2 using key
    -- Threshold and the difference bound.
    set N : ℤ := 4 * (|A| + |B| + |C|) + 4 with hNdef
    have hbound : ∀ x : ℤ, N ≤ x → 1 ≤ m (x + 1) - m x ∧ m (x + 1) - m x ≤ 2 * A + |A + B| := by
      intro x hx
      have hxpos : 0 < x := by nlinarith [hx, abs_nonneg A, abs_nonneg B, abs_nonneg C]
      have hx1 : 1 ≤ x := hxpos
      have hgx : 0 < 2 * A * x + A + B := by
        nlinarith [hA1, hx, le_abs_self A, le_abs_self B, neg_abs_le A, neg_abs_le B,
          abs_nonneg A, abs_nonneg B, abs_nonneg C]
      have hdiff : (m (x + 1)) ^ 2 - (m x) ^ 2 = 2 * A * x + A + B := by
        have e1 : (m (x + 1)) ^ 2 = A * (x + 1) ^ 2 + B * (x + 1) + C := hm2 (x + 1)
        have e2 : (m x) ^ 2 = A * x ^ 2 + B * x + C := hm2 x
        rw [e1, e2]; ring
      have hsq : x ^ 2 ≤ 4 * (m x) ^ 2 := by
        rw [hm2 x]
        nlinarith [hA1, hx, le_abs_self A, le_abs_self B, le_abs_self C, neg_abs_le B,
          neg_abs_le C, abs_nonneg A, abs_nonneg B, abs_nonneg C]
      have h2mx : x ≤ 2 * (m x) := by nlinarith [hsq, hmnn x, hxpos]
      have hid : (m (x + 1) - m x) * (m (x + 1) + m x) = 2 * A * x + A + B := by
        have : (m (x + 1) - m x) * (m (x + 1) + m x) = (m (x + 1)) ^ 2 - (m x) ^ 2 := by ring
        rw [this, hdiff]
      have hd0 : 0 < m (x + 1) - m x := by
        nlinarith [hid, hgx, hmnn x, hmnn (x + 1)]
      have hd1 : 1 ≤ m (x + 1) - m x := hd0
      have hsum : x ≤ m (x + 1) + m x := by linarith [h2mx, hd0]
      have hstep1 : (m (x + 1) - m x) * x ≤ 2 * A * x + A + B := by
        have h4 : (m (x + 1) - m x) * x ≤ (m (x + 1) - m x) * (m (x + 1) + m x) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt hd0)
        rw [hid] at h4; exact h4
      have hstep2 : 2 * A * x + A + B ≤ (2 * A + |A + B|) * x := by
        nlinarith [le_abs_self (A + B), abs_nonneg (A + B), hx1,
          mul_nonneg (abs_nonneg (A + B)) (by linarith [hx1] : (0 : ℤ) ≤ x - 1)]
      have hdle : m (x + 1) - m x ≤ 2 * A + |A + B| := by
        nlinarith [hstep1, hstep2, hxpos]
      exact ⟨hd1, hdle⟩
    -- Pigeonhole on `d x := m (x+1) - m x`.
    set Kb : ℤ := 2 * A + |A + B| with hKbdef
    have hKbpos : 0 < Kb := by rw [hKbdef]; nlinarith [hA1, abs_nonneg (A + B)]
    set K : ℕ := Kb.toNat with hKdef
    have hKcast : (K : ℤ) = Kb := Int.toNat_of_nonneg (le_of_lt hKbpos)
    set s : Finset ℤ := Finset.Icc N (N + 2 * (K : ℤ)) with hsdef
    set t : Finset ℤ := Finset.Icc 1 (K : ℤ) with htdef
    set dd : ℤ → ℤ := fun x => m (x + 1) - m x with hdddef
    have hmaps : ∀ x ∈ s, dd x ∈ t := by
      intro x hx
      rw [hsdef, Finset.mem_Icc] at hx
      obtain ⟨hlo, hhi⟩ := hbound x hx.1
      rw [htdef, Finset.mem_Icc, hdddef]
      exact ⟨hlo, by rw [hKcast]; exact hhi⟩
    have hcs : s.card = 2 * K + 1 := by
      rw [hsdef, Int.card_Icc]
      rw [show N + 2 * (K : ℤ) + 1 - N = 2 * (K : ℤ) + 1 by ring]
      omega
    have hct : t.card = K := by
      rw [htdef, Int.card_Icc]
      rw [show (K : ℤ) + 1 - 1 = (K : ℤ) by ring]
      simp
    have hlt : t.card * 2 < s.card := by rw [hcs, hct]; omega
    obtain ⟨r, hrt, hrcard⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
    obtain ⟨x₁, x₂, x₃, hx1m, hx2m, hx3m, d12, d13, d23⟩ := Finset.two_lt_card_iff.1 hrcard
    -- Extract membership and the fiber condition.
    have hr1 : 1 ≤ r := by
      have := hrt; rw [htdef, Finset.mem_Icc] at this; exact this.1
    have hr_pos : 0 < r := hr1
    -- The identity available at every fiber point.
    have hident : ∀ x : ℤ, N ≤ x → m (x + 1) - m x = r →
        4 * r ^ 2 * (A * x ^ 2 + B * x + C) = (2 * A * x + A + B - r ^ 2) ^ 2 := by
      intro x hxN hdr
      have hdiff : (m (x + 1)) ^ 2 - (m x) ^ 2 = 2 * A * x + A + B := by
        have e1 : (m (x + 1)) ^ 2 = A * (x + 1) ^ 2 + B * (x + 1) + C := hm2 (x + 1)
        have e2 : (m x) ^ 2 = A * x ^ 2 + B * x + C := hm2 x
        rw [e1, e2]; ring
      have hmx1 : m (x + 1) = m x + r := by linarith [hdr]
      have hkey : 2 * r * (m x) = 2 * A * x + A + B - r ^ 2 := by
        have hh : (m x + r) ^ 2 - (m x) ^ 2 = 2 * A * x + A + B := by rw [← hmx1]; exact hdiff
        linear_combination hh
      have hsq : (2 * r * (m x)) ^ 2 = (2 * A * x + A + B - r ^ 2) ^ 2 := by rw [hkey]
      have hΔ : (m x) ^ 2 = A * x ^ 2 + B * x + C := hm2 x
      linear_combination hsq - 4 * r ^ 2 * hΔ
    -- Membership unpacking for the three fiber points.
    have unpack : ∀ z : ℤ, z ∈ ({x ∈ s | dd x = r} : Finset ℤ) → N ≤ z ∧ dd z = r := by
      intro z hz
      rw [Finset.mem_filter, hsdef, Finset.mem_Icc] at hz
      exact ⟨hz.1.1, hz.2⟩
    obtain ⟨hz1N, hz1r⟩ := unpack x₁ hx1m
    obtain ⟨hz2N, hz2r⟩ := unpack x₂ hx2m
    obtain ⟨hz3N, hz3r⟩ := unpack x₃ hx3m
    have hq1 := hident x₁ hz1N (by rw [hdddef] at hz1r; exact hz1r)
    have hq2 := hident x₂ hz2N (by rw [hdddef] at hz2r; exact hz2r)
    have hq3 := hident x₃ hz3N (by rw [hdddef] at hz3r; exact hz3r)
    -- Turn into `p x² + q x + r0 = 0` and apply the three-roots lemma.
    have hp1 : (4 * A * (r ^ 2 - A)) * x₁ ^ 2 + (4 * r ^ 2 * B - 4 * A * (A + B - r ^ 2)) * x₁
        + (4 * r ^ 2 * C - (A + B - r ^ 2) ^ 2) = 0 := by linear_combination hq1
    have hp2 : (4 * A * (r ^ 2 - A)) * x₂ ^ 2 + (4 * r ^ 2 * B - 4 * A * (A + B - r ^ 2)) * x₂
        + (4 * r ^ 2 * C - (A + B - r ^ 2) ^ 2) = 0 := by linear_combination hq2
    have hp3 : (4 * A * (r ^ 2 - A)) * x₃ ^ 2 + (4 * r ^ 2 * B - 4 * A * (A + B - r ^ 2)) * x₃
        + (4 * r ^ 2 * C - (A + B - r ^ 2) ^ 2) = 0 := by linear_combination hq3
    obtain ⟨hcoef2, _, hcoef0⟩ := quad_three_roots hp1 hp2 hp3 d12 d13 d23
    -- A = r².
    have hAr : A = r ^ 2 := by
      rcases mul_eq_zero.1 hcoef2 with hh | hh
      · exact absurd hh (by nlinarith [hApos])
      · linarith [hh]
    have hAB : A + B - r ^ 2 = B := by rw [hAr]; ring
    have hBC : B ^ 2 = 4 * r ^ 2 * C := by
      have hh := hcoef0; rw [hAB] at hh; linarith
    have hdvd : (2 * r) ∣ B := by
      have h1 : (2 * r) ^ 2 ∣ B ^ 2 := ⟨C, by rw [hBC]; ring⟩
      exact (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).1 h1
    obtain ⟨sVal, hs⟩ := hdvd
    have h4 : (4 * r ^ 2 : ℤ) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hr_pos.ne')
    have hsC : sVal ^ 2 = C := by
      have hcc : (4 * r ^ 2) * sVal ^ 2 = (4 * r ^ 2) * C := by rw [← hBC, hs]; ring
      exact mul_left_cancel₀ h4 hcc
    refine ⟨r, sVal, fun x => ?_⟩
    rw [hAr, hs, ← hsC]; ring

/-- **Rigidity (requested corollary forms).** From the core form: the completed-square identity
holds always, and (unconditionally, in fact) `4AC = B²` and `A` is a perfect square. -/
theorem rigidity_deg_le_two (A B C : ℤ) (h : ∀ x : ℤ, IsSquare (A * x ^ 2 + B * x + C)) :
    (∀ x : ℤ, 4 * A * (A * x ^ 2 + B * x + C) = (2 * A * x + B) ^ 2 + (4 * A * C - B ^ 2)) ∧
    4 * A * C - B ^ 2 = 0 ∧ IsSquare A := by
  obtain ⟨r, s, hrs⟩ := rigidity_core A B C h
  -- Read off A = r², B = 2rs, C = s² from three evaluations.
  have h0 := hrs 0
  have h1 := hrs 1
  have hm1 := hrs (-1)
  have hAeq : A = r ^ 2 := by nlinarith [h0, h1, hm1]
  have hBeq : B = 2 * r * s := by nlinarith [h0, h1, hm1]
  have hCeq : C = s ^ 2 := by nlinarith [h0, h1, hm1]
  refine ⟨fun x => by ring, ?_, ?_⟩
  · rw [hAeq, hBeq, hCeq]; ring
  · exact ⟨r, by rw [hAeq]; ring⟩

/-! ### Theorem 2 — the degenerate branch `a = 0` gives a single global quadratic. -/

theorem a_zero_global (a b d e f g : ℤ) (hT : RelTotal (R1 a b d e f g))
    (hU : RelUnique (R1 a b d e f g)) (ha : a = 0) :
    GlobalQuadratic (f1 a b d e f g hT) := by
  subst ha
  set gfun : ℤ → ℤ := fun n => Classical.choose (hT n) with hgfun
  have hf1 : ∀ x : Fin 1 → ℤ, f1 0 b d e f g hT x = gfun (x 0) := fun _ => rfl
  have hspec : ∀ n : ℤ, (b * n + d) * gfun n + (e * n ^ 2 + f * n + g) = 0 := by
    intro n
    have h := Classical.choose_spec (hT n)
    have h' : (0 : ℤ) * gfun n ^ 2 + (b * n + d) * gfun n + (e * n ^ 2 + f * n + g) = 0 := by
      simpa [R1, P1, hgfun] using h
    linarith [h']
  -- `b n + d ≠ 0` for all `n` (uniqueness).
  have hbd : ∀ n : ℤ, b * n + d ≠ 0 := by
    intro n hbd0
    have hc : e * n ^ 2 + f * n + g = 0 := by have := hspec n; rw [hbd0] at this; linarith
    have r0 : R1 0 b d e f g n 0 := by simp only [R1, P1]; ring_nf; linarith [hc]
    have r1 : R1 0 b d e f g n 1 := by
      simp only [R1, P1]; rw [hbd0]; ring_nf; linarith [hc]
    exact absurd (hU n 0 1 r0 r1) (by norm_num)
  rcases eq_or_ne b 0 with hb0 | hb0
  · -- Sub-case `b = 0`: `d ≠ 0`, `f(n) = -(e n² + f n + g)/d`.
    have hd0 : d ≠ 0 := by have := hbd 0; simpa [hb0] using this
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
    refine ⟨⟨-g / d, fun _ => -f / d, fun _ _ => -e / d⟩, fun x => ?_⟩
    rw [hf1]
    have hs0 : d * gfun (x 0) + (e * (x 0) ^ 2 + f * (x 0) + g) = 0 := by
      have := hspec (x 0); rw [hb0] at this; linear_combination this
    have hsQ : (d : ℚ) * (gfun (x 0) : ℚ) + ((e : ℚ) * (x 0 : ℚ) ^ 2 + (f : ℚ) * (x 0 : ℚ)
        + (g : ℚ)) = 0 := by exact_mod_cast hs0
    simp only [QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
    field_simp
    linear_combination hsQ
  · -- Sub-case `b ≠ 0`: the residual `d²e − dfb + gb²` must vanish.
    have hrho0 : d ^ 2 * e - d * f * b + g * b ^ 2 = 0 := by
      by_contra hne
      set ρ : ℤ := d ^ 2 * e - d * f * b + g * b ^ 2 with hρ
      have habs : 0 < |ρ| := abs_pos.2 hne
      have hdvd : ∀ n : ℤ, (b * n + d) ∣ ρ :=
        fun n => ⟨-(e * b * n + (f * b - e * d) + b ^ 2 * gfun n), by
          rw [hρ]; linear_combination b ^ 2 * hspec n⟩
      set n₀ : ℤ := |ρ| + |d| + 1 with hn0
      have hle : |b * n₀ + d| ≤ |ρ| :=
        Int.le_of_dvd habs ((dvd_abs _ _).2 ((abs_dvd _ _).2 (hdvd n₀)))
      have h1b : 1 ≤ |b| := Int.one_le_abs hb0
      have hn0pos : 0 < n₀ := by rw [hn0]; positivity
      have hbn0 : |b * n₀| = |b| * n₀ := by
        rw [abs_mul, abs_of_pos hn0pos]
      have htri : |b * n₀| ≤ |b * n₀ + d| + |d| := by
        have := abs_add_le (b * n₀ + d) (-d); simpa using this
      have hbig : |ρ| < |b * n₀ + d| := by
        rw [hbn0] at htri
        nlinarith [htri, h1b, hn0pos, abs_nonneg d, le_abs_self d]
      linarith [hle, hbig]
    -- affine formula `b² gfun n + e b n + (f b − e d) = 0`.
    have hlin : ∀ n : ℤ, b ^ 2 * gfun n + e * b * n + (f * b - e * d) = 0 := by
      intro n
      have hz : (b * n + d) * (b ^ 2 * gfun n + e * b * n + (f * b - e * d)) = 0 := by
        linear_combination b ^ 2 * hspec n - hrho0
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h (hbd n)
      · exact h
    have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
    refine ⟨⟨-(f * b - e * d) / b ^ 2, fun _ => -e / b, fun _ _ => 0⟩, fun x => ?_⟩
    rw [hf1]
    have hl := hlin (x 0)
    have hlQ : (b : ℚ) ^ 2 * (gfun (x 0) : ℚ) + (e : ℚ) * (b : ℚ) * (x 0 : ℚ)
        + ((f : ℚ) * (b : ℚ) - (e : ℚ) * (d : ℚ)) = 0 := by exact_mod_cast hl
    simp only [QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
    field_simp
    linear_combination hlQ

/-! ### Theorem 3 — the generic branch `a ≠ 0` gives the full-residue coset normal form. -/

theorem a_ne_zero_full (a b d e f g : ℤ) (hT : RelTotal (R1 a b d e f g))
    (hU : RelUnique (R1 a b d e f g)) (ha : a ≠ 0) :
    FullCosetNF (f1 a b d e f g hT) := by
  set gfun : ℤ → ℤ := fun n => Classical.choose (hT n) with hgfun
  have hf1 : ∀ x : Fin 1 → ℤ, f1 a b d e f g hT x = gfun (x 0) := fun _ => rfl
  have hspec : ∀ n : ℤ, a * gfun n ^ 2 + (b * n + d) * gfun n + (e * n ^ 2 + f * n + g) = 0 := by
    intro n; have h := Classical.choose_spec (hT n); simpa [R1, P1, hgfun] using h
  -- The discriminant `Δ(n)` is a perfect square at every integer.
  have hdisc : ∀ n : ℤ, IsSquare ((b ^ 2 - 4 * a * e) * n ^ 2 + (2 * b * d - 4 * a * f) * n
      + (d ^ 2 - 4 * a * g)) := by
    intro n
    refine ⟨2 * a * gfun n + (b * n + d), ?_⟩
    have hs := hspec n
    linear_combination (-4 * a) * hs
  obtain ⟨r, sV, hrs⟩ := rigidity_core (b ^ 2 - 4 * a * e) (2 * b * d - 4 * a * f)
    (d ^ 2 - 4 * a * g) hdisc
  have hΔ : ∀ n : ℤ, (b * n + d) ^ 2 - 4 * a * (e * n ^ 2 + f * n + g) = (r * n + sV) ^ 2 := by
    intro n; have := hrs n; linear_combination this
  -- The `±` branch fact.
  have hsplit : ∀ n : ℤ, 2 * a * gfun n + (b * n + d) = r * n + sV
      ∨ 2 * a * gfun n + (b * n + d) = -(r * n + sV) := by
    intro n
    have hsq : (2 * a * gfun n + (b * n + d)) ^ 2 = (r * n + sV) ^ 2 := by
      have hs := hspec n; have hd := hΔ n; linear_combination 4 * a * hs + hd
    have hfac : (2 * a * gfun n + (b * n + d) - (r * n + sV))
        * (2 * a * gfun n + (b * n + d) + (r * n + sV)) = 0 := by linear_combination hsq
    rcases mul_eq_zero.1 hfac with h | h
    · left; linarith
    · right; linarith
  -- The modulus `M = 2|a|`.
  set M : ℕ := 2 * a.natAbs with hMdef
  have hMcast : (M : ℤ) = 2 * |a| := by rw [hMdef]; push_cast; rw [Int.abs_eq_natAbs]
  have hMdvd : (2 * a) ∣ (M : ℤ) := by
    rw [hMcast]
    exact mul_dvd_mul_left 2 ((dvd_abs a a).mpr (dvd_refl a))
  have h2a : (2 * a : ℤ) ≠ 0 := by intro hh; apply ha; linarith
  refine ⟨M, ?_, fun ρ => ?_⟩
  · have : a.natAbs ≠ 0 := Int.natAbs_ne_zero.2 ha
    rw [hMdef]; omega
  · set ρ₀ : ℤ := ρ 0 with hρ0
    obtain ⟨ε, hε2, hερ⟩ : ∃ ε : ℤ, ε ^ 2 = 1
        ∧ 2 * a * gfun ρ₀ + (b * ρ₀ + d) = ε * (r * ρ₀ + sV) := by
      rcases hsplit ρ₀ with h | h
      · exact ⟨1, by norm_num, by rw [one_mul]; exact h⟩
      · exact ⟨-1, by norm_num, by rw [neg_one_mul]; exact h⟩
    -- On the whole coset `ρ₀ + Mℤ` the output follows the `ε`-branch (uniqueness).
    have hval : ∀ τ : ℤ, 2 * a * gfun (ρ₀ + (M : ℤ) * τ)
        = -(b * (ρ₀ + (M : ℤ) * τ) + d) + ε * (r * (ρ₀ + (M : ℤ) * τ) + sV) := by
      intro τ
      set n : ℤ := ρ₀ + (M : ℤ) * τ with hn
      have hV0 : (2 * a) ∣ (-(b * ρ₀ + d) + ε * (r * ρ₀ + sV)) :=
        ⟨gfun ρ₀, by linear_combination -hερ⟩
      have hstep : (2 * a) ∣ ((-b + ε * r) * ((M : ℤ) * τ)) :=
        dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hMdvd τ) _
      have hVdvd : (2 * a) ∣ (-(b * n + d) + ε * (r * n + sV)) := by
        have heq : -(b * n + d) + ε * (r * n + sV)
            = (-(b * ρ₀ + d) + ε * (r * ρ₀ + sV)) + (-b + ε * r) * ((M : ℤ) * τ) := by
          rw [hn]; ring
        rw [heq]; exact dvd_add hV0 hstep
      obtain ⟨k, hk⟩ := hVdvd
      have hyc : 2 * a * k = -(b * n + d) + ε * (r * n + sV) := by linear_combination -hk
      have hRk : a * k ^ 2 + (b * n + d) * k + (e * n ^ 2 + f * n + g) = 0 := by
        have h4 : (4 * a) * (a * k ^ 2 + (b * n + d) * k + (e * n ^ 2 + f * n + g)) = 0 := by
          have hbranch : 2 * a * k + (b * n + d) = ε * (r * n + sV) := by linear_combination hyc
          have hd := hΔ n
          linear_combination (2 * a * k + (b * n + d) + ε * (r * n + sV)) * hbranch
            + (r * n + sV) ^ 2 * hε2 - hd
        rcases mul_eq_zero.1 h4 with hh | hh
        · exact absurd hh (by intro hz; apply ha; linarith)
        · exact hh
      have hRgn : R1 a b d e f g n (gfun n) := hspec n
      have hRkR : R1 a b d e f g n k := hRk
      have hgn : gfun n = k := hU n (gfun n) k hRgn hRkR
      rw [hgn]; linear_combination hyc
    -- Assemble the (affine) `QuadForm` for this coset.
    refine ⟨⟨((-(b * ρ₀ + d) + ε * (r * ρ₀ + sV) : ℤ) : ℚ) / ((2 * a : ℤ) : ℚ),
             fun _ => (((-b + ε * r) * (M : ℤ) : ℤ) : ℚ) / ((2 * a : ℤ) : ℚ),
             fun _ _ => 0⟩, fun t => ?_⟩
    rw [hf1]
    have harg : (ρ + (M : ℤ) • t) 0 = ρ₀ + (M : ℤ) * (t 0) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hρ0]
    rw [harg]
    have h2aQ : ((2 * a : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h2a
    have hgQ : ((2 * a : ℤ) : ℚ) * (gfun (ρ₀ + (M : ℤ) * (t 0)) : ℚ)
        = ((-(b * (ρ₀ + (M : ℤ) * (t 0)) + d)
            + ε * (r * (ρ₀ + (M : ℤ) * (t 0)) + sV) : ℤ) : ℚ) := by
      exact_mod_cast hval (t 0)
    simp only [QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
    push_cast at hgQ ⊢
    field_simp
    linear_combination hgQ

/-! ### Theorem 4 — combine, and the `GlobalQuadratic ⇒ FullCosetNF` bridge (n = 1). -/

/-- A single global quadratic in one variable also has the full-residue coset form (`M = 1`). -/
theorem globalQuadratic_imp_fullCoset_one {F : (Fin 1 → ℤ) → ℤ} (h : GlobalQuadratic F) :
    FullCosetNF F := by
  obtain ⟨q, hq⟩ := h
  refine ⟨1, le_refl 1, fun ρ => ?_⟩
  refine ⟨⟨q.c + q.l 0 * (ρ 0 : ℚ) + q.Q 0 0 * (ρ 0 : ℚ) ^ 2,
           fun _ => q.l 0 + 2 * q.Q 0 0 * (ρ 0 : ℚ), fun _ _ => q.Q 0 0⟩, fun t => ?_⟩
  have hval := hq (ρ + ((1 : ℕ) : ℤ) • t)
  rw [hval]
  simp only [QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **Main C1 deliverable.** The output of a total, unique C1 relation has the full-residue
coset normal form. -/
theorem oneInputNoWitness_full (a b d e f g : ℤ) (hT : RelTotal (R1 a b d e f g))
    (hU : RelUnique (R1 a b d e f g)) : FullCosetNF (f1 a b d e f g hT) := by
  rcases eq_or_ne a 0 with ha | ha
  · exact globalQuadratic_imp_fullCoset_one (a_zero_global a b d e f g hT hU ha)
  · exact a_ne_zero_full a b d e f g hT hU ha

/-- **Main C1 deliverable (weak form).** Corollary of the full-residue form. -/
theorem oneInputNoWitness_weak (a b d e f g : ℤ) (hT : RelTotal (R1 a b d e f g))
    (hU : RelUnique (R1 a b d e f g)) : WeakScalarCosetNF (f1 a b d e f g hT) :=
  WeakScalarCosetNF.of_full (oneInputNoWitness_full a b d e f g hT hU)

/-! ### Controls. -/

/-- `⌈x/2⌉` control: `P1 (4,−4,−2,1,1,0) = (2y−x)(2y−x−1)`. -/
example (x y : ℤ) : P1 4 (-4) (-2) 1 1 0 x y = (2 * y - x) * (2 * y - x - 1) := by
  unfold P1; ring

/-- `x²` control (the `a = 0` branch): `R1 (0,0,1,−1,0,0)` is exactly `y = x²`. -/
example (x y : ℤ) : R1 0 0 1 (-1) 0 0 x y ↔ y = x ^ 2 := by
  unfold R1 P1; constructor <;> intro h <;> linarith [h]

/-- NON-total control: `y² = x` (i.e. `R1 (1,0,0,0,−1,0)`) has no output at `x = 2`. -/
example : ¬ ∃ y : ℤ, R1 1 0 0 0 (-1) 0 2 y := by
  rintro ⟨y, hy⟩
  unfold R1 P1 at hy
  have h1 : y ^ 2 = 2 := by linear_combination hy
  have hb1 : y ≤ 2 := by nlinarith [h1, sq_nonneg (y - 2)]
  have hb2 : -2 ≤ y := by nlinarith [h1, sq_nonneg (y + 2)]
  interval_cases y <;> norm_num at h1

/-- NON-unique control: `y² = x²` (i.e. `R1 (1,0,0,−1,0,0)`) fails uniqueness at `x = 1`. -/
example : ¬ RelUnique (R1 1 0 0 (-1) 0 0) := by
  intro hU
  have r0 : R1 1 0 0 (-1) 0 0 1 1 := by unfold R1 P1; ring
  have r1 : R1 1 0 0 (-1) 0 0 1 (-1) := by unfold R1 P1; ring
  exact absurd (hU 1 1 (-1) r0 r1) (by norm_num)

end DiophCompression.ResearchUpgrade
