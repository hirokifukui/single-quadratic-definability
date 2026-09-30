/-
  DiscriminantRigidity.lean — Gate-20 Packet N2, task N2.2.

  The assembly of N1.1a + N1.2 + N2.1.  Reviewer §4, Proposition N (the `A ≠ 0` branch):
  if every integer specialisation of `F(T) = A T² + B T + C` is a rational value of `x² + D y²`,
  then the discriminant satisfies `δ = 0` or `δ = −D h²` for some rational `h`.

  Proved here in contrapositive form, which is what the route actually needs and what keeps the
  dependency honest:

      a separating prime for the pair (D, δ) exists  ⟹  F is NOT totally represented.

  `SeparatingPrimeInput D δ` is exactly the output of N1.1a, so the theorem is UNCONDITIONAL
  given a residue witness (`discriminant_rigidity_of_residueWitness`).  It is NOT unconditional in
  `¬ IsSquare (−D·δ)`: that implication is the open leaf N1.1b (character separation).  The
  hypothesis is never introduced as an axiom; it is carried as a `Prop` argument so that the
  kernel footprint shows exactly what is assumed.

  Route (reviewer §4, with the bad-prime set as a single `Finset ℕ`):
  `(δ/p) = +1` and `p ∤ 2A` give `F` a simple root `a` mod `p` — explicitly
  `a = (−B + w)/(2A)` with `w² = δ`, whose derivative `F'(a) = w ≠ 0`.  N1.2 lifts it to `n` with
  `v_p(F(n)) = 1` exactly.  N2.1 says such a value is not `r² + D s²` over ℚ, because `(−D/p) = −1`.
  Contradiction with totality at `t = n`.

  Claim tags: [P] (std-3) for everything below; the leaf N1.1b is [OPEN].
  Baseline (mpup-lean r39) read-only.
-/
import Mathlib.Data.Fintype.Parity
import Mathlib.Data.ZMod.Defs
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import ResearchUpgrade.NormValuation
import ResearchUpgrade.SeparatingPrime

namespace DiophCompression.ResearchUpgrade

/-- The separating-prime input for the pair `(D, δ)`: primes outside any prescribed finite bad
set carrying `(−D/p) = −1` and `(δ/p) = +1`.  This is precisely what N1.1a produces. -/
def SeparatingPrimeInput (D δ : ℤ) : Prop :=
  ∀ S : Finset ℕ, ∃ p : ℕ, p ∉ S ∧ p.Prime ∧ Odd p ∧
    jacobiSym (-D) p = -1 ∧ jacobiSym δ p = 1

/-- N1.1a supplies the input. -/
theorem separatingPrimeInput_of_residueWitness (D δ : ℤ) (M a : ℕ)
    (hw : ResidueWitness D δ M a) : SeparatingPrimeInput D δ := by
  intro S
  obtain ⟨p, hS, hp, hodd, _, h1, h2⟩ := separating_prime_avoiding D δ M a hw S
  exact ⟨p, hS, hp, hodd, h1, h2⟩

/-- **N2.2 (contrapositive).**  If a separating prime exists for `(D, B² − 4AC)` and `A ≠ 0`,
then `A T² + B T + C` is not represented by `x² + D y²` at every integer. -/
theorem not_total_norm_of_separatingPrime (D A B C : ℤ) (hA : A ≠ 0)
    (hsep : SeparatingPrimeInput D (B ^ 2 - 4 * A * C)) :
    ¬ ∀ t : ℤ, ∃ r s : ℚ, ((A * t ^ 2 + B * t + C : ℤ) : ℚ) = r ^ 2 + (D : ℚ) * s ^ 2 := by
  intro htotal
  obtain ⟨p, hS, hp, hodd, hjD, hjδ⟩ := hsep (Finset.range (A.natAbs + 1))
  haveI := Fact.mk hp
  have hpA : A.natAbs < p := by
    simp only [Finset.mem_range, not_lt] at hS
    omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    simp [Nat.odd_iff] at hodd
  -- transport the two symbol values to Legendre symbols
  have hLD : legendreSym p (-D) = -1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; exact hjD
  have hLδ : legendreSym p (B ^ 2 - 4 * A * C) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; exact hjδ
  -- the discriminant is a nonzero square mod p
  have hδ0 : ((B ^ 2 - 4 * A * C : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff p _).mpr h0] at hLδ
    exact absurd hLδ (by norm_num)
  obtain ⟨w, hw⟩ := (legendreSym.eq_one_iff p hδ0).mp hLδ
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, mul_zero] at hw
    exact hδ0 hw
  -- `2A` is invertible mod p
  have hA0 : ((A : ℤ) : ZMod p) ≠ 0 := by
    intro h
    have hd : (p : ℤ) ∣ A := (ZMod.intCast_zmod_eq_zero_iff_dvd A p).mp h
    have hd2 : (p : ℤ) ∣ (A.natAbs : ℤ) := Int.dvd_natAbs.mpr hd
    have hd3 : p ∣ A.natAbs := by exact_mod_cast hd2
    have hpos : 0 < A.natAbs := by omega
    have hle := Nat.le_of_dvd hpos hd3
    omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hc : ((2 : ℤ) : ZMod p) = 0 := by push_cast; exact h
    have hd : (p : ℤ) ∣ (2 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp hc
    have hd' : p ∣ 2 := by exact_mod_cast hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd')
  have h2A : 2 * ((A : ℤ) : ZMod p) ≠ 0 := mul_ne_zero h2ne hA0
  -- the simple root
  set a : ZMod p := (-((B : ℤ) : ZMod p) + w) * (2 * ((A : ℤ) : ZMod p))⁻¹ with ha
  have hlin : 2 * ((A : ℤ) : ZMod p) * a + ((B : ℤ) : ZMod p) = w := by
    have hinv : (2 * ((A : ℤ) : ZMod p)) * (2 * ((A : ℤ) : ZMod p))⁻¹ = 1 :=
      mul_inv_cancel₀ h2A
    calc 2 * ((A : ℤ) : ZMod p) * a + ((B : ℤ) : ZMod p)
        = ((2 * ((A : ℤ) : ZMod p)) * (2 * ((A : ℤ) : ZMod p))⁻¹)
            * (-((B : ℤ) : ZMod p) + w) + ((B : ℤ) : ZMod p) := by rw [ha]; ring
      _ = (-((B : ℤ) : ZMod p) + w) + ((B : ℤ) : ZMod p) := by rw [hinv]; ring
      _ = w := by ring
  have hδcast : ((B ^ 2 - 4 * A * C : ℤ) : ZMod p)
      = ((B : ℤ) : ZMod p) ^ 2 - 4 * ((A : ℤ) : ZMod p) * ((C : ℤ) : ZMod p) := by
    push_cast; ring
  have h4A : 4 * ((A : ℤ) : ZMod p) ≠ 0 := by
    have h4 : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [h4, mul_assoc]
    exact mul_ne_zero h2ne (mul_ne_zero h2ne hA0)
  have hFa : ((A : ℤ) : ZMod p) * a ^ 2 + ((B : ℤ) : ZMod p) * a + ((C : ℤ) : ZMod p) = 0 := by
    have key : 4 * ((A : ℤ) : ZMod p)
        * (((A : ℤ) : ZMod p) * a ^ 2 + ((B : ℤ) : ZMod p) * a + ((C : ℤ) : ZMod p)) = 0 := by
      have e : 4 * ((A : ℤ) : ZMod p)
          * (((A : ℤ) : ZMod p) * a ^ 2 + ((B : ℤ) : ZMod p) * a + ((C : ℤ) : ZMod p))
          = (2 * ((A : ℤ) : ZMod p) * a + ((B : ℤ) : ZMod p)) ^ 2
            - (((B : ℤ) : ZMod p) ^ 2 - 4 * ((A : ℤ) : ZMod p) * ((C : ℤ) : ZMod p)) := by ring
      rw [e, hlin, ← hδcast, hw]; ring
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h h4A
    · exact h
  -- lift the root to ℤ
  have hcast : ((a.val : ℕ) : ZMod p) = a := by simp
  have hroot : (p : ℤ) ∣ A * (a.val : ℤ) ^ 2 + B * (a.val : ℤ) + C := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_
    push_cast
    rw [hcast]
    exact_mod_cast hFa
  have hder : ¬ (p : ℤ) ∣ (2 * A * (a.val : ℤ) + B) := by
    intro hdvd
    have h0 : ((2 * A * (a.val : ℤ) + B : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    push_cast at h0
    rw [hcast] at h0
    have hw' : w = 0 := by rw [← hlin]; linear_combination h0
    exact hw0 hw'
  -- N1.2 then N2.1
  obtain ⟨n, -, hn2, hn3⟩ := exists_valuation_exactly_one p hp A B C (a.val : ℤ) hroot hder
  have hnsD : ¬ IsSquare (-((D : ℤ) : ZMod p)) := by
    have hcast2 : (((-D : ℤ)) : ZMod p) = -((D : ℤ) : ZMod p) := by push_cast; ring
    have := (legendreSym.eq_neg_one_iff p).mp hLD
    rwa [hcast2] at this
  exact not_norm_rat_of_val_one p hp D hnsD (A * n ^ 2 + B * n + C) hn2 hn3 (htotal n)

/-- **N2.2, packaged.**  With a residue witness for `(D, δ)` — the concrete form of
"`δ/(−D)` is not a square" — total representability of `A T² + B T + C` by `x² + D y²` is
impossible.  Equivalently: totality forces `δ = 0` or `δ = −D h²`. -/
theorem discriminant_rigidity_of_residueWitness (D A B C : ℤ) (hA : A ≠ 0) (M a : ℕ)
    (hw : ResidueWitness D (B ^ 2 - 4 * A * C) M a)
    (htotal : ∀ t : ℤ, ∃ r s : ℚ, ((A * t ^ 2 + B * t + C : ℤ) : ℚ) = r ^ 2 + (D : ℚ) * s ^ 2) :
    False :=
  not_total_norm_of_separatingPrime D A B C hA
    (separatingPrimeInput_of_residueWitness D (B ^ 2 - 4 * A * C) M a hw) htotal

/-! ## An UNCONDITIONAL end-to-end instance

`D = 1`, `F(T) = T² + T + 1`, `δ = −3`.  Here `−Dδ = 3` is not a square, and the residue class
`7 mod 12` is an explicit residue witness — so the open leaf N1.1b is discharged BY HAND for this
pair and the whole chain N1.1a → N1.2 → N2.1 → N2.2 runs with no open hypothesis.
(Sanity: `F(1) = 3`, and `smoke_three_not_norm` says `3` is not a sum of two rational squares.) -/

private theorem notSquare_neg_one_seven : ¬ IsSquare (((-1 : ℤ)) : ZMod 7) := by decide

private theorem neg_three_ne_zero_seven : (((-3 : ℤ)) : ZMod 7) ≠ 0 := by decide

private theorem isSquare_neg_three_seven : IsSquare (((-3 : ℤ)) : ZMod 7) := by decide

/-- Explicit residue witness for `D = 1`, `δ = −3`: the class `7 mod 12`. -/
theorem residueWitness_one_minusThree : ResidueWitness 1 (-3) 12 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide, ?_, ?_⟩
  · rw [← jacobiSym.legendreSym.to_jacobiSym]
    exact (legendreSym.eq_neg_one_iff 7).mpr notSquare_neg_one_seven
  · rw [← jacobiSym.legendreSym.to_jacobiSym]
    exact (legendreSym.eq_one_iff 7 neg_three_ne_zero_seven).mpr isSquare_neg_three_seven

/-- `T² + T + 1` is not represented by `x² + y²` over ℚ at every integer.  Unconditional. -/
theorem quadratic_TT1_not_total_sum_two_squares :
    ¬ ∀ t : ℤ, ∃ r s : ℚ,
      ((1 * t ^ 2 + 1 * t + 1 : ℤ) : ℚ) = r ^ 2 + ((1 : ℤ) : ℚ) * s ^ 2 := by
  have hw : ResidueWitness 1 ((1 : ℤ) ^ 2 - 4 * 1 * 1) 12 7 := by
    have h : ((1 : ℤ) ^ 2 - 4 * 1 * 1) = -3 := by norm_num
    rw [h]; exact residueWitness_one_minusThree
  exact fun htotal =>
    discriminant_rigidity_of_residueWitness 1 1 1 1 (by norm_num) 12 7 hw htotal

end DiophCompression.ResearchUpgrade
