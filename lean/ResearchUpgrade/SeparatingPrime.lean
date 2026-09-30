/-
  SeparatingPrime.lean — Gate-20 Packet N1, tasks N1.1a, N1.2, N1.3.

  N1.1 (reviewer §2) asks for a prime `p`, outside any prescribed finite bad set, at which two
  quadratic characters take prescribed values: `(−D/p) = −1` and `(δ/p) = +1`.  The mathlib
  coverage probe (scripts/probe_n1{,b}_s46.lean, pin d46bd45) found BOTH load-bearing inputs
  present — `Nat.forall_exists_prime_gt_and_eq_mod` (Dirichlet on an arithmetic progression, in
  the "arbitrarily large prime in a unit class" form) and `jacobiSym.mod_right` (the symbol in the
  lower argument is periodic mod `4|a|`).  So N1.1 is NOT shipped as conditional on Dirichlet.

  The task splits, and the split is the honest boundary:
  * N1.1a (here, UNCONDITIONAL) — from a RESIDUE WITNESS `a mod M` carrying the two prescribed
    symbol values, produce arbitrarily large primes carrying them, hence one outside any finite
    bad set.  `ResidueWitness`, `separating_prime_of_residueWitness`, `separating_prime_avoiding`.
  * N1.1b (NOT proved here) — existence of the residue witness from `¬ IsSquare (−D·δ)`.  That is
    the finite-group character-separation step the reviewer flags as a proof obligation; it is
    `decide`-able for every concrete `(D, δ)` (`residueWitness_example`) and is recorded in
    TARGETS.md as a named leaf.  It is NEVER introduced as an axiom.

  N1.2 (reviewer §4, Taylor mod p²) is `exists_valuation_exactly_one`: at a simple root mod `p`
  of a quadratic, some lift has `v_p(F(n)) = 1` exactly.  Only two lifts are ever needed, `k = 0`
  and `k = 1`, because the derivative is a unit.

  N1.3 (bad-prime accounting) is `separating_prime_avoiding`: every finite exclusion set — the
  denominators, `2`, `A`, `D`, `δ` — is absorbed into one `Finset ℕ`, so no infinitely many
  primes are smuggled into a conclusion.

  Claim tags: all [P] (std-3).  Baseline (mpup-lean r39) read-only.
-/
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

namespace DiophCompression.ResearchUpgrade

/-! ## N1.1a — separating primes from a residue witness -/

/-- A residue class `a mod M` witnessing the two prescribed quadratic-character values, with `M`
even and divisible by the two periods `4|D|`, `4|δ|` of the symbols. -/
def ResidueWitness (D δ : ℤ) (M a : ℕ) : Prop :=
  0 < M ∧ 2 ∣ M ∧ 4 * D.natAbs ∣ M ∧ 4 * δ.natAbs ∣ M ∧ Nat.Coprime a M ∧
    jacobiSym (-D) a = -1 ∧ jacobiSym δ a = 1

/-- **N1.1a.** From a residue witness, arbitrarily large primes with `(−D/p) = −1`, `(δ/p) = +1`.
Unconditional: Dirichlet on the progression `a mod M` plus periodicity of the Jacobi symbol. -/
theorem separating_prime_of_residueWitness (D δ : ℤ) (M a : ℕ)
    (hw : ResidueWitness D δ M a) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ Odd p ∧ p ≡ a [MOD M] ∧
      jacobiSym (-D) p = -1 ∧ jacobiSym δ p = 1 := by
  obtain ⟨hM0, h2M, h4D, h4δ, hcop, hjD, hjδ⟩ := hw
  haveI : NeZero M := ⟨by omega⟩
  -- the witness class is odd, because `M` is even and `a` is a unit mod `M`
  have hgcd : Nat.gcd a M = 1 := hcop
  have hodd_a : Odd a := by
    rw [Nat.odd_iff]
    by_contra hev
    have h2a : 2 ∣ a := by omega
    have : (2 : ℕ) ∣ Nat.gcd a M := Nat.dvd_gcd h2a h2M
    rw [hgcd] at this
    omega
  -- Dirichlet
  have hunit : IsUnit ((a : ZMod M)) := (ZMod.isUnit_iff_coprime a M).mpr hcop
  obtain ⟨p, hpN, hpP, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit N
  have hmod : p ≡ a [MOD M] := (ZMod.natCast_eq_natCast_iff p a M).mp hpa
  have hodd_p : Odd p := by
    have h2 : p ≡ a [MOD 2] := Nat.ModEq.of_dvd h2M hmod
    rw [Nat.odd_iff] at hodd_a ⊢
    unfold Nat.ModEq at h2
    omega
  refine ⟨p, hpN, hpP, hodd_p, hmod, ?_, ?_⟩
  · have hper : 4 * (-D).natAbs ∣ M := by rwa [Int.natAbs_neg]
    have hstep : p % (4 * (-D).natAbs) = a % (4 * (-D).natAbs) := Nat.ModEq.of_dvd hper hmod
    rw [jacobiSym.mod_right _ hodd_p, hstep, ← jacobiSym.mod_right _ hodd_a]
    exact hjD
  · have hstep : p % (4 * δ.natAbs) = a % (4 * δ.natAbs) := Nat.ModEq.of_dvd h4δ hmod
    rw [jacobiSym.mod_right _ hodd_p, hstep, ← jacobiSym.mod_right _ hodd_a]
    exact hjδ

/-- **N1.3 (bad-prime accounting).** One finite exclusion set absorbs every bad prime: no
infinitely many primes are hidden in the conclusion. -/
theorem separating_prime_avoiding (D δ : ℤ) (M a : ℕ)
    (hw : ResidueWitness D δ M a) (S : Finset ℕ) :
    ∃ p : ℕ, p ∉ S ∧ p.Prime ∧ Odd p ∧ p ≡ a [MOD M] ∧
      jacobiSym (-D) p = -1 ∧ jacobiSym δ p = 1 := by
  obtain ⟨p, hgt, hpP, hodd, hmod, h1, h2⟩ :=
    separating_prime_of_residueWitness D δ M a hw (S.sup id)
  refine ⟨p, ?_, hpP, hodd, hmod, h1, h2⟩
  intro hmem
  have hle : p ≤ S.sup id := Finset.le_sup (f := id) hmem
  omega

/-! ## N1.2 — a simple root mod `p` lifts to valuation exactly one -/

/-- **N1.2.** Let `F(T) = A T² + B T + C` and let `a` be a root of `F` mod `p` at which the
derivative `F'(a) = 2Aa + B` is a unit mod `p`.  Then some `n ≡ a (mod p)` has `v_p(F(n)) = 1`
exactly.  Only the lifts `n = a` and `n = a + p` are needed: the derivative being a unit means at
most one residue `k mod p` can push `F(a + pk)` into `p²`, so one of `k = 0, 1` escapes. -/
theorem exists_valuation_exactly_one (p : ℕ) (hp : p.Prime) (A B C a : ℤ)
    (hroot : (p : ℤ) ∣ A * a ^ 2 + B * a + C)
    (hder : ¬ (p : ℤ) ∣ (2 * A * a + B)) :
    ∃ n : ℤ, (p : ℤ) ∣ (n - a) ∧ (p : ℤ) ∣ (A * n ^ 2 + B * n + C) ∧
      ¬ ((p : ℤ) ^ 2 ∣ (A * n ^ 2 + B * n + C)) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  obtain ⟨m, hm⟩ := hroot
  by_cases hpm : (p : ℤ) ∣ m
  · -- `k = 1`: `F(a + p) = p (p m' + F'(a) + p A)`, and `p ∣ m`, `p ∤ F'(a)`
    obtain ⟨m', hm'⟩ := hpm
    have hexp : A * (a + (p : ℤ)) ^ 2 + B * (a + (p : ℤ)) + C
        = (p : ℤ) * ((p : ℤ) * m' + (2 * A * a + B) + (p : ℤ) * A) := by
      linear_combination hm + (p : ℤ) * hm'
    refine ⟨a + (p : ℤ), ⟨1, by ring⟩,
      ⟨(p : ℤ) * m' + (2 * A * a + B) + (p : ℤ) * A, hexp⟩, ?_⟩
    rintro ⟨k, hk⟩
    apply hder
    refine ⟨k - m' - A, ?_⟩
    have hcancel : (p : ℤ) * ((p : ℤ) * m' + (2 * A * a + B) + (p : ℤ) * A)
        = (p : ℤ) * ((p : ℤ) * k) := by rw [← hexp, hk]; ring
    have h2 := mul_left_cancel₀ hp0 hcancel
    linear_combination h2
  · -- `k = 0`: `F(a) = p m` with `p ∤ m`
    refine ⟨a, ⟨0, by ring⟩, ⟨m, hm⟩, ?_⟩
    rintro ⟨k, hk⟩
    apply hpm
    refine ⟨k, ?_⟩
    have hcancel : (p : ℤ) * m = (p : ℤ) * ((p : ℤ) * k) := by rw [← hm, hk]; ring
    exact mul_left_cancel₀ hp0 hcancel

/-! ## Control for the N1.1b leaf: the interface is not vacuous -/

/-- `D = δ = 1`, `M = 4`, `a = 3`: here `δ/(−D) = −1` is not a square and the class `3 mod 4`
carries `(−1/p) = −1`, `(1/p) = +1`.  A concrete residue witness exists, so
`separating_prime_of_residueWitness` is not vacuously true. -/
theorem residueWitness_example : ResidueWitness 1 1 4 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [jacobiSym.at_neg_one (by decide : Odd 3), ZMod.χ₄_nat_eq_if_mod_four]
    norm_num
  · exact jacobiSym.one_left 3

/-- The witness of `residueWitness_example` yields primes `≡ 3 (mod 4)` beyond any bound. -/
theorem separating_prime_example (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ Odd p ∧ p ≡ 3 [MOD 4] ∧
      jacobiSym (-1) p = -1 ∧ jacobiSym 1 p = 1 :=
  separating_prime_of_residueWitness 1 1 4 3 residueWitness_example N

end DiophCompression.ResearchUpgrade
