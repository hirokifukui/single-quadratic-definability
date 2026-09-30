/-
  Hensel.lean — Gate-18 research program, Packet B1 (elementary Hensel lifting, finite mod p^e).
  B1-1: for an integer polynomial f with p ∣ f(x₁) and p ∤ f'(x₁), every level e ≥ 1 has a root
        x_e ≡ x₁ (mod p) with p^e ∣ f(x_e). Proved by the one-digit lift x_{e+1} = x_e + p^e t and the
        Taylor identity f(x+y) = f(x) + f'(x) y + k y² (mathlib `Polynomial.binomExpansion`).
  B1-3: only per-level roots are produced (no compatible p-adic limit) — that is all the counting needs.
  No use of the p-adic Hensel lemma; no analytic input.
-/
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.PrincipalIdealDomain

namespace DiophCompression.ResearchUpgrade

open Polynomial

/-- Derivative values are congruent at congruent points. -/
theorem dvd_derivative_eval_sub (f : ℤ[X]) (d x y : ℤ) (h : d ∣ x - y) :
    d ∣ f.derivative.eval x - f.derivative.eval y := by
  obtain ⟨z, hz⟩ := f.derivative.evalSubFactor x y
  rw [hz]; exact h.mul_left z

/-- One Hensel step: from a root mod `p^e` with unit derivative to a root mod `p^(e+1)`. -/
theorem hensel_step (f : ℤ[X]) (p : ℕ) (hp : p.Prime) (e : ℕ) (he : 1 ≤ e) (x : ℤ)
    (hx : (p : ℤ) ^ e ∣ f.eval x) (hd : ¬ (p : ℤ) ∣ f.derivative.eval x) :
    ∃ x' : ℤ, (p : ℤ) ^ (e + 1) ∣ f.eval x' ∧ (p : ℤ) ^ e ∣ x' - x := by
  obtain ⟨a, ha⟩ := hx
  -- inverse of f'(x) mod p
  have hcop : IsCoprime (f.derivative.eval x) (p : ℤ) := by
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    exact (Int.isCoprime_iff_gcd_eq_one.mpr (by
      have := (Prime.coprime_iff_not_dvd hpZ).mpr hd
      rw [Int.isCoprime_iff_gcd_eq_one] at this
      rw [Int.gcd_comm]; exact this))
  obtain ⟨α, β, hαβ⟩ := hcop
  set t : ℤ := -(α * a) with ht
  obtain ⟨k, hk⟩ := f.binomExpansion x ((p : ℤ) ^ e * t)
  refine ⟨x + (p : ℤ) ^ e * t, ?_, ⟨t, by ring⟩⟩
  rw [hk, ha]
  -- p^e (a + f'(x) t) + k p^{2e} t², and a + f'(x) t = a β p
  have h1 : a + f.derivative.eval x * t = a * β * p := by
    rw [ht]; linear_combination (-a) * hαβ
  have h2 : (p : ℤ) ^ e * a + f.derivative.eval x * ((p : ℤ) ^ e * t) + k * ((p : ℤ) ^ e * t) ^ 2
      = (p : ℤ) ^ (e + 1) * (a * β) + (p : ℤ) ^ (e + 1) * ((p : ℤ) ^ (e - 1) * k * t ^ 2) := by
    have hpe : (p : ℤ) ^ (e * 2) = (p : ℤ) ^ (e + 1) * (p : ℤ) ^ (e - 1) := by
      rw [← pow_add]; congr 1; omega
    have : (p : ℤ) ^ e * a + f.derivative.eval x * ((p : ℤ) ^ e * t) = (p : ℤ) ^ e * (a + f.derivative.eval x * t) := by ring
    rw [this, h1, mul_pow, ← pow_mul, hpe]
    ring
  rw [h2]
  exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)

/-- B1-1. Hensel lifting to every level: `p ∣ f(x₁)`, `p ∤ f'(x₁)` ⇒ for all `e ≥ 1` there is
`x_e ≡ x₁ (mod p)` with `p^e ∣ f(x_e)`. -/
theorem hensel_lift (f : ℤ[X]) (p : ℕ) (hp : p.Prime) (x₁ : ℤ) (h1 : (p : ℤ) ∣ f.eval x₁)
    (hd : ¬ (p : ℤ) ∣ f.derivative.eval x₁) :
    ∀ e : ℕ, 1 ≤ e → ∃ x : ℤ, (p : ℤ) ^ e ∣ f.eval x ∧ (p : ℤ) ∣ x - x₁ := by
  intro e he
  induction e with
  | zero => omega
  | succ e ih =>
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · exact ⟨x₁, by simpa using h1, by simp⟩
    · obtain ⟨x, hx, hx1⟩ := ih hpos
      have hd' : ¬ (p : ℤ) ∣ f.derivative.eval x := by
        intro hc; apply hd
        have := dvd_derivative_eval_sub f (p : ℤ) x x₁ hx1
        have h3 : (p : ℤ) ∣ f.derivative.eval x₁ := by
          have := dvd_sub hc this; simpa using this
        exact h3
      obtain ⟨x', hx', hxx⟩ := hensel_step f p hp e hpos x hx hd'
      refine ⟨x', hx', ?_⟩
      have hpe : (p : ℤ) ∣ (p : ℤ) ^ e := dvd_pow_self _ (by omega)
      have := dvd_add (hpe.trans hxx) hx1
      simpa using this

end DiophCompression.ResearchUpgrade
