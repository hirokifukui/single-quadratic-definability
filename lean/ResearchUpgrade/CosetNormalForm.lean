/-
  CosetNormalForm.lean — Gate-18 research program, Packet C0.
  Three SEPARATE predicates (weak scalar coset / weak vector coset / full-residue) plus the
  global-polynomial predicate, totality and uniqueness of a relation as separate predicates,
  and the negative controls x², x(x−1)/2 (ℚ-coefficients needed), ⌈x/2⌉ (not one polynomial;
  full coset form with M = 2).
  A polynomial of total degree ≤ 2 in n variables over ℚ is represented explicitly as
  c + l·t + tᵀQt (QuadForm); the bridge to MvPolynomial is a listed leaf, not assumed.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.Star
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.TypeStar

namespace DiophCompression.ResearchUpgrade

open Matrix

/-- An explicit polynomial of degree ≤ 2 in `n` variables over ℚ: `c + l·t + tᵀ Q t`. -/
structure QuadForm (n : ℕ) where
  c : ℚ
  l : Fin n → ℚ
  Q : Matrix (Fin n) (Fin n) ℚ

namespace QuadForm

def eval {n : ℕ} (q : QuadForm n) (t : Fin n → ℚ) : ℚ :=
  q.c + q.l ⬝ᵥ t + t ⬝ᵥ (q.Q *ᵥ t)

/-- The linear part `L(t) = l·t` (used by the C4-3 kernel argument). -/
def linearPart {n : ℕ} (q : QuadForm n) (t : Fin n → ℚ) : ℚ := q.l ⬝ᵥ t

end QuadForm

/-- Cast an integer vector to ℚ. -/
def castQ {n : ℕ} (t : Fin n → ℤ) : Fin n → ℚ := fun i => (t i : ℚ)

/-- Weak scalar coset normal form: on ONE full lattice coset `ρ + M ℤⁿ`, `f` is a
polynomial of degree ≤ 2 over ℚ. -/
def WeakScalarCosetNF {n : ℕ} (f : (Fin n → ℤ) → ℤ) : Prop :=
  ∃ (M : ℕ) (ρ : Fin n → ℤ) (q : QuadForm n), 1 ≤ M ∧
    ∀ t : Fin n → ℤ, (f (ρ + (M : ℤ) • t) : ℚ) = q.eval (castQ t)

/-- Weak vector coset normal form: one coset for all `m` coordinates at once. -/
def WeakVectorCosetNF {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop :=
  ∃ (M : ℕ) (ρ : Fin n → ℤ) (q : Fin m → QuadForm n), 1 ≤ M ∧
    ∀ (t : Fin n → ℤ) (j : Fin m), (f (ρ + (M : ℤ) • t) j : ℚ) = (q j).eval (castQ t)

/-- Full-residue normal form: one modulus `M` works for EVERY coset `ρ + M ℤⁿ`
(quantifying over all `ρ ∈ ℤⁿ` is the same as over `{0,…,M−1}ⁿ`). -/
def FullCosetNF {n : ℕ} (f : (Fin n → ℤ) → ℤ) : Prop :=
  ∃ M : ℕ, 1 ≤ M ∧ ∀ ρ : Fin n → ℤ, ∃ q : QuadForm n,
    ∀ t : Fin n → ℤ, (f (ρ + (M : ℤ) • t) : ℚ) = q.eval (castQ t)

/-- `f` is a single polynomial of degree ≤ 2 on all of ℤⁿ (the false target to exclude). -/
def GlobalQuadratic {n : ℕ} (f : (Fin n → ℤ) → ℤ) : Prop :=
  ∃ q : QuadForm n, ∀ x : Fin n → ℤ, (f x : ℚ) = q.eval (castQ x)

/-- Totality of a relation (every input has an output). -/
def RelTotal {α β : Type*} (R : α → β → Prop) : Prop := ∀ x, ∃ y, R x y

/-- Uniqueness of a relation (at most one output per input). -/
def RelUnique {α β : Type*} (R : α → β → Prop) : Prop := ∀ x y y', R x y → R x y' → y = y'

/-! ### Trivial implications and the `n = 0` boundary -/

theorem WeakScalarCosetNF.of_global {n : ℕ} {f : (Fin n → ℤ) → ℤ} (h : GlobalQuadratic f) :
    WeakScalarCosetNF f := by
  obtain ⟨q, hq⟩ := h
  refine ⟨1, 0, q, le_refl _, fun t => ?_⟩
  rw [hq]; congr 1; funext i; simp [castQ]

theorem WeakScalarCosetNF.of_full {n : ℕ} {f : (Fin n → ℤ) → ℤ} (h : FullCosetNF f) :
    WeakScalarCosetNF f := by
  obtain ⟨M, hM, hq⟩ := h
  obtain ⟨q, hq0⟩ := hq 0
  exact ⟨M, 0, q, hM, hq0⟩

/-- `n = 0`: every function `(Fin 0 → ℤ) → ℤ` is constant, hence globally quadratic. -/
theorem globalQuadratic_of_zero (f : (Fin 0 → ℤ) → ℤ) : GlobalQuadratic f := by
  refine ⟨⟨(f (fun i => i.elim0) : ℚ), fun i => i.elim0, fun i => i.elim0⟩, fun x => ?_⟩
  have hx : x = fun i => i.elim0 := funext fun i => i.elim0
  subst hx
  simp [QuadForm.eval, dotProduct]

/-! ### Controls (n = 1) -/

/-- `x ↦ x²`. -/
def sq1 : (Fin 1 → ℤ) → ℤ := fun x => x 0 ^ 2
/-- `x ↦ x(x−1)/2` (integer division; exact since `x(x−1)` is even). -/
def tri1 : (Fin 1 → ℤ) → ℤ := fun x => x 0 * (x 0 - 1) / 2
/-- `x ↦ ⌈x/2⌉`, realised as `(x + 1) / 2` with floor division. -/
def ceilHalf1 : (Fin 1 → ℤ) → ℤ := fun x => (x 0 + 1) / 2

/-- `⌈x/2⌉` is exactly `(x+1)/2` with floor division. -/
theorem ceilHalf1_eq_ceil (x : Fin 1 → ℤ) : ceilHalf1 x = ⌈((x 0 : ℚ)) / 2⌉ := by
  unfold ceilHalf1
  symm
  rw [Int.ceil_eq_iff]
  constructor
  · have h := Int.emod_add_mul_ediv (x 0 + 1) 2
    have h2 := Int.emod_nonneg (x 0 + 1) (by norm_num : (2 : ℤ) ≠ 0)
    have h3 := Int.emod_lt_of_pos (x 0 + 1) (by norm_num : (0 : ℤ) < 2)
    have : ((x 0 + 1) / 2 : ℤ) - 1 < ((x 0 : ℚ)) / 2 := by
      have hq : ((x 0 : ℚ) + 1) = ((x 0 + 1) % 2 : ℤ) + 2 * (((x 0 + 1) / 2 : ℤ) : ℚ) := by
        exact_mod_cast h.symm
      have hm : (0 : ℚ) ≤ (((x 0 + 1) % 2 : ℤ) : ℚ) := by exact_mod_cast h2
      have hm' : (((x 0 + 1) % 2 : ℤ) : ℚ) < 2 := by exact_mod_cast h3
      push_cast at hq ⊢
      linarith
    exact this
  · have h := Int.emod_add_mul_ediv (x 0 + 1) 2
    have h3 := Int.emod_lt_of_pos (x 0 + 1) (by norm_num : (0 : ℤ) < 2)
    have hq : ((x 0 : ℚ) + 1) = ((x 0 + 1) % 2 : ℤ) + 2 * (((x 0 + 1) / 2 : ℤ) : ℚ) := by
      exact_mod_cast h.symm
    have hm' : (((x 0 + 1) % 2 : ℤ) : ℚ) < 2 := by exact_mod_cast h3
    have hm'' : (((x 0 + 1) % 2 : ℤ) : ℚ) ≤ 1 := by
      have : (x 0 + 1) % 2 ≤ 1 := by omega
      exact_mod_cast this
    push_cast at hq ⊢
    linarith

theorem sq1_global : GlobalQuadratic sq1 := by
  refine ⟨⟨0, fun _ => 0, fun _ _ => 1⟩, fun x => ?_⟩
  simp [sq1, QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
  ring

/-- Control: `x(x−1)/2` is globally quadratic — with the ℚ-coefficient `1/2`. -/
theorem tri1_global : GlobalQuadratic tri1 := by
  refine ⟨⟨0, fun _ => -(1/2 : ℚ), fun _ _ => (1/2 : ℚ)⟩, fun x => ?_⟩
  simp only [tri1, QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
  have hev : 2 ∣ x 0 * (x 0 - 1) := by
    rcases Int.even_or_odd (x 0) with h | h
    · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp h) _
    · apply Dvd.dvd.mul_left
      have : Even (x 0 - 1) := by
        obtain ⟨k, hk⟩ := h; exact ⟨k, by omega⟩
      exact even_iff_two_dvd.mp this
  obtain ⟨k, hk⟩ := hev
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  have hkq : ((x 0 : ℚ)) * ((x 0 : ℚ) - 1) = 2 * (k : ℚ) := by exact_mod_cast hk
  push_cast
  linarith

/-- Control: `⌈x/2⌉` has the full-residue normal form with `M = 2`
(`ρ` even: `t + ρ/2`; `ρ` odd: `t + (ρ+1)/2`). -/
theorem ceilHalf1_full : FullCosetNF ceilHalf1 := by
  refine ⟨2, by norm_num, fun ρ => ?_⟩
  refine ⟨⟨(((ρ 0 + 1) / 2 : ℤ) : ℚ), fun _ => 1, fun _ _ => 0⟩, fun t => ?_⟩
  simp only [ceilHalf1, QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_ofNat]
  have : (ρ 0 + 2 * t 0 + 1) / 2 = (ρ 0 + 1) / 2 + t 0 := by
    rw [show ρ 0 + 2 * t 0 + 1 = (ρ 0 + 1) + t 0 * 2 by ring, Int.add_mul_ediv_right _ _ (by norm_num)]
  push_cast [this]
  ring

/-- Control: `⌈x/2⌉` is NOT a single polynomial of degree ≤ 2 on ℤ
(values 0,1,1,2 at 0,1,2,3 are not quadratically interpolable). -/
theorem ceilHalf1_not_global : ¬ GlobalQuadratic ceilHalf1 := by
  rintro ⟨q, hq⟩
  have h0 := hq (fun _ => 0)
  have h1 := hq (fun _ => 1)
  have h2 := hq (fun _ => 2)
  have h3 := hq (fun _ => 3)
  simp only [ceilHalf1, QuadForm.eval, castQ, dotProduct, Matrix.mulVec, Fin.sum_univ_one] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  linarith

end DiophCompression.ResearchUpgrade
