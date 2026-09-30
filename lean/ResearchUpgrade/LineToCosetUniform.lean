/-
  LineToCosetUniform.lean — Gate-20 Packet 9, task T28.

  `LineToCosetUniform` (GeneralResidual.lean, R2) was shipped at s46 as an OPEN statement.
  It is TRUE, and the proof is elementary: with the line modulus UNIFORM, the restriction of
  `f` to the lattice `M ℤⁿ` satisfies the Jensen identity `g(a+v) + g(a-v) = 2 g(a)`; the
  shifted function `h = g - g 0` is then additive, hence ℤ-linear, hence `f` is affine on that
  one coset — a degree-≤2 normal form with zero quadratic part.

  This does NOT prove `LineToCoset` (R1, the crux): the non-uniform hypothesis gives a modulus
  that may grow with the direction, and no single `M` need exist.  Regression control #17 and
  the reviewer's T28 pass condition ("非一様 LineAffine ⇒ uniform を証明したことにしない")
  both bite exactly here.

  Claim tag: [P] (std-3).  Baseline read-only.
-/
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Rat.Init
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.GeneralResidual

namespace DiophCompression.ResearchUpgrade

open Matrix

section

variable {n : ℕ} (f : (Fin n → ℤ) → ℤ) (M : ℕ)

/-- The restriction of `f` to the lattice `M ℤⁿ`, valued in ℚ. -/
private def latticeRestrict : (Fin n → ℤ) → ℚ := fun a => ((f ((M : ℤ) • a) : ℤ) : ℚ)

end

/-- **T28.**  A uniform line modulus does give a normal form on one full lattice coset. -/
theorem lineToCosetUniform_holds : LineToCosetUniform := by
  intro n f hf
  obtain ⟨M, hM, hline⟩ := hf
  set g : (Fin n → ℤ) → ℚ := latticeRestrict f M with hgdef
  -- (1) Jensen identity on the lattice
  have hjensen : ∀ a v : Fin n → ℤ, g (a + v) + g (a - v) = 2 * g a := by
    intro a v
    obtain ⟨c₁, c₀, hc⟩ := hline ((M : ℤ) • a) v
    have key : ∀ s : ℤ, g (a + s • v) = c₁ * (s : ℚ) + c₀ := by
      intro s
      have hsm : (M : ℤ) • a + ((M : ℤ) * s) • v = (M : ℤ) • (a + s • v) := by
        rw [smul_add, mul_smul]
      have h2 := hc s
      rw [hsm] at h2
      simpa [hgdef, latticeRestrict] using h2
    have h1 := key 1
    have hm1 := key (-1)
    have h0 := key 0
    rw [one_smul] at h1
    rw [show a + (-1 : ℤ) • v = a - v by rw [neg_smul, one_smul, ← sub_eq_add_neg]] at hm1
    rw [show a + (0 : ℤ) • v = a by rw [zero_smul, add_zero]] at h0
    rw [h1, hm1, h0]; push_cast; ring
  -- (2) the shifted function is additive
  set h : (Fin n → ℤ) → ℚ := fun a => g a - g 0 with hhdef
  have hdouble : ∀ x : Fin n → ℤ, h (x + x) = 2 * h x := by
    intro x
    have := hjensen x x
    rw [show x - x = (0 : Fin n → ℤ) by abel] at this
    simp only [hhdef]; linarith
  have hadd : ∀ x y : Fin n → ℤ, h (x + y) = h x + h y := by
    intro x y
    have hj := hjensen (x + y) (x - y)
    rw [show x + y + (x - y) = x + x by abel, show x + y - (x - y) = y + y by abel] at hj
    have hx := hdouble x
    have hy := hdouble y
    simp only [hhdef] at hx hy ⊢
    linarith
  -- (3) additive ⇒ ℤ-linear ⇒ a dot product
  let H : (Fin n → ℤ) →+ ℚ := AddMonoidHom.mk' h hadd
  set l : Fin n → ℚ := fun i => h (Pi.single i 1) with hldef
  have hsingle : ∀ (i : Fin n) (r : ℤ),
      (Pi.single i r : Fin n → ℤ) = r • (Pi.single i 1 : Fin n → ℤ) := by
    intro i r
    have := Pi.single_smul' (I := Fin n) (β := ℤ) i r (1 : ℤ)
    simpa using this
  have hlin : ∀ a : Fin n → ℤ, h a = ∑ i, (a i : ℚ) * l i := by
    intro a
    have hHa : H a = h a := rfl
    have hsum : a = ∑ i, (Pi.single i (a i) : Fin n → ℤ) := (Finset.univ_sum_single a).symm
    calc h a = H (∑ i, (Pi.single i (a i) : Fin n → ℤ)) := by rw [← hsum]; exact hHa.symm
      _ = ∑ i, H (Pi.single i (a i) : Fin n → ℤ) := map_sum H _ _
      _ = ∑ i, (a i : ℚ) * l i := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [hsingle i (a i), map_zsmul H (a i) _]
            simp [hldef, H, zsmul_eq_mul]
  -- (4) assemble the normal form on the coset ρ = 0, modulus M, zero quadratic part
  refine ⟨M, 0, ⟨g 0, l, 0⟩, hM, fun t => ?_⟩
  have hlhs : ((f (0 + (M : ℤ) • t) : ℤ) : ℚ) = g t := by
    rw [zero_add]; rfl
  rw [hlhs]
  have hgt : g t = h t + g 0 := by simp [hhdef]
  rw [hgt, hlin t]
  simp [QuadForm.eval, dotProduct, Matrix.zero_mulVec, castQ, mul_comm]
  ring

/-! ### Controls (reviewer's 共通の成果物形式: POSITIVE_CONTROL / NEGATIVE_CONTROL) -/

/-- POSITIVE control (the hypothesis of T28 is satisfiable): a coordinate projection has a
uniform line modulus, with `M = 1`. -/
theorem lineAffineUniform_proj {n : ℕ} (i : Fin n) :
    LineAffineUniform (fun a : Fin n → ℤ => a i) := by
  refine ⟨1, le_refl 1, fun ρ v => ⟨(v i : ℚ), (ρ i : ℚ), fun s => ?_⟩⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]
  push_cast
  ring

/-- NEGATIVE control (the hypothesis of T28 is not trivially true): `x ↦ x²` has no uniform
line modulus.  Without this, T28 could be vacuous in the other direction. -/
theorem not_lineAffineUniform_sq1 : ¬ LineAffineUniform sq1 := by
  rintro ⟨M, hM, hu⟩
  obtain ⟨c₁, c₀, hc⟩ := hu 0 (fun _ => 1)
  have key : ∀ s : ℤ, (((M : ℤ) * s : ℤ) : ℚ) ^ 2 = c₁ * (s : ℚ) + c₀ := by
    intro s
    have h := hc s
    simpa [sq1, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  push_cast at h0 h1 h2
  have hM' : (1 : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
  nlinarith [h0, h1, h2, hM']

end DiophCompression.ResearchUpgrade
