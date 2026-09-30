/-
  CharacterSeparationReduction.lean — Gate-20 Packet N1, shrinking the N1.1b leaf.

  `CharacterSeparation` asks for a class carrying TWO prescribed symbol values,
  `J(−D | a) = −1` and `J(δ | a) = +1`.  This file reduces it to ONE character statement:

      NonResidueClass :=
        a non-square integer `n` is a non-residue on some unit class modulo any modulus
        carrying its period, i.e. `∃ a, Coprime a M ∧ J(n | a) = −1`.

  The reduction is elementary and uses only multiplicativity of the Jacobi symbol in its upper
  argument (`jacobiSym.mul_left`) plus a three-case argument on ±1 values:

  write `χ₁(a) = J(−D | a)` and `χ₃(a) = J(−Dδ | a)`.  Since `χ₁ · J(δ | ·) = χ₃`, what is wanted
  is a single `a` with `χ₁(a) = χ₃(a) = −1`.  Given `a₁` with `χ₁(a₁) = −1` and `a₂` with
  `χ₃(a₂) = −1`:
    * if `χ₃(a₁) = −1`, take `a₁`;
    * else if `χ₁(a₂) = −1`, take `a₂`;
    * else take `a₁ a₂`, where `χ₁ = (−1)(+1) = −1` and `χ₃ = (+1)(−1) = −1`.

  Both inputs are instances of `NonResidueClass`: `−D < 0` is never a rational square (this is
  where `0 < D` is used — see the s46 erratum in WeakAffine.lean), and `−Dδ` is not a square
  exactly when `δ = −D h²` has no rational solution.

  So the whole of N1.1b now rests on one classical statement about a SINGLE character.

  Claim tags: [P] (std-3); `NonResidueClass` is the remaining [OPEN] leaf.
  Baseline read-only.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.LinearCombination
import ResearchUpgrade.WeakAffine

namespace DiophCompression.ResearchUpgrade

/-- **The remaining leaf of N1.1b**, for a SINGLE character: a non-square integer is a
non-residue on some unit class modulo any modulus carrying its period. -/
def NonResidueClass : Prop :=
  ∀ (n : ℤ) (M : ℕ), 0 < M → 2 ∣ M → 4 * n.natAbs ∣ M → (¬ ∃ h : ℚ, (n : ℚ) = h ^ 2) →
    ∃ a : ℕ, Nat.Coprime a M ∧ jacobiSym n a = -1

/-- A negative integer is never a rational square. -/
theorem not_ratSquare_of_neg (n : ℤ) (hn : n < 0) : ¬ ∃ h : ℚ, (n : ℚ) = h ^ 2 := by
  rintro ⟨h, hh⟩
  have h1 : (n : ℚ) < 0 := by exact_mod_cast hn
  nlinarith [sq_nonneg h]

/-- `δ = −D h²` is solvable iff `−Dδ` is a rational square (for `D ≠ 0`). -/
theorem neg_mul_isSquare_iff (D δ : ℤ) (hD : D ≠ 0) :
    (∃ h : ℚ, ((-D * δ : ℤ) : ℚ) = h ^ 2) ↔ (∃ h : ℚ, (δ : ℚ) = -(D : ℚ) * h ^ 2) := by
  have hDQ : ((D : ℚ)) ≠ 0 := by exact_mod_cast hD
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h / (D : ℚ), ?_⟩
    push_cast at hh
    linear_combination (norm := (field_simp; ring)) (-(1 : ℚ) / (D : ℚ)) * hh
  · rintro ⟨h, hh⟩
    refine ⟨(D : ℚ) * h, ?_⟩
    push_cast
    linear_combination -(D : ℚ) * hh

/-- **The reduction.**  One character statement suffices for N1.1b. -/
theorem characterSeparation_of_nonResidueClass (hNR : NonResidueClass) : CharacterSeparation := by
  intro D δ hD hδ hno
  have hDne : D ≠ 0 := hD.ne'
  set M : ℕ := 8 * D.natAbs * δ.natAbs with hM
  have hDa : 0 < D.natAbs := by omega
  have hδa : 0 < δ.natAbs := by omega
  have hM0 : 0 < M := by rw [hM]; positivity
  have h2M : 2 ∣ M := ⟨4 * D.natAbs * δ.natAbs, by rw [hM]; ring⟩
  have h4D : 4 * D.natAbs ∣ M := ⟨2 * δ.natAbs, by rw [hM]; ring⟩
  have h4δ : 4 * δ.natAbs ∣ M := ⟨2 * D.natAbs, by rw [hM]; ring⟩
  have hnegD : 4 * (-D).natAbs ∣ M := by rwa [Int.natAbs_neg]
  have hprod : 4 * (-D * δ).natAbs ∣ M := by
    rw [Int.natAbs_mul, Int.natAbs_neg]
    exact ⟨2, by rw [hM]; ring⟩
  -- the symbol is ±1 on classes coprime to M
  have hpm : ∀ (x : ℤ) (aa : ℕ), x.natAbs ∣ M → Nat.Coprime aa M →
      jacobiSym x aa = 1 ∨ jacobiSym x aa = -1 := by
    intro x aa hx hcop
    refine jacobiSym.eq_one_or_neg_one ?_
    have hco : Nat.Coprime aa x.natAbs := Nat.Coprime.coprime_dvd_right hx hcop
    have : Nat.gcd x.natAbs aa = 1 := Nat.coprime_comm.mp hco
    simpa [Int.gcd, Int.natAbs_natCast] using this
  have hDdvd : (-D).natAbs ∣ M := by
    rw [Int.natAbs_neg]
    exact dvd_trans ⟨4, by ring⟩ h4D
  have hPdvd : (-D * δ).natAbs ∣ M := dvd_trans ⟨4, by ring⟩ hprod
  have hM8 : 8 ≤ M := by
    rw [hM]
    calc 8 = 8 * 1 * 1 := by ring
      _ ≤ 8 * D.natAbs * δ.natAbs := by
          exact Nat.mul_le_mul (Nat.mul_le_mul_left 8 hDa) hδa
  have hne : ∀ aa : ℕ, Nat.Coprime aa M → aa ≠ 0 := by
    intro aa hcop h0
    rw [h0] at hcop
    have : M = 1 := by simpa [Nat.Coprime] using hcop
    omega
  -- the two single-character inputs
  obtain ⟨a₁, hc₁, hj₁⟩ :=
    hNR (-D) M hM0 h2M hnegD (not_ratSquare_of_neg (-D) (by omega))
  obtain ⟨a₂, hc₂, hj₂⟩ :=
    hNR (-D * δ) M hM0 h2M hprod (fun hsq => hno ((neg_mul_isSquare_iff D δ hDne).mp hsq))
  haveI : NeZero a₁ := ⟨hne a₁ hc₁⟩
  haveI : NeZero a₂ := ⟨hne a₂ hc₂⟩
  -- the three-case combination
  have key : ∃ a : ℕ, Nat.Coprime a M ∧ jacobiSym (-D) a = -1 ∧ jacobiSym (-D * δ) a = -1 := by
    by_cases h1 : jacobiSym (-D * δ) a₁ = -1
    · exact ⟨a₁, hc₁, hj₁, h1⟩
    · by_cases h2 : jacobiSym (-D) a₂ = -1
      · exact ⟨a₂, hc₂, h2, hj₂⟩
      · have e1 : jacobiSym (-D * δ) a₁ = 1 := by
          rcases hpm (-D * δ) a₁ hPdvd hc₁ with h | h
          · exact h
          · exact absurd h h1
        have e2 : jacobiSym (-D) a₂ = 1 := by
          rcases hpm (-D) a₂ hDdvd hc₂ with h | h
          · exact h
          · exact absurd h h2
        refine ⟨a₁ * a₂, Nat.Coprime.mul_left hc₁ hc₂, ?_, ?_⟩
        · rw [jacobiSym.mul_right (-D) a₁ a₂, hj₁, e2]; ring
        · rw [jacobiSym.mul_right (-D * δ) a₁ a₂, e1, hj₂]; ring
  obtain ⟨a, hca, hja, hjb⟩ := key
  refine ⟨M, a, hM0, h2M, h4D, h4δ, hca, hja, ?_⟩
  -- J(δ | a) = +1 follows from multiplicativity
  have hmul : jacobiSym (-D * δ) a = jacobiSym (-D) a * jacobiSym δ a := jacobiSym.mul_left _ _ _
  rw [hja] at hmul
  rw [hjb] at hmul
  linarith [hmul]

end DiophCompression.ResearchUpgrade
