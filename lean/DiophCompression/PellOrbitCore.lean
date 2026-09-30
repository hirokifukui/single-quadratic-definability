/-
  DiophCompression/PellOrbitCore.lean — APAL Structural Theory Gate 5, 必須F step 2 (Pell pattern)
  (s28, 2026-09-02, claude.ai direct).

  The arithmetic core shared by the two Pell leaves (A1 in the full-rank block, D7 in the one-witness
  normal form). Both sealed proofs contain a STEP: from a fibre point with a positive `X = 2Dc + β` they
  produce a larger fibre point, by multiplying `(X, Y)` with a fixed unit `(P, Q)` of `x² − D y² = 1`, and
  then conclude infinitude — the orbit itself is never named. Here the orbit is a definition and its four
  load-bearing properties are theorems: the recurrence, norm preservation, strict growth, and the
  congruence `M ∣ X k − X 0` that keeps the output in its residue class (hence integral after division by
  the denominator). This is exactly the data `PellUnitOrbitRealization` asks for. No sorry; std-3.
-/
import Mathlib

namespace DiophCompression

/-- The orbit of `(X₀, Y₀)` under multiplication by the unit `P + Q√D`. -/
def pellOrbit (D P Q X₀ Y₀ : ℤ) : ℕ → ℤ × ℤ
  | 0 => (X₀, Y₀)
  | k + 1 =>
      ((pellOrbit D P Q X₀ Y₀ k).1 * P + D * (pellOrbit D P Q X₀ Y₀ k).2 * Q,
        (pellOrbit D P Q X₀ Y₀ k).1 * Q + (pellOrbit D P Q X₀ Y₀ k).2 * P)

@[simp] theorem pellOrbit_zero (D P Q X₀ Y₀ : ℤ) : pellOrbit D P Q X₀ Y₀ 0 = (X₀, Y₀) := rfl

theorem pellOrbit_succ_fst (D P Q X₀ Y₀ : ℤ) (k : ℕ) :
    (pellOrbit D P Q X₀ Y₀ (k + 1)).1
      = (pellOrbit D P Q X₀ Y₀ k).1 * P + D * (pellOrbit D P Q X₀ Y₀ k).2 * Q := rfl

theorem pellOrbit_succ_snd (D P Q X₀ Y₀ : ℤ) (k : ℕ) :
    (pellOrbit D P Q X₀ Y₀ (k + 1)).2
      = (pellOrbit D P Q X₀ Y₀ k).1 * Q + (pellOrbit D P Q X₀ Y₀ k).2 * P := rfl

/-- Norm preservation along the orbit (the unit has norm 1). -/
theorem pellOrbit_norm (D P Q X₀ Y₀ : ℤ) (hunit : P ^ 2 - D * Q ^ 2 = 1) (k : ℕ) :
    (pellOrbit D P Q X₀ Y₀ k).1 ^ 2 - D * (pellOrbit D P Q X₀ Y₀ k).2 ^ 2
      = X₀ ^ 2 - D * Y₀ ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pellOrbit_succ_fst, pellOrbit_succ_snd]
    have := ih
    linear_combination (pellOrbit D P Q X₀ Y₀ k).1 ^ 2 * hunit
      - D * (pellOrbit D P Q X₀ Y₀ k).2 ^ 2 * hunit + this

/-- Positivity is preserved: with `D > 0`, `P ≥ 1`, `Q ≥ 0` and a nonnegative base, both coordinates stay
    nonnegative and the first stays positive. -/
theorem pellOrbit_pos (D P Q X₀ Y₀ : ℤ) (hD : 0 < D) (hP : 1 ≤ P) (hQ : 0 ≤ Q)
    (hX₀ : 0 < X₀) (hY₀ : 0 ≤ Y₀) (k : ℕ) :
    0 < (pellOrbit D P Q X₀ Y₀ k).1 ∧ 0 ≤ (pellOrbit D P Q X₀ Y₀ k).2 := by
  induction k with
  | zero => exact ⟨hX₀, hY₀⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [pellOrbit_succ_fst, pellOrbit_succ_snd]
    constructor
    · have e1 : 0 < (pellOrbit D P Q X₀ Y₀ k).1 * P := by positivity
      have e2 : 0 ≤ D * (pellOrbit D P Q X₀ Y₀ k).2 * Q := by positivity
      linarith
    · positivity

/-- Strict growth of the first coordinate, from `P ≥ 2` (a nontrivial unit). -/
theorem pellOrbit_strictMono_fst (D P Q X₀ Y₀ : ℤ) (hD : 0 < D) (hP : 2 ≤ P) (hQ : 0 ≤ Q)
    (hX₀ : 0 < X₀) (hY₀ : 0 ≤ Y₀) :
    StrictMono (fun k => (pellOrbit D P Q X₀ Y₀ k).1) := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  obtain ⟨h1, h2⟩ := pellOrbit_pos D P Q X₀ Y₀ hD (by linarith) hQ hX₀ hY₀ k
  rw [pellOrbit_succ_fst]
  have e1 : (pellOrbit D P Q X₀ Y₀ k).1 * 2 ≤ (pellOrbit D P Q X₀ Y₀ k).1 * P :=
    mul_le_mul_of_nonneg_left hP (le_of_lt h1)
  have e2 : 0 ≤ D * (pellOrbit D P Q X₀ Y₀ k).2 * Q := by positivity
  linarith

/-- The congruence that keeps the output integral: if the modulus divides `P − 1` and `Q`, then every
    orbit coordinate stays in the residue class of the base. -/
theorem pellOrbit_congr (D P Q X₀ Y₀ M : ℤ) (hP : M ∣ P - 1) (hQ : M ∣ Q) (k : ℕ) :
    M ∣ (pellOrbit D P Q X₀ Y₀ k).1 - X₀ ∧ M ∣ (pellOrbit D P Q X₀ Y₀ k).2 - Y₀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [pellOrbit_succ_fst, pellOrbit_succ_snd]
    constructor
    · have e : (pellOrbit D P Q X₀ Y₀ k).1 * P + D * (pellOrbit D P Q X₀ Y₀ k).2 * Q - X₀
          = ((pellOrbit D P Q X₀ Y₀ k).1 - X₀) + (pellOrbit D P Q X₀ Y₀ k).1 * (P - 1)
            + D * (pellOrbit D P Q X₀ Y₀ k).2 * Q := by ring
      rw [e]
      exact dvd_add (dvd_add h1 (Dvd.dvd.mul_left hP _)) (Dvd.dvd.mul_left hQ _)
    · have e : (pellOrbit D P Q X₀ Y₀ k).1 * Q + (pellOrbit D P Q X₀ Y₀ k).2 * P - Y₀
          = (pellOrbit D P Q X₀ Y₀ k).1 * Q + ((pellOrbit D P Q X₀ Y₀ k).2 - Y₀)
            + (pellOrbit D P Q X₀ Y₀ k).2 * (P - 1) := by ring
      rw [e]
      exact dvd_add (dvd_add (Dvd.dvd.mul_left hQ _) h2) (Dvd.dvd.mul_left hP _)

/-- Unboundedness of the first coordinate (what the sealed proofs actually use, now a corollary of the
    orbit rather than an existence statement). -/
theorem pellOrbit_unbounded_fst (D P Q X₀ Y₀ : ℤ) (hD : 0 < D) (hP : 2 ≤ P) (hQ : 0 ≤ Q)
    (hX₀ : 0 < X₀) (hY₀ : 0 ≤ Y₀) (b : ℤ) : ∃ k : ℕ, b < (pellOrbit D P Q X₀ Y₀ k).1 := by
  have hmono := pellOrbit_strictMono_fst D P Q X₀ Y₀ hD hP hQ hX₀ hY₀
  have hb : ∀ k : ℕ, X₀ + (k : ℤ) ≤ (pellOrbit D P Q X₀ Y₀ k).1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep : (pellOrbit D P Q X₀ Y₀ k).1 < (pellOrbit D P Q X₀ Y₀ (k + 1)).1 :=
        hmono (Nat.lt_succ_self k)
      push_cast
      linarith
  refine ⟨(b - X₀ + 1).toNat, ?_⟩
  have h1 := hb (b - X₀ + 1).toNat
  have h2 : b - X₀ + 1 ≤ ((b - X₀ + 1).toNat : ℤ) := Int.self_le_toNat _
  linarith



/-- Flipping the sign of the unit's second coordinate flips the second orbit coordinate and leaves the
    first unchanged. This reduces the case `Y₀ ≤ 0` of the growth lemma to the case `Y₀ ≥ 0`, so a single
    sign choice at the base suffices (the sealed proofs chose a sign at every step). -/
theorem pellOrbit_neg_snd (D P Q X₀ Y₀ : ℤ) (k : ℕ) :
    pellOrbit D P (-Q) X₀ (-Y₀) k
      = ((pellOrbit D P Q X₀ Y₀ k).1, -(pellOrbit D P Q X₀ Y₀ k).2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (pellOrbit D P (-Q) X₀ (-Y₀) k).1 = (pellOrbit D P Q X₀ Y₀ k).1 := by rw [ih]
    have h2 : (pellOrbit D P (-Q) X₀ (-Y₀) k).2 = -(pellOrbit D P Q X₀ Y₀ k).2 := by rw [ih]
    refine Prod.ext ?_ ?_
    · rw [pellOrbit_succ_fst, pellOrbit_succ_fst, h1, h2]; ring
    · rw [pellOrbit_succ_snd, pellOrbit_succ_snd, h1, h2]; ring

/-- Growth in the mirrored case: a nonpositive base and a nonpositive `Q` also give strict growth of the
    first coordinate. -/
theorem pellOrbit_strictMono_fst_neg (D P Q X₀ Y₀ : ℤ) (hD : 0 < D) (hP : 2 ≤ P) (hQ : Q ≤ 0)
    (hX₀ : 0 < X₀) (hY₀ : Y₀ ≤ 0) :
    StrictMono (fun k => (pellOrbit D P Q X₀ Y₀ k).1) := by
  have hmono := pellOrbit_strictMono_fst D P (-Q) X₀ (-Y₀) hD hP (by linarith) hX₀ (by linarith)
  have heq : ∀ k, (pellOrbit D P (-Q) X₀ (-Y₀) k).1 = (pellOrbit D P Q X₀ Y₀ k).1 := by
    intro k
    rw [pellOrbit_neg_snd D P Q X₀ Y₀ k]
  intro i j hij
  have h := hmono hij
  simp only at h
  rw [heq i, heq j] at h
  exact h

/-! ### The output layer: the affine projection with denominator `2D` -/

/-- The output stays integral. `X k − β` is divisible by `2D` at every stage, because the orbit stays in
    the residue class of the base modulo `M` and `2D ∣ M`. This is the integrality that makes
    `c k = (X k − β)/(2D)` a legitimate output (the `denom` field of `PellUnitOrbitRealization`). -/
theorem pellOrbit_output_dvd (D P Q X₀ Y₀ β M : ℤ) (hM2D : 2 * D ∣ M)
    (hP : M ∣ P - 1) (hQ : M ∣ Q) (h₀ : 2 * D ∣ X₀ - β) (k : ℕ) :
    2 * D ∣ (pellOrbit D P Q X₀ Y₀ k).1 - β := by
  have hk := (pellOrbit_congr D P Q X₀ Y₀ M hP hQ k).1
  have h1 : 2 * D ∣ (pellOrbit D P Q X₀ Y₀ k).1 - X₀ := dvd_trans hM2D hk
  have e : (pellOrbit D P Q X₀ Y₀ k).1 - β
      = ((pellOrbit D P Q X₀ Y₀ k).1 - X₀) + (X₀ - β) := by ring
  rw [e]
  exact dvd_add h1 h₀

/-- The extracted output is strictly increasing, because `X` is and the denominator is positive. -/
theorem pellOrbit_output_strictMono (D P Q X₀ Y₀ β : ℤ) (hD : 0 < D) (hP : 2 ≤ P) (hQ : 0 ≤ Q)
    (hX₀ : 0 < X₀) (hY₀ : 0 ≤ Y₀) (c : ℕ → ℤ)
    (hc : ∀ k, (pellOrbit D P Q X₀ Y₀ k).1 = 2 * D * c k + β) : StrictMono c := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  have hstep : (pellOrbit D P Q X₀ Y₀ k).1 < (pellOrbit D P Q X₀ Y₀ (k + 1)).1 :=
    pellOrbit_strictMono_fst D P Q X₀ Y₀ hD hP hQ hX₀ hY₀ (Nat.lt_succ_self k)
  rw [hc k, hc (k + 1)] at hstep
  nlinarith

/-- Packaged: with the hypotheses of the two lemmas above, the orbit yields an explicit strictly increasing
    integer output sequence `c` with `2D·c k + β = X k` — the affine-projection-with-denominator shape that
    `PellUnitOrbitRealization` requires (`pc = −β`, `px = 1`, `py = 0`, `denom = 2D`). -/
theorem pellOrbit_output (D P Q X₀ Y₀ β M : ℤ) (hD : 0 < D) (hP2 : 2 ≤ P) (hQ0 : 0 ≤ Q)
    (hX₀ : 0 < X₀) (hY₀ : 0 ≤ Y₀) (hM2D : 2 * D ∣ M) (hP : M ∣ P - 1) (hQ : M ∣ Q)
    (h₀ : 2 * D ∣ X₀ - β) :
    ∃ c : ℕ → ℤ, StrictMono c ∧ ∀ k, 2 * D * c k + β = (pellOrbit D P Q X₀ Y₀ k).1 := by
  choose c hc using fun k => pellOrbit_output_dvd D P Q X₀ Y₀ β M hM2D hP hQ h₀ k
  refine ⟨fun k => c k, ?_, fun k => by linarith [hc k]⟩
  refine pellOrbit_output_strictMono D P Q X₀ Y₀ β hD hP2 hQ0 hX₀ hY₀ (fun k => c k) (fun k => ?_)
  linarith [hc k]

end DiophCompression

#print axioms DiophCompression.pellOrbit_norm
#print axioms DiophCompression.pellOrbit_pos
#print axioms DiophCompression.pellOrbit_strictMono_fst
#print axioms DiophCompression.pellOrbit_congr
#print axioms DiophCompression.pellOrbit_unbounded_fst
#print axioms DiophCompression.pellOrbit_output_dvd
#print axioms DiophCompression.pellOrbit_output_strictMono
#print axioms DiophCompression.pellOrbit_output
#print axioms DiophCompression.pellOrbit_neg_snd
#print axioms DiophCompression.pellOrbit_strictMono_fst_neg
