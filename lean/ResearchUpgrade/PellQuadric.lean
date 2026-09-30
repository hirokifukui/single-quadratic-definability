/-
  PellQuadric.lean — s48.  Gate22 **G22-T15**, the arithmetic core of reviewer §6.2.

  On an ORTHOGONAL plane the form is diagonal, `Q(αv + βw) = α²Q(v) + β²Q(w)`.  Put
  `A = L²Q(v)`, `C = L²Q(w)`, `d = −AC`.  Then for any Pell solution `T² − dS² = 1` the point

      p(T,S) = T·v + (A·S)·w

  satisfies `Q(p) = Q(v)` — it lies on the SAME quadric as the off-centre vector, so it defines
  another solution at the same input.  The computation is one line once the plane is diagonal:

      Q(p) = T²Q(v) + A²S²Q(w) = Q(v)·(T² + A·C·S²) = Q(v)·(T² − dS²) = Q(v).

  Squaring the Pell unit gives a SECOND such point, `(2T²−1, 2TS)`, and the two output relations
  those points produce have coefficient determinant `2S(1−T) ≠ 0`.  `pell_two_step_obstruction`
  (T17, held) does that over `ℤ`; the output coordinates here are rational, so the same
  determinant argument is transcribed over `ℚ`.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import Mathlib.Tactic.LinearCombination
import ResearchUpgrade.GraphVocabulary
import ResearchUpgrade.PellNonsquare
import ResearchUpgrade.PolarAnnihilator

namespace DiophCompression.ResearchUpgrade

/-- **T17 over `ℚ`.**  The two-step obstruction, transcribed for rational output coordinates.
The determinant `2S₁(1 − T₁)` is non-zero for any `T₁ > 1`, `S₁ > 0`, so both vectors vanish. -/
theorem pell_two_step_obstruction_rat {ι : Type*} {T₁ S₁ : ℚ} (hT : 1 < T₁) (hS : 0 < S₁)
    {U V : ι → ℚ}
    (h1 : ∀ i, (T₁ - 1) * U i + S₁ * V i = 0)
    (h2 : ∀ i, (2 * T₁ ^ 2 - 1 - 1) * U i + (2 * T₁ * S₁) * V i = 0) :
    (∀ i, U i = 0) ∧ (∀ i, V i = 0) := by
  have hdet : 2 * S₁ * (1 - T₁) ≠ 0 := by
    have hp : 0 < S₁ * (T₁ - 1) := mul_pos hS (by linarith)
    have hneg : 2 * S₁ * (1 - T₁) < 0 := by nlinarith
    exact ne_of_lt hneg
  have hU : ∀ i, U i = 0 := by
    intro i
    have e1 := h1 i
    have e2 := h2 i
    have hz : (2 * S₁ * (1 - T₁)) * U i = 0 := by
      linear_combination (2 * T₁ * S₁) * e1 - S₁ * e2
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h hdet
    · exact h
  refine ⟨hU, fun i => ?_⟩
  have e1 := h1 i
  rw [hU i, mul_zero, zero_add] at e1
  rcases mul_eq_zero.mp e1 with h | h
  · exact absurd h (ne_of_gt hS)
  · exact h

/-- The Pell unit squared is again a Pell unit, and stays in the positive cone. -/
theorem pell_square_rat {d T S : ℚ} (hpell : T ^ 2 - d * S ^ 2 = 1) (hT : 1 < T) (hS : 0 < S) :
    (2 * T ^ 2 - 1) ^ 2 - d * (2 * T * S) ^ 2 = 1 ∧ 1 < 2 * T ^ 2 - 1 ∧ 0 < 2 * T * S := by
  refine ⟨by linear_combination (4 * T ^ 2) * hpell, by nlinarith, by positivity⟩

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- On an orthogonal plane the form is diagonal. -/
theorem zQuadQ_plane {v w : OutWit m r → ℚ} (hperp : D.zPolarQ v w = 0) (α β : ℚ) :
    D.zQuadQ (α • v + β • w) = α ^ 2 * D.zQuadQ v + β ^ 2 * D.zQuadQ w := by
  rw [D.zQuadQ_add, D.zQuadQ_smul, D.zQuadQ_smul, D.zPolarQ_smul_left, D.zPolarQ_smul_right,
    hperp]
  ring

/-- **G22-T15, the quadric step.**  The Pell point `T·v + (A·S)·w` lies on the same quadric as
`v`.  `A = L²·Q(v)` and `C = L²·Q(w)` are the integral-plane invariants; `d = −A·C`. -/
theorem zQuadQ_pell_point {v w : OutWit m r → ℚ} (hperp : D.zPolarQ v w = 0)
    {L A C T S : ℚ} (hL : L ≠ 0)
    (hA : A = L ^ 2 * D.zQuadQ v) (hC : C = L ^ 2 * D.zQuadQ w)
    (hpell : T ^ 2 - (-(A * C)) * S ^ 2 = 1) :
    D.zQuadQ (T • v + (A * S) • w) = D.zQuadQ v := by
  rw [D.zQuadQ_plane hperp]
  have hQw : D.zQuadQ w = C / L ^ 2 := by
    rw [hC]; field_simp
  have hQv : D.zQuadQ v = A / L ^ 2 := by
    rw [hA]; field_simp
  rw [hQw]
  have hkey : A ^ 2 * S ^ 2 * (C / L ^ 2) = D.zQuadQ v * (A * C * S ^ 2) := by
    rw [hQv]; field_simp
  calc T ^ 2 * D.zQuadQ v + (A * S) ^ 2 * (C / L ^ 2)
      = T ^ 2 * D.zQuadQ v + A ^ 2 * S ^ 2 * (C / L ^ 2) := by ring
    _ = D.zQuadQ v * (T ^ 2 + A * C * S ^ 2) := by rw [hkey]; ring
    _ = D.zQuadQ v * 1 := by rw [show T ^ 2 + A * C * S ^ 2 = 1 from by linarith [hpell]]
    _ = D.zQuadQ v := by ring

/-- The displacement of the Pell point from `v` itself — the vector that must be integral for the
new point to be an integer solution. -/
theorem pell_point_sub {v w : OutWit m r → ℚ} (A S T : ℚ) :
    (T • v + (A * S) • w) - v = (T - 1) • v + (A * S) • w := by
  funext k
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **G22-T15, the obstruction step.**  If the outputs at the base point and at the two Pell
points agree, both `v` and `w` are invisible to the output. -/
theorem pell_invisible {v w : OutWit m r → ℚ} {A T S : ℚ} (hA : A ≠ 0)
    (hT : 1 < T) (hS : 0 < S)
    (h1 : ∀ j : Fin m, ((T - 1) • v + (A * S) • w) (Sum.inl j) = 0)
    (h2 : ∀ j : Fin m,
      ((2 * T ^ 2 - 1 - 1) • v + (A * (2 * T * S)) • w) (Sum.inl j) = 0) :
    (∀ j, v (Sum.inl j) = 0) ∧ (∀ j, w (Sum.inl j) = 0) := by
  obtain ⟨hU, hV⟩ := pell_two_step_obstruction_rat (U := fun j : Fin m => v (Sum.inl j))
    (V := fun j : Fin m => A * w (Sum.inl j)) hT hS
    (fun j => by
      have := h1 j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      linarith [this])
    (fun j => by
      have := h2 j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      linarith [this])
  refine ⟨hU, fun j => ?_⟩
  rcases mul_eq_zero.mp (hV j) with h | h
  · exact absurd h hA
  · exact h

/-! ### Controls -/

/-- POSITIVE control: the Pell point is a genuine second point — at `T = 1, S = 0` it is `v`
itself, and any `T > 1` moves it, while the quadric value is unchanged either way. -/
theorem zQuadQ_pell_point_trivial (v w : OutWit m r → ℚ)
    (A : ℚ) : (1 : ℚ) • v + (A * 0) • w = v := by
  funext k
  simp

/-- NEGATIVE control: the Pell relation is load-bearing.  Without `T² − dS² = 1` the point leaves
the quadric by exactly `Q(v)·(T² + A·C·S² − 1)`, so an arbitrary `(T,S)` does NOT give another
solution. -/
theorem zQuadQ_pell_point_defect {v w : OutWit m r → ℚ} (hperp : D.zPolarQ v w = 0)
    {L A C T S : ℚ} (hL : L ≠ 0)
    (hA : A = L ^ 2 * D.zQuadQ v) (hC : C = L ^ 2 * D.zQuadQ w) :
    D.zQuadQ (T • v + (A * S) • w) - D.zQuadQ v
      = D.zQuadQ v * (T ^ 2 + A * C * S ^ 2 - 1) := by
  rw [D.zQuadQ_plane hperp]
  have hQw : D.zQuadQ w = C / L ^ 2 := by rw [hC]; field_simp
  have hQv : D.zQuadQ v = A / L ^ 2 := by rw [hA]; field_simp
  rw [hQw]
  have hkey : (A * S) ^ 2 * (C / L ^ 2) = D.zQuadQ v * (A * C * S ^ 2) := by
    rw [hQv]; field_simp
  rw [hkey]
  ring

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
