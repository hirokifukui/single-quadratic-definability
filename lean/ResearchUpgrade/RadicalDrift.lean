/-
  RadicalDrift.lean — Gate-20 Packet 1, tasks T04 and T05.

  T04.  The integer radical-drift identity.  For `e` in the radical of the output/witness
  quadratic form, the two-parameter family

      z_t = z₀ + (d₀ t) • v − (t β_v + d₀ t² Q(v)) • e,
      d₀ = ℓ_a(e),   β_v = polar(z₀, v) + ℓ_a(v)

  consists of INTEGER points and satisfies `P(a, z_t) = P(a, z₀)` identically in `t` and `v`.
  No denominators, both signs of `t`, and `d₀ ≠ 0` is NOT needed for the identity (only later).

  T05.  Output uniqueness forces radical annihilation: `ℓ_a` and `π` both vanish on the radical.
  Witness uniqueness is never used — control #2.  The hypotheses that ARE used are named:
  `0 < m`, output uniqueness, the existence of one integer `v` with `Q(v) ≠ 0` (i.e. `Q ≠ 0`),
  and one integer solution at the input `a`.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import Mathlib
import ResearchUpgrade.GraphVocabulary

namespace DiophCompression.ResearchUpgrade

open Matrix

/-- Forget the outputs. -/
def witProj {m r : ℕ} (z : OutWit m r → ℤ) : Fin r → ℤ := fun j => z (Sum.inr j)

theorem elim_outProj_witProj {m r : ℕ} (z : OutWit m r → ℤ) :
    Sum.elim (outProj z) (witProj z) = z := by
  funext k; cases k <;> rfl

theorem outProj_add {m r : ℕ} (v w : OutWit m r → ℤ) :
    outProj (v + w) = outProj v + outProj w := rfl

theorem outProj_smul {m r : ℕ} (c : ℤ) (v : OutWit m r → ℤ) :
    outProj (c • v) = c • outProj v := rfl

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- The polar form of `zQuad`: `polar v w = Q(v+w) − Q(v) − Q(w)`, written out so that it is
manifestly integer-valued on the lattice. -/
def zPolar (v w : OutWit m r → ℤ) : ℤ :=
  ∑ k, ∑ k', (v k * (D.P.Q (Sum.inr k) (Sum.inr k') * w k')
              + w k * (D.P.Q (Sum.inr k) (Sum.inr k') * v k'))

/-- `ℓ_a(z)`, the linear part in the output/witness variables. -/
def zLinEval (a : Fin n → ℤ) (z : OutWit m r → ℤ) : ℤ := ∑ k, D.zLin a k * z k

/-- The equation, read at the level of `z = (b, u)`. -/
def SolZ (a : Fin n → ℤ) (z : OutWit m r → ℤ) : Prop := D.P.eval (Sum.elim a z) = 0

theorem evalZ (a : Fin n → ℤ) (z : OutWit m r → ℤ) :
    D.P.eval (Sum.elim a z) = D.zQuad z + D.zLinEval a z + D.aPart a := by
  have h := D.eval_split a (outProj z) (witProj z)
  rw [elim_outProj_witProj] at h
  simpa [pt, elim_outProj_witProj, zLinEval] using h

theorem solZ_iff_sol (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin r → ℤ) :
    D.SolZ a (Sum.elim b u) ↔ D.Sol a b u := Iff.rfl

theorem graph_of_solZ {a : Fin n → ℤ} {z : OutWit m r → ℤ} (h : D.SolZ a z) :
    D.Graph a (outProj z) := by
  refine ⟨witProj z, ?_⟩
  have : Sum.elim (outProj z) (witProj z) = z := elim_outProj_witProj z
  unfold QuadraticGraphData.Sol pt
  rw [this]
  exact h

/-! ### Bilinear algebra of `zQuad` / `zPolar` / `zLinEval` -/

theorem zQuad_add (v w : OutWit m r → ℤ) :
    D.zQuad (v + w) = D.zQuad v + D.zPolar v w + D.zQuad w := by
  simp only [zQuad, zPolar, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem zQuad_smul (c : ℤ) (v : OutWit m r → ℤ) : D.zQuad (c • v) = c ^ 2 * D.zQuad v := by
  simp only [zQuad, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  ring

theorem zPolar_symm (v w : OutWit m r → ℤ) : D.zPolar v w = D.zPolar w v := by
  simp only [zPolar]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  ring

theorem zPolar_add_left (v v' w : OutWit m r → ℤ) :
    D.zPolar (v + v') w = D.zPolar v w + D.zPolar v' w := by
  simp only [zPolar, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem zPolar_smul_left (c : ℤ) (v w : OutWit m r → ℤ) :
    D.zPolar (c • v) w = c * D.zPolar v w := by
  simp only [zPolar, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  ring

theorem zPolar_smul_right (c : ℤ) (v w : OutWit m r → ℤ) :
    D.zPolar v (c • w) = c * D.zPolar v w := by
  rw [zPolar_symm, zPolar_smul_left, zPolar_symm]

theorem zLinEval_add (a : Fin n → ℤ) (v w : OutWit m r → ℤ) :
    D.zLinEval a (v + w) = D.zLinEval a v + D.zLinEval a w := by
  simp only [zLinEval, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem zLinEval_smul (a : Fin n → ℤ) (c : ℤ) (v : OutWit m r → ℤ) :
    D.zLinEval a (c • v) = c * D.zLinEval a v := by
  simp only [zLinEval, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-! ### The radical -/

/-- `e` lies in the radical of the output/witness quadratic form. -/
def InRadical (e : OutWit m r → ℤ) : Prop := ∀ w, D.zPolar e w = 0

theorem zQuad_of_radical {e : OutWit m r → ℤ} (he : D.InRadical e) : D.zQuad e = 0 := by
  have h := he e
  have h2 : D.zPolar e e = 2 * D.zQuad e := by
    simp only [zPolar, zQuad, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun k' _ => ?_)
    ring
  omega

/-! ### T04 — the drift identity -/

/-- The drift point.  `d₀ = ℓ_a(e)`, `β = polar(z₀,v) + ℓ_a(v)`; all coefficients are integers. -/
def driftPt (a : Fin n → ℤ) (z₀ v e : OutWit m r → ℤ) (t : ℤ) : OutWit m r → ℤ :=
  z₀ + (D.zLinEval a e * t) • v
     - (t * (D.zPolar z₀ v + D.zLinEval a v) + D.zLinEval a e * t ^ 2 * D.zQuad v) • e

/-- Radical on the right as well (the polar form is symmetric). -/
theorem zPolar_right_radical {e : OutWit m r → ℤ} (he : D.InRadical e) (w : OutWit m r → ℤ) :
    D.zPolar w e = 0 := by rw [D.zPolar_symm]; exact he w

/-- **T04.**  `P(a, z_t) = P(a, z₀)` identically in `t` and `v`, for any radical `e`. -/
theorem eval_driftPt (a : Fin n → ℤ) (z₀ v e : OutWit m r → ℤ) (he : D.InRadical e) (t : ℤ) :
    D.P.eval (Sum.elim a (D.driftPt a z₀ v e t)) = D.P.eval (Sum.elim a z₀) := by
  have hrad := D.zPolar_right_radical he
  have hQe : D.zQuad e = 0 := D.zQuad_of_radical he
  have hsub : D.driftPt a z₀ v e t
      = (z₀ + (D.zLinEval a e * t) • v)
        + (-(t * (D.zPolar z₀ v + D.zLinEval a v)
              + D.zLinEval a e * t ^ 2 * D.zQuad v)) • e := by
    rw [driftPt, sub_eq_add_neg, neg_smul]
  rw [D.evalZ, D.evalZ, hsub]
  simp only [D.zQuad_add, D.zLinEval_add, D.zQuad_smul, D.zLinEval_smul,
    D.zPolar_add_left, D.zPolar_smul_left, D.zPolar_smul_right, hrad, he, hQe]
  ring

/-! ### T05 — output uniqueness annihilates the radical -/

/-- If `ℓ_a` already vanishes on a radical vector, translating a solution by it is again a
solution, so output uniqueness kills `π e`. -/
theorem outProj_radical_eq_zero {a : Fin n → ℤ} {z₀ e : OutWit m r → ℤ}
    (hOU : D.OutputUnique) (he : D.InRadical e) (hlin : D.zLinEval a e = 0)
    (hz : D.SolZ a z₀) : outProj e = 0 := by
  have hrad := D.zPolar_right_radical he
  have hQe : D.zQuad e = 0 := D.zQuad_of_radical he
  have hsol : D.SolZ a (z₀ + e) := by
    unfold QuadraticGraphData.SolZ at hz ⊢
    rw [D.evalZ] at hz ⊢
    rw [D.zQuad_add, D.zLinEval_add, hrad z₀, hQe, hlin]
    simpa using hz
  have heq := hOU a _ _ (D.graph_of_solZ hsol) (D.graph_of_solZ hz)
  rw [outProj_add] at heq
  funext i
  have hi := congrFun heq i
  simp only [Pi.add_apply, Pi.zero_apply] at hi ⊢
  linarith

/-- **T05.**  With `0 < m`, output uniqueness, one solution at `a`, and `Q ≠ 0` (witnessed by an
integer `v` with `Q(v) ≠ 0`), the linear form vanishes on the whole radical.  Witness uniqueness
is NOT used. -/
theorem zLinEval_radical_eq_zero {a : Fin n → ℤ} {z₀ e : OutWit m r → ℤ}
    (hm : 0 < m) (hOU : D.OutputUnique) (hz : D.SolZ a z₀) (he : D.InRadical e)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) : D.zLinEval a e = 0 := by
  classical
  by_contra hd
  -- every drift point has the same output as z₀
  have hdrift : ∀ (v : OutWit m r → ℤ) (t : ℤ) (i : Fin m),
      (D.zLinEval a e * t) * outProj v i
        = (t * (D.zPolar z₀ v + D.zLinEval a v)
            + D.zLinEval a e * t ^ 2 * D.zQuad v) * outProj e i := by
    intro v t i
    have hsol : D.SolZ a (D.driftPt a z₀ v e t) := by
      unfold QuadraticGraphData.SolZ
      rw [D.eval_driftPt a z₀ v e he t]; exact hz
    have heq := hOU a _ _ (D.graph_of_solZ hsol) (D.graph_of_solZ hz)
    have hi := congrFun heq i
    simp only [outProj, driftPt, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    linarith
  obtain ⟨v, hv⟩ := hQ
  have hcoef : (2 : ℤ) * D.zLinEval a e * D.zQuad v ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hd) hv
  have hpe : outProj e = 0 := by
    funext i
    have e1 := hdrift v 1 i
    have e2 := hdrift v (-1) i
    have hkey : ((2 : ℤ) * D.zLinEval a e * D.zQuad v) * outProj e i = 0 := by
      linear_combination -e1 - e2
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h hcoef
    · simpa using h
  -- with π e = 0 the drift at t = 1 gives d₀ · π w = 0 for EVERY w, so π is the zero map
  have hzero : ∀ (w : OutWit m r → ℤ) (i : Fin m), outProj w i = 0 := by
    intro w i
    have h1 := hdrift w 1 i
    rw [hpe] at h1
    simp only [Pi.zero_apply, mul_zero, mul_one] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hd
    · exact h
  obtain ⟨w, hw⟩ := outProj_surjective (m := m) (r := r) (fun _ => 1)
  have h0 := hzero w ⟨0, hm⟩
  rw [hw] at h0
  simp at h0

/-! ### Controls -/

/-- POSITIVE control (anchoring): the drift family passes through `z₀` at `t = 0`, so it really
is a deformation OF the given solution and not of some other point. -/
theorem driftPt_zero (a : Fin n → ℤ) (z₀ v e : OutWit m r → ℤ) :
    D.driftPt a z₀ v e 0 = z₀ := by
  simp [driftPt]

/-- POSITIVE control: `d₀ ≠ 0` is NOT needed for the identity — `eval_driftPt` holds for every
`a`, in particular when `ℓ_a(e) = 0`, where the family degenerates to `z₀ − (t·β) • e`. -/
theorem eval_driftPt_of_lin_zero (a : Fin n → ℤ) (z₀ v e : OutWit m r → ℤ)
    (he : D.InRadical e) (t : ℤ) (h0 : D.zLinEval a e = 0) :
    D.P.eval (Sum.elim a (D.driftPt a z₀ v e t)) = D.P.eval (Sum.elim a z₀) :=
  D.eval_driftPt a z₀ v e he t

end QuadraticGraphData

/-- NEGATIVE control for the `0 < m` hypothesis of T05 (reviewer control #6): when `m = 0` the
projection is identically zero, so the final step of T05 — contradicting surjectivity of `π` —
evaporates.  Together with `outputUnique_of_m_zero` (output uniqueness is FREE at `m = 0`) this
shows the hypothesis is load-bearing and not decoration. -/
theorem outProj_eq_zero_of_m_zero {r : ℕ} (z : OutWit 0 r → ℤ) : outProj z = 0 := by
  funext i
  exact i.elim0

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- The radical-annihilation package: both `ℓ_a` and `π` vanish on the radical. -/
theorem radical_annihilation {a : Fin n → ℤ} {z₀ e : OutWit m r → ℤ}
    (hm : 0 < m) (hOU : D.OutputUnique) (hz : D.SolZ a z₀) (he : D.InRadical e)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) :
    D.zLinEval a e = 0 ∧ outProj e = 0 := by
  have h1 := D.zLinEval_radical_eq_zero hm hOU hz he hQ
  exact ⟨h1, D.outProj_radical_eq_zero hOU he h1 hz⟩

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
