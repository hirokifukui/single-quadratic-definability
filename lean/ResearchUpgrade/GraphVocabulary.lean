/-
  GraphVocabulary.lean — Gate-20 Packet 0, tasks T01 and T02.

  T01.  The general `(n, m, r)` vocabulary: one integer polynomial of TOTAL degree ≤ 2 in
  `n` inputs, `m` outputs and `r` witnesses, together with totality, output functionality,
  witness uniqueness (kept SEPARATE — 実行規約 4) and the output projection.  `n`, `m`, `r`
  are arbitrary; `m = 0` and `n = 0` are inside the type, not excluded by it.

  T02.  The fixed-quadratic-part compiler: `P(a,z) = Q(z) + ℓ_a(z) + q(a)` with `z = (b,u)`,
  where `Q` does NOT depend on `a`, the coefficients of `ℓ_a` are AFFINE in `a`, and `q` has
  degree ≤ 2 in `a`.  At total degree ≤ 2 this is forced; the reviewer's pass condition is that
  a control mixing `aᵢ yⱼ²` be rejected, which is `not_representable_input_times_output_sq`.

  Design notes (why the types are what they are):
  * variables are indexed by `Fin n ⊕ (Fin m ⊕ Fin r)`, not by `Fin (n+m+r)`: the split into
    input / output / witness is then definitional, and no `Fin` arithmetic appears in any proof.
  * `Q` is an arbitrary (not necessarily symmetric) matrix.  `x ⬝ᵥ (Q *ᵥ x)` already ranges over
    every quadratic form, and symmetrising is a choice a later packet can make, not a constraint
    the vocabulary should impose.
  * coefficients are in ℤ, and `2B(v,w) = Q(v+w) − Q(v) − Q(w)` is therefore integer-valued on
    the lattice for free — the hypothesis the radical-drift argument (Packet 1) silently needs.

  Claim tags: all theorems [P] (std-3).  Baseline read-only.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.Star
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Notation
import Mathlib.LinearAlgebra.Matrix.Defs
import ResearchUpgrade.CosetNormalForm

namespace DiophCompression.ResearchUpgrade

open Matrix

/-- Output-and-witness variables. -/
abbrev OutWit (m r : ℕ) := Fin m ⊕ Fin r
/-- All variables of an SE₂ graph: `n` inputs, `m` outputs, `r` witnesses. -/
abbrev Vars (n m r : ℕ) := Fin n ⊕ OutWit m r

/-- An integer polynomial of total degree ≤ 2 in the variables `ι`, written explicitly as
`c + l·x + xᵀ Q x`. -/
structure IntQuad (ι : Type*) [Fintype ι] where
  c : ℤ
  l : ι → ℤ
  Q : Matrix ι ι ℤ

namespace IntQuad

variable {ι : Type*} [Fintype ι]

def eval (P : IntQuad ι) (x : ι → ℤ) : ℤ := P.c + P.l ⬝ᵥ x + x ⬝ᵥ (P.Q *ᵥ x)

end IntQuad

/-- **T01.**  The data of an SE₂-definable graph in `n` inputs, `m` outputs, `r` witnesses. -/
structure QuadraticGraphData (n m r : ℕ) where
  P : IntQuad (Vars n m r)

/-- The evaluation point assembled from input, output and witness blocks. -/
def pt {n m r : ℕ} (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin r → ℤ) : Vars n m r → ℤ :=
  Sum.elim a (Sum.elim b u)

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- `(a, b, u)` solves the equation. -/
def Sol (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin r → ℤ) : Prop := D.P.eval (pt a b u) = 0

/-- The relation defined existentially over the witnesses. -/
def Graph (a : Fin n → ℤ) (b : Fin m → ℤ) : Prop := ∃ u, D.Sol a b u

/-- Every input has at least one output. -/
def Total : Prop := ∀ a, ∃ b, D.Graph a b

/-- At most one output per input — the WHOLE `m`-vector, not one coordinate. -/
def OutputUnique : Prop := ∀ a b b', D.Graph a b → D.Graph a b' → b = b'

/-- At most one witness per (input, output).  Deliberately separate from `OutputUnique`:
control #2 says unique output gives neither unique witness nor finiteness. -/
def WitnessUnique : Prop := ∀ a b u u', D.Sol a b u → D.Sol a b u' → u = u'

/-- `D` defines the function `f`. -/
def Defines (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop := ∀ a b, D.Graph a b ↔ b = f a

end QuadraticGraphData

/-! ### The output projection π, and that it is surjective (not a hypothesis) -/

/-- `π` : forget the witnesses. -/
def outProj {m r : ℕ} (z : OutWit m r → ℤ) : Fin m → ℤ := fun i => z (Sum.inl i)

theorem outProj_surjective {m r : ℕ} : Function.Surjective (outProj (m := m) (r := r)) := by
  intro b
  exact ⟨Sum.elim b 0, rfl⟩

theorem outProj_pt {m r : ℕ} (b : Fin m → ℤ) (u : Fin r → ℤ) :
    outProj (Sum.elim b u) = b := rfl

/-! ### Totality + output uniqueness is exactly functionhood -/

theorem QuadraticGraphData.exists_defines_iff {n m r : ℕ} (D : QuadraticGraphData n m r) :
    (∃ f, D.Defines f) ↔ D.Total ∧ D.OutputUnique := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun a => ⟨f a, (hf a (f a)).2 rfl⟩, fun a b b' hb hb' => ?_⟩
    rw [(hf a b).1 hb, (hf a b').1 hb']
  · rintro ⟨htot, huniq⟩
    classical
    refine ⟨fun a => (htot a).choose, fun a b => ⟨fun hb => huniq a b _ hb (htot a).choose_spec,
      fun hb => ?_⟩⟩
    rw [hb]; exact (htot a).choose_spec

/-! ### The boundaries `m = 0` and `n = 0` are inside the type -/

/-- `m = 0`: the empty output tuple is unique, whatever the equation says. -/
theorem outputUnique_of_m_zero {n r : ℕ} (D : QuadraticGraphData n 0 r) : D.OutputUnique := by
  intro a b b' _ _
  funext i
  exact i.elim0

/-- `n = 0`: there is only one input, so any total graph with unique output defines a function
on a one-point domain.  (Recorded so the boundary is a theorem, not an assumption.) -/
theorem subsingleton_input_of_n_zero : Subsingleton (Fin 0 → ℤ) :=
  ⟨fun x y => funext fun i => i.elim0⟩

/-! ### Bridge to the scalar root (`m = 1`) -/

/-- The scalar reading of a one-output function. -/
def scalarOut {n : ℕ} (f : (Fin n → ℤ) → (Fin 1 → ℤ)) : (Fin n → ℤ) → ℤ := fun a => f a 0

theorem weakScalarCosetNF_of_weakVector {n : ℕ} {f : (Fin n → ℤ) → (Fin 1 → ℤ)}
    (h : WeakVectorCosetNF f) : WeakScalarCosetNF (scalarOut f) := by
  obtain ⟨M, ρ, q, hM, hq⟩ := h
  exact ⟨M, ρ, q 0, hM, fun t => hq t 0⟩

/-! ### T02 — the fixed-quadratic-part compiler -/

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- The quadratic part in the output/witness variables.  It does NOT mention `a`. -/
def zQuad (z : OutWit m r → ℤ) : ℤ :=
  ∑ k, ∑ k', z k * (D.P.Q (Sum.inr k) (Sum.inr k') * z k')

/-- The coefficient of `z k` in the linear part.  AFFINE in `a`. -/
def zLin (a : Fin n → ℤ) (k : OutWit m r) : ℤ :=
  D.P.l (Sum.inr k) + ∑ i, a i * (D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i))

/-- The part depending on `a` only.  Degree ≤ 2 in `a`. -/
def aPart (a : Fin n → ℤ) : ℤ :=
  D.P.c + (∑ i, D.P.l (Sum.inl i) * a i) + ∑ i, ∑ j, a i * (D.P.Q (Sum.inl i) (Sum.inl j) * a j)

/-- **T02.**  `P(a,z) = Q(z) + ℓ_a(z) + q(a)`, with `Q` independent of `a`. -/
theorem eval_split (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin r → ℤ) :
    D.P.eval (pt a b u)
      = D.zQuad (Sum.elim b u) + (∑ k, D.zLin a k * (Sum.elim b u) k) + D.aPart a := by
  classical
  set z : OutWit m r → ℤ := Sum.elim b u with hz
  have hpt : pt a b u = Sum.elim a z := rfl
  have hinner : ∀ x : Vars n m r,
      ∑ y, D.P.Q x y * (Sum.elim a z) y
        = (∑ j, D.P.Q x (Sum.inl j) * a j) + (∑ k, D.P.Q x (Sum.inr k) * z k) := by
    intro x; rw [Fintype.sum_sum_type]; simp
  have hlin : D.P.l ⬝ᵥ (Sum.elim a z)
      = (∑ i, D.P.l (Sum.inl i) * a i) + (∑ k, D.P.l (Sum.inr k) * z k) := by
    simp only [dotProduct]; rw [Fintype.sum_sum_type]; simp
  have hquad : (Sum.elim a z) ⬝ᵥ (D.P.Q *ᵥ (Sum.elim a z))
      = (∑ i, ∑ j, a i * (D.P.Q (Sum.inl i) (Sum.inl j) * a j))
        + (∑ i, ∑ k, a i * (D.P.Q (Sum.inl i) (Sum.inr k) * z k))
        + (∑ k, ∑ j, z k * (D.P.Q (Sum.inr k) (Sum.inl j) * a j))
        + (∑ k, ∑ k', z k * (D.P.Q (Sum.inr k) (Sum.inr k') * z k')) := by
    simp only [dotProduct, Matrix.mulVec]
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, hinner, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    ring
  have hswap : (∑ k, ∑ j, z k * (D.P.Q (Sum.inr k) (Sum.inl j) * a j))
      = ∑ k, (∑ i, a i * D.P.Q (Sum.inr k) (Sum.inl i)) * z k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hcross : (∑ i, ∑ k, a i * (D.P.Q (Sum.inl i) (Sum.inr k) * z k))
      = ∑ k, (∑ i, a i * D.P.Q (Sum.inl i) (Sum.inr k)) * z k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hzl : (∑ k, D.zLin a k * z k)
      = (∑ k, D.P.l (Sum.inr k) * z k)
        + (∑ k, (∑ i, a i * D.P.Q (Sum.inl i) (Sum.inr k)) * z k)
        + (∑ k, (∑ i, a i * D.P.Q (Sum.inr k) (Sum.inl i)) * z k) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [zLin, mul_add, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    ring
  simp only [IntQuad.eval, hpt, hlin, hquad, zQuad, aPart, hzl, hcross, hswap]
  ring

end QuadraticGraphData

/-! ### Control: a degree-3 mixed term is NOT representable -/

/-- NEGATIVE control for T02 (the reviewer's pass condition): `a · b²` mixes an input with the
square of an output and has TOTAL degree 3, so no `IntQuad` evaluates to it.  This is what
forbids `aᵢ yⱼ²` and `aᵢ yⱼ u_k` from the vocabulary — total degree, not per-variable degree. -/
theorem not_representable_input_times_output_sq :
    ¬ ∃ P : IntQuad (Vars 1 1 0),
        ∀ (a : Fin 1 → ℤ) (b : Fin 1 → ℤ),
          P.eval (pt a b ![]) = a 0 * (b 0) ^ 2 := by
  rintro ⟨P, hP⟩
  have e00 := hP ![0] ![0]
  have e01 := hP ![0] ![1]
  have e02 := hP ![0] ![2]
  have e10 := hP ![1] ![0]
  have e11 := hP ![1] ![1]
  have e12 := hP ![1] ![2]
  simp [IntQuad.eval, pt, dotProduct, Matrix.mulVec, Fin.sum_univ_one,
    Fintype.sum_sum_type] at e00 e01 e02 e10 e11 e12
  linarith [e00, e01, e02, e10, e11, e12]

end DiophCompression.ResearchUpgrade
