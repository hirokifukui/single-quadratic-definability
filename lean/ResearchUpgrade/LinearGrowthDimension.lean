/-
  LinearGrowthDimension.lean — Gate-20 Packet 2, task T09.

  Linear output growth + injectivity ⇒ `n ≤ m`, by counting integer boxes.  This is the
  exponent-1 counting the reviewer asks to be made explicit: the input box `{‖a‖∞ ≤ N}` has
  `(2N+1)^n` points and lands inside an output box with `(2C(1+N)+1)^m` points, so

      (1+N)^(m+1) ≤ (2N+1)^n ≤ ((2C+1)(1+N))^m = (2C+1)^m (1+N)^m

  and `N = (2C+1)^m` is already a contradiction.  No limits, no asymptotics: ONE value of `N`.

  This is NOT the existing `n ≤ 2m` theorem under a new name (reviewer's T09 pass condition):
  the hypothesis here is a linear bound on the OUTPUT sup-norm, and the conclusion is the sharp
  `n ≤ m`.  Nothing about normal forms, cosets or sections is used.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import ResearchUpgrade.GraphVocabulary

namespace DiophCompression.ResearchUpgrade

/-- Sup-norm of an integer vector, for any finite index type (the output/witness index is a
sum type, not a `Fin`, so this must be general). -/
def supNorm {ι : Type*} [Fintype ι] (a : ι → ℤ) : ℕ := Finset.univ.sup fun i => (a i).natAbs

/-- Each coordinate is bounded by the sup-norm. -/
theorem abs_le_supNorm {ι : Type*} [Fintype ι] (z : ι → ℤ) (k : ι) :
    |z k| ≤ (supNorm z : ℤ) := by
  have h : (z k).natAbs ≤ supNorm z :=
    Finset.le_sup (f := fun i => (z i).natAbs) (Finset.mem_univ k)
  have hc : |z k| = ((z k).natAbs : ℤ) := by
    first
      | exact Int.abs_eq_natAbs _
      | exact (Int.natCast_natAbs _).symm
      | simp
  rw [hc]
  exact_mod_cast h

theorem supNorm_eq_zero {ι : Type*} [Fintype ι] {z : ι → ℤ} (h : supNorm z = 0) : z = 0 := by
  funext k
  have := abs_le_supNorm z k
  rw [h] at this
  simpa using this

/-- The sup-norm bound for a dot product. -/
theorem abs_dot_le {ι : Type*} [Fintype ι] (c z : ι → ℤ) :
    |∑ k, c k * z k| ≤ (∑ k, |c k|) * (supNorm z : ℤ) := by
  calc |∑ k, c k * z k| ≤ ∑ k, |c k * z k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |c k| * |z k| := by simp [abs_mul]
    _ ≤ ∑ k, |c k| * (supNorm z : ℤ) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (abs_le_supNorm z k) (abs_nonneg _)
    _ = (∑ k, |c k|) * (supNorm z : ℤ) := by rw [Finset.sum_mul]

/-- `f` has linearly bounded output: one constant `C` for all inputs. -/
def LinearGrowth {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop :=
  ∃ C : ℕ, ∀ a, supNorm (f a) ≤ C * (1 + supNorm a)

/-- The integer box `{x : ‖x‖∞ ≤ N}`. -/
noncomputable def box (k N : ℕ) : Finset (Fin k → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem mem_box {k N : ℕ} (a : Fin k → ℤ) : a ∈ box k N ↔ supNorm a ≤ N := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, supNorm, Finset.sup_le_iff,
    Finset.mem_univ, true_implies]
  constructor
  · intro h i; have := h i; omega
  · intro h i; have := h i; omega

theorem card_box (k N : ℕ) : (box k N).card = (2 * N + 1) ^ k := by
  rw [box, Fintype.card_piFinset]
  have h : ∀ i : Fin k, (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    intro _; rw [Int.card_Icc]; omega
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The counting inequality: exponent `n` on the left, exponent `m` on the right. -/
theorem box_card_le {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} {C : ℕ}
    (hC : ∀ a, supNorm (f a) ≤ C * (1 + supNorm a)) (hinj : Function.Injective f) (N : ℕ) :
    (2 * N + 1) ^ n ≤ (2 * (C * (1 + N)) + 1) ^ m := by
  have hmaps : Set.MapsTo f (box n N) (box m (C * (1 + N))) := by
    intro a ha
    have ha' : supNorm a ≤ N := (mem_box a).1 ha
    have : supNorm (f a) ≤ C * (1 + N) :=
      le_trans (hC a) (Nat.mul_le_mul_left C (by omega))
    exact (mem_box (f a)).2 this
  have hinjOn : Set.InjOn f (box n N) := fun x _ y _ h => hinj h
  have h := Finset.card_le_card_of_injOn f hmaps hinjOn
  rwa [card_box, card_box] at h

/-- **T09.**  A linearly bounded injective map `ℤⁿ → ℤᵐ` forces `n ≤ m`. -/
theorem dim_le_of_linearGrowth_injective {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hgrow : LinearGrowth f) (hinj : Function.Injective f) : n ≤ m := by
  obtain ⟨C, hC⟩ := hgrow
  by_contra hnm
  push_neg at hnm
  set N : ℕ := (2 * C + 1) ^ m with hNdef
  have h1 := box_card_le hC hinj N
  have hA : (1 + N) ^ (m + 1) ≤ (2 * N + 1) ^ n :=
    le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.pow_le_pow_left (by omega) n)
  have hstep : 2 * (C * (1 + N)) + 1 ≤ (2 * C + 1) * (1 + N) := by
    have heq : (2 * C + 1) * (1 + N) = 2 * (C * (1 + N)) + (1 + N) := by ring
    rw [heq]
    exact Nat.add_le_add_left (by omega) _
  have hB : (2 * (C * (1 + N)) + 1) ^ m ≤ (1 + N) ^ m * (2 * C + 1) ^ m := by
    calc (2 * (C * (1 + N)) + 1) ^ m ≤ ((2 * C + 1) * (1 + N)) ^ m := Nat.pow_le_pow_left hstep m
      _ = (2 * C + 1) ^ m * (1 + N) ^ m := by rw [mul_pow]
      _ = (1 + N) ^ m * (2 * C + 1) ^ m := by ring
  have hchain : (1 + N) ^ m * (1 + N) ≤ (1 + N) ^ m * (2 * C + 1) ^ m := by
    calc (1 + N) ^ m * (1 + N) = (1 + N) ^ (m + 1) := by rw [pow_succ]
      _ ≤ (2 * N + 1) ^ n := hA
      _ ≤ (2 * (C * (1 + N)) + 1) ^ m := h1
      _ ≤ (1 + N) ^ m * (2 * C + 1) ^ m := hB
  have hpos : 0 < (1 + N) ^ m := pow_pos (by omega) m
  have hfinal : 1 + N ≤ (2 * C + 1) ^ m := Nat.le_of_mul_le_mul_left hchain hpos
  omega

/-! ### Controls -/

/-- POSITIVE control: the identity is linearly bounded and injective, so the hypotheses of T09
are satisfiable and the conclusion is not vacuous. -/
theorem linearGrowth_id {n : ℕ} : LinearGrowth (id : (Fin n → ℤ) → (Fin n → ℤ)) :=
  ⟨1, fun a => by simp⟩

/-- NEGATIVE control: squaring has NO linear bound, so `LinearGrowth` is a real restriction and
not a hypothesis that every definable function satisfies. -/
theorem not_linearGrowth_sq : ¬ LinearGrowth (fun a : Fin 1 → ℤ => ![a 0 ^ 2]) := by
  rintro ⟨C, hC⟩
  have h := hC (fun _ => ((C : ℤ) + 1))
  have hl : supNorm ((fun a : Fin 1 → ℤ => ![a 0 ^ 2]) (fun _ => ((C : ℤ) + 1)))
      = (C + 1) ^ 2 := by
    simp only [supNorm, Finset.univ_unique, Finset.sup_singleton, Matrix.cons_val_fin_one,
      Int.natAbs_pow]
    congr 1
  have hr : supNorm (fun _ : Fin 1 => ((C : ℤ) + 1)) = C + 1 := by
    simp only [supNorm, Finset.univ_unique, Finset.sup_singleton]
    omega
  rw [hl, hr] at h
  nlinarith [h]

end DiophCompression.ResearchUpgrade
