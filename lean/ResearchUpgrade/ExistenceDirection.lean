/-
  ExistenceDirection.lean — Gate-20 Packet 6, task T21 (boundaries and the existence direction).

  The reviewer's T21 asks for: `n = 0`, `m = 0`, the non-existence at `m = 0 < n`, and the
  `n ≤ m` sum-of-squares graph, all realised by ONE quadratic equation.  What is proved here:
  the `m = 0 < n` non-existence, and the `n = m` identity graph — one equation
  `∑ᵢ (bᵢ − aᵢ)² = 0`, no witnesses, total and output-unique, defining an injective function.
  The `n < m` zero-padded embedding is the same construction composed with an index injection and
  is NOT done (it needs the pullback along `Fin n ↪ Fin m`); it is recorded in the report.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Int.Defs
import ResearchUpgrade.GraphVocabulary

namespace DiophCompression.ResearchUpgrade

open Matrix

/-- **T21, the `m = 0 < n` boundary.**  With no outputs there is no injective total function. -/
theorem not_injective_of_m_zero {n : ℕ} (hn : 0 < n) (f : (Fin n → ℤ) → (Fin 0 → ℤ)) :
    ¬ Function.Injective f := by
  intro hinj
  have h0 : f (fun _ => (0 : ℤ)) = f (fun _ => (1 : ℤ)) := by
    funext i; exact i.elim0
  have h1 := hinj h0
  have h2 := congrFun h1 ⟨0, hn⟩
  simp at h2

/-- The identity graph: `∑ᵢ (bᵢ − aᵢ)² = 0`, no witnesses. -/
def idGraph (n : ℕ) : QuadraticGraphData n n 0 where
  P :=
    { c := 0
      l := fun _ => 0
      Q := fun x y =>
        match x, y with
        | Sum.inl i, Sum.inl i' => if i = i' then 1 else 0
        | Sum.inr (Sum.inl j), Sum.inr (Sum.inl j') => if j = j' then 1 else 0
        | Sum.inl i, Sum.inr (Sum.inl j) => if i = j then -1 else 0
        | Sum.inr (Sum.inl j), Sum.inl i => if i = j then -1 else 0
        | _, _ => 0 }

theorem idGraph_eval (n : ℕ) (a b : Fin n → ℤ) (u : Fin 0 → ℤ) :
    (idGraph n).P.eval (pt a b u) = ∑ i, (b i - a i) ^ 2 := by
  have hinner : ∀ x : Vars n n 0,
      (∑ y, (idGraph n).P.Q x y * (pt a b u) y)
        = (match x with
           | Sum.inl i => a i - b i
           | Sum.inr (Sum.inl j) => b j - a j
           | Sum.inr (Sum.inr j) => j.elim0) := by
    intro x
    cases x with
    | inl i =>
        rw [Fintype.sum_sum_type]
        rw [Fintype.sum_sum_type]
        simp [idGraph, pt]
        ring
    | inr x' =>
        cases x' with
        | inl j =>
            rw [Fintype.sum_sum_type]
            rw [Fintype.sum_sum_type]
            simp [idGraph, pt, Finset.sum_ite_eq, Finset.sum_ite_eq']
            ring
        | inr j => exact j.elim0
  simp only [IntQuad.eval, dotProduct, Matrix.mulVec, hinner]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [idGraph, pt]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem idGraph_defines (n : ℕ) : (idGraph n).Defines (id : (Fin n → ℤ) → (Fin n → ℤ)) := by
  intro a b
  constructor
  · rintro ⟨u, hu⟩
    have h := hu
    unfold QuadraticGraphData.Sol at h
    rw [idGraph_eval] at h
    have hz : ∀ i ∈ (Finset.univ : Finset (Fin n)), (b i - a i) ^ 2 = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 h
    funext i
    have := hz i (Finset.mem_univ i)
    have : b i - a i = 0 := by
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    simp [id]
    omega
  · rintro rfl
    refine ⟨fun i => i.elim0, ?_⟩
    unfold QuadraticGraphData.Sol
    rw [idGraph_eval]
    simp [id]

/-- **T21, existence at `n = m`.**  One quadratic equation with NO witnesses realises an injective
total function `ℤⁿ → ℤⁿ`. -/
theorem exists_graph_injective (n : ℕ) :
    ∃ (D : QuadraticGraphData n n 0) (f : (Fin n → ℤ) → (Fin n → ℤ)),
      D.Defines f ∧ Function.Injective f :=
  ⟨idGraph n, id, idGraph_defines n, Function.injective_id⟩

end DiophCompression.ResearchUpgrade
