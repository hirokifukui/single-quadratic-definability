/-
  PadGraph.lean — s48.  **G22-T18**: the `n < m` zero-padded graph.

  `idGraph` (T21) realises the bound `n ≤ m` only at `n = m`.  T18 asks for the whole range: for
  every `n ≤ m` there is a single quadratic equation, with NO witnesses, defining an injective
  total function `ℤⁿ → ℤᵐ`.  The construction pads with zeros:

      P = ∑_{j : Fin (n+k)} (b j − pad(a) j)² ,   pad(a) = a on the first block, 0 on the rest.

  `m` is written `n + k` so that `Fin.addCases` and `Fin.sum_univ_add` do the index bookkeeping;
  that is the same device as `pairVec` in `FidelityBridge.lean`.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import Lean.Parser.Command
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Notation
import ResearchUpgrade.GraphVocabulary

namespace DiophCompression.ResearchUpgrade

open Matrix

variable {n k : ℕ}

/-- The padded input: `a` on the first `n` coordinates, `0` on the last `k`. -/
def padF (a : Fin n → ℤ) : Fin (n + k) → ℤ :=
  Fin.addCases a (fun _ => 0)

@[simp] theorem padF_left (a : Fin n → ℤ) (i : Fin n) :
    padF (k := k) a (Fin.castAdd k i) = a i := by simp [padF]

@[simp] theorem padF_right (a : Fin n → ℤ) (j : Fin k) :
    padF (k := k) a (Fin.natAdd n j) = 0 := by simp [padF]

theorem padF_injective : Function.Injective (padF (n := n) (k := k)) := by
  intro a a' h
  funext i
  have := congrFun h (Fin.castAdd k i)
  simpa using this

/-- The zero-padded graph: `∑ⱼ (bⱼ − pad(a)ⱼ)² = 0`, no witnesses. -/
def padGraph (n k : ℕ) : QuadraticGraphData n (n + k) 0 where
  P :=
    { c := 0
      l := fun _ => 0
      Q := fun x y =>
        match x, y with
        | Sum.inl i, Sum.inl i' => if i = i' then 1 else 0
        | Sum.inr (Sum.inl j), Sum.inr (Sum.inl j') => if j = j' then 1 else 0
        | Sum.inl i, Sum.inr (Sum.inl j) => if j = Fin.castAdd k i then -1 else 0
        | Sum.inr (Sum.inl j), Sum.inl i => if j = Fin.castAdd k i then -1 else 0
        | _, _ => 0 }

/-- The column sum against the input block picks out `pad(a)`. -/
theorem sum_match (a : Fin n → ℤ) (j : Fin (n + k)) :
    (∑ i : Fin n, (if j = Fin.castAdd k i then a i else 0)) = padF (k := k) a j := by
  classical
  induction j using Fin.addCases with
  | left i₀ =>
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro b _ hb
        have hne : Fin.castAdd k i₀ ≠ Fin.castAdd k b := by
          intro hc
          have hv := congrArg Fin.val hc
          simp at hv
          exact hb (Fin.ext hv.symm)
        simp [hne]
      · intro hcon; exact absurd (Finset.mem_univ i₀) hcon
  | right j₀ =>
      have hne : ∀ i : Fin n, Fin.natAdd n j₀ ≠ Fin.castAdd k i := by
        intro i hc
        have := congrArg Fin.val hc
        simp [Fin.natAdd, Fin.castAdd, Fin.castLE] at this
        omega
      simp [hne]

theorem padGraph_eval (n k : ℕ) (a : Fin n → ℤ) (b : Fin (n + k) → ℤ) (u : Fin 0 → ℤ) :
    (padGraph n k).P.eval (pt a b u) = ∑ j, (b j - padF (k := k) a j) ^ 2 := by
  classical
  have hinner : ∀ x : Vars n (n + k) 0,
      (∑ y, (padGraph n k).P.Q x y * (pt a b u) y)
        = (match x with
           | Sum.inl i => a i - b (Fin.castAdd k i)
           | Sum.inr (Sum.inl j) => b j - padF (k := k) a j
           | Sum.inr (Sum.inr j) => j.elim0) := by
    intro x
    cases x with
    | inl i =>
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
        simp [padGraph, pt, Finset.sum_ite_eq]
        ring
    | inr x' =>
        cases x' with
        | inl j =>
            rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
            simp only [padGraph, pt, Sum.elim_inl, Sum.elim_inr]
            have h1 : (∑ i : Fin n, (if j = Fin.castAdd k i then (-1 : ℤ) else 0) * a i)
                = - padF (k := k) a j := by
              rw [← sum_match (k := k) a j, ← Finset.sum_neg_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              by_cases hc : j = Fin.castAdd k i <;> simp [hc]
            rw [h1]
            simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
            ring
        | inr j => exact j.elim0
  have hc : (padGraph n k).P.c = 0 := rfl
  have hl : (padGraph n k).P.l = fun _ => (0 : ℤ) := rfl
  simp only [IntQuad.eval, dotProduct, Matrix.mulVec]
  simp only [hinner]
  simp only [hc, hl, zero_mul, Finset.sum_const_zero, zero_add, Fintype.sum_sum_type,
    Fintype.sum_empty, add_zero, pt, Sum.elim_inl, Sum.elim_inr]
  have hcross : (∑ i : Fin n, a i * (a i - b (Fin.castAdd k i)))
      = (∑ j, padF (k := k) a j * (padF (k := k) a j - b j)) := by
    rw [Fin.sum_univ_add]
    simp
  rw [hcross, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem padGraph_defines (n k : ℕ) :
    (padGraph n k).Defines (fun a => padF (k := k) a) := by
  intro a b
  constructor
  · rintro ⟨u, hu⟩
    have h : (padGraph n k).P.eval (pt a b u) = 0 := hu
    rw [padGraph_eval] at h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 h
    funext j
    have h2 := hz j (Finset.mem_univ j)
    have h3 : b j - padF (k := k) a j = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
    show b j = padF (k := k) a j
    omega
  · rintro rfl
    refine ⟨fun i => i.elim0, ?_⟩
    show (padGraph n k).P.eval (pt a _ _) = 0
    rw [padGraph_eval]
    simp

/-- **G22-T18.**  For every `n ≤ m` there is ONE quadratic equation, with no witnesses, defining an
injective total function `ℤⁿ → ℤᵐ`.  So the bound `n ≤ m` of `dim_le_of_defines` is attained at
every point of its range, not only at `n = m`. -/
theorem exists_graph_injective_pad (n m : ℕ) (h : n ≤ m) :
    ∃ (D : QuadraticGraphData n m 0) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      D.Defines f ∧ Function.Injective f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨padGraph n k, fun a => padF (k := k) a, padGraph_defines n k, padF_injective⟩

end DiophCompression.ResearchUpgrade
