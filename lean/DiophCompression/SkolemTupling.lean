/-
  DiophCompression/SkolemTupling.lean — r04 Task 2 (session 4, 2026-08-26, claude.ai direct).
  skolem x = Σ_{k<e} C(S_{k+1} + k, k+1) with S_{k+1} = x_0+…+x_k (combinatorial number system),
  written recursively: skolem_{e+1} x = skolem_e (init x) + C(Σx + e, e+1).
  Facts: skolem x < C(Σx + e, e); skolem injective on ℕ^e; e!·skolem is an integer polynomial
  of total degree ≤ e (skolemPoly). Sharpness: ℕ^e ↪ ℤ by a degree-≤e polynomial.
-/
import Mathlib

namespace DiophCompression

open MvPolynomial

/-- Recursive Skolem tupling. -/
def skolem : {e : ℕ} → (Fin e → ℕ) → ℕ
  | 0, _ => 0
  | e + 1, x => skolem (Fin.init x) + (∑ i, x i + e).choose (e + 1)

@[simp] theorem skolem_zero (x : Fin 0 → ℕ) : skolem x = 0 := rfl

theorem skolem_succ {e : ℕ} (x : Fin (e + 1) → ℕ) :
    skolem x = skolem (Fin.init x) + (∑ i, x i + e).choose (e + 1) := rfl

theorem sum_init_le {e : ℕ} (x : Fin (e + 1) → ℕ) : ∑ i, Fin.init x i ≤ ∑ i, x i := by
  rw [Fin.sum_univ_castSucc x]
  exact Nat.le_add_right _ _

/-- The combinatorial-number-system bound: skolem x < C(Σx + e, e). -/
theorem skolem_lt : ∀ {e : ℕ} (x : Fin e → ℕ), skolem x < (∑ i, x i + e).choose e := by
  intro e
  induction e with
  | zero => intro x; simp
  | succ e ih =>
    intro x
    rw [skolem_succ]
    have h1 := ih (Fin.init x)
    have h2 : (∑ i, Fin.init x i + e).choose e ≤ (∑ i, x i + e).choose e :=
      Nat.choose_le_choose _ (by have := sum_init_le x; omega)
    rw [show ∑ i, x i + (e + 1) = (∑ i, x i + e) + 1 by ring, Nat.choose_succ_succ' (∑ i, x i + e) e]
    omega

/-- Skolem tupling is injective. -/
theorem skolem_injective : ∀ {e : ℕ}, Function.Injective (skolem (e := e)) := by
  intro e
  induction e with
  | zero => intro x y _; exact Subsingleton.elim x y
  | succ e ih =>
    intro x y hxy
    rw [skolem_succ, skolem_succ] at hxy
    -- key: the total sums agree
    have hkey : ∀ (u v : Fin (e + 1) → ℕ), ∑ i, u i < ∑ i, v i →
        skolem (Fin.init u) + (∑ i, u i + e).choose (e + 1)
          < skolem (Fin.init v) + (∑ i, v i + e).choose (e + 1) := by
      intro u v huv
      have hlt : skolem u < (∑ i, u i + (e + 1)).choose (e + 1) := skolem_lt u
      rw [skolem_succ] at hlt
      have hle : (∑ i, u i + (e + 1)).choose (e + 1) ≤ (∑ i, v i + e).choose (e + 1) :=
        Nat.choose_le_choose _ (by omega)
      omega
    have hS : ∑ i, x i = ∑ i, y i := by
      rcases lt_trichotomy (∑ i, x i) (∑ i, y i) with h | h | h
      · exact absurd hxy (ne_of_lt (hkey x y h))
      · exact h
      · exact absurd hxy (ne_of_gt (hkey y x h))
    rw [hS] at hxy
    have hinit : Fin.init x = Fin.init y := ih (by omega)
    have hlast : x (Fin.last e) = y (Fin.last e) := by
      rw [Fin.sum_univ_castSucc x, Fin.sum_univ_castSucc y] at hS
      have hx : ∑ i : Fin e, x i.castSucc = ∑ i : Fin e, Fin.init x i := rfl
      have hy : ∑ i : Fin e, y i.castSucc = ∑ i : Fin e, Fin.init y i := rfl
      rw [hx, hy, hinit] at hS
      omega
    rw [← Fin.snoc_init_self x, ← Fin.snoc_init_self y, hinit, hlast]

/-! ### The integer polynomial e!·skolem -/

/-- Integer polynomial with eval = e! · skolem. -/
noncomputable def skolemPoly : (e : ℕ) → MvPolynomial (Fin e) ℤ
  | 0 => 0
  | e + 1 => C ((e + 1 : ℕ) : ℤ) * rename Fin.castSucc (skolemPoly e)
      + ∏ i ∈ Finset.range (e + 1),
          ((∑ j : Fin (e + 1), (X j : MvPolynomial (Fin (e + 1)) ℤ)) + C (i : ℤ))

theorem ascFactorial_eq_choose (S e : ℕ) :
    S.ascFactorial (e + 1) = (e + 1).factorial * (S + e).choose (e + 1) := by
  cases S with
  | zero =>
    have h0 : ∀ k, (0 : ℕ).ascFactorial (k + 1) = 0 := by
      intro k
      induction k with
      | zero => simp [Nat.ascFactorial_succ]
      | succ k ih => rw [Nat.ascFactorial_succ, ih]; simp
    rw [h0, Nat.zero_add, Nat.choose_succ_self]; simp
  | succ n =>
    rw [Nat.ascFactorial_eq_factorial_mul_choose, show n + 1 + e = n + (e + 1) by ring]

theorem prod_range_shift (S k : ℕ) :
    (∏ i ∈ Finset.range (k + 1), ((S : ℤ) + (i : ℤ))) = ((S.ascFactorial (k + 1) : ℕ) : ℤ) := by
  induction k with
  | zero => simp [Nat.ascFactorial_succ]
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.ascFactorial_succ (k := k + 1)]
    push_cast; ring

theorem eval_skolemPoly : ∀ (e : ℕ) (x : Fin e → ℕ),
    eval (fun i => (x i : ℤ)) (skolemPoly e) = ((e.factorial * skolem x : ℕ) : ℤ) := by
  intro e
  induction e with
  | zero => intro x; simp [skolemPoly]
  | succ e ih =>
    intro x
    simp only [skolemPoly, map_add, map_mul, eval_C, eval_rename, eval_prod, eval_sum, eval_X]
    have hinit : (fun i => (x i : ℤ)) ∘ Fin.castSucc = fun i => (Fin.init x i : ℤ) := rfl
    rw [hinit, ih]
    have hS : (∑ j, (x j : ℤ)) = ((∑ j, x j : ℕ) : ℤ) := by push_cast; rfl
    rw [hS, prod_range_shift, ascFactorial_eq_choose, skolem_succ]
    push_cast
    rw [Nat.factorial_succ]
    push_cast
    ring

theorem skolemPoly_totalDegree : ∀ e : ℕ, (skolemPoly e).totalDegree ≤ e := by
  intro e
  induction e with
  | zero => simp [skolemPoly]
  | succ e ih =>
    simp only [skolemPoly]
    refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
    · refine le_trans (totalDegree_mul _ _) ?_
      rw [totalDegree_C, zero_add]
      exact le_trans (totalDegree_rename_le _ _) (le_trans ih (Nat.le_succ e))
    · refine le_trans (totalDegree_finsetProd _ _) ?_
      refine le_trans (Finset.sum_le_sum (g := fun _ => 1) ?_) ?_
      · intro i _
        refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
        · refine le_trans (totalDegree_finsetSum _ _) ?_
          exact Finset.sup_le (fun j _ => (totalDegree_X j).le)
        · rw [totalDegree_C]; exact Nat.zero_le _
      · simp

/-- The polynomial e!·skolem is injective on ℕ^e. -/
theorem skolemPoly_injective (e : ℕ) :
    Function.Injective (fun x : Fin e → ℕ => eval (fun i => (x i : ℤ)) (skolemPoly e)) := by
  intro x y hxy
  simp only [eval_skolemPoly] at hxy
  have h : e.factorial * skolem x = e.factorial * skolem y := by exact_mod_cast hxy
  exact skolem_injective (Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos e) h)

/-- SHARPNESS (one coordinate): ℕ^e embeds in ℤ by an integer polynomial of degree ≤ e. -/
theorem exists_injective_poly_degree (e : ℕ) :
    ∃ p : MvPolynomial (Fin e) ℤ, p.totalDegree ≤ e ∧
      Function.Injective (fun x : Fin e → ℕ => eval (fun i => (x i : ℤ)) p) :=
  ⟨skolemPoly e, skolemPoly_totalDegree e, skolemPoly_injective e⟩

end DiophCompression

#print axioms DiophCompression.skolem_injective
#print axioms DiophCompression.eval_skolemPoly
#print axioms DiophCompression.skolemPoly_totalDegree
#print axioms DiophCompression.exists_injective_poly_degree
