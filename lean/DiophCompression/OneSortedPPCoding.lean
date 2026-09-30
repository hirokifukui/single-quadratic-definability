/-
  DiophCompression/OneSortedPPCoding.lean — APAL r20 Gate 2 (session 22, 2026-08-31, claude.ai direct).
  Statements frozen in frozen_statements/OneSortedPPCoding_STATEMENTS.lean (md5 7a835202). See that header.
  All-arity pp-quadratic tuple coding over ℤ via η(x) = 2x² − x (DDF Lemma 8.20) and the scaled Cantor pairing.
-/
import DiophCompression.OneSorted

namespace DiophCompression

open MvPolynomial MPUP

/-! ### η and π on ℤ (verbatim from the freeze) -/

/-- DDF's polynomial injection ℤ → ℕ: `η(x) = 2x² − x`. -/
def intToNatPoly (x : ℤ) : ℤ := 2 * x ^ 2 - x

theorem intToNatPoly_nonneg (x : ℤ) : 0 ≤ intToNatPoly x := by
  unfold intToNatPoly
  rcases le_or_gt x 0 with h | h
  · nlinarith [sq_nonneg x]
  · nlinarith

theorem intToNatPoly_injective : Function.Injective intToNatPoly := by
  intro x y h
  unfold intToNatPoly at h
  have h2 : (x - y) * (2 * (x + y) - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · linarith
  · omega

/-- The scaled Cantor pairing as an integer polynomial map (= `cantorScaledPair` on ℕ²). -/
def pairZ (x y : ℤ) : ℤ := (x + y) * (x + y + 1) + 2 * y

theorem pairZ_nonneg {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ pairZ x y := by
  unfold pairZ
  nlinarith [mul_nonneg (add_nonneg hx hy) (by linarith : (0 : ℤ) ≤ x + y + 1)]

theorem pairZ_eq_cast (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    pairZ x y = ((cantorScaledPair x.toNat y.toNat : ℕ) : ℤ) := by
  rw [cast_cantorScaledPair, Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy]
  unfold pairZ; ring

theorem pairZ_inj {x y x' y' : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hx' : 0 ≤ x') (hy' : 0 ≤ y')
    (h : pairZ x y = pairZ x' y') : x = x' ∧ y = y' := by
  rw [pairZ_eq_cast x y hx hy, pairZ_eq_cast x' y' hx' hy'] at h
  have h1 : cantorScaledPair x.toNat y.toNat = cantorScaledPair x'.toNat y'.toNat := by
    exact_mod_cast h
  have h2 : (x.toNat, y.toNat) = (x'.toNat, y'.toNat) := cantorScaledPair_injective h1
  simp only [Prod.mk.injEq] at h2
  refine ⟨?_, ?_⟩
  · rw [← Int.toNat_of_nonneg hx, ← Int.toNat_of_nonneg hx', h2.1]
  · rw [← Int.toNat_of_nonneg hy, ← Int.toNat_of_nonneg hy', h2.2]

/-! ### The integer tuple code -/

/-- `intTupleCode a = π(π(…π(η a₀, η a₁)…), η aₙ₋₁)`; `0` at arity 0, `η a₀` at arity 1. -/
def intTupleCode : ∀ {n : ℕ}, (Fin n → ℤ) → ℤ
  | 0, _ => 0
  | 1, a => intToNatPoly (a 0)
  | n + 2, a => pairZ (intTupleCode (Fin.init a)) (intToNatPoly (a (Fin.last (n + 1))))

theorem intTupleCode_nonneg {n : ℕ} (a : Fin n → ℤ) : 0 ≤ intTupleCode a := by
  revert a
  refine Nat.twoStepInduction ?_ ?_ ?_ n
  · intro a; simp [intTupleCode]
  · intro a; simp only [intTupleCode]; exact intToNatPoly_nonneg _
  · intro k _ ih a
    simp only [intTupleCode]
    exact pairZ_nonneg (ih (Fin.init a)) (intToNatPoly_nonneg _)

theorem intTupleCode_injective (n : ℕ) : Function.Injective (@intTupleCode n) := by
  refine Nat.twoStepInduction ?_ ?_ ?_ n
  · exact fun a b _ => funext fun i => i.elim0
  · intro a b h
    simp only [intTupleCode] at h
    have h1 := intToNatPoly_injective h
    funext i
    rw [Fin.eq_zero i]
    exact h1
  · intro k _ ih a b h
    simp only [intTupleCode] at h
    obtain ⟨h1, h2⟩ := pairZ_inj (intTupleCode_nonneg _) (intToNatPoly_nonneg _)
      (intTupleCode_nonneg _) (intToNatPoly_nonneg _) h
    have h3 := ih h1
    have h4 := intToNatPoly_injective h2
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact h4
    · exact congrFun h3 j

theorem intTupleCode_one (a : Fin 1 → ℤ) : intTupleCode a = intToNatPoly (a 0) := by
  simp [intTupleCode]
theorem intTupleCode_succ_succ {n : ℕ} (a : Fin (n + 2) → ℤ) :
    intTupleCode a = pairZ (intTupleCode (Fin.init a)) (intToNatPoly (a (Fin.last (n + 1)))) := by
  simp [intTupleCode]

/-! ### The equations -/

/-- `X y − (2·X a·X a − X a)`: the equation `y = η(a)`. -/
noncomputable def etaPoly {σ : Type} (y a : σ) : MvPolynomial σ ℤ := X y - (2 * X a * X a - X a)

theorem etaPoly_totalDegree {σ : Type} (y a : σ) : (etaPoly y a).totalDegree ≤ 2 := by
  have h2 : (2 * X a * X a : MvPolynomial σ ℤ) = X a * X a + X a * X a := by ring
  unfold etaPoly
  rw [h2]
  refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
  · exact (totalDegree_X_le_one _).trans (by norm_num)
  · refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
    · exact le_trans (totalDegree_add _ _) (max_le (totalDegree_XX_le_two _ _) (totalDegree_XX_le_two _ _))
    · exact (totalDegree_X_le_one _).trans (by norm_num)

theorem eval_etaPoly {σ : Type} (f : σ → ℤ) (y a : σ) :
    eval f (etaPoly y a) = f y - intToNatPoly (f a) := by
  simp [etaPoly, intToNatPoly]; ring

/-! ### The chain step -/

section Step

variable (n r : ℕ)

/-- New witness slot for the old output. -/
def zW : Fin (r + 2) := Fin.natAdd r 0
/-- New witness slot for `η(a_last)`. -/
def wW : Fin (r + 2) := Fin.natAdd r 1

/-- Variable relabelling: old inputs `j ↦ j.castSucc.castSucc`, old output `↦ zW`, old witnesses `↦ castAdd 2`. -/
def stepMap : Fin (n + 1) ⊕ Fin r → Fin (n + 2) ⊕ Fin (r + 2)
  | Sum.inl i => Fin.lastCases (Sum.inr (zW r)) (fun j => Sum.inl j.castSucc.castSucc) i
  | Sum.inr t => Sum.inr (Fin.castAdd 2 t)

/-- The (m+2)-equation system: old equations relabelled, then `w = η(a_last)`, then `c = π(z, w)`. -/
noncomputable def stepSystem {m : ℕ} (S : PolySystem (n + 1) r m) : PolySystem (n + 2) (r + 2) (m + 2) :=
  Fin.snoc (Fin.snoc (fun i => rename (stepMap n r) (S i))
      (etaPoly (Sum.inr (wW r)) (Sum.inl (Fin.castSucc (Fin.last n)))))
    (X (Sum.inl (Fin.last (n + 1))) - pairPolyX (Sum.inr (zW r)) (Sum.inr (wW r)))

theorem evalAtZZ_stepMap {m : ℕ} (S : PolySystem (n + 1) r m) (i : Fin m) (v : Fin (n + 2) → ℤ)
    (y' : Fin (r + 2) → ℤ) :
    evalAtZZ (rename (stepMap n r) (S i)) v y'
      = evalAtZZ (S i) (Fin.snoc (Fin.init (Fin.init v)) (y' (zW r))) (fun t => y' (Fin.castAdd 2 t)) := by
  unfold evalAtZZ
  rw [eval_rename]
  refine congrArg (fun h => (eval h) (S i)) ?_
  funext x
  rcases x with j | t
  · induction j using Fin.lastCases with
    | last => simp [stepMap, Fin.snoc_last]
    | cast j => simp [stepMap, Fin.snoc_castSucc]; rfl
  · rfl

theorem stepSystem_totalDegree {m : ℕ} (S : PolySystem (n + 1) r m) (hd : ∀ i, (S i).totalDegree ≤ 2) :
    ∀ i, (stepSystem n r S i).totalDegree ≤ 2 := by
  intro i
  induction i using Fin.lastCases with
  | last =>
    simp only [stepSystem, Fin.snoc_last]
    exact le_trans (totalDegree_sub _ _)
      (max_le ((totalDegree_X_le_one _).trans (by norm_num)) (pairPolyX_totalDegree _ _))
  | cast i =>
    induction i using Fin.lastCases with
    | last =>
      simp only [stepSystem, Fin.snoc_castSucc, Fin.snoc_last]
      exact etaPoly_totalDegree _ _
    | cast i =>
      simp only [stepSystem, Fin.snoc_castSucc]
      exact (totalDegree_rename_le _ _).trans (hd i)

theorem stepSystem_representsZZ {m : ℕ} (e : (Fin n → ℤ) → ℤ) (S : PolySystem (n + 1) r m)
    (hS : SystemRepresentsZZ S (graphZZ e)) :
    SystemRepresentsZZ (stepSystem n r S)
      (graphZZ (fun a : Fin (n + 1) → ℤ => pairZ (e (Fin.init a)) (intToNatPoly (a (Fin.last n))))) := by
  intro v
  have hg : v ∈ graphZZ (fun a : Fin (n + 1) → ℤ => pairZ (e (Fin.init a)) (intToNatPoly (a (Fin.last n))))
      ↔ v (Fin.last (n + 1)) = pairZ (e (Fin.init (Fin.init v))) (intToNatPoly (v (Fin.castSucc (Fin.last n)))) :=
    Iff.rfl
  rw [hg]
  constructor
  · intro hv
    obtain ⟨y, hy⟩ := (hS (Fin.snoc (Fin.init (Fin.init v)) (e (Fin.init (Fin.init v))))).1
      ((snoc_mem_graphZZ e _ _).2 rfl)
    refine ⟨Fin.append y ![e (Fin.init (Fin.init v)), intToNatPoly (v (Fin.castSucc (Fin.last n)))], ?_⟩
    intro i
    induction i using Fin.lastCases with
    | last =>
      simp only [stepSystem, Fin.snoc_last, evalAtZZ, map_sub, eval_X, eval_pairPolyX, Sum.elim_inl,
        Sum.elim_inr, zW, wW, Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
      rw [hv]; unfold pairZ; ring
    | cast i =>
      induction i using Fin.lastCases with
      | last =>
        simp only [stepSystem, Fin.snoc_castSucc, Fin.snoc_last, evalAtZZ, eval_etaPoly, Sum.elim_inl,
          Sum.elim_inr, wW, Fin.append_right, Matrix.cons_val_one, Matrix.cons_val_zero,
          Matrix.cons_val_fin_one]
        ring
      | cast i =>
        simp only [stepSystem, Fin.snoc_castSucc]
        rw [evalAtZZ_stepMap]
        have hz : Fin.append y ![e (Fin.init (Fin.init v)), intToNatPoly (v (Fin.castSucc (Fin.last n)))] (zW r)
            = e (Fin.init (Fin.init v)) := by
          simp [zW, Fin.append_right]
        have hy' : (fun t => Fin.append y
            ![e (Fin.init (Fin.init v)), intToNatPoly (v (Fin.castSucc (Fin.last n)))] (Fin.castAdd 2 t)) = y := by
          funext t; simp [Fin.append_left]
        rw [hz, hy']
        exact hy i
  · rintro ⟨y', hy'⟩
    have hc := hy' (Fin.last (m + 1))
    have hw := hy' (Fin.castSucc (Fin.last m))
    simp only [stepSystem, Fin.snoc_last, Fin.snoc_castSucc, evalAtZZ, map_sub, eval_X, eval_pairPolyX,
      eval_etaPoly, Sum.elim_inl, Sum.elim_inr] at hc hw
    have hold : ∀ i : Fin m, evalAtZZ (S i) (Fin.snoc (Fin.init (Fin.init v)) (y' (zW r)))
        (fun t => y' (Fin.castAdd 2 t)) = 0 := by
      intro i
      have := hy' (Fin.castSucc (Fin.castSucc i))
      simp only [stepSystem, Fin.snoc_castSucc] at this
      rw [evalAtZZ_stepMap] at this
      exact this
    have hmem := (hS _).2 ⟨_, hold⟩
    rw [snoc_mem_graphZZ] at hmem
    rw [← hmem]
    have hw' : y' (wW r) = intToNatPoly (v (Fin.castSucc (Fin.last n))) := by linarith
    rw [← hw']
    unfold pairZ
    linarith

end Step

/-- Chain step: a degree-≤2 system for `graphZZ e` (inputs ℤⁿ, r witnesses, m equations) yields a degree-≤2
    system for the graph of `a ↦ π(e(init a), η(a last))` (inputs ℤⁿ⁺¹) with r+2 witnesses and m+2 equations. -/
theorem ppGraphZZ_step {n r m : ℕ} (e : (Fin n → ℤ) → ℤ) (S : PolySystem (n + 1) r m)
    (hd : ∀ i, (S i).totalDegree ≤ 2) (hS : SystemRepresentsZZ S (graphZZ e)) :
    ∃ S' : PolySystem (n + 2) (r + 2) (m + 2), (∀ i, (S' i).totalDegree ≤ 2) ∧
      SystemRepresentsZZ S'
        (graphZZ (fun a : Fin (n + 1) → ℤ => pairZ (e (Fin.init a)) (intToNatPoly (a (Fin.last n))))) :=
  ⟨stepSystem n r S, stepSystem_totalDegree n r S hd, stepSystem_representsZZ n r e S hS⟩

/-! ### Arity 1 and the induction -/

/-- Arity 1: the single equation `c = η(a₀)`, no witnesses. -/
noncomputable def unarySystem : PolySystem 2 0 1 := ![etaPoly (Sum.inl 1) (Sum.inl 0)]

theorem unarySystem_totalDegree : ∀ i, (unarySystem i).totalDegree ≤ 2 := by
  intro i
  rw [Fin.eq_zero i]
  exact etaPoly_totalDegree _ _

theorem unarySystem_representsZZ : SystemRepresentsZZ unarySystem (graphZZ (@intTupleCode 1)) := by
  intro v
  have hg : v ∈ graphZZ (@intTupleCode 1) ↔ v 1 = intToNatPoly (v 0) := by
    show v (Fin.last 1) = intTupleCode (Fin.init v) ↔ _
    rw [intTupleCode_one]
    exact Iff.rfl
  rw [hg]
  constructor
  · intro hv
    refine ⟨fun t => t.elim0, ?_⟩
    intro i
    rw [Fin.eq_zero i]
    simp only [unarySystem, Matrix.cons_val_zero, evalAtZZ, eval_etaPoly, Sum.elim_inl]
    rw [hv]; ring
  · rintro ⟨y, hy⟩
    have := hy 0
    simp only [unarySystem, Matrix.cons_val_zero, evalAtZZ, eval_etaPoly, Sum.elim_inl] at this
    linarith

theorem graphZZ_intTupleCode_succ_succ (k : ℕ) :
    graphZZ (fun a : Fin (k + 2) → ℤ =>
        pairZ (intTupleCode (Fin.init a)) (intToNatPoly (a (Fin.last (k + 1)))))
      = graphZZ (@intTupleCode (k + 2)) := by
  have h : (fun a : Fin (k + 2) → ℤ =>
      pairZ (intTupleCode (Fin.init a)) (intToNatPoly (a (Fin.last (k + 1))))) = @intTupleCode (k + 2) :=
    funext fun a => (intTupleCode_succ_succ a).symm
  rw [h]

/-- Resource bound (upper bound only; minimality not claimed): for n ≥ 1 the graph of `intTupleCode`
    on ℤⁿ is defined by 2n−1 quadratic equations with 2n−2 integer existential variables. -/
theorem intTupleCode_system (n : ℕ) (hn : 1 ≤ n) :
    ∃ (r m : ℕ) (S : PolySystem (n + 1) r m), r = 2 * n - 2 ∧ m = 2 * n - 1 ∧
      (∀ i, (S i).totalDegree ≤ 2) ∧ SystemRepresentsZZ S (graphZZ (@intTupleCode n)) := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases k with _ | k
    · exact ⟨0, 1, unarySystem, rfl, rfl, unarySystem_totalDegree, unarySystem_representsZZ⟩
    · obtain ⟨r, m, S, hr, hm, hd, hS⟩ := ih (by omega)
      obtain ⟨S', hd', hS'⟩ := ppGraphZZ_step (@intTupleCode (k + 1)) S hd hS
      rw [graphZZ_intTupleCode_succ_succ] at hS'
      exact ⟨r + 2, m + 2, S', by omega, by omega, hd', hS'⟩

/-- Theorem (all-arity pp-quadratic coding over ℤ): `PPGraphZZ 2 n` for every n. -/
theorem ppGraphZZ_degree_two_all : ∀ n, PPGraphZZ 2 n := by
  intro n
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    refine ⟨0, 1, fun _ => 0, fun a b _ => funext fun i => i.elim0, ![X (Sum.inl 0)], ?_, ?_⟩
    · intro i
      rw [Fin.eq_zero i]
      simp only [Matrix.cons_val_zero]
      exact (totalDegree_X_le_one _).trans (by norm_num)
    · intro v
      have hg : v ∈ graphZZ (fun _ : Fin 0 → ℤ => (0 : ℤ)) ↔ v 0 = 0 := Iff.rfl
      rw [hg]
      constructor
      · intro hv
        refine ⟨fun t => t.elim0, ?_⟩
        intro i
        rw [Fin.eq_zero i]
        simp only [Matrix.cons_val_zero, evalAtZZ, eval_X, Sum.elim_inl]
        exact hv
      · rintro ⟨y, hy⟩
        have := hy 0
        simp only [Matrix.cons_val_zero, evalAtZZ, eval_X, Sum.elim_inl] at this
        exact this
  · obtain ⟨r, m, S, _, _, hd, hS⟩ := intTupleCode_system n hpos
    exact ⟨r, m, intTupleCode, intTupleCode_injective n, S, hd, hS⟩

end DiophCompression

#print axioms DiophCompression.intToNatPoly_injective
#print axioms DiophCompression.intTupleCode_injective
#print axioms DiophCompression.ppGraphZZ_step
#print axioms DiophCompression.intTupleCode_system
#print axioms DiophCompression.ppGraphZZ_degree_two_all
