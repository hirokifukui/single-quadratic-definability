/-
  MPUP/Task1.lean — statements frozen with the spec (r01 freeze); proofs completed 2026-08-26 (std-3, see spec/FREEZE.md; E2/r04 comment fix only).
  Task 1: audit GPT's architecture  MPUP ⟺ bounded-complexity tuple coder  by proving both
  Arch_* propositions of MPUP/Spec.lean as theorems, with explicit constants.
  Combinator layer (weaken / conj / project) + a Diophantine injective ℕ^n → ℕ (iterated Nat.pair).
-/
import MPUP.Spec

namespace MPUP
open MvPolynomial

/-! ### Combinators on `Poly n r` with `RepresentsN` transfer and complexity accounting -/

/-- Add `m` parameters after the existing `n`; the polynomial ignores them. -/
noncomputable def weakenParams {n r : ℕ} (m : ℕ) (P : Poly n r) : Poly (n + m) r :=
  rename (Sum.map (Fin.castAdd m) id) P

theorem evalAt_weakenParams {n r m : ℕ} (P : Poly n r) (a : Fin (n + m) → ℕ) (y : Fin r → ℤ) :
    evalAt (weakenParams m P) a y = evalAt P (fun i => a (Fin.castAdd m i)) y := by
  simp only [evalAt, weakenParams, eval_rename]
  congr 2
  funext v; cases v <;> rfl

theorem representsN_weakenParams {n r m : ℕ} (P : Poly n r) (A : Set (Fin n → ℕ))
    (h : RepresentsN P A) :
    RepresentsN (weakenParams m P) {a | (fun i => a (Fin.castAdd m i)) ∈ A} := by
  intro a
  show (fun i => a (Fin.castAdd m i)) ∈ A ↔ _
  refine (h _).trans (exists_congr fun y => ?_)
  rw [evalAt_weakenParams]

theorem totalDegree_weakenParams_le {n r m : ℕ} (P : Poly n r) :
    (weakenParams m P).totalDegree ≤ P.totalDegree :=
  totalDegree_rename_le _ _

/-- Conjunction via sum of squares; unknown blocks are disjoint. -/
noncomputable def conj {n r₁ r₂ : ℕ} (P : Poly n r₁) (Q : Poly n r₂) : Poly n (r₁ + r₂) :=
  (rename (Sum.map id (Fin.castAdd r₂)) P) ^ 2 + (rename (Sum.map id (Fin.natAdd r₁)) Q) ^ 2

theorem aux_evalAt_conj {n r₁ r₂ : ℕ} (P : Poly n r₁) (Q : Poly n r₂)
    (a : Fin n → ℕ) (z : Fin (r₁ + r₂) → ℤ) :
    evalAt (conj P Q) a z
      = (evalAt P a (fun j => z (Fin.castAdd r₂ j)))^2
        + (evalAt Q a (fun j => z (Fin.natAdd r₁ j)))^2 := by
  simp only [evalAt, conj, map_add, map_pow, eval_rename]
  have k1 : (Sum.elim (fun i => ((a i : ℤ))) z) ∘ (Sum.map id (Fin.castAdd r₂))
      = Sum.elim (fun i => ((a i : ℤ))) (fun j => z (Fin.castAdd r₂ j)) := by
    funext v; cases v <;> rfl
  have k2 : (Sum.elim (fun i => ((a i : ℤ))) z) ∘ (Sum.map id (Fin.natAdd r₁))
      = Sum.elim (fun i => ((a i : ℤ))) (fun j => z (Fin.natAdd r₁ j)) := by
    funext v; cases v <;> rfl
  rw [k1, k2]

theorem representsN_conj {n r₁ r₂ : ℕ} (P : Poly n r₁) (Q : Poly n r₂)
    (A B : Set (Fin n → ℕ)) (hP : RepresentsN P A) (hQ : RepresentsN Q B) :
    RepresentsN (conj P Q) (A ∩ B) := by
  intro a
  rw [Set.mem_inter_iff, hP a, hQ a]
  constructor
  · rintro ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩⟩
    refine ⟨Fin.append y₁ y₂, ?_⟩
    rw [aux_evalAt_conj]
    have e1 : (fun j => ((Fin.append y₁ y₂ (Fin.castAdd r₂ j) : ℕ) : ℤ)) = (fun j => ((y₁ j : ℕ):ℤ)) := by
      funext j; rw [Fin.append_left]
    have e2 : (fun j => ((Fin.append y₁ y₂ (Fin.natAdd r₁ j) : ℕ) : ℤ)) = (fun j => ((y₂ j : ℕ):ℤ)) := by
      funext j; rw [Fin.append_right]
    rw [e1, e2, hy₁, hy₂]; ring
  · rintro ⟨y, hy⟩
    rw [aux_evalAt_conj] at hy
    have hz := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hy
    have h1 := (pow_eq_zero_iff (two_ne_zero)).mp hz.1
    have h2 := (pow_eq_zero_iff (two_ne_zero)).mp hz.2
    exact ⟨⟨fun j => y (Fin.castAdd r₂ j), h1⟩, ⟨fun j => y (Fin.natAdd r₁ j), h2⟩⟩

theorem totalDegree_conj_le {n r₁ r₂ : ℕ} (P : Poly n r₁) (Q : Poly n r₂) :
    (conj P Q).totalDegree ≤ 2 * max P.totalDegree Q.totalDegree := by
  unfold conj
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_pow _ _).trans ?_
    have := totalDegree_rename_le (Sum.map id (Fin.castAdd r₂)) P
    calc 2 * (rename (Sum.map id (Fin.castAdd r₂)) P).totalDegree
        ≤ 2 * P.totalDegree := by omega
      _ ≤ 2 * max P.totalDegree Q.totalDegree := by omega
  · refine (totalDegree_pow _ _).trans ?_
    have := totalDegree_rename_le (Sum.map id (Fin.natAdd r₁)) Q
    calc 2 * (rename (Sum.map id (Fin.natAdd r₁)) Q).totalDegree
        ≤ 2 * Q.totalDegree := by omega
      _ ≤ 2 * max P.totalDegree Q.totalDegree := by omega

/-- Turn the LAST parameter into a new unknown (index 0 among unknowns). -/
noncomputable def projectLast {n r : ℕ} (P : Poly (n + 1) r) : Poly n (r + 1) :=
  rename (fun v => match v with
    | Sum.inl i => if h : (i : ℕ) < n then Sum.inl ⟨i, h⟩ else Sum.inr 0
    | Sum.inr j => Sum.inr j.succ) P

theorem aux_evalAt_projectLast {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℕ) (y' : Fin (r + 1) → ℕ) :
    evalAt (projectLast P) a (fun i => (y' i : ℤ))
      = evalAt P (Fin.snoc a (y' 0)) (fun j => (y' j.succ : ℤ)) := by
  simp only [evalAt, projectLast, eval_rename]
  refine congrArg (fun h => (eval h) P) ?_
  funext v
  rcases v with i | j
  · simp only [Function.comp_apply]
    induction i using Fin.lastCases with
    | last =>
      have hn : ¬ ((Fin.last n : Fin (n+1)) : ℕ) < n := by rw [Fin.val_last]; exact lt_irrefl n
      simp only [hn, dif_neg, not_false_iff, Sum.elim_inl, Sum.elim_inr, Fin.snoc_last]
    | cast j =>
      have hlt : ((Fin.castSucc j : Fin (n+1)) : ℕ) < n := by rw [Fin.val_castSucc]; exact j.isLt
      simp only [hlt, dif_pos, Sum.elim_inl, Fin.snoc_castSucc]
      congr 2
  · simp only [Function.comp_apply, Sum.elim_inr]

theorem representsN_projectLast {n r : ℕ} (P : Poly (n + 1) r) (S : Set (Fin (n + 1) → ℕ))
    (h : RepresentsN P S) :
    RepresentsN (projectLast P) {a | ∃ c, Fin.snoc a c ∈ S} := by
  intro a
  simp only [Set.mem_setOf_eq, aux_evalAt_projectLast]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨y, hy⟩ := (h (Fin.snoc a c)).mp hc
    refine ⟨Fin.cons c y, ?_⟩
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact hy
  · rintro ⟨y', hy'⟩
    refine ⟨y' 0, (h (Fin.snoc a (y' 0))).mpr ⟨fun j => y' j.succ, hy'⟩⟩

theorem totalDegree_projectLast_le {n r : ℕ} (P : Poly (n + 1) r) :
    (projectLast P).totalDegree ≤ P.totalDegree :=
  totalDegree_rename_le _ _

/-- Turn the FIRST parameter into a new unknown (index 0 among unknowns). -/
noncomputable def projectFirst {n r : ℕ} (P : Poly (n + 1) r) : Poly n (r + 1) :=
  rename (fun v => match v with
    | Sum.inl i => Fin.cases (Sum.inr 0) (fun j => Sum.inl j) i
    | Sum.inr j => Sum.inr j.succ) P

theorem aux_evalAt_projectFirst {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℕ) (y' : Fin (r + 1) → ℕ) :
    evalAt (projectFirst P) a (fun i => (y' i : ℤ))
      = evalAt P (Fin.cons (y' 0) a) (fun j => (y' j.succ : ℤ)) := by
  simp only [evalAt, projectFirst, eval_rename]
  refine congrArg (fun h => (eval h) P) ?_
  funext v
  rcases v with i | j
  · simp only [Function.comp_apply]
    induction i using Fin.cases with
    | zero => simp only [Fin.cases_zero, Sum.elim_inl, Sum.elim_inr, Fin.cons_zero]
    | succ j => simp only [Fin.cases_succ, Sum.elim_inl, Fin.cons_succ]
  · simp only [Function.comp_apply, Sum.elim_inr]

theorem representsN_projectFirst {n r : ℕ} (P : Poly (n + 1) r) (S : Set (Fin (n + 1) → ℕ))
    (h : RepresentsN P S) :
    RepresentsN (projectFirst P) {a | ∃ x, Fin.cons x a ∈ S} := by
  intro a
  simp only [Set.mem_setOf_eq, aux_evalAt_projectFirst]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := (h (Fin.cons x a)).mp hx
    refine ⟨Fin.cons x y, ?_⟩
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact hy
  · rintro ⟨y', hy'⟩
    refine ⟨y' 0, (h (Fin.cons (y' 0) a)).mpr ⟨fun j => y' j.succ, hy'⟩⟩

theorem totalDegree_projectFirst_le {n r : ℕ} (P : Poly (n + 1) r) :
    (projectFirst P).totalDegree ≤ P.totalDegree :=
  totalDegree_rename_le _ _

/-- `DiophN` is preserved by reindexing the parameters along an equivalence. -/
theorem aux_diophN_reindex {k l : ℕ} (e : Fin k ≃ Fin l) {S : Set (Fin k → ℕ)} (h : DiophN S) :
    DiophN {v : Fin l → ℕ | (fun i => v (e i)) ∈ S} := by
  obtain ⟨r, P, hP⟩ := h
  refine ⟨r, rename (Sum.map e id) P, ?_⟩
  have key : ∀ (v : Fin l → ℕ) (z : Fin r → ℤ),
      evalAt (rename (Sum.map e id) P) v z = evalAt P (fun i => v (e i)) z := by
    intro v z
    simp only [evalAt, eval_rename]
    refine congrArg (fun h => (eval h) P) ?_
    funext w; cases w <;> rfl
  intro v
  simp only [Set.mem_setOf_eq]
  rw [hP (fun i => v (e i))]
  exact exists_congr (fun y => by rw [key])

/-- `DiophN` transfers across set equality. -/
theorem aux_diophN_congr {n : ℕ} {S T : Set (Fin n → ℕ)} (hst : S = T) (h : DiophN S) : DiophN T := by
  rw [← hst]; exact h

/-- `DiophN` is closed under projecting away the first parameter. -/
theorem aux_diophN_projectFirst {k : ℕ} (S : Set (Fin (k + 1) → ℕ)) (h : DiophN S) :
    DiophN {a : Fin k → ℕ | ∃ x, Fin.cons x a ∈ S} := by
  obtain ⟨r, P, hP⟩ := h
  exact ⟨r + 1, projectFirst P, representsN_projectFirst P S hP⟩

/-- Diophantine sets are closed under projecting away a leading block of `n` parameters
    (induction on `n` via `projectFirst`; no complexity bound needed here). -/
theorem diophN_projectBlock {n m : ℕ} (S : Set (Fin (n + m) → ℕ)) (h : DiophN S) :
    DiophN {b : Fin m → ℕ | ∃ a : Fin n → ℕ, Fin.append a b ∈ S} := by
  suffices H : ∀ (n : ℕ) (S : Set (Fin (n + m) → ℕ)), DiophN S →
      DiophN {b : Fin m → ℕ | ∃ a : Fin n → ℕ, Fin.append a b ∈ S} from H n S h
  clear h S n
  intro n
  induction n with
  | zero =>
    intro S h
    have hab : ∀ (a : Fin 0 → ℕ), Fin.append a = fun b (i : Fin (0 + m)) => b (finCongr (Nat.zero_add m) i) := by
      intro a; funext b; rw [Fin.append_left_nil a b rfl]; rfl
    refine aux_diophN_congr ?_ (aux_diophN_reindex (finCongr (Nat.zero_add m)) h)
    ext b
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hb
      refine ⟨Fin.elim0, ?_⟩
      rw [hab Fin.elim0]; exact hb
    · rintro ⟨a, ha⟩
      rw [hab a] at ha; exact ha
  | succ n ih =>
    intro S h
    have step_id : ∀ (x : ℕ) (a' : Fin n → ℕ) (b : Fin m → ℕ),
        Fin.append (Fin.cons x a') b
          = fun i => (Fin.cons x (Fin.append a' b) : Fin (n + m + 1) → ℕ)
              (finCongr (Nat.add_right_comm n 1 m) i) := by
      intro x a' b; rw [Fin.append_cons]; rfl
    have hS1 := aux_diophN_reindex (finCongr (Nat.add_right_comm n 1 m)) h
    have hS2 := aux_diophN_projectFirst _ hS1
    have hS3 := ih _ hS2
    refine aux_diophN_congr ?_ hS3
    ext b
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨a', x, hax⟩
      refine ⟨Fin.cons x a', ?_⟩
      rw [step_id x a' b]; exact hax
    · rintro ⟨a, ha⟩
      refine ⟨Fin.tail a, a 0, ?_⟩
      rw [← step_id (a 0) (Fin.tail a) b, Fin.cons_self_tail]; exact ha

/-! ### A Diophantine injective ℕ^n → ℕ (iterated `Nat.pair`) -/

/-- Graph of `Nat.pair` as a subset of ℕ³ (v 2 = pair (v 0) (v 1)); one unknown, degree ≤ 8.
    pair a b = if a < b then b*b + a else a*a + a + b, so the graph is the union of two
    Diophantine pieces; the union is encoded as a product. -/
noncomputable def pairPoly : Poly 3 1 :=
  let a := X (Sum.inl 0); let b := X (Sum.inl 1); let c := X (Sum.inl 2); let u := X (Sum.inr 0)
  ((b - a - u - 1) ^ 2 + (c - b * b - a) ^ 2) * ((a - b - u) ^ 2 + (c - a * a - a - b) ^ 2)

theorem aux_evalAt_pairPoly (a : Fin 3 → ℕ) (y : Fin 1 → ℤ) :
    evalAt pairPoly a y =
      (((a 1 : ℤ) - a 0 - y 0 - 1) ^ 2 + ((a 2 : ℤ) - (a 1) * (a 1) - a 0) ^ 2)
      * (((a 0 : ℤ) - a 1 - y 0) ^ 2 + ((a 2 : ℤ) - (a 0) * (a 0) - a 0 - a 1) ^ 2) := by
  simp only [evalAt, pairPoly, map_add, map_sub, map_mul, map_pow, map_one, eval_X,
    Sum.elim_inl, Sum.elim_inr]

theorem representsN_pairPoly :
    RepresentsN pairPoly {v | v 2 = Nat.pair (v 0) (v 1)} := by
  intro a
  simp only [Set.mem_setOf_eq, aux_evalAt_pairPoly]
  constructor
  · intro hC
    rw [Nat.pair] at hC
    by_cases hab : a 0 < a 1
    · refine ⟨fun _ => a 1 - a 0 - 1, ?_⟩
      simp only [hab, if_true] at hC
      have hu : ((a 1 - a 0 - 1 : ℕ) : ℤ) = (a 1 : ℤ) - a 0 - 1 := by omega
      rw [hu]
      have : (a 2 : ℤ) = (a 1) * (a 1) + a 0 := by exact_mod_cast hC
      rw [this]; ring
    · refine ⟨fun _ => a 0 - a 1, ?_⟩
      simp only [hab, if_false] at hC
      have hu : ((a 0 - a 1 : ℕ) : ℤ) = (a 0 : ℤ) - a 1 := by omega
      rw [hu]
      have : (a 2 : ℤ) = (a 0) * (a 0) + a 0 + a 1 := by exact_mod_cast hC
      rw [this]; ring
  · rintro ⟨y, hy⟩
    have hz := mul_eq_zero.mp hy
    rw [Nat.pair]
    rcases hz with h | h
    · have h2 := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp h
      have e1 : (a 1 : ℤ) - a 0 - y 0 - 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h2.1
      have e2 : (a 2 : ℤ) - (a 1) * (a 1) - a 0 = 0 := (pow_eq_zero_iff two_ne_zero).mp h2.2
      have hlt : a 0 < a 1 := by
        have : (y 0 : ℤ) ≥ 0 := Int.natCast_nonneg _
        omega
      simp only [hlt, if_true]
      have : (a 2 : ℤ) = (a 1) * (a 1) + a 0 := by omega
      exact_mod_cast this
    · have h2 := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp h
      have e1 : (a 0 : ℤ) - a 1 - y 0 = 0 := (pow_eq_zero_iff two_ne_zero).mp h2.1
      have e2 : (a 2 : ℤ) - (a 0) * (a 0) - a 0 - a 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h2.2
      have hge : ¬ a 0 < a 1 := by
        have : (y 0 : ℤ) ≥ 0 := Int.natCast_nonneg _
        omega
      simp only [hge, if_false]
      have : (a 2 : ℤ) = (a 0) * (a 0) + a 0 + a 1 := by omega
      exact_mod_cast this

theorem totalDegree_pairPoly_le : pairPoly.totalDegree ≤ 8 := by
  unfold pairPoly
  simp only []
  set a : Poly 3 1 := X (Sum.inl 0) with ha
  set b : Poly 3 1 := X (Sum.inl 1) with hb
  set c : Poly 3 1 := X (Sum.inl 2) with hc
  set u : Poly 3 1 := X (Sum.inr 0) with hu
  have da : a.totalDegree ≤ 1 := by rw [ha, totalDegree_X]
  have db : b.totalDegree ≤ 1 := by rw [hb, totalDegree_X]
  have dc : c.totalDegree ≤ 1 := by rw [hc, totalDegree_X]
  have du : u.totalDegree ≤ 1 := by rw [hu, totalDegree_X]
  have d1 : (1 : Poly 3 1).totalDegree ≤ 0 := by rw [totalDegree_one]
  have sub_le : ∀ (P Q : Poly 3 1) (m : ℕ), P.totalDegree ≤ m → Q.totalDegree ≤ m →
      (P - Q).totalDegree ≤ m := fun P Q m hP hQ => (totalDegree_sub _ _).trans (max_le hP hQ)
  have add_le : ∀ (P Q : Poly 3 1) (m : ℕ), P.totalDegree ≤ m → Q.totalDegree ≤ m →
      (P + Q).totalDegree ≤ m := fun P Q m hP hQ => (totalDegree_add _ _).trans (max_le hP hQ)
  have mul_le : ∀ (P Q : Poly 3 1) (m k : ℕ), P.totalDegree ≤ m → Q.totalDegree ≤ k →
      (P * Q).totalDegree ≤ m + k := fun P Q m k hP hQ => (totalDegree_mul _ _).trans (Nat.add_le_add hP hQ)
  have pow_le : ∀ (P : Poly 3 1) (e m : ℕ), P.totalDegree ≤ m → (P ^ e).totalDegree ≤ e * m :=
    fun P e m hP => (totalDegree_pow _ _).trans (Nat.mul_le_mul_left e hP)
  have base1 : (b - a - u - 1).totalDegree ≤ 1 := sub_le _ _ 1 (sub_le _ _ 1 (sub_le _ _ 1 db da) du) (d1.trans (by omega))
  have dbb : (b * b).totalDegree ≤ 2 := mul_le _ _ 1 1 db db
  have base2 : (c - b * b - a).totalDegree ≤ 2 := sub_le _ _ 2 (sub_le _ _ 2 (dc.trans (by omega)) dbb) (da.trans (by omega))
  have base3 : (a - b - u).totalDegree ≤ 1 := sub_le _ _ 1 (sub_le _ _ 1 da db) du
  have daa : (a * a).totalDegree ≤ 2 := mul_le _ _ 1 1 da da
  have base4 : (c - a * a - a - b).totalDegree ≤ 2 :=
    sub_le _ _ 2 (sub_le _ _ 2 (sub_le _ _ 2 (dc.trans (by omega)) daa) (da.trans (by omega))) (db.trans (by omega))
  have s1 : ((b - a - u - 1) ^ 2).totalDegree ≤ 2 := (pow_le _ 2 1 base1).trans (by omega)
  have s2 : ((c - b * b - a) ^ 2).totalDegree ≤ 4 := (pow_le _ 2 2 base2).trans (by omega)
  have s3 : ((a - b - u) ^ 2).totalDegree ≤ 2 := (pow_le _ 2 1 base3).trans (by omega)
  have s4 : ((c - a * a - a - b) ^ 2).totalDegree ≤ 4 := (pow_le _ 2 2 base4).trans (by omega)
  have f1 : ((b - a - u - 1) ^ 2 + (c - b * b - a) ^ 2).totalDegree ≤ 4 := add_le _ _ 4 (s1.trans (by omega)) s2
  have f2 : ((a - b - u) ^ 2 + (c - a * a - a - b) ^ 2).totalDegree ≤ 4 := add_le _ _ 4 (s3.trans (by omega)) s4
  exact (mul_le _ _ 4 4 f1 f2).trans (by omega)

/-- Iterated pairing code of a tuple: `code (snoc a x) = pair (code a) x`, `code ![] = 0`. -/
def code : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | _ + 1, a => Nat.pair (code (Fin.init a)) (a (Fin.last _))

theorem code_injective (n : ℕ) : Function.Injective (code (n := n)) := by
  induction n with
  | zero => intro a b _; exact Subsingleton.elim a b
  | succ n ih =>
    intro a b hab
    simp only [code] at hab
    rw [Nat.pair_eq_pair] at hab
    obtain ⟨h1, h2⟩ := hab
    have hinit : Fin.init a = Fin.init b := ih h1
    calc a = Fin.snoc (Fin.init a) (a (Fin.last n)) := (Fin.snoc_init_self a).symm
      _ = Fin.snoc (Fin.init b) (b (Fin.last n)) := by rw [hinit, h2]
      _ = b := Fin.snoc_init_self b

/-- `DiophN` is preserved by pulling back the parameters along an arbitrary map. -/
theorem aux_diophN_pullback {k K : ℕ} (g : Fin k → Fin K) {S : Set (Fin k → ℕ)} (h : DiophN S) :
    DiophN {V : Fin K → ℕ | (fun i => V (g i)) ∈ S} := by
  obtain ⟨r, P, hP⟩ := h
  refine ⟨r, rename (Sum.map g id) P, ?_⟩
  have key : ∀ (V : Fin K → ℕ) (z : Fin r → ℤ),
      evalAt (rename (Sum.map g id) P) V z = evalAt P (fun i => V (g i)) z := by
    intro V z; simp only [evalAt, eval_rename]
    refine congrArg (fun h => (eval h) P) ?_; funext w; cases w <;> rfl
  intro V; simp only [Set.mem_setOf_eq]; rw [hP (fun i => V (g i))]
  exact exists_congr (fun y => by rw [key])

/-- `DiophN` is closed under intersection (via `conj`). -/
theorem aux_diophN_conj {k : ℕ} {A B : Set (Fin k → ℕ)} (hA : DiophN A) (hB : DiophN B) :
    DiophN (A ∩ B) := by
  obtain ⟨r₁, P, hP⟩ := hA
  obtain ⟨r₂, Q, hQ⟩ := hB
  exact ⟨r₁ + r₂, conj P Q, representsN_conj P Q A B hP hQ⟩

/-- `DiophN` is closed under projecting away the last parameter. -/
theorem aux_diophN_projectLast {k : ℕ} (S : Set (Fin (k + 1) → ℕ)) (h : DiophN S) :
    DiophN {a : Fin k → ℕ | ∃ c, Fin.snoc a c ∈ S} := by
  obtain ⟨r, P, hP⟩ := h
  exact ⟨r + 1, projectLast P, representsN_projectLast P S hP⟩

/-- The graph of `Nat.pair` is `DiophN`. -/
theorem aux_diophN_pairPolySet : DiophN {v : Fin 3 → ℕ | v 2 = Nat.pair (v 0) (v 1)} :=
  ⟨1, pairPoly, representsN_pairPoly⟩

theorem diophN_graph_code (n : ℕ) : DiophN (graph (code (n := n))) := by
  induction n with
  | zero =>
    refine ⟨0, X (Sum.inl 0), fun v => ?_⟩
    have hc : code (Fin.init v) = 0 := rfl
    have hl : v (Fin.last 0) = v 0 := rfl
    simp only [graph, Set.mem_setOf_eq, hc, evalAt, eval_X, Sum.elim_inl]
    rw [hl]
    constructor
    · intro h; exact ⟨fun i => i.elim0, by rw [h]; rfl⟩
    · rintro ⟨y, hy⟩; exact_mod_cast hy
  | succ n ih =>
    let g1 : Fin (n+1) → Fin (n+3) :=
      Fin.lastCases (Fin.last (n+2)) (fun j => Fin.castSucc (Fin.castSucc (Fin.castSucc j)))
    let g2 : Fin 3 → Fin (n+3) := ![Fin.last (n+2),
        Fin.castSucc (Fin.castSucc (Fin.last n)),
        Fin.castSucc (Fin.last (n+1))]
    have hC1 : DiophN {V : Fin (n+3) → ℕ | (fun i => V (g1 i)) ∈ graph (code (n:=n))} :=
      aux_diophN_pullback g1 ih
    have hC2 : DiophN {V : Fin (n+3) → ℕ |
        (fun i => V (g2 i)) ∈ {t : Fin 3 → ℕ | t 2 = Nat.pair (t 0) (t 1)}} :=
      aux_diophN_pullback g2 aux_diophN_pairPolySet
    have hProj := aux_diophN_projectLast _ (aux_diophN_conj hC1 hC2)
    refine aux_diophN_congr ?_ hProj
    ext v
    have e1 : ∀ c : ℕ, (fun i => (Fin.snoc v c : Fin (n+3) → ℕ) (g1 i))
        = (Fin.snoc (Fin.init (Fin.init v)) c : Fin (n+1) → ℕ) := by
      intro c; funext i
      induction i using Fin.lastCases with
      | last => simp only [g1, Fin.lastCases_last, Fin.snoc_last]
      | cast j => simp only [g1, Fin.lastCases_castSucc, Fin.snoc_castSucc, Fin.init]
    have e2a : ∀ c : ℕ, (Fin.snoc v c : Fin (n+3) → ℕ) (g2 0) = c := by
      intro c; simp only [g2, Matrix.cons_val_zero, Fin.snoc_last]
    have e2b : ∀ c : ℕ, (Fin.snoc v c : Fin (n+3) → ℕ) (g2 1) = v (Fin.castSucc (Fin.last n)) := by
      intro c
      simp only [g2, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.snoc_castSucc]
    have e2c : ∀ c : ℕ, (Fin.snoc v c : Fin (n+3) → ℕ) (g2 2) = v (Fin.last (n+1)) := by
      intro c
      simp only [g2, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Fin.snoc_castSucc]
    have hcode : code (Fin.init v)
        = Nat.pair (code (Fin.init (Fin.init v))) (v (Fin.castSucc (Fin.last n))) := rfl
    constructor
    · intro h
      obtain ⟨c, hc⟩ := h
      rw [Set.mem_inter_iff] at hc
      obtain ⟨hc1, hc2⟩ := hc
      simp only [Set.mem_setOf_eq] at hc1 hc2
      rw [e1] at hc1
      simp only [graph, Set.mem_setOf_eq, Fin.snoc_last, Fin.init_snoc] at hc1
      simp only [e2a, e2b, e2c] at hc2
      show v (Fin.last (n+1)) = code (Fin.init v)
      rw [hc2, hc1, hcode]
    · intro hv
      replace hv : v (Fin.last (n+1)) = code (Fin.init v) := hv
      refine ⟨code (Fin.init (Fin.init v)), ?_⟩
      rw [Set.mem_inter_iff]
      constructor
      · simp only [Set.mem_setOf_eq]
        rw [e1]
        simp only [graph, Set.mem_setOf_eq, Fin.snoc_last, Fin.init_snoc]
      · simp only [Set.mem_setOf_eq, e2a, e2b, e2c]
        rw [hv, hcode]

/-! ### The two directions with explicit constants -/

/-- Represent a set on `Fin K` obtained by pulling back the parameters of `P` along `g`. -/
theorem aux_representsN_renameParams {k K r : ℕ} (g : Fin k → Fin K) (P : Poly k r)
    (S : Set (Fin k → ℕ)) (h : RepresentsN P S) :
    RepresentsN (rename (Sum.map g id) P) {V : Fin K → ℕ | (fun i => V (g i)) ∈ S} := by
  intro V
  simp only [Set.mem_setOf_eq]
  rw [h (fun i => V (g i))]
  refine exists_congr (fun y => ?_)
  have key : evalAt (rename (Sum.map g id) P) V (fun i => (y i : ℤ))
      = evalAt P (fun i => V (g i)) (fun i => (y i : ℤ)) := by
    simp only [evalAt, eval_rename]
    refine congrArg (fun h => (eval h) P) ?_; funext w; cases w <;> rfl
  rw [key]

theorem multiUniversal_of_coder {ν δ r d : ℕ} (hU : UniversalPairN ν δ) (hC : TupleCoderN r d) :
    MultiUniversalN (fun _ => r + 1 + ν) (fun _ => 2 * max d δ) := by
  intro n A hA
  obtain ⟨e, he, r', hr', C, hCd, hCrep⟩ := hC n
  obtain ⟨rA, PA, hPArep⟩ := hA
  have hA'rep : RepresentsN (weakenParams 1 PA)
      {v : Fin (n+1) → ℕ | (fun i => v (Fin.castAdd 1 i)) ∈ A} :=
    representsN_weakenParams PA A hPArep
  have hSrep := representsN_conj C (weakenParams 1 PA) (graph e)
    {v : Fin (n+1) → ℕ | (fun i => v (Fin.castAdd 1 i)) ∈ A} hCrep hA'rep
  have hSdioph : DiophN (graph e ∩ {v : Fin (n+1) → ℕ | (fun i => v (Fin.castAdd 1 i)) ∈ A}) :=
    ⟨_, _, hSrep⟩
  have hBdioph := diophN_projectBlock _ hSdioph
  obtain ⟨ν'', hν'', PB, hPBd, hPBrep⟩ := hU _ hBdioph
  let g : Fin 1 → Fin (n+1) := fun _ => Fin.last n
  have hPB'rep := aux_representsN_renameParams g PB _ hPBrep
  have hConjrep := representsN_conj C (rename (Sum.map g id) PB) (graph e)
    {V : Fin (n+1) → ℕ | (fun i => V (g i)) ∈
      {c : Fin 1 → ℕ | ∃ a : Fin n → ℕ, Fin.append a c ∈
        graph e ∩ {v : Fin (n+1) → ℕ | (fun i => v (Fin.castAdd 1 i)) ∈ A}}}
    hCrep hPB'rep
  have hDrep := representsN_projectLast (conj C (rename (Sum.map g id) PB)) _ hConjrep
  have initA : ∀ (w : Fin n → ℕ) (x : ℕ),
      (fun i => (Fin.snoc w x : Fin (n+1) → ℕ) (Fin.castAdd 1 i)) = w := by
    intro w x; funext i; exact Fin.snoc_castSucc (α := fun _ => ℕ) x w i
  have hset : {a : Fin n → ℕ | ∃ cc, Fin.snoc a cc ∈
      (graph e ∩ {V : Fin (n+1) → ℕ | (fun i => V (g i)) ∈
        {c : Fin 1 → ℕ | ∃ a : Fin n → ℕ, Fin.append a c ∈
          graph e ∩ {v : Fin (n+1) → ℕ | (fun i => v (Fin.castAdd 1 i)) ∈ A}}})} = A := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨cc, hg, hb⟩
      simp only [graph, Set.mem_setOf_eq, Fin.snoc_last, Fin.init_snoc] at hg
      simp only [g, Fin.snoc_last] at hb
      obtain ⟨a', hab⟩ := hb
      rw [Fin.append_right_eq_snoc] at hab
      simp only [graph, Set.mem_setOf_eq, Fin.snoc_last, Fin.init_snoc] at hab
      obtain ⟨hc', haA⟩ := hab
      rw [initA a' cc] at haA
      have : a = a' := he (by rw [← hg, ← hc'])
      rw [this]; exact haA
    · intro ha
      refine ⟨e a, ?_, ?_⟩
      · simp only [graph, Set.mem_setOf_eq, Fin.snoc_last, Fin.init_snoc]
      · simp only [g, Fin.snoc_last]
        refine ⟨a, ?_⟩
        rw [Fin.append_right_eq_snoc]
        refine ⟨?_, ?_⟩
        · simp only [graph, Set.mem_setOf_eq, Fin.snoc_last, Fin.init_snoc]
        · rw [initA a (e a)]; exact ha
  rw [hset] at hDrep
  refine ⟨r' + ν'' + 1, ?_, projectLast (conj C (rename (Sum.map g id) PB)), ?_, hDrep⟩
  · show r' + ν'' + 1 ≤ r + 1 + ν; omega
  · refine (totalDegree_projectLast_le _).trans ?_
    refine (totalDegree_conj_le _ _).trans ?_
    have h1 : C.totalDegree ≤ d := hCd
    have h2 : (rename (Sum.map g id) PB).totalDegree ≤ δ := (totalDegree_rename_le _ _).trans hPBd
    exact Nat.mul_le_mul (le_refl 2) (max_le_max h1 h2)

theorem coder_to_MPUP_N : Arch_coder_to_MPUP_N := by
  rintro ⟨ν, δ, hU⟩ ⟨r, d, hC⟩
  exact ⟨_, _, multiUniversal_of_coder hU hC⟩

theorem coder_of_multiUniversal {ν δ : ℕ} (h : MultiUniversalN (fun _ => ν) (fun _ => δ)) :
    TupleCoderN ν δ := by
  intro n
  exact ⟨code, code_injective n, h (n + 1) _ (diophN_graph_code n)⟩

theorem MPUP_to_coder_N : Arch_MPUP_to_coder_N := by
  rintro ⟨ν, δ, h⟩
  exact ⟨ν, δ, coder_of_multiUniversal h⟩

end MPUP

#print axioms MPUP.coder_to_MPUP_N
#print axioms MPUP.MPUP_to_coder_N
