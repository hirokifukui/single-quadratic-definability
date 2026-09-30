/-
  DiophCompression/TreeCoding.lean — r04 Task 7 (session 4, 2026-08-26, claude.ai direct).
  Statements frozen as the session-4 draft (md5 3a21f7c9); proofs filled the same session; std-3.
  Design (session-4 decision, ruled "proceed"): a CHAIN of Skolem gates instead of a complete b-ary
  tree. Gate arity β+1: input = (previous output, β fresh leaves); r witnesses = the r intermediate
  outputs; the last output is the code c. Leaves = 1 + (r+1)β = (b−1)(r+1)+1 for b = β+1 — the same
  count as GPT's complete-tree formula, with one-dimensional indexing. Total degree 2(β+1) = 2b.
-/
import DiophCompression.SkolemTupling
import DiophCompression.Definitions

namespace DiophCompression

open MvPolynomial MPUP

section Chain
variable (r β : ℕ)

/-- ℕ-valued gate: T(prev, block) = (β+1)!·skolem. -/
def gateN (prev : ℕ) (blk : Fin β → ℕ) : ℕ :=
  (β + 1).factorial * skolem (Fin.cons prev blk : Fin (β + 1) → ℕ)

theorem gateN_injective : Function.Injective (fun pb : ℕ × (Fin β → ℕ) => gateN β pb.1 pb.2) := by
  rintro ⟨p, b⟩ ⟨p', b'⟩ h
  simp only [gateN] at h
  have h1 := skolem_injective (Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos _) h)
  obtain ⟨hp, hb⟩ := Fin.cons_injective2 h1
  simp only [hp, hb]

/-- Chain values: output of gate i (blocks indexed by ℕ, extended arbitrarily). -/
def chainN (a0 : ℕ) (blk : ℕ → Fin β → ℕ) : ℕ → ℕ
  | 0 => gateN β a0 (blk 0)
  | i + 1 => gateN β (chainN a0 blk i) (blk (i + 1))

/-- Leaf index type: one seed leaf and (r+1) blocks of β leaves. -/
abbrev LeafIdx := Fin 1 ⊕ (Fin (r + 1) × Fin β)

def leafCount : ℕ := 1 + (r + 1) * β

def leafEquiv : LeafIdx r β ≃ Fin (leafCount r β) :=
  (Equiv.sumCongr (Equiv.refl (Fin 1)) finProdFinEquiv).trans finSumFinEquiv

/-- The chain coder e : ℕ^{leafCount} → ℕ. -/
def chainCode (a : Fin (leafCount r β) → ℕ) : ℕ :=
  chainN β (a ((leafEquiv r β) (Sum.inl 0)))
    (fun i j => if h : i < r + 1 then a ((leafEquiv r β) (Sum.inr (⟨i, h⟩, j))) else 0) r

theorem chainN_inj_aux (a0 a0' : ℕ) (blk blk' : ℕ → Fin β → ℕ) :
    ∀ i, chainN β a0 blk i = chainN β a0' blk' i → a0 = a0' ∧ ∀ j ≤ i, blk j = blk' j := by
  intro i
  induction i with
  | zero =>
    intro h
    have := gateN_injective β (a₁ := (a0, blk 0)) (a₂ := (a0', blk' 0))
      (show (fun pb : ℕ × (Fin β → ℕ) => gateN β pb.1 pb.2) (a0, blk 0)
        = (fun pb : ℕ × (Fin β → ℕ) => gateN β pb.1 pb.2) (a0', blk' 0) from h)
    simp only [Prod.mk.injEq] at this
    exact ⟨this.1, fun j hj => by rw [Nat.le_zero.1 hj]; exact this.2⟩
  | succ i ih =>
    intro h
    have := gateN_injective β (a₁ := (chainN β a0 blk i, blk (i + 1)))
      (a₂ := (chainN β a0' blk' i, blk' (i + 1)))
      (show (fun pb : ℕ × (Fin β → ℕ) => gateN β pb.1 pb.2) (chainN β a0 blk i, blk (i + 1))
        = (fun pb : ℕ × (Fin β → ℕ) => gateN β pb.1 pb.2) (chainN β a0' blk' i, blk' (i + 1)) from h)
    simp only [Prod.mk.injEq] at this
    obtain ⟨h0, hj⟩ := ih this.1
    refine ⟨h0, fun j hj' => ?_⟩
    rcases Nat.lt_or_ge j (i + 1) with hlt | hge
    · exact hj j (by omega)
    · rw [show j = i + 1 by omega]; exact this.2

theorem chainCode_injective : Function.Injective (chainCode r β) := by
  intro a a' h
  unfold chainCode at h
  obtain ⟨h0, hb⟩ := chainN_inj_aux β _ _ _ _ r h
  funext v
  obtain ⟨ℓ, rfl⟩ := (leafEquiv r β).surjective v
  cases ℓ with
  | inl z =>
    have hz : z = 0 := Subsingleton.elim _ _
    subst hz; exact h0
  | inr ij =>
    obtain ⟨i, j⟩ := ij
    have := congrFun (hb i (by omega)) j
    simp only [i.isLt, dif_pos] at this
    exact this

/-! ### The Diophantine representation (variables: Fin (leafCount+1) ⊕ Fin r; inl last = c). -/

abbrev Var := Fin (leafCount r β + 1) ⊕ Fin r

def leafVar (ℓ : LeafIdx r β) : Var r β := Sum.inl (Fin.castSucc ((leafEquiv r β) ℓ))
def cVar : Var r β := Sum.inl (Fin.last _)
/-- Output variable of gate i: witness u_i for i < r, the code c for i = r. -/
def outVar (i : Fin (r + 1)) : Var r β :=
  if h : (i : ℕ) < r then Sum.inr ⟨i, h⟩ else cVar r β
/-- Input "previous" variable of gate i. -/
def prevVar (i : Fin (r + 1)) : Var r β :=
  if h : (i : ℕ) = 0 then leafVar r β (Sum.inl 0) else outVar r β ⟨i - 1, by omega⟩

/-- Gate polynomial i = T(prevVar i, block i) as a polynomial in the chain variables. -/
noncomputable def gatePoly (i : Fin (r + 1)) : MvPolynomial (Var r β) ℤ :=
  rename (Fin.cons (prevVar r β i) (fun j => leafVar r β (Sum.inr (i, j))) : Fin (β + 1) → Var r β)
    (skolemPoly (β + 1))

/-- The chain polynomial: Σ_i (X(out_i) − gate_i)². -/
noncomputable def chainPoly : Poly (leafCount r β + 1) r :=
  ∑ i : Fin (r + 1), (X (outVar r β i) - gatePoly r β i) ^ 2

theorem gatePoly_totalDegree (i : Fin (r + 1)) : (gatePoly r β i).totalDegree ≤ β + 1 :=
  le_trans (totalDegree_rename_le _ _) (skolemPoly_totalDegree _)

theorem chainPoly_totalDegree : (chainPoly r β).totalDegree ≤ 2 * (β + 1) := by
  unfold chainPoly
  refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le ?_)
  intro i _
  refine le_trans (totalDegree_pow _ _) ?_
  apply Nat.mul_le_mul_left
  refine le_trans (totalDegree_sub _ _) (max_le ?_ (gatePoly_totalDegree r β i))
  rw [totalDegree_X]; omega

/-! ### Evaluation of the chain polynomial -/

/-- The valuation of the chain variables at parameters `v` and unknowns `y`. -/
def val (v : Fin (leafCount r β + 1) → ℕ) (y : Fin r → ℤ) : Var r β → ℤ :=
  Sum.elim (fun i => (v i : ℤ)) y

theorem val_leafVar (v : Fin (leafCount r β + 1) → ℕ) (y : Fin r → ℤ) (ℓ : LeafIdx r β) :
    val r β v y (leafVar r β ℓ) = (Fin.init v ((leafEquiv r β) ℓ) : ℤ) := rfl

theorem outVar_castSucc (i : Fin r) : outVar r β i.castSucc = Sum.inr i := by
  simp [outVar, i.isLt]

theorem outVar_last : outVar r β (Fin.last r) = cVar r β := by
  simp [outVar]

theorem prevVar_zero : prevVar r β 0 = leafVar r β (Sum.inl 0) := by
  simp [prevVar]

theorem prevVar_succ (i : Fin r) : prevVar r β i.succ = outVar r β i.castSucc := by
  simp only [prevVar, Fin.val_succ, Nat.add_one_ne_zero, dite_false]
  congr 1

/-- Leaf data extracted from the parameter vector. -/
def seed (v : Fin (leafCount r β + 1) → ℕ) : ℕ := Fin.init v ((leafEquiv r β) (Sum.inl 0))
def blocks (v : Fin (leafCount r β + 1) → ℕ) : ℕ → Fin β → ℕ :=
  fun i j => if h : i < r + 1 then Fin.init v ((leafEquiv r β) (Sum.inr (⟨i, h⟩, j))) else 0

theorem chainCode_init (v : Fin (leafCount r β + 1) → ℕ) :
    chainCode r β (Fin.init v) = chainN β (seed r β v) (blocks r β v) r := rfl

/-- Gate evaluation when the previous input is a natural number. -/
theorem eval_gatePoly (v : Fin (leafCount r β + 1) → ℕ) (y : Fin r → ℤ) (i : Fin (r + 1)) (p : ℕ)
    (hp : val r β v y (prevVar r β i) = (p : ℤ)) :
    eval (val r β v y) (gatePoly r β i) = ((gateN β p (blocks r β v i) : ℕ) : ℤ) := by
  unfold gatePoly gateN
  rw [eval_rename]
  have hfun : (val r β v y ∘ (Fin.cons (prevVar r β i) (fun j => leafVar r β (Sum.inr (i, j)))
      : Fin (β + 1) → Var r β)) = fun k => ((Fin.cons p (blocks r β v i) : Fin (β + 1) → ℕ) k : ℤ) := by
    funext k
    refine Fin.cases ?_ ?_ k
    · simp only [Function.comp, Fin.cons_zero]; exact hp
    · intro j
      simp only [Function.comp, Fin.cons_succ, val_leafVar, blocks, i.isLt, dif_pos]
  rw [hfun, eval_skolemPoly]

theorem evalAt_chainPoly (v : Fin (leafCount r β + 1) → ℕ) (y : Fin r → ℤ) :
    evalAt (chainPoly r β) v y
      = ∑ i : Fin (r + 1), (val r β v y (outVar r β i) - eval (val r β v y) (gatePoly r β i)) ^ 2 := by
  unfold evalAt chainPoly
  simp only [map_sum, map_pow, map_sub, eval_X]
  rfl

theorem evalAt_chainPoly_eq_zero_iff (v : Fin (leafCount r β + 1) → ℕ) (y : Fin r → ℤ) :
    evalAt (chainPoly r β) v y = 0
      ↔ ∀ i : Fin (r + 1), val r β v y (outVar r β i) = eval (val r β v y) (gatePoly r β i) := by
  rw [evalAt_chainPoly, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  constructor
  · intro h i; have := h i (Finset.mem_univ i); rw [sq_eq_zero_iff] at this; linarith
  · intro h i _; rw [h i]; ring

/-- The chain equations determine every output as the chain value. -/
theorem chain_forced (v : Fin (leafCount r β + 1) → ℕ) (y : Fin r → ℤ)
    (h : ∀ i : Fin (r + 1), val r β v y (outVar r β i) = eval (val r β v y) (gatePoly r β i)) :
    ∀ i : Fin (r + 1), val r β v y (outVar r β i) = ((chainN β (seed r β v) (blocks r β v) i : ℕ) : ℤ) := by
  intro i
  induction i using Fin.induction with
  | zero =>
    rw [h 0, eval_gatePoly r β v y 0 (seed r β v) (by rw [prevVar_zero]; rfl)]
    rfl
  | succ i ih =>
    rw [h i.succ, eval_gatePoly r β v y i.succ _ (by rw [prevVar_succ]; exact ih)]
    rfl

theorem chain_sol_iff (v : Fin (leafCount r β + 1) → ℕ) (y : Fin r → ℤ) :
    (∀ i : Fin (r + 1), val r β v y (outVar r β i) = eval (val r β v y) (gatePoly r β i))
      ↔ (∀ i : Fin r, y i = ((chainN β (seed r β v) (blocks r β v) i : ℕ) : ℤ))
          ∧ (v (Fin.last _) : ℤ) = ((chainN β (seed r β v) (blocks r β v) r : ℕ) : ℤ) := by
  constructor
  · intro h
    have hf := chain_forced r β v y h
    refine ⟨fun i => ?_, ?_⟩
    · have := hf i.castSucc; rw [outVar_castSucc] at this; exact this
    · have := hf (Fin.last r); rw [outVar_last] at this; exact this
  · rintro ⟨hy, hl⟩ i
    -- every output equals the chain value
    have hout : ∀ i : Fin (r + 1),
        val r β v y (outVar r β i) = ((chainN β (seed r β v) (blocks r β v) i : ℕ) : ℤ) := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [outVar_last]; exact hl
      · intro j; rw [outVar_castSucc]; exact hy j
    refine Fin.cases ?_ ?_ i
    · rw [hout 0, eval_gatePoly r β v y 0 (seed r β v) (by rw [prevVar_zero]; rfl)]; rfl
    · intro j
      rw [hout j.succ, eval_gatePoly r β v y j.succ _ (by rw [prevVar_succ]; exact hout j.castSucc)]
      rfl

theorem chainPoly_representsZ : RepresentsZ (chainPoly r β) (graph (chainCode r β)) := by
  intro v
  constructor
  · intro hv
    have hv' : v (Fin.last _) = chainCode r β (Fin.init v) := hv
    refine ⟨fun i => ((chainN β (seed r β v) (blocks r β v) i : ℕ) : ℤ), ?_⟩
    rw [evalAt_chainPoly_eq_zero_iff, chain_sol_iff]
    exact ⟨fun i => rfl, by rw [hv', chainCode_init]⟩
  · rintro ⟨y, hy⟩
    rw [evalAt_chainPoly_eq_zero_iff, chain_sol_iff] at hy
    show v (Fin.last _) = chainCode r β (Fin.init v)
    rw [chainCode_init]
    exact_mod_cast hy.2

theorem chainPoly_representsN : RepresentsN (chainPoly r β) (graph (chainCode r β)) := by
  intro v
  constructor
  · intro hv
    have hv' : v (Fin.last _) = chainCode r β (Fin.init v) := hv
    refine ⟨fun i => chainN β (seed r β v) (blocks r β v) i, ?_⟩
    rw [evalAt_chainPoly_eq_zero_iff, chain_sol_iff]
    exact ⟨fun i => rfl, by rw [hv', chainCode_init]⟩
  · rintro ⟨y, hy⟩
    rw [evalAt_chainPoly_eq_zero_iff, chain_sol_iff] at hy
    show v (Fin.last _) = chainCode r β (Fin.init v)
    rw [chainCode_init]
    exact_mod_cast hy.2

/-- TREE (CHAIN) CODING LOWER BOUND, ℕ-witnesses: G_ℕ(r, 2(β+1)) ≥ 1 + (r+1)β. -/
theorem chain_graph_achievable_N : GraphAchievableN (leafCount r β) r (2 * (β + 1)) :=
  ⟨chainCode r β, chainCode_injective r β, r, le_rfl, chainPoly r β, chainPoly_totalDegree r β,
    chainPoly_representsN r β⟩

theorem chain_graph_achievable_Z : GraphAchievableZ (leafCount r β) r (2 * (β + 1)) :=
  ⟨chainCode r β, chainCode_injective r β, r, le_rfl, chainPoly r β, chainPoly_totalDegree r β,
    chainPoly_representsZ r β⟩

end Chain

/-- GPT r03 Task 7 form: for b ≥ 1, G_ℕ(r, 2b) ≥ (b−1)(r+1)+1. -/
theorem graph_achievable_tree_form (r b : ℕ) (hb : 1 ≤ b) :
    GraphAchievableN ((b - 1) * (r + 1) + 1) r (2 * b) := by
  have h := chain_graph_achievable_N r (b - 1)
  rw [show 2 * (b - 1 + 1) = 2 * b by omega] at h
  rw [show (b - 1) * (r + 1) + 1 = leafCount r (b - 1) by unfold leafCount; ring]
  exact h

end DiophCompression

#print axioms DiophCompression.chain_graph_achievable_N
#print axioms DiophCompression.chain_graph_achievable_Z
#print axioms DiophCompression.graph_achievable_tree_form
