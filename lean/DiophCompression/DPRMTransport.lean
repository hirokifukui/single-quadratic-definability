/-
  DiophCompression/DPRMTransport.lean — APAL Structural Theory Gate 3, 必須B (DPRM over ℕ ⇒ DPRM over ℤ)
  (session 26, 2026-09-01, claude.ai direct). Statements frozen in frozen_statements/DPRMTransport_STATEMENTS.lean.

  The paper's hypothesis `DPRM_ZZ` (every r.e. relation on ℤᵏ is Diophantine with integer unknowns) is
  derived here from the classical form `DPRM_NN` (Davis–Putnam–Robinson–Matiyasevich 1970: every r.e.
  relation on ℕᵏ is `{a | ∃ y ∈ ℕˢ, P(a, y) = 0}` for an integer-coefficient polynomial P). Transport:
    A ⊆ ℤᵏ r.e.  ⇒  A' := {b ∈ ℕ^{k+k} | (b_i − b_{k+i})_i ∈ A} r.e. (composition with the computable
    difference map)  ⇒  A' = {b | ∃ y ∈ ℕˢ, P(b, y) = 0}  ⇒  a ∈ A ⟺ ∃ integers p, q ∈ ℤᵏ, y ∈ ℤˢ and
    w ∈ ℤ^{(2k+s)×4} with a = p − q, P(p, q, y) = 0 and each of p, q, y a sum of four squares of the w's
    (Lagrange; mathlib `Nat.sum_four_squares`). The single equation is the sum of squares of these
    conditions. Witness arity of the ℤ-representation: 5(2k+s) (transportWitnessArity); total degree
    ≤ max(2·deg P, 4) (transportPoly_totalDegree_le, kernel theorem since s27 / Gate 4 必須D;
    dprmTransport_resource_bound bundles arity and degree). No sorry; std-3. Only `DPRM_NN` is external.
-/
import DiophCompression.ComputabilityFragments
import DiophCompression.IntPrimrec
import Mathlib.NumberTheory.SumFourSquares

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Diophantine relations over ℕ and the classical DPRM hypothesis -/

/-- Evaluation of an integer polynomial at NATURAL parameters and NATURAL unknowns. -/
noncomputable def evalAtNN {k s : ℕ} (P : Poly k s) (a : Fin k → ℕ) (y : Fin s → ℕ) : ℤ :=
  eval (Sum.elim (fun i => (a i : ℤ)) (fun j => (y j : ℤ))) P

/-- `A ⊆ ℕᵏ` is Diophantine over ℕ: an integer-coefficient polynomial with natural unknowns. -/
def WithinDiophNN {k : ℕ} (A : Set (Fin k → ℕ)) : Prop :=
  ∃ s : ℕ, ∃ P : Poly k s, ∀ a, a ∈ A ↔ ∃ y : Fin s → ℕ, evalAtNN P a y = 0

/-- External hypothesis: the DPRM theorem over ℕ. -/
def DPRM_NN : Prop := ∀ (k : ℕ) (A : Set (Fin k → ℕ)), REPred (fun a => a ∈ A) → WithinDiophNN A

/-! ### The difference map and r.e. transport -/

/-- `b ↦ (b_i − b_{k+i})_i : ℕ^{k+k} → ℤᵏ`. -/
def diffMapZZ (k : ℕ) (b : Fin (k + k) → ℕ) : Fin k → ℤ :=
  fun i => (b (Fin.castAdd k i) : ℤ) - (b (Fin.natAdd k i) : ℤ)

theorem primrec_natCastInt : Primrec fun n : ℕ => (n : ℤ) :=
  (primrec_intOfS.comp Primrec.sumInl).of_eq fun _ => rfl

theorem primrec_int_neg : Primrec fun z : ℤ => -z :=
  (primrec₂_int_mul.comp (Primrec.const (-1)) Primrec.id).of_eq fun z => by simp

theorem primrec₂_int_sub : Primrec₂ ((· - ·) : ℤ → ℤ → ℤ) :=
  (primrec₂_int_add.comp Primrec.fst (primrec_int_neg.comp Primrec.snd)).of_eq fun p => by
    simp [sub_eq_add_neg]

theorem primrec_diffMapZZ (k : ℕ) : Primrec (diffMapZZ k) := by
  unfold diffMapZZ
  refine Primrec.fin_curry.2 ?_
  have hc : Primrec fun p : (Fin (k + k) → ℕ) × Fin k => Fin.castAdd k p.2 :=
    Primrec.fin_val_iff.1 ((Primrec.fin_val.comp Primrec.snd).of_eq fun _ => rfl)
  have hn : Primrec fun p : (Fin (k + k) → ℕ) × Fin k => Fin.natAdd k p.2 :=
    Primrec.fin_val_iff.1 ((Primrec.nat_add.comp (Primrec.const k) (Primrec.fin_val.comp Primrec.snd)).of_eq
      fun _ => rfl)
  exact primrec₂_int_sub.comp (primrec_natCastInt.comp (Primrec.fin_app.comp Primrec.fst hc))
    (primrec_natCastInt.comp (Primrec.fin_app.comp Primrec.fst hn))

theorem rePred_comp_computable {α β : Type} [Primcodable α] [Primcodable β] {p : β → Prop}
    (hp : REPred p) {f : α → β} (hf : Computable f) : REPred fun a => p (f a) :=
  Partrec.comp hp hf

/-- r.e. transport: the ℕ-preimage of an r.e. relation on ℤᵏ under the difference map is r.e. -/
theorem rePred_diffPreimage {k : ℕ} (A : Set (Fin k → ℤ)) (hA : REPred fun a => a ∈ A) :
    REPred fun b : Fin (k + k) → ℕ => diffMapZZ k b ∈ A :=
  rePred_comp_computable hA (primrec_diffMapZZ k).to_comp

/-! ### The transported polynomial -/

/-- Variable type of the transported equation: parameters `Fin k`; unknowns = the ℕ-unknowns
    `T = Fin (k+k) ⊕ Fin s` (p, q, y) and their four-square witnesses `T × Fin 4`. -/
abbrev TransportVars (k s : ℕ) : Type := (Fin (k + k) ⊕ Fin s) ⊕ ((Fin (k + k) ⊕ Fin s) × Fin 4)

/-- Number of integer unknowns of the transported equation: 5(2k + s). -/
def transportWitnessArity (k s : ℕ) : ℕ := Fintype.card (TransportVars k s)

theorem transportWitnessArity_eq (k s : ℕ) : transportWitnessArity k s = 5 * (k + k + s) := by
  unfold transportWitnessArity TransportVars
  simp [Fintype.card_sum, Fintype.card_prod]
  ring

/-- The transported polynomial in `MvPolynomial (Fin k ⊕ TransportVars k s) ℤ`:
    Σᵢ (aᵢ − pᵢ + qᵢ)² + P(p, q, y)² + Σ_t (t − Σₗ w_{t,l}²)². -/
noncomputable def transportPoly (k s : ℕ) (P : Poly (k + k) s) :
    MvPolynomial (Fin k ⊕ TransportVars k s) ℤ :=
  (∑ i : Fin k, (X (Sum.inl i) - X (Sum.inr (Sum.inl (Sum.inl (Fin.castAdd k i))))
      + X (Sum.inr (Sum.inl (Sum.inl (Fin.natAdd k i))))) ^ 2)
  + (rename (fun t => Sum.inr (Sum.inl t)) P) ^ 2
  + ∑ t : Fin (k + k) ⊕ Fin s, (X (Sum.inr (Sum.inl t)) - ∑ l : Fin 4, X (Sum.inr (Sum.inr (t, l))) ^ 2) ^ 2

theorem int_sum_sq_eq_zero_iff {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    ∑ i ∈ s, (f i) ^ 2 = 0 ↔ ∀ i ∈ s, f i = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  simp

/-- Zero set of the transported polynomial, coordinatewise. -/
theorem transportPoly_eval_eq_zero_iff (k s : ℕ) (P : Poly (k + k) s) (a : Fin k → ℤ)
    (w : TransportVars k s → ℤ) :
    eval (Sum.elim a w) (transportPoly k s P) = 0 ↔
      (∀ i, a i = w (Sum.inl (Sum.inl (Fin.castAdd k i))) - w (Sum.inl (Sum.inl (Fin.natAdd k i)))) ∧
      eval (fun t => w (Sum.inl t)) P = 0 ∧
      (∀ t, w (Sum.inl t) = ∑ l : Fin 4, (w (Sum.inr (t, l))) ^ 2) := by
  have hS1 : (0 : ℤ) ≤ ∑ i : Fin k, (a i - w (Sum.inl (Sum.inl (Fin.castAdd k i)))
      + w (Sum.inl (Sum.inl (Fin.natAdd k i)))) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS2 : (0 : ℤ) ≤ (eval (fun t => w (Sum.inl t)) P) ^ 2 := sq_nonneg _
  have hS3 : (0 : ℤ) ≤ ∑ t : Fin (k + k) ⊕ Fin s, (w (Sum.inl t) - ∑ l : Fin 4, (w (Sum.inr (t, l))) ^ 2) ^ 2 :=
    Finset.sum_nonneg fun t _ => sq_nonneg _
  have hev : eval (Sum.elim a w) (transportPoly k s P) =
      (∑ i : Fin k, (a i - w (Sum.inl (Sum.inl (Fin.castAdd k i))) + w (Sum.inl (Sum.inl (Fin.natAdd k i)))) ^ 2)
      + (eval (fun t => w (Sum.inl t)) P) ^ 2
      + ∑ t : Fin (k + k) ⊕ Fin s, (w (Sum.inl t) - ∑ l : Fin 4, (w (Sum.inr (t, l))) ^ 2) ^ 2 := by
    unfold transportPoly
    simp only [map_add, map_sum, map_pow, map_sub, eval_X, Sum.elim_inl, Sum.elim_inr, eval_rename]
    rfl
  rw [hev, add_eq_zero_iff_of_nonneg (add_nonneg hS1 hS2) hS3, add_eq_zero_iff_of_nonneg hS1 hS2,
    int_sum_sq_eq_zero_iff, int_sum_sq_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    sub_eq_zero]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨fun i => by have := h1 i; linarith, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨fun i => by have := h1 i; linarith, h2⟩, h3⟩

/-- Four-square witnesses for every natural number, as a `Fin 4`-indexed family. -/
theorem exists_fourSquares (n : ℕ) : ∃ f : Fin 4 → ℕ, ∑ l : Fin 4, (f l) ^ 2 = n := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  exact ⟨![a, b, c, d], by simp [Fin.sum_univ_four, h]⟩

/-- 必須B: DPRM over ℕ implies DPRM over ℤ. -/
theorem DPRM_ZZ_of_DPRM_NN (hN : DPRM_NN) : DPRM_ZZ := by
  intro k A hA
  obtain ⟨s, P, hP⟩ := hN (k + k) {b | diffMapZZ k b ∈ A} (rePred_diffPreimage A hA)
  choose fs hfs using exists_fourSquares
  -- the ℤ-representation: rename the transported polynomial to `Fin (transportWitnessArity k s)` unknowns
  let e : TransportVars k s ≃ Fin (transportWitnessArity k s) := Fintype.equivFin _
  refine ⟨transportWitnessArity k s, rename (Sum.map id e) (transportPoly k s P), fun a => ?_⟩
  have hev : ∀ z : Fin (transportWitnessArity k s) → ℤ,
      evalAtZZ (rename (Sum.map id e) (transportPoly k s P)) a z = eval (Sum.elim a (z ∘ e)) (transportPoly k s P) := by
    intro z
    unfold evalAtZZ
    rw [eval_rename]
    have : (Sum.elim a z ∘ Sum.map id e) = Sum.elim a (z ∘ e) := by
      funext v
      rcases v with i | t <;> rfl
    rw [this]
  -- reduce to unknowns indexed by TransportVars
  have hred : (∃ z : Fin (transportWitnessArity k s) → ℤ, evalAtZZ (rename (Sum.map id e) (transportPoly k s P)) a z = 0)
      ↔ ∃ w : TransportVars k s → ℤ, eval (Sum.elim a w) (transportPoly k s P) = 0 := by
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z ∘ e, by rw [← hev]; exact hz⟩
    · rintro ⟨w, hw⟩
      refine ⟨w ∘ e.symm, ?_⟩
      rw [hev]
      have : (w ∘ e.symm) ∘ e = w := by
        funext v
        simp
      rw [this]
      exact hw
  rw [hred]
  constructor
  · intro ha
    -- natural parts of a
    let b : Fin (k + k) → ℕ := Fin.addCases (fun i => (a i).toNat) (fun i => (-(a i)).toNat)
    have hb : diffMapZZ k b = a := by
      funext i
      simp only [diffMapZZ, b, Fin.addCases_left, Fin.addCases_right]
      exact Int.toNat_sub_toNat_neg (a i)
    have hbA : b ∈ {b | diffMapZZ k b ∈ A} := by
      show diffMapZZ k b ∈ A
      rw [hb]; exact ha
    obtain ⟨y, hy⟩ := (hP b).1 hbA
    let nt : Fin (k + k) ⊕ Fin s → ℕ := Sum.elim b y
    refine ⟨Sum.elim (fun t => (nt t : ℤ)) (fun tl : (Fin (k + k) ⊕ Fin s) × Fin 4 => (fs (nt tl.1) tl.2 : ℤ)), ?_⟩
    rw [transportPoly_eval_eq_zero_iff]
    refine ⟨fun i => ?_, ?_, fun t => ?_⟩
    · simp only [Sum.elim_inl, nt, b, Fin.addCases_left, Fin.addCases_right]
      exact (Int.toNat_sub_toNat_neg (a i)).symm
    · have : (fun t => Sum.elim (fun t => (nt t : ℤ))
          (fun tl : (Fin (k + k) ⊕ Fin s) × Fin 4 => (fs (nt tl.1) tl.2 : ℤ)) (Sum.inl t))
          = Sum.elim (fun i => (b i : ℤ)) (fun j => (y j : ℤ)) := by
        funext t; rcases t with i | j <;> rfl
      rw [this]
      exact hy
    · simp only [Sum.elim_inl, Sum.elim_inr]
      exact_mod_cast (hfs (nt t)).symm
  · rintro ⟨w, hw⟩
    rw [transportPoly_eval_eq_zero_iff] at hw
    obtain ⟨h1, h2, h3⟩ := hw
    have hnn : ∀ t, 0 ≤ w (Sum.inl t) := fun t => by rw [h3 t]; exact Finset.sum_nonneg fun l _ => sq_nonneg _
    let nt : Fin (k + k) ⊕ Fin s → ℕ := fun t => (w (Sum.inl t)).toNat
    have hnt : ∀ t, (nt t : ℤ) = w (Sum.inl t) := fun t => Int.toNat_of_nonneg (hnn t)
    let b : Fin (k + k) → ℕ := fun i => nt (Sum.inl i)
    let y : Fin s → ℕ := fun j => nt (Sum.inr j)
    have hbA : b ∈ {b | diffMapZZ k b ∈ A} := by
      refine (hP b).2 ⟨y, ?_⟩
      unfold evalAtNN
      have : Sum.elim (fun i => (b i : ℤ)) (fun j => (y j : ℤ)) = fun t => w (Sum.inl t) := by
        funext t; rcases t with i | j <;> exact hnt _
      rw [this]; exact h2
    have hb : diffMapZZ k b = a := by
      funext i
      simp only [diffMapZZ, b, hnt]
      exact (h1 i).symm
    have := hbA
    simp only [Set.mem_setOf_eq, hb] at this
    exact this

/-! ### 必須D (Gate 4): degree resource of the transport -/

theorem totalDegree_neg_eq {σ : Type} (p : MvPolynomial σ ℤ) : (-p).totalDegree = p.totalDegree := by
  simp [totalDegree, support_neg]

theorem totalDegree_sub_le' {σ : Type} (p q : MvPolynomial σ ℤ) :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  rw [sub_eq_add_neg]
  exact (totalDegree_add _ _).trans (by rw [totalDegree_neg_eq])

/-- 必須D (Gate 4): total degree of the transported polynomial is at most `max (2·deg P) 4`. -/
theorem transportPoly_totalDegree_le (k s : ℕ) (P : Poly (k + k) s) :
    (transportPoly k s P).totalDegree ≤ max (2 * P.totalDegree) 4 := by
  unfold transportPoly
  have hX : ∀ v : Fin k ⊕ TransportVars k s, (X v : MvPolynomial (Fin k ⊕ TransportVars k s) ℤ).totalDegree = 1 :=
    fun v => totalDegree_X v
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le ?h1 ?h2)) ?h3)
  · -- Σ (a_i − p_i + q_i)²
    refine le_max_of_le_right (le_trans ?_ (by norm_num : (2:ℕ) ≤ 4))
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
    refine (totalDegree_pow _ 2).trans ?_
    have h : (X (Sum.inl i) - X (Sum.inr (Sum.inl (Sum.inl (Fin.castAdd k i))))
        + X (Sum.inr (Sum.inl (Sum.inl (Fin.natAdd k i)))) :
        MvPolynomial (Fin k ⊕ TransportVars k s) ℤ).totalDegree ≤ 1 := by
      refine (totalDegree_add _ _).trans (max_le ?_ (by rw [hX]))
      exact (totalDegree_sub_le' _ _).trans (max_le (by rw [hX]) (by rw [hX]))
    omega
  · -- (rename P)²
    refine le_max_of_le_left ?_
    refine (totalDegree_pow _ 2).trans ?_
    have := totalDegree_rename_le (fun t : Fin (k + k) ⊕ Fin s => (Sum.inr (Sum.inl t) : Fin k ⊕ TransportVars k s)) P
    omega
  · -- Σ (t − Σ w²)²
    refine le_max_of_le_right ?_
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun t _ => ?_)
    refine (totalDegree_pow _ 2).trans ?_
    have hsq : (∑ l : Fin 4, (X (Sum.inr (Sum.inr (t, l))) : MvPolynomial (Fin k ⊕ TransportVars k s) ℤ) ^ 2).totalDegree ≤ 2 := by
      refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
      refine (totalDegree_pow _ 2).trans ?_
      rw [hX]
    have h : (X (Sum.inr (Sum.inl t)) - ∑ l : Fin 4, (X (Sum.inr (Sum.inr (t, l))) :
        MvPolynomial (Fin k ⊕ TransportVars k s) ℤ) ^ 2).totalDegree ≤ 2 := by
      refine (totalDegree_sub_le' _ _).trans (max_le ?_ hsq)
      rw [hX]; norm_num
    omega

/-- 必須D (Gate 4): the resource summary of the transport — witness arity and total degree in one statement. -/
theorem dprmTransport_resource_bound (k s : ℕ) (P : Poly (k + k) s) :
    transportWitnessArity k s = 5 * (k + k + s) ∧
      (transportPoly k s P).totalDegree ≤ max (2 * P.totalDegree) 4 :=
  ⟨transportWitnessArity_eq k s, transportPoly_totalDegree_le k s P⟩


/-! ### 必須G (Gate 5): the resource bound on the FINAL representation polynomial -/

/-- Renaming never raises the total degree, so any renamed image of the transport polynomial
    (in particular the `Fin`-indexed representation actually produced by `DPRM_ZZ_of_DPRM_NN`)
    inherits the bound `max (2·deg P, 4)`. -/
theorem transportedRepresentation_totalDegree_le {k s : ℕ} {ι : Type} (P : Poly (k + k) s)
    (f : TransportVars k s → ι) :
    (rename (Sum.map (id : Fin k → Fin k) f) (transportPoly k s P)).totalDegree
      ≤ max (2 * P.totalDegree) 4 :=
  (totalDegree_rename_le _ _).trans (transportPoly_totalDegree_le k s P)

/-- 必須G (Gate 5): the transport delivers, for every r.e. `A ⊆ ℤᵏ`, a SINGLE integer polynomial in
    `5(2k+s)` unknowns defining `A`, whose total degree is bounded by `max (2·deg P, 4)` for the
    ℕ-side polynomial `P` supplied by DPRM. The bound is stated for the FINAL representation, not
    for the intermediate `transportPoly`. -/
theorem DPRM_ZZ_resource_bound_final (hN : DPRM_NN) {k : ℕ} (A : Set (Fin k → ℤ))
    (hA : REPred fun a => a ∈ A) :
    ∃ (s : ℕ) (P : Poly (k + k) s) (Q : Poly k (transportWitnessArity k s)),
      (∀ a : Fin k → ℤ, a ∈ A ↔ ∃ z : Fin (transportWitnessArity k s) → ℤ, evalAtZZ Q a z = 0)
      ∧ transportWitnessArity k s = 5 * (k + k + s)
      ∧ Q.totalDegree ≤ max (2 * P.totalDegree) 4 := by
  obtain ⟨s, P, hP⟩ := hN (k + k) {b | diffMapZZ k b ∈ A} (rePred_diffPreimage A hA)
  choose fs hfs using exists_fourSquares
  let e : TransportVars k s ≃ Fin (transportWitnessArity k s) := Fintype.equivFin _
  refine ⟨s, P, rename (Sum.map id e) (transportPoly k s P), fun a => ?_,
    transportWitnessArity_eq k s,
    transportedRepresentation_totalDegree_le P _⟩
  have hev : ∀ z : Fin (transportWitnessArity k s) → ℤ,
      evalAtZZ (rename (Sum.map id e) (transportPoly k s P)) a z = eval (Sum.elim a (z ∘ e)) (transportPoly k s P) := by
    intro z
    unfold evalAtZZ
    rw [eval_rename]
    have : (Sum.elim a z ∘ Sum.map id e) = Sum.elim a (z ∘ e) := by
      funext v
      rcases v with i | t <;> rfl
    rw [this]
  -- reduce to unknowns indexed by TransportVars
  have hred : (∃ z : Fin (transportWitnessArity k s) → ℤ, evalAtZZ (rename (Sum.map id e) (transportPoly k s P)) a z = 0)
      ↔ ∃ w : TransportVars k s → ℤ, eval (Sum.elim a w) (transportPoly k s P) = 0 := by
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z ∘ e, by rw [← hev]; exact hz⟩
    · rintro ⟨w, hw⟩
      refine ⟨w ∘ e.symm, ?_⟩
      rw [hev]
      have : (w ∘ e.symm) ∘ e = w := by
        funext v
        simp
      rw [this]
      exact hw
  rw [hred]
  constructor
  · intro ha
    -- natural parts of a
    let b : Fin (k + k) → ℕ := Fin.addCases (fun i => (a i).toNat) (fun i => (-(a i)).toNat)
    have hb : diffMapZZ k b = a := by
      funext i
      simp only [diffMapZZ, b, Fin.addCases_left, Fin.addCases_right]
      exact Int.toNat_sub_toNat_neg (a i)
    have hbA : b ∈ {b | diffMapZZ k b ∈ A} := by
      show diffMapZZ k b ∈ A
      rw [hb]; exact ha
    obtain ⟨y, hy⟩ := (hP b).1 hbA
    let nt : Fin (k + k) ⊕ Fin s → ℕ := Sum.elim b y
    refine ⟨Sum.elim (fun t => (nt t : ℤ)) (fun tl : (Fin (k + k) ⊕ Fin s) × Fin 4 => (fs (nt tl.1) tl.2 : ℤ)), ?_⟩
    rw [transportPoly_eval_eq_zero_iff]
    refine ⟨fun i => ?_, ?_, fun t => ?_⟩
    · simp only [Sum.elim_inl, nt, b, Fin.addCases_left, Fin.addCases_right]
      exact (Int.toNat_sub_toNat_neg (a i)).symm
    · have : (fun t => Sum.elim (fun t => (nt t : ℤ))
          (fun tl : (Fin (k + k) ⊕ Fin s) × Fin 4 => (fs (nt tl.1) tl.2 : ℤ)) (Sum.inl t))
          = Sum.elim (fun i => (b i : ℤ)) (fun j => (y j : ℤ)) := by
        funext t; rcases t with i | j <;> rfl
      rw [this]
      exact hy
    · simp only [Sum.elim_inl, Sum.elim_inr]
      exact_mod_cast (hfs (nt t)).symm
  · rintro ⟨w, hw⟩
    rw [transportPoly_eval_eq_zero_iff] at hw
    obtain ⟨h1, h2, h3⟩ := hw
    have hnn : ∀ t, 0 ≤ w (Sum.inl t) := fun t => by rw [h3 t]; exact Finset.sum_nonneg fun l _ => sq_nonneg _
    let nt : Fin (k + k) ⊕ Fin s → ℕ := fun t => (w (Sum.inl t)).toNat
    have hnt : ∀ t, (nt t : ℤ) = w (Sum.inl t) := fun t => Int.toNat_of_nonneg (hnn t)
    let b : Fin (k + k) → ℕ := fun i => nt (Sum.inl i)
    let y : Fin s → ℕ := fun j => nt (Sum.inr j)
    have hbA : b ∈ {b | diffMapZZ k b ∈ A} := by
      refine (hP b).2 ⟨y, ?_⟩
      unfold evalAtNN
      have : Sum.elim (fun i => (b i : ℤ)) (fun j => (y j : ℤ)) = fun t => w (Sum.inl t) := by
        funext t; rcases t with i | j <;> exact hnt _
      rw [this]; exact h2
    have hb : diffMapZZ k b = a := by
      funext i
      simp only [diffMapZZ, b, hnt]
      exact (h1 i).symm
    have := hbA
    simp only [Set.mem_setOf_eq, hb] at this
    exact this
end DiophCompression

#print axioms DiophCompression.rePred_diffPreimage
#print axioms DiophCompression.transportWitnessArity_eq
#print axioms DiophCompression.transportPoly_eval_eq_zero_iff
#print axioms DiophCompression.DPRM_ZZ_of_DPRM_NN
#print axioms DiophCompression.transportPoly_totalDegree_le
#print axioms DiophCompression.dprmTransport_resource_bound

#print axioms DiophCompression.transportedRepresentation_totalDegree_le
#print axioms DiophCompression.DPRM_ZZ_resource_bound_final