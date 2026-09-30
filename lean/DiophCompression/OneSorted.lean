/-
  DiophCompression/OneSorted.lean — APAL Logic Pivot, Gate 3 (session 20, 2026-08-31, claude.ai direct).
  Statements frozen in frozen_statements/OneSorted_STATEMENTS.lean (md5 bddcd486). See that header.
-/
import DiophCompression.QuadraticPPSeparation
import DiophCompression.SemanticQuadraticSingular.SingularAssembly
import DiophCompression.Folding

namespace DiophCompression

open MvPolynomial MPUP

/-! ### One-sorted definitions (verbatim from the freeze) -/

noncomputable def evalAtZZ {n r : ℕ} (P : Poly n r) (a : Fin n → ℤ) (y : Fin r → ℤ) : ℤ :=
  eval (Sum.elim a y) P

def RepresentsZZ {n r : ℕ} (P : Poly n r) (A : Set (Fin n → ℤ)) : Prop :=
  ∀ a, a ∈ A ↔ ∃ y : Fin r → ℤ, evalAtZZ P a y = 0

def graphZZ {n : ℕ} (e : (Fin n → ℤ) → ℤ) : Set (Fin (n + 1) → ℤ) :=
  {v | v (Fin.last n) = e (Fin.init v)}

def AtomGraphZZ (d n : ℕ) : Prop :=
  ∃ (r : ℕ) (e : (Fin n → ℤ) → ℤ), Function.Injective e ∧
    ∃ P : Poly (n + 1) r, P.totalDegree ≤ d ∧ RepresentsZZ P (graphZZ e)

def SystemRepresentsZZ {n r m : ℕ} (S : PolySystem n r m) (A : Set (Fin n → ℤ)) : Prop :=
  ∀ a, a ∈ A ↔ ∃ y : Fin r → ℤ, ∀ i, evalAtZZ (S i) a y = 0

def PPGraphZZ (d n : ℕ) : Prop :=
  ∃ (r m : ℕ) (e : (Fin n → ℤ) → ℤ), Function.Injective e ∧
    ∃ S : PolySystem (n + 1) r m, (∀ i, (S i).totalDegree ≤ d) ∧ SystemRepresentsZZ S (graphZZ e)

theorem evalAtZZ_natCast {n r : ℕ} (P : Poly n r) (a : Fin n → ℕ) (y : Fin r → ℤ) :
    evalAtZZ P (fun i => (a i : ℤ)) y = evalAt P a y := rfl

/-! ### Theorem E_ℤ: the core -/

open SemanticQuadraticGeneral in
theorem eval_relabelG_ZZ {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) (c : ℤ) (u : Fin r → ℤ) :
    eval (Sum.elim (Fin.cons c u) a) (rename (relabelG n r) P) = evalAtZZ P (Fin.snoc a c) u := by
  unfold evalAtZZ
  rw [eval_rename]
  refine congrArg (fun h => (eval h) P) ?_
  funext v
  rcases v with i | j
  · simp only [Function.comp_apply]
    induction i using Fin.lastCases with
    | last => simp [relabelG, Fin.snoc_last]
    | cast j => simp [relabelG, Fin.snoc_castSucc]
  · simp [relabelG]

theorem snoc_mem_graphZZ {n : ℕ} (e : (Fin n → ℤ) → ℤ) (a : Fin n → ℤ) (c : ℤ) :
    Fin.snoc a c ∈ graphZZ e ↔ c = e a := by
  simp only [graphZZ, Set.mem_setOf_eq, Fin.snoc_last, Fin.init_snoc]

/-- Sign flip of the output coordinate: `H⁻(x₀, x') = H(−x₀, x')`. -/
noncomputable def flipZero {k : ℕ} (H : MvPolynomial (Fin (k + 1)) ℤ) : MvPolynomial (Fin (k + 1)) ℤ :=
  eval₂ C (fun i => if i = 0 then -X 0 else X i) H

theorem flipZero_isHomogeneous {k : ℕ} (H : MvPolynomial (Fin (k + 1)) ℤ) (hH : H.IsHomogeneous 2) :
    (flipZero H).IsHomogeneous 2 := by
  have := hH.eval₂ C (fun i => if i = 0 then -X 0 else X i) (fun r => isHomogeneous_C _ _)
    (fun i => by
      split_ifs
      · exact (isHomogeneous_X _ _).neg
      · exact isHomogeneous_X _ _) (n := 1)
  unfold flipZero
  simpa using this

theorem eval_flipZero {k : ℕ} (H : MvPolynomial (Fin (k + 1)) ℤ) (c : ℤ) (u : Fin k → ℤ) :
    eval (Fin.cons c u) (flipZero H) = eval (Fin.cons (-c) u) H := by
  unfold flipZero
  rw [← eval_assoc]
  have hf : ((eval (Fin.cons c u)) ∘ fun i : Fin (k + 1) => if i = 0 then -X 0 else X i)
      = Fin.cons (-c) u := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  rw [hf]

open SemanticQuadraticGeneral in
theorem fiberVal_flip {k : ℕ} (H : MvPolynomial (Fin (k + 1)) ℤ) (ℓ : Fin (k + 1) → ℤ) (q : ℤ)
    (m : ℤ) (u : Fin k → ℤ) :
    fiberVal (flipZero H) (fun i => if i = 0 then -ℓ i else ℓ i) q (Fin.cons m u)
      = fiberVal H ℓ q (Fin.cons (-m) u) := by
  unfold fiberVal
  rw [eval_flipZero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, if_true, Fin.succ_ne_zero, if_false]
  ring

theorem sum_abs_flip {k : ℕ} (ℓ : Fin (k + 1) → ℤ) :
    ∑ i, |(fun i => if i = 0 then -ℓ i else ℓ i) i| = ∑ i, |ℓ i| := by
  refine Finset.sum_congr rfl fun i _ => ?_
  show |if i = 0 then -ℓ i else ℓ i| = |ℓ i|
  split_ifs <;> simp

open SemanticQuadraticGeneral in
theorem fboundG_flip {k : ℕ} (K : ℕ) (ℓ : Fin (k + 1) → ℤ) (q : ℤ) :
    fboundG K (fun i => if i = 0 then -ℓ i else ℓ i) q = fboundG K ℓ q := by
  unfold fboundG; rw [sum_abs_flip]

open SemanticQuadraticGeneral in
theorem fboundG_mono_K {k : ℕ} {K K' : ℕ} (h : K ≤ K') (ℓ : Fin (k + 1) → ℤ) (q : ℤ) :
    fboundG K ℓ q ≤ fboundG K' ℓ q := by
  unfold fboundG
  apply mul_le_mul_of_nonneg_right (by exact_mod_cast h)
  positivity

open SemanticQuadraticGeneral in
theorem fboundG_nonneg {k : ℕ} (K : ℕ) (ℓ : Fin (k + 1) → ℤ) (q : ℤ) : 0 ≤ fboundG K ℓ q := by
  unfold fboundG; positivity

open SemanticQuadraticGeneral in
/-- Core of Theorem E_ℤ: given the dichotomy for r witnesses and an injective `e : ℤⁿ → ℤ` whose graph is
    represented (one-sorted) by a degree-≤2 polynomial with r integer unknowns, box counting on ℕⁿ forces
    `n ≤ 2`. -/
theorem capacity_two_aux_ZZ {r : ℕ} (hD : QuadraticProjectionDichotomyZ r)
    {n : ℕ} (e : (Fin n → ℤ) → ℤ) (he : Function.Injective e)
    (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2) (hrep : RepresentsZZ P (graphZZ e)) :
    n ≤ 2 := by
  classical
  obtain ⟨H, ℓ, q, hH, _, hℓ, hq, heval⟩ :=
    normal_form_general_quadratic (r + 1) (rename (relabelG n r) P)
      ((totalDegree_rename_le _ _).trans hP)
  -- e restricted to ℕⁿ
  let e' : (Fin n → ℕ) → ℤ := fun a => e (fun i => (a i : ℤ))
  have he' : Function.Injective e' := by
    intro a b hab
    have := he hab
    funext i
    exact_mod_cast congrFun this i
  let ℓa : (Fin n → ℕ) → Fin (r + 1) → ℤ := fun a i => eval (fun j => (a j : ℤ)) (ℓ i)
  let qa : (Fin n → ℕ) → ℤ := fun a => eval (fun j => (a j : ℤ)) q
  have hfib : ∀ (a : Fin n → ℕ) (c : ℤ) (u : Fin r → ℤ),
      fiberVal H (ℓa a) (qa a) (Fin.cons c u) = evalAtZZ P (Fin.snoc (fun j => (a j : ℤ)) c) u := by
    intro a c u
    rw [← eval_relabelG_ZZ, heval]
    rfl
  have hsol : ∀ (a : Fin n → ℕ) (c : ℤ),
      (∃ u, fiberVal H (ℓa a) (qa a) (Fin.cons c u) = 0) ↔ c = e' a := by
    intro a c
    rw [← snoc_mem_graphZZ e, hrep]
    exact exists_congr fun u => by rw [hfib]
  -- positive fiber ⊆ {e' a}; negative fiber ⊆ {−e' a}
  obtain ⟨K₁, hK₁⟩ := hD H hH
  obtain ⟨K₂, hK₂⟩ := hD (flipZero H) (flipZero_isHomogeneous H hH)
  let ℓa' : (Fin n → ℕ) → Fin (r + 1) → ℤ := fun a i => if i = 0 then -ℓa a i else ℓa a i
  have hpos : ∀ a : Fin n → ℕ, e' a ≤ fboundG K₁ (ℓa a) (qa a) := by
    intro a
    rcases hK₁ (ℓa a) (qa a) with hinf | hb
    · exfalso
      refine hinf (Set.Finite.subset (Set.finite_singleton ((e' a).toNat)) ?_)
      intro c hc
      rw [Set.mem_singleton_iff]
      obtain ⟨u, hu⟩ := hc
      have := (hsol a c).mp ⟨u, hu⟩
      omega
    · rcases le_or_gt 0 (e' a) with h0 | h0
      · have hmem : (e' a).toNat ∈ fiberSetG H (ℓa a) (qa a) := by
          obtain ⟨u, hu⟩ := (hsol a (e' a)).mpr rfl
          exact ⟨u, by rw [Int.toNat_of_nonneg h0]; exact hu⟩
        have := hb _ hmem
        rw [Int.toNat_of_nonneg h0] at this
        exact this
      · exact le_trans h0.le (fboundG_nonneg _ _ _)
  have hneg : ∀ a : Fin n → ℕ, -e' a ≤ fboundG K₂ (ℓa a) (qa a) := by
    intro a
    have hsol' : ∀ m : ℤ, (∃ u, fiberVal (flipZero H) (ℓa' a) (qa a) (Fin.cons m u) = 0) ↔ -m = e' a := by
      intro m
      rw [← hsol a (-m)]
      exact exists_congr fun u => by rw [fiberVal_flip]
    rw [← fboundG_flip K₂ (ℓa a) (qa a)]
    rcases hK₂ (ℓa' a) (qa a) with hinf | hb
    · exfalso
      refine hinf (Set.Finite.subset (Set.finite_singleton ((-e' a).toNat)) ?_)
      intro c hc
      rw [Set.mem_singleton_iff]
      obtain ⟨u, hu⟩ := hc
      have := (hsol' c).mp ⟨u, hu⟩
      omega
    · rcases le_or_gt 0 (-e' a) with h0 | h0
      · have hmem : (-e' a).toNat ∈ fiberSetG (flipZero H) (ℓa' a) (qa a) := by
          obtain ⟨u, hu⟩ := (hsol' (-e' a)).mpr (by ring)
          exact ⟨u, by rw [Int.toNat_of_nonneg h0]; exact hu⟩
        have := hb _ hmem
        rw [Int.toNat_of_nonneg h0] at this
        exact this
      · exact le_trans h0.le (fboundG_nonneg _ _ _)
  set Kd : ℕ := K₁ + K₂ with hKd
  have habs : ∀ a : Fin n → ℕ, |e' a| ≤ fboundG Kd (ℓa a) (qa a) := by
    intro a
    rw [abs_le]
    constructor
    · have := hneg a
      have h2 := fboundG_mono_K (by omega : K₂ ≤ Kd) (ℓa a) (qa a)
      linarith
    · exact le_trans (hpos a) (fboundG_mono_K (by omega : K₁ ≤ Kd) _ _)
  -- coefficient magnitude sums (as in capacity_two_aux)
  set SL : ℕ := ∑ i, ∑ β ∈ (ℓ i).support, (coeff β (ℓ i)).natAbs with hSL
  set SQ : ℕ := ∑ β ∈ q.support, (coeff β q).natAbs with hSQ
  have hSLcast : (SL : ℤ) = ∑ i, ∑ β ∈ (ℓ i).support, |coeff β (ℓ i)| := by
    rw [hSL, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun β _ => Int.natCast_natAbs _
  have hSQcast : (SQ : ℤ) = ∑ β ∈ q.support, |coeff β q| := by
    rw [hSQ, Nat.cast_sum]; exact Finset.sum_congr rfl fun β _ => Int.natCast_natAbs _
  have hfinalbound : ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℕ, (∀ i, a i ≤ N) →
      fboundG Kd (ℓa a) (qa a) ≤ ((Kd * ((1 + SL) ^ 2 + SQ) : ℕ) : ℤ) * (N : ℤ) ^ 2 := by
    intro N h1 a ha
    have hNz : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast h1
    have hℓb : ∀ i, |ℓa a i| ≤ (∑ β ∈ (ℓ i).support, |coeff β (ℓ i)|) * (N : ℤ) := by
      intro i
      have h := eval_abs_le (ℓ i) h1 a ha
      calc |ℓa a i|
          ≤ (∑ β ∈ (ℓ i).support, |coeff β (ℓ i)|) * (N : ℤ) ^ (ℓ i).totalDegree := h
        _ ≤ (∑ β ∈ (ℓ i).support, |coeff β (ℓ i)|) * (N : ℤ) ^ 1 := by
            apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hNz (hℓ i))
            positivity
        _ = (∑ β ∈ (ℓ i).support, |coeff β (ℓ i)|) * (N : ℤ) := by ring
    have hsum : ∑ i, |ℓa a i| ≤ (SL : ℤ) * (N : ℤ) := by
      rw [hSLcast, Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => hℓb i
    have hQb : |qa a| ≤ (SQ : ℤ) * (N : ℤ) ^ 2 := by
      have h := eval_abs_le q h1 a ha
      rw [hSQcast]
      calc |qa a|
          ≤ (∑ β ∈ q.support, |coeff β q|) * (N : ℤ) ^ q.totalDegree := h
        _ ≤ (∑ β ∈ q.support, |coeff β q|) * (N : ℤ) ^ 2 := by
            apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hNz hq)
            rw [← hSQcast]; positivity
    have hnn : (0 : ℤ) ≤ 1 + ∑ i, |ℓa a i| := by positivity
    have step1 : 1 + ∑ i, |ℓa a i| ≤ (1 + (SL : ℤ)) * N := by nlinarith [hsum, hNz]
    have step2 : (1 + ∑ i, |ℓa a i|) ^ 2 ≤ ((1 + (SL : ℤ)) * N) ^ 2 := pow_le_pow_left₀ hnn step1 2
    have hexp : ((1 + (SL : ℤ)) * N) ^ 2 = (1 + (SL : ℤ)) ^ 2 * N ^ 2 := by ring
    rw [hexp] at step2
    have inner : (1 + ∑ i, |ℓa a i|) ^ 2 + |qa a| ≤ ((1 + (SL : ℤ)) ^ 2 + SQ) * N ^ 2 := by
      nlinarith [step2, hQb]
    calc fboundG Kd (ℓa a) (qa a)
        = (Kd : ℤ) * ((1 + ∑ i, |ℓa a i|) ^ 2 + |qa a|) := rfl
      _ ≤ (Kd : ℤ) * (((1 + (SL : ℤ)) ^ 2 + SQ) * N ^ 2) :=
          mul_le_mul_of_nonneg_left inner (by positivity)
      _ = ((Kd * ((1 + SL) ^ 2 + SQ) : ℕ) : ℤ) * (N : ℤ) ^ 2 := by push_cast; ring
  have hbc := box_counting_bound (ι := Fin 1) (fun a (_ : Fin 1) => e' a) ?inj
    (fun _ => 2) (Kd * ((1 + SL) ^ 2 + SQ)) ?bd
  · simpa using hbc
  case inj =>
    intro a b hab
    exact he' (congrFun hab 0)
  case bd =>
    intro N h1 a ha j
    exact le_trans (habs a) (hfinalbound N h1 a ha)

theorem atomGraphZZ_degree_two_le_two : ∀ n, AtomGraphZZ 2 n → n ≤ 2 := by
  intro n h
  obtain ⟨r, e, he, P, hP, hrep⟩ := h
  exact capacity_two_aux_ZZ (SemanticQuadraticSingular.quadraticProjectionDichotomyZ_all r) e he P hP hrep

theorem one_sorted_quadratic_no_injective_ternary_graph :
    ∀ (r : ℕ) (P : Poly 4 r), P.totalDegree ≤ 2 →
      ∀ e : (Fin 3 → ℤ) → ℤ, Function.Injective e → ¬ RepresentsZZ P (graphZZ e) := by
  intro r P hP e he hrep
  have := atomGraphZZ_degree_two_le_two 3 ⟨r, e, he, P, hP, hrep⟩
  omega

theorem atomGraphZZ_degree_one_one : AtomGraphZZ 1 1 := by
  refine ⟨0, fun a => a 0, fun a b h => ?_, X (Sum.inl 1) - X (Sum.inl 0), ?_, fun v => ?_⟩
  · funext i; rw [Subsingleton.elim i 0]; exact h
  · refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_) <;> rw [totalDegree_X]
  · simp only [graphZZ, Set.mem_setOf_eq, evalAtZZ, map_sub, eval_X, Sum.elim_inl]
    constructor
    · intro h
      exact ⟨Fin.elim0, by
        show v 1 - v 0 = 0
        have : Fin.init v 0 = v 0 := rfl
        rw [sub_eq_zero]; simpa [this] using h⟩
    · rintro ⟨_, h⟩
      show v (Fin.last 1) = Fin.init v 0
      have h' : v 1 - v 0 = 0 := h
      rw [sub_eq_zero] at h'
      exact h'

/-! ### The one-sorted contrast at degree two -/

def zToNat (x : ℤ) : ℤ := if 0 ≤ x then 2 * x else -2 * x - 1

theorem zToNat_injective : Function.Injective zToNat := by
  intro x y h
  unfold zToNat at h
  split_ifs at h <;> omega

theorem zToNat_nonneg (x : ℤ) : 0 ≤ zToNat x := by
  unfold zToNat; split_ifs <;> omega

noncomputable def ternaryPairZZ (a : Fin 3 → ℤ) : ℤ :=
  ((cantorScaledPair (cantorScaledPair (zToNat (a 0)).toNat (zToNat (a 1)).toNat)
    (zToNat (a 2)).toNat : ℕ) : ℤ)

theorem zToNat_toNat_injective : Function.Injective (fun x : ℤ => (zToNat x).toNat) := by
  intro x y h
  apply zToNat_injective
  have hx := Int.toNat_of_nonneg (zToNat_nonneg x)
  have hy := Int.toNat_of_nonneg (zToNat_nonneg y)
  simp only at h
  rw [← hx, ← hy, h]

theorem ternaryPairZZ_injective : Function.Injective ternaryPairZZ := by
  intro a b h
  unfold ternaryPairZZ at h
  have hn : cantorScaledPair (cantorScaledPair (zToNat (a 0)).toNat (zToNat (a 1)).toNat)
      (zToNat (a 2)).toNat = cantorScaledPair (cantorScaledPair (zToNat (b 0)).toNat
      (zToNat (b 1)).toNat) (zToNat (b 2)).toNat := by exact_mod_cast h
  have h1 := Prod.mk.inj (cantorScaledPair_injective
    (a₁ := (cantorScaledPair (zToNat (a 0)).toNat (zToNat (a 1)).toNat, (zToNat (a 2)).toNat))
    (a₂ := (cantorScaledPair (zToNat (b 0)).toNat (zToNat (b 1)).toNat, (zToNat (b 2)).toNat)) hn)
  have h2 := Prod.mk.inj (cantorScaledPair_injective
    (a₁ := ((zToNat (a 0)).toNat, (zToNat (a 1)).toNat))
    (a₂ := ((zToNat (b 0)).toNat, (zToNat (b 1)).toNat)) h1.1)
  have e0 := zToNat_toNat_injective h2.1
  have e1 := zToNat_toNat_injective h2.2
  have e2 := zToNat_toNat_injective h1.2
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

/-! ### The pp system over ℤ: per-coordinate sign block, then two pairing gates -/

section ContrastSystem

/-- `X s · X s − 1`. -/
noncomputable def sqOnePoly {σ : Type} (s : σ) : MvPolynomial σ ℤ := X s * X s - 1

/-- `2·Σ w_j² − (2·s·a + s − 1)`, written without numeral coefficients. -/
noncomputable def fourSqPoly {σ : Type} (a s : σ) (w : Fin 4 → σ) : MvPolynomial σ ℤ :=
  (∑ j, X (w j) * X (w j)) + (∑ j, X (w j) * X (w j)) - (X s * X a + X s * X a + X s - 1)

/-- `2·y + 1 − s·(4·a + 1)`, written without numeral coefficients. -/
noncomputable def halfPoly {σ : Type} (a s y : σ) : MvPolynomial σ ℤ :=
  X y + X y + 1 - X s * (X a + X a + X a + X a + 1)

theorem totalDegree_X_le_one {σ : Type} (w : σ) : (X w : MvPolynomial σ ℤ).totalDegree ≤ 1 := by
  rw [totalDegree_X]

theorem totalDegree_XX_le_two {σ : Type} (u v : σ) :
    (X u * X v : MvPolynomial σ ℤ).totalDegree ≤ 2 :=
  le_trans (totalDegree_mul _ _) (by have := totalDegree_X_le_one (σ := σ) u; have := totalDegree_X_le_one (σ := σ) v; omega)

theorem sqOnePoly_totalDegree {σ : Type} (s : σ) : (sqOnePoly s).totalDegree ≤ 2 := by
  unfold sqOnePoly
  refine le_trans (totalDegree_sub _ _) (max_le (totalDegree_XX_le_two _ _) ?_)
  rw [totalDegree_one]; omega

theorem fourSqPoly_totalDegree {σ : Type} (a s : σ) (w : Fin 4 → σ) :
    (fourSqPoly a s w).totalDegree ≤ 2 := by
  unfold fourSqPoly
  have hsum : (∑ j, X (w j) * X (w j) : MvPolynomial σ ℤ).totalDegree ≤ 2 :=
    le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun j _ => totalDegree_XX_le_two _ _)
  refine le_trans (totalDegree_sub _ _) (max_le (le_trans (totalDegree_add _ _) (max_le hsum hsum)) ?_)
  refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
  · refine le_trans (totalDegree_add _ _) (max_le (le_trans (totalDegree_add _ _)
      (max_le (totalDegree_XX_le_two _ _) (totalDegree_XX_le_two _ _))) ?_)
    have := totalDegree_X_le_one (σ := σ) s; omega
  · rw [totalDegree_one]; omega

theorem halfPoly_totalDegree {σ : Type} (a s y : σ) : (halfPoly a s y).totalDegree ≤ 2 := by
  unfold halfPoly
  have hX := fun v => totalDegree_X_le_one (σ := σ) v
  have hlin : (X a + X a + X a + X a + 1 : MvPolynomial σ ℤ).totalDegree ≤ 1 := by
    refine le_trans (totalDegree_add _ _) (max_le ?_ (by rw [totalDegree_one]; omega))
    refine le_trans (totalDegree_add _ _) (max_le ?_ (hX a))
    refine le_trans (totalDegree_add _ _) (max_le ?_ (hX a))
    exact le_trans (totalDegree_add _ _) (max_le (hX a) (hX a))
  refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
  · refine le_trans (totalDegree_add _ _) (max_le ?_ (by rw [totalDegree_one]; omega))
    exact le_trans (totalDegree_add _ _) (max_le (by have := hX y; omega) (by have := hX y; omega))
  · exact le_trans (totalDegree_mul _ _) (by have := hX s; omega)

theorem eval_sqOnePoly {σ : Type} (f : σ → ℤ) (s : σ) : eval f (sqOnePoly s) = f s * f s - 1 := by
  simp [sqOnePoly]

theorem eval_fourSqPoly {σ : Type} (f : σ → ℤ) (a s : σ) (w : Fin 4 → σ) :
    eval f (fourSqPoly a s w)
      = (∑ j, f (w j) * f (w j)) + (∑ j, f (w j) * f (w j)) - (f s * f a + f s * f a + f s - 1) := by
  simp [fourSqPoly]

theorem eval_halfPoly {σ : Type} (f : σ → ℤ) (a s y : σ) :
    eval f (halfPoly a s y) = f y + f y + 1 - f s * (f a + f a + f a + f a + 1) := by
  simp [halfPoly]

/-- The sign block characterizes `zToNat`. -/
theorem zToNat_of_block (a s y : ℤ) (w : Fin 4 → ℤ) (h1 : s * s - 1 = 0)
    (h2 : (∑ j, w j * w j) + (∑ j, w j * w j) - (s * a + s * a + s - 1) = 0)
    (h3 : y + y + 1 - s * (a + a + a + a + 1) = 0) : y = zToNat a := by
  have hSum : 0 ≤ ∑ j, w j * w j := Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hs : (s - 1) * (s + 1) = 0 := by ring_nf; linarith
  unfold zToNat
  rcases mul_eq_zero.mp hs with hs | hs
  · have : s = 1 := by linarith
    subst this
    split_ifs <;> omega
  · have : s = -1 := by linarith
    subst this
    split_ifs <;> omega

theorem block_of_zToNat (a : ℤ) : ∃ (s : ℤ) (w : Fin 4 → ℤ), s * s - 1 = 0 ∧
    (∑ j, w j * w j) + (∑ j, w j * w j) - (s * a + s * a + s - 1) = 0 ∧
    zToNat a + zToNat a + 1 - s * (a + a + a + a + 1) = 0 := by
  rcases le_or_gt 0 a with h | h
  · obtain ⟨w, hw⟩ := exists_four_sq a.toNat
    refine ⟨1, w, by ring, ?_, ?_⟩
    · have : (∑ j, w j * w j) = a := by
        rw [Int.toNat_of_nonneg h, sub_eq_zero] at hw
        rw [hw]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]; ring
    · unfold zToNat; rw [if_pos h]; ring
  · obtain ⟨w, hw⟩ := exists_four_sq (-a - 1).toNat
    refine ⟨-1, w, by ring, ?_, ?_⟩
    · have : (∑ j, w j * w j) = -a - 1 := by
        rw [Int.toNat_of_nonneg (by omega), sub_eq_zero] at hw
        rw [hw]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]; ring
    · unfold zToNat; rw [if_neg (by omega)]; ring

/-- Witness layout: three sign blocks of six (s, w₁..w₄, y) and one pairing intermediate z. -/
def bIdx0 (j : Fin 6) : Fin (6 + 6 + 6 + 1) := Fin.castAdd 1 (Fin.castAdd 6 (Fin.castAdd 6 j))
def bIdx1 (j : Fin 6) : Fin (6 + 6 + 6 + 1) := Fin.castAdd 1 (Fin.castAdd 6 (Fin.natAdd 6 j))
def bIdx2 (j : Fin 6) : Fin (6 + 6 + 6 + 1) := Fin.castAdd 1 (Fin.natAdd (6 + 6) j)
def zIdx : Fin (6 + 6 + 6 + 1) := Fin.natAdd (6 + 6 + 6) 0

/-- Variables `Fin 4 ⊕ Fin 19`: inputs `a₀ a₁ a₂ = inl 0,1,2`, output `c = inl 3`. -/
noncomputable def ternaryPairZZSystem : PolySystem 4 (6 + 6 + 6 + 1) 11 :=
  ![sqOnePoly (Sum.inr (bIdx0 0)),
    fourSqPoly (Sum.inl 0) (Sum.inr (bIdx0 0)) (fun j => Sum.inr (bIdx0 j.succ.castSucc)),
    halfPoly (Sum.inl 0) (Sum.inr (bIdx0 0)) (Sum.inr (bIdx0 5)),
    sqOnePoly (Sum.inr (bIdx1 0)),
    fourSqPoly (Sum.inl 1) (Sum.inr (bIdx1 0)) (fun j => Sum.inr (bIdx1 j.succ.castSucc)),
    halfPoly (Sum.inl 1) (Sum.inr (bIdx1 0)) (Sum.inr (bIdx1 5)),
    sqOnePoly (Sum.inr (bIdx2 0)),
    fourSqPoly (Sum.inl 2) (Sum.inr (bIdx2 0)) (fun j => Sum.inr (bIdx2 j.succ.castSucc)),
    halfPoly (Sum.inl 2) (Sum.inr (bIdx2 0)) (Sum.inr (bIdx2 5)),
    X (Sum.inr zIdx) - pairPolyX (Sum.inr (bIdx0 5)) (Sum.inr (bIdx1 5)),
    X (Sum.inl 3) - pairPolyX (Sum.inr zIdx) (Sum.inr (bIdx2 5))]

theorem ternaryPairZZSystem_totalDegree : ∀ i, (ternaryPairZZSystem i).totalDegree ≤ 2 := by
  have hpair : ∀ (u v : Fin 4 ⊕ Fin (6 + 6 + 6 + 1)) (w : Fin 4 ⊕ Fin (6 + 6 + 6 + 1)),
      (X u - pairPolyX v w : MvPolynomial _ ℤ).totalDegree ≤ 2 := fun u v w =>
    le_trans (totalDegree_sub _ _) (max_le (by rw [totalDegree_X]; omega) (pairPolyX_totalDegree _ _))
  simp only [ternaryPairZZSystem, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    IsEmpty.forall_iff, and_true]
  exact ⟨sqOnePoly_totalDegree _, fourSqPoly_totalDegree _ _ _, halfPoly_totalDegree _ _ _,
    sqOnePoly_totalDegree _, fourSqPoly_totalDegree _ _ _, halfPoly_totalDegree _ _ _,
    sqOnePoly_totalDegree _, fourSqPoly_totalDegree _ _ _, halfPoly_totalDegree _ _ _,
    hpair _ _ _, hpair _ _ _⟩

/-- A block vector `(s, w₀, w₁, w₂, w₃, y)`. -/
def blockVec (s : ℤ) (w : Fin 4 → ℤ) (y : ℤ) : Fin 6 → ℤ := Fin.cons s (Fin.snoc w y)

theorem blockVec_zero (s : ℤ) (w : Fin 4 → ℤ) (y : ℤ) : blockVec s w y 0 = s := rfl
theorem blockVec_five (s : ℤ) (w : Fin 4 → ℤ) (y : ℤ) : blockVec s w y 5 = y := rfl
theorem blockVec_w (s : ℤ) (w : Fin 4 → ℤ) (y : ℤ) (j : Fin 4) :
    blockVec s w y j.succ.castSucc = w j := by
  unfold blockVec
  rw [show (j.succ.castSucc : Fin 6) = (j.castSucc).succ from rfl, Fin.cons_succ, Fin.snoc_castSucc]

def assembleT (B0 B1 B2 : Fin 6 → ℤ) (z : ℤ) : Fin (6 + 6 + 6 + 1) → ℤ :=
  Fin.append (Fin.append (Fin.append B0 B1) B2) (fun _ => z)

theorem assembleT_b0 (B0 B1 B2 : Fin 6 → ℤ) (z : ℤ) (j : Fin 6) :
    assembleT B0 B1 B2 z (bIdx0 j) = B0 j := by
  unfold assembleT bIdx0; rw [Fin.append_left, Fin.append_left, Fin.append_left]
theorem assembleT_b1 (B0 B1 B2 : Fin 6 → ℤ) (z : ℤ) (j : Fin 6) :
    assembleT B0 B1 B2 z (bIdx1 j) = B1 j := by
  unfold assembleT bIdx1; rw [Fin.append_left, Fin.append_left, Fin.append_right]
theorem assembleT_b2 (B0 B1 B2 : Fin 6 → ℤ) (z : ℤ) (j : Fin 6) :
    assembleT B0 B1 B2 z (bIdx2 j) = B2 j := by
  unfold assembleT bIdx2; rw [Fin.append_left, Fin.append_right]
theorem assembleT_z (B0 B1 B2 : Fin 6 → ℤ) (z : ℤ) : assembleT B0 B1 B2 z zIdx = z := by
  unfold assembleT zIdx; rw [Fin.append_right]

theorem cast_zToNat_toNat (x : ℤ) : (((zToNat x).toNat : ℕ) : ℤ) = zToNat x :=
  Int.toNat_of_nonneg (zToNat_nonneg x)

theorem ternaryPairZZSystem_representsZZ :
    SystemRepresentsZZ ternaryPairZZSystem (graphZZ ternaryPairZZ) := by
  intro v
  have hg : v ∈ graphZZ ternaryPairZZ ↔ v 3 = ternaryPairZZ (Fin.init v) := Iff.rfl
  have hinit : ∀ i : Fin 3, Fin.init v i = v i.castSucc := fun i => rfl
  have h0 : Fin.init v 0 = v 0 := rfl
  have h1 : Fin.init v 1 = v 1 := rfl
  have h2 : Fin.init v 2 = v 2 := rfl
  rw [hg]
  constructor
  · intro hv
    obtain ⟨s0, w0, e10, e20, e30⟩ := block_of_zToNat (v 0)
    obtain ⟨s1, w1, e11, e21, e31⟩ := block_of_zToNat (v 1)
    obtain ⟨s2, w2, e12, e22, e32⟩ := block_of_zToNat (v 2)
    let zv : ℤ := ((cantorScaledPair (zToNat (v 0)).toNat (zToNat (v 1)).toNat : ℕ) : ℤ)
    refine ⟨assembleT (blockVec s0 w0 (zToNat (v 0))) (blockVec s1 w1 (zToNat (v 1)))
      (blockVec s2 w2 (zToNat (v 2))) zv, ?_⟩
    simp only [ternaryPairZZSystem, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      IsEmpty.forall_iff, and_true, evalAtZZ, eval_sqOnePoly, eval_fourSqPoly,
      eval_halfPoly, map_sub, eval_X, eval_pairPolyX, Sum.elim_inl, Sum.elim_inr,
      assembleT_b0, assembleT_b1, assembleT_b2, assembleT_z, blockVec_zero, blockVec_five, blockVec_w]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact e10
    · exact e20
    · exact e30
    · exact e11
    · exact e21
    · exact e31
    · exact e12
    · exact e22
    · exact e32
    · show zv - _ = 0
      simp only [zv]
      rw [cast_cantorScaledPair, cast_zToNat_toNat, cast_zToNat_toNat]; ring
    · rw [hv]
      unfold ternaryPairZZ
      rw [h0, h1, h2, cast_cantorScaledPair, cast_zToNat_toNat]
      simp only [zv]
      rw [cast_cantorScaledPair, cast_zToNat_toNat, cast_zToNat_toNat]; ring
  · rintro ⟨y, hy⟩
    simp only [ternaryPairZZSystem, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      IsEmpty.forall_iff, and_true, evalAtZZ, eval_sqOnePoly, eval_fourSqPoly,
      eval_halfPoly, map_sub, eval_X, eval_pairPolyX, Sum.elim_inl, Sum.elim_inr] at hy
    obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩ := hy
    have y0 := zToNat_of_block (v 0) _ _ _ k0 k1 k2
    have y1 := zToNat_of_block (v 1) _ _ _ k3 k4 k5
    have y2 := zToNat_of_block (v 2) _ _ _ k6 k7 k8
    rw [y0, y1] at k9
    rw [y2] at k10
    have hz : y zIdx = ((cantorScaledPair (zToNat (v 0)).toNat (zToNat (v 1)).toNat : ℕ) : ℤ) := by
      rw [cast_cantorScaledPair, cast_zToNat_toNat, cast_zToNat_toNat]; linarith
    rw [hz] at k10
    unfold ternaryPairZZ
    rw [h0, h1, h2, cast_cantorScaledPair, cast_zToNat_toNat]
    linarith

theorem ppGraphZZ_degree_two_three : PPGraphZZ 2 3 :=
  ⟨6 + 6 + 6 + 1, 11, ternaryPairZZ, ternaryPairZZ_injective, ternaryPairZZSystem,
    ternaryPairZZSystem_totalDegree, ternaryPairZZSystem_representsZZ⟩

end ContrastSystem

end DiophCompression

#print axioms DiophCompression.atomGraphZZ_degree_two_le_two
#print axioms DiophCompression.one_sorted_quadratic_no_injective_ternary_graph
#print axioms DiophCompression.atomGraphZZ_degree_one_one
#print axioms DiophCompression.ternaryPairZZ_injective
#print axioms DiophCompression.ppGraphZZ_degree_two_three
