/-
  DiophCompression/NatGuard.lean — r06 必須D (session 6, 2026-08-27, claude.ai direct, no CC).
  Statements frozen first: frozen statement file `NatGuard_STATEMENTS.lean` (md5 89f9be74).
  GPT r05 §3 Q1 / §5 必須D: the natural-number guard of `GraphToUniversalityZ.lean` is abstracted into a
  structure `NatGuard` (arity, degree ≥ 1, polynomial, non-negative on ℤ^arity, surjective onto ℕ).
  `graph_to_universality_Z_of_guard` is the r05 proof with the four-square guard replaced by an arbitrary
  guard: resources (r + ν₀ + 1 + arity, 2·max{d, δ₀, degree}). `fourSquareGuard` (4, 2) via mathlib
  `Nat.sum_four_squares` recovers the r05 theorem verbatim (`graph_to_universality_Z_fourSquare`).
  A three-variable guard x²+y²+z²+z (arity 3) would give r + ν₀ + 4 but needs Legendre's three-square
  theorem, absent from mathlib — not constructed here (UNDERFLOW 2A). GraphToUniversalityZ.lean is untouched.
-/
import DiophCompression.GraphToUniversalityZ

namespace DiophCompression

open MvPolynomial MPUP

/-- A natural-number guard: a polynomial in `arity` ℤ-unknowns, of total degree ≤ `degree` (≥ 1),
    non-negative on all of ℤ^arity and hitting every natural number. -/
structure NatGuard where
  arity : ℕ
  degree : ℕ
  one_le_degree : 1 ≤ degree
  poly : MvPolynomial (Fin arity) ℤ
  totalDegree_le : poly.totalDegree ≤ degree
  nonneg : ∀ g : Fin arity → ℤ, 0 ≤ eval g poly
  surjective : ∀ c : ℕ, ∃ g : Fin arity → ℤ, eval g poly = (c : ℤ)

/-! ### Guard polynomial for an abstract guard -/

/-- `c − G(g)` with `c` = unknown 0 and the guard variables = the last `G.arity` unknowns. -/
noncomputable def guardPolyG (n r : ℕ) (G : NatGuard) : Poly n (r + 1 + G.arity) :=
  X (Sum.inr (Fin.castAdd G.arity (0 : Fin (r + 1))))
    - rename (fun k => Sum.inr (Fin.natAdd (r + 1) k)) G.poly

theorem evalAt_guardPolyG {n r : ℕ} (G : NatGuard) (a : Fin n → ℕ) (z : Fin (r + 1 + G.arity) → ℤ) :
    evalAt (guardPolyG n r G) a z
      = z (Fin.castAdd G.arity (0 : Fin (r + 1))) - eval (fun k => z (Fin.natAdd (r + 1) k)) G.poly := by
  simp only [evalAt, guardPolyG, map_sub, eval_X, Sum.elim_inr, eval_rename]
  rfl

theorem guardPolyG_totalDegree (n r : ℕ) (G : NatGuard) : (guardPolyG n r G).totalDegree ≤ G.degree := by
  unfold guardPolyG
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X]; exact G.one_le_degree
  · exact (totalDegree_rename_le _ _).trans G.totalDegree_le

/-- Guarded projection with an abstract guard. -/
noncomputable def projectLastGuardG {n r : ℕ} (G : NatGuard) (P : Poly (n + 1) r) :
    Poly n (r + 1 + G.arity) :=
  weakenUnknowns G.arity (projectLast P) + (guardPolyG n r G) ^ 2

theorem totalDegree_projectLastGuardG_le {n r : ℕ} (G : NatGuard) (P : Poly (n + 1) r) :
    (projectLastGuardG G P).totalDegree ≤ max P.totalDegree (2 * G.degree) := by
  unfold projectLastGuardG
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · have h1 : (weakenUnknowns G.arity (projectLast P)).totalDegree ≤ P.totalDegree :=
      (totalDegree_weakenUnknowns_le _).trans (totalDegree_projectLast_le P)
    omega
  · refine (totalDegree_pow _ _).trans ?_
    have h2 := guardPolyG_totalDegree n r G
    omega

theorem evalAt_projectLastGuardG {n r : ℕ} (G : NatGuard) (P : Poly (n + 1) r) (a : Fin n → ℕ)
    (z : Fin (r + 1 + G.arity) → ℤ) :
    evalAt (projectLastGuardG G P) a z
      = evalAt (projectLast P) a (fun j => z (Fin.castAdd G.arity j))
        + (z (Fin.castAdd G.arity (0 : Fin (r + 1)))
            - eval (fun k => z (Fin.natAdd (r + 1) k)) G.poly) ^ 2 := by
  have h1 := evalAt_weakenUnknowns (m := G.arity) (projectLast P) a z
  have h2 := evalAt_guardPolyG (r := r) G a z
  unfold projectLastGuardG
  unfold evalAt at h1 h2 ⊢
  rw [map_add, map_pow, h1, h2]

theorem representsZ_projectLastGuardG {n r : ℕ} (G : NatGuard) (P : Poly (n + 1) r)
    (S : Set (Fin (n + 1) → ℕ))
    (hnn : ∀ ρ : (Fin (n + 1) ⊕ Fin r) → ℤ, 0 ≤ eval ρ P) (h : RepresentsZ P S) :
    RepresentsZ (projectLastGuardG G P) {a | ∃ c, Fin.snoc a c ∈ S} := by
  intro a
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨w, hw⟩ := (h _).mp hc
    obtain ⟨gv, hg⟩ := G.surjective c
    refine ⟨Fin.append (Fin.cons (c : ℤ) w) gv, ?_⟩
    rw [evalAt_projectLastGuardG]
    have e1 : (fun j => Fin.append (Fin.cons (c : ℤ) w) gv (Fin.castAdd G.arity j))
        = Fin.cons (c : ℤ) w := by
      funext j; rw [Fin.append_left]
    rw [e1, aux_evalAt_projectLast_int, hw]
    have e2 : Fin.append (Fin.cons (c : ℤ) w) gv (Fin.castAdd G.arity (0 : Fin (r + 1))) = c := by
      rw [Fin.append_left, Fin.cons_zero]
    have e3 : (fun k => Fin.append (Fin.cons (c : ℤ) w) gv (Fin.natAdd (r + 1) k)) = gv := by
      funext k; rw [Fin.append_right]
    rw [e2, e3, hg]; ring
  · rintro ⟨z, hz⟩
    rw [evalAt_projectLastGuardG] at hz
    have hfirst : 0 ≤ evalAt (projectLast P) a (fun j => z (Fin.castAdd G.arity j)) := by
      unfold evalAt projectLast
      rw [eval_rename]
      exact hnn _
    have hz' := (add_eq_zero_iff_of_nonneg hfirst (sq_nonneg _)).mp hz
    have h1 := hz'.1
    have h2 := (pow_eq_zero_iff (two_ne_zero)).mp hz'.2
    have hnn0 : 0 ≤ z (Fin.castAdd G.arity (0 : Fin (r + 1))) := by
      rw [sub_eq_zero] at h2; rw [h2]; exact G.nonneg _
    refine ⟨(z (Fin.castAdd G.arity (0 : Fin (r + 1)))).toNat,
      (h _).mpr ⟨fun j => z (Fin.castAdd G.arity j.succ), ?_⟩⟩
    rw [← aux_evalAt_projectLast_int, Int.toNat_of_nonneg hnn0]
    have hq : Fin.cons (z (Fin.castAdd G.arity (0 : Fin (r + 1)))) (fun j => z (Fin.castAdd G.arity j.succ))
        = fun j => z (Fin.castAdd G.arity j) :=
      Fin.cons_self_tail (fun j => z (Fin.castAdd G.arity j))
    rw [hq]
    exact h1

/-! ### Main theorem with an abstract guard (r05 proof body, guard abstracted) -/

theorem graph_to_universality_Z_of_guard (G : NatGuard) {n r d ν₀ δ₀ : ℕ}
    (hU : UniversalPairZ ν₀ δ₀) (hG : GraphAchievableZ n r d) :
    UniversalAchievableZ n (r + ν₀ + 1 + G.arity) (2 * max d (max δ₀ G.degree)) := by
  intro A hA
  obtain ⟨e, he, r', hr', C, hCd, hCrep⟩ := hG
  obtain ⟨rA, PA, hPArep⟩ := hA
  have hCrepN := representsN_splitUnknowns C _ hCrep
  have hA'rep : RepresentsN (weakenParams 1 PA)
      {v : Fin (n+1) → ℕ | (fun i => v (Fin.castAdd 1 i)) ∈ A} :=
    representsN_weakenParams PA A hPArep
  have hSrep := representsN_conj (splitUnknowns C) (weakenParams 1 PA) (graph e)
    {v : Fin (n+1) → ℕ | (fun i => v (Fin.castAdd 1 i)) ∈ A} hCrepN hA'rep
  have hSdioph : DiophN (graph e ∩ {v : Fin (n+1) → ℕ | (fun i => v (Fin.castAdd 1 i)) ∈ A}) :=
    ⟨_, _, hSrep⟩
  have hBdioph := diophN_projectBlock _ hSdioph
  obtain ⟨ν'', hν'', PB, hPBd, hPBrep⟩ := hU _ hBdioph
  let g : Fin 1 → Fin (n+1) := fun _ => Fin.last n
  have hPB'rep := representsZ_renameParams g PB _ hPBrep
  have hConjrep := representsZ_conj C (rename (Sum.map g id) PB) (graph e)
    {V : Fin (n+1) → ℕ | (fun i => V (g i)) ∈
      {c : Fin 1 → ℕ | ∃ a : Fin n → ℕ, Fin.append a c ∈
        graph e ∩ {v : Fin (n+1) → ℕ | (fun i => v (Fin.castAdd 1 i)) ∈ A}}}
    hCrep hPB'rep
  have hnnC : ∀ ρ : (Fin (n + 1) ⊕ Fin (r' + ν'')) → ℤ, 0 ≤ eval ρ (conj C (rename (Sum.map g id) PB)) := by
    intro ρ
    unfold conj
    simp only [map_add, map_pow]
    positivity
  have hDrep := representsZ_projectLastGuardG G (conj C (rename (Sum.map g id) PB)) _ hnnC hConjrep
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
  refine ⟨r' + ν'' + 1 + G.arity, ?_, projectLastGuardG G (conj C (rename (Sum.map g id) PB)), ?_, hDrep⟩
  · show r' + ν'' + 1 + G.arity ≤ r + ν₀ + 1 + G.arity; omega
  · refine (totalDegree_projectLastGuardG_le _ _).trans ?_
    have hc := totalDegree_conj_le C (rename (Sum.map g id) PB)
    have h1 : C.totalDegree ≤ d := hCd
    have h2 : (rename (Sum.map g id) PB).totalDegree ≤ δ₀ := (totalDegree_rename_le _ _).trans hPBd
    have hc' : (conj C (rename (Sum.map g id) PB)).totalDegree ≤ 2 * max d δ₀ :=
      hc.trans (Nat.mul_le_mul (le_refl 2) (max_le_max h1 h2))
    have hm1 : 2 * max d δ₀ ≤ 2 * max d (max δ₀ G.degree) :=
      Nat.mul_le_mul (le_refl 2) (max_le_max le_rfl (le_max_left _ _))
    have hm2 : 2 * G.degree ≤ 2 * max d (max δ₀ G.degree) :=
      Nat.mul_le_mul (le_refl 2) ((le_max_right _ _).trans (le_max_right _ _))
    exact max_le (hc'.trans hm1) hm2

/-! ### The four-square instance (mathlib `Nat.sum_four_squares`) -/

noncomputable def fourSquareGuard : NatGuard where
  arity := 4
  degree := 2
  one_le_degree := by norm_num
  poly := ∑ k : Fin 4, (X k) ^ 2
  totalDegree_le := by
    apply totalDegree_finsetSum_le
    intro k _
    rw [totalDegree_X_pow]
  nonneg := by
    intro g
    simp only [map_sum, map_pow, eval_X]
    positivity
  surjective := by
    intro c
    obtain ⟨a, b, c', d, h⟩ := Nat.sum_four_squares c
    refine ⟨![(a : ℤ), b, c', d], ?_⟩
    have h' : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c' : ℤ) ^ 2 + (d : ℤ) ^ 2 = (c : ℤ) := by exact_mod_cast h
    simpa [Fin.sum_univ_four] using h'

theorem fourSquareGuard_arity : fourSquareGuard.arity = 4 := rfl
theorem fourSquareGuard_degree : fourSquareGuard.degree = 2 := rfl

/-- The r05 statement, now a corollary of the abstract guard theorem. -/
theorem graph_to_universality_Z_fourSquare {n r d ν₀ δ₀ : ℕ}
    (hU : UniversalPairZ ν₀ δ₀) (hG : GraphAchievableZ n r d) :
    UniversalAchievableZ n (r + ν₀ + 5) (2 * max d (max δ₀ 2)) := by
  have h := graph_to_universality_Z_of_guard fourSquareGuard hU hG
  rw [fourSquareGuard_arity, fourSquareGuard_degree] at h
  rwa [show r + ν₀ + 1 + 4 = r + ν₀ + 5 by omega] at h

end DiophCompression

#print axioms DiophCompression.representsZ_projectLastGuardG
#print axioms DiophCompression.totalDegree_projectLastGuardG_le
#print axioms DiophCompression.graph_to_universality_Z_of_guard
#print axioms DiophCompression.fourSquareGuard
#print axioms DiophCompression.graph_to_universality_Z_fourSquare
