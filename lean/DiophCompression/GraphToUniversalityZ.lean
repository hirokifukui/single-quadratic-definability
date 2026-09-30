/-
  DiophCompression/GraphToUniversalityZ.lean — r05 必須D part 2 (session 5, 2026-08-26, claude.ai direct, no CC).
  Graph coding → universality with ℤ-unknowns, at one arity n, with the non-negativity guard:
    UniversalPairZ ν₀ δ₀ ∧ GraphAchievableZ n r d ⟹ UniversalAchievableZ n (r + ν₀ + 5) (2·max d (max δ₀ 2)).
  Mechanism (GPT r04 §6 必須D, guard = four squares by ruling): a ∈ A ⟺ ∃ c, w, y, g₁..g₄ ∈ ℤ:
    Φ(a, c, w)² + U(c, y)² + (c − (g₁²+g₂²+g₃²+g₄²))² = 0.
  The output variable c is turned into a ℤ-unknown (`projectLast`, a renaming); the guard equation forces
  c ≥ 0 so that c = ↑(c.toNat) and the frozen ℕ-parameter semantics of Φ and U apply at c.toNat.
  Witnesses: r' + ν'' + 1 + 4 ≤ r + ν₀ + 5. Degree: max(2·max(deg Φ, deg U), 4) = 2·max(d, δ₀, 2)
  (conj is already a sum of squares; the guard square has degree 4; the sum is NOT squared again).
  B = e(A) is certified DiophN through `splitUnknowns` (ℤ-unknowns of Φ become differences of ℕ-unknowns),
  since UniversalPairZ takes a DiophN hypothesis (Spec.lean, as in the AFP).
  FORBIDDEN and not used: `RepresentsN P A → RepresentsZ P A` (false); substituting a negative c into Φ/U.
  Statements frozen 2026-08-26 (frozen statement file `NatGuardZ_GraphToUniversalityZ_STATEMENTS.lean`, md5 edc39cad).
-/
import DiophCompression.NatGuardZ
import DiophCompression.WeakenUnknowns
import DiophCompression.Sandwich

namespace DiophCompression

open MvPolynomial MPUP

/-! ### ℤ-unknown versions of the frozen Task1 combinators -/

theorem representsZ_conj {n r₁ r₂ : ℕ} (P : Poly n r₁) (Q : Poly n r₂)
    (A B : Set (Fin n → ℕ)) (hP : RepresentsZ P A) (hQ : RepresentsZ Q B) :
    RepresentsZ (conj P Q) (A ∩ B) := by
  intro a
  rw [Set.mem_inter_iff, hP a, hQ a]
  constructor
  · rintro ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩⟩
    refine ⟨Fin.append y₁ y₂, ?_⟩
    rw [aux_evalAt_conj]
    have e1 : (fun j => Fin.append y₁ y₂ (Fin.castAdd r₂ j)) = y₁ := by
      funext j; rw [Fin.append_left]
    have e2 : (fun j => Fin.append y₁ y₂ (Fin.natAdd r₁ j)) = y₂ := by
      funext j; rw [Fin.append_right]
    rw [e1, e2, hy₁, hy₂]; ring
  · rintro ⟨y, hy⟩
    rw [aux_evalAt_conj] at hy
    have hz := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hy
    have h1 := (pow_eq_zero_iff (two_ne_zero)).mp hz.1
    have h2 := (pow_eq_zero_iff (two_ne_zero)).mp hz.2
    exact ⟨⟨fun j => y (Fin.castAdd r₂ j), h1⟩, ⟨fun j => y (Fin.natAdd r₁ j), h2⟩⟩

theorem representsZ_renameParams {k K r : ℕ} (g : Fin k → Fin K) (P : Poly k r)
    (S : Set (Fin k → ℕ)) (h : RepresentsZ P S) :
    RepresentsZ (rename (Sum.map g id) P) {V : Fin K → ℕ | (fun i => V (g i)) ∈ S} := by
  intro V
  simp only [Set.mem_setOf_eq]
  rw [h (fun i => V (g i))]
  refine exists_congr (fun y => ?_)
  have key : evalAt (rename (Sum.map g id) P) V y = evalAt P (fun i => V (g i)) y := by
    simp only [evalAt, eval_rename]
    refine congrArg (fun h => (eval h) P) ?_; funext w; cases w <;> rfl
  rw [key]

/-- `projectLast` evaluated at a ℤ-unknown vector whose first entry is a natural number `c`. -/
theorem aux_evalAt_projectLast_int {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℕ) (c : ℕ)
    (y : Fin r → ℤ) :
    evalAt (projectLast P) a (Fin.cons (c : ℤ) y) = evalAt P (Fin.snoc a c) y := by
  simp only [evalAt, projectLast, eval_rename]
  refine congrArg (fun h => (eval h) P) ?_
  funext v
  rcases v with i | j
  · simp only [Function.comp_apply]
    induction i using Fin.lastCases with
    | last =>
      have hn : ¬ ((Fin.last n : Fin (n+1)) : ℕ) < n := by rw [Fin.val_last]; exact lt_irrefl n
      simp only [hn, dif_neg, not_false_iff, Sum.elim_inl, Sum.elim_inr, Fin.snoc_last, Fin.cons_zero]
    | cast j =>
      have hlt : ((Fin.castSucc j : Fin (n+1)) : ℕ) < n := by rw [Fin.val_castSucc]; exact j.isLt
      simp only [hlt, dif_pos, Sum.elim_inl, Fin.snoc_castSucc]
      congr 2
  · simp only [Function.comp_apply, Sum.elim_inr, Fin.cons_succ]

/-! ### The guard polynomial and the guarded projection -/

/-- `c − (g₁² + g₂² + g₃² + g₄²)` with `c` = unknown 0 and the guards = the last four unknowns. -/
noncomputable def guardPoly (n r : ℕ) : Poly n (r + 1 + 4) :=
  X (Sum.inr (Fin.castAdd 4 (0 : Fin (r + 1)))) - ∑ k : Fin 4, (X (Sum.inr (Fin.natAdd (r + 1) k))) ^ 2

theorem evalAt_guardPoly {n r : ℕ} (a : Fin n → ℕ) (z : Fin (r + 1 + 4) → ℤ) :
    evalAt (guardPoly n r) a z
      = z (Fin.castAdd 4 (0 : Fin (r + 1))) - ∑ k : Fin 4, (z (Fin.natAdd (r + 1) k)) ^ 2 := by
  simp [evalAt, guardPoly]

theorem guardPoly_totalDegree (n r : ℕ) : (guardPoly n r).totalDegree ≤ 2 := by
  unfold guardPoly
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X]; omega
  · apply totalDegree_finsetSum_le
    intro k _
    rw [totalDegree_X_pow]

/-- Turn the last parameter into a ℤ-unknown guarded to be a natural number: `projectLast P`
    (padded by 4 unknowns) plus the square of the guard. Intended for `P` non-negative on ℤ-points
    (a sum of squares, e.g. `conj`), so that the sum vanishes iff both summands vanish. -/
noncomputable def projectLastGuard {n r : ℕ} (P : Poly (n + 1) r) : Poly n (r + 1 + 4) :=
  weakenUnknowns 4 (projectLast P) + (guardPoly n r) ^ 2

theorem totalDegree_projectLastGuard_le {n r : ℕ} (P : Poly (n + 1) r) :
    (projectLastGuard P).totalDegree ≤ max P.totalDegree 4 := by
  unfold projectLastGuard
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · have h1 : (weakenUnknowns 4 (projectLast P)).totalDegree ≤ P.totalDegree :=
      (totalDegree_weakenUnknowns_le _).trans (totalDegree_projectLast_le P)
    omega
  · refine (totalDegree_pow _ _).trans ?_
    have h2 := guardPoly_totalDegree n r
    omega

theorem evalAt_projectLastGuard {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℕ)
    (z : Fin (r + 1 + 4) → ℤ) :
    evalAt (projectLastGuard P) a z
      = evalAt (projectLast P) a (fun j => z (Fin.castAdd 4 j))
        + (z (Fin.castAdd 4 (0 : Fin (r + 1))) - ∑ k : Fin 4, (z (Fin.natAdd (r + 1) k)) ^ 2) ^ 2 := by
  have h1 := evalAt_weakenUnknowns (m := 4) (projectLast P) a z
  have h2 := evalAt_guardPoly (r := r) a z
  unfold projectLastGuard
  unfold evalAt at h1 h2 ⊢
  rw [map_add, map_pow, h1, h2]

theorem representsZ_projectLastGuard {n r : ℕ} (P : Poly (n + 1) r) (S : Set (Fin (n + 1) → ℕ))
    (hnn : ∀ ρ : (Fin (n + 1) ⊕ Fin r) → ℤ, 0 ≤ eval ρ P) (h : RepresentsZ P S) :
    RepresentsZ (projectLastGuard P) {a | ∃ c, Fin.snoc a c ∈ S} := by
  intro a
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨w, hw⟩ := (h _).mp hc
    obtain ⟨g1, g2, g3, g4, hg⟩ := Nat.sum_four_squares c
    let gv : Fin 4 → ℤ := ![(g1 : ℤ), g2, g3, g4]
    refine ⟨Fin.append (Fin.cons (c : ℤ) w) gv, ?_⟩
    rw [evalAt_projectLastGuard]
    have e1 : (fun j => Fin.append (Fin.cons (c : ℤ) w) gv (Fin.castAdd 4 j)) = Fin.cons (c : ℤ) w := by
      funext j; rw [Fin.append_left]
    rw [e1, aux_evalAt_projectLast_int, hw]
    have e2 : Fin.append (Fin.cons (c : ℤ) w) gv (Fin.castAdd 4 (0 : Fin (r + 1))) = c := by
      rw [Fin.append_left, Fin.cons_zero]
    have e3 : ∑ k : Fin 4, (Fin.append (Fin.cons (c : ℤ) w) gv (Fin.natAdd (r + 1) k)) ^ 2 = c := by
      simp only [Fin.append_right]
      simp [gv, Fin.sum_univ_four]
      exact_mod_cast hg
    rw [e2, e3]; ring
  · rintro ⟨z, hz⟩
    rw [evalAt_projectLastGuard] at hz
    have hfirst : 0 ≤ evalAt (projectLast P) a (fun j => z (Fin.castAdd 4 j)) := by
      unfold evalAt projectLast
      rw [eval_rename]
      exact hnn _
    have hz' := (add_eq_zero_iff_of_nonneg hfirst (sq_nonneg _)).mp hz
    have h1 := hz'.1
    have h2 := (pow_eq_zero_iff (two_ne_zero)).mp hz'.2
    have hnn : 0 ≤ z (Fin.castAdd 4 (0 : Fin (r + 1))) := by
      rw [sub_eq_zero] at h2; rw [h2]; positivity
    refine ⟨(z (Fin.castAdd 4 (0 : Fin (r + 1)))).toNat,
      (h _).mpr ⟨fun j => z (Fin.castAdd 4 j.succ), ?_⟩⟩
    rw [← aux_evalAt_projectLast_int, Int.toNat_of_nonneg hnn]
    have hq : Fin.cons (z (Fin.castAdd 4 (0 : Fin (r + 1)))) (fun j => z (Fin.castAdd 4 j.succ))
        = fun j => z (Fin.castAdd 4 j) :=
      Fin.cons_self_tail (fun j => z (Fin.castAdd 4 j))
    rw [hq]
    exact h1

/-! ### Main theorem -/

theorem graph_to_universality_Z {n r d ν₀ δ₀ : ℕ}
    (hU : UniversalPairZ ν₀ δ₀) (hG : GraphAchievableZ n r d) :
    UniversalAchievableZ n (r + ν₀ + 5) (2 * max d (max δ₀ 2)) := by
  intro A hA
  obtain ⟨e, he, r', hr', C, hCd, hCrep⟩ := hG
  obtain ⟨rA, PA, hPArep⟩ := hA
  -- B = e(A) ⊆ ℕ is DiophN: split the ℤ-unknowns of C, conjoin with A, project the parameter block
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
  have hDrep := representsZ_projectLastGuard (conj C (rename (Sum.map g id) PB)) _ hnnC hConjrep
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
  refine ⟨r' + ν'' + 1 + 4, ?_, projectLastGuard (conj C (rename (Sum.map g id) PB)), ?_, hDrep⟩
  · show r' + ν'' + 1 + 4 ≤ r + ν₀ + 5; omega
  · refine (totalDegree_projectLastGuard_le _).trans ?_
    have hc := totalDegree_conj_le C (rename (Sum.map g id) PB)
    have h1 : C.totalDegree ≤ d := hCd
    have h2 : (rename (Sum.map g id) PB).totalDegree ≤ δ₀ := (totalDegree_rename_le _ _).trans hPBd
    have hc' : (conj C (rename (Sum.map g id) PB)).totalDegree ≤ 2 * max d δ₀ :=
      hc.trans (Nat.mul_le_mul (le_refl 2) (max_le_max h1 h2))
    omega

/-- The resource-distorted equivalence U ⟺ G at fixed arity (ℤ-unknowns), assuming a universal pair. -/
theorem graph_universality_equivalence_Z {ν₀ δ₀ : ℕ} (hU : UniversalPairZ ν₀ δ₀) (n r d : ℕ) :
    (UniversalAchievableZ (n + 1) r d → GraphAchievableZ n r d) ∧
    (GraphAchievableZ n r d → UniversalAchievableZ n (r + ν₀ + 5) (2 * max d (max δ₀ 2))) :=
  ⟨universal_implies_graph_Z, graph_to_universality_Z hU⟩

end DiophCompression

#print axioms DiophCompression.representsZ_conj
#print axioms DiophCompression.representsZ_projectLastGuard
#print axioms DiophCompression.totalDegree_projectLastGuard_le
#print axioms DiophCompression.graph_to_universality_Z
#print axioms DiophCompression.graph_universality_equivalence_Z
