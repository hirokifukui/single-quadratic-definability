/-
  DiophCompression/Folding.lean — APAL Logic Pivot, Gate 2 (session 20, 2026-08-30, claude.ai direct).
  Statements frozen in frozen_statements/Folding_STATEMENTS.lean (md5 074d54d4). See that header.
-/
import DiophCompression.QuadraticPPSeparation
import DiophCompression.AtomicDegreeRank

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Definitions (verbatim from the freeze) -/

noncomputable def PPWitnessRankZ {n : ℕ} (d : ℕ) (A : Set (Fin n → ℕ)) : WithTop ℕ :=
  ⨅ (r : ℕ) (_ : ∃ m, ∃ S : PolySystem n r m, (∀ i, (S i).totalDegree ≤ d) ∧ SystemRepresentsZ S A),
    (r : WithTop ℕ)

noncomputable def PPArityRankZ (d n : ℕ) : WithTop ℕ :=
  ⨆ (A : Set (Fin n → ℕ)) (_ : WithinPPZ d A), PPWitnessRankZ d A

def preimageRel {n : ℕ} (e : (Fin n → ℕ) → ℕ) (B : Set (Fin 1 → ℕ)) : Set (Fin n → ℕ) :=
  {a | (fun _ => e a) ∈ B}

def imageRel {n : ℕ} (e : (Fin n → ℕ) → ℕ) (A : Set (Fin n → ℕ)) : Set (Fin 1 → ℕ) :=
  {c | ∃ a ∈ A, e a = c 0}

/-! ### Generic infimum-over-ℕ lemmas -/

theorem iInf_nat_eq_top_iff (p : ℕ → Prop) :
    (⨅ (r : ℕ) (_ : p r), (r : WithTop ℕ)) = ⊤ ↔ ∀ r, ¬ p r := by
  rw [iInf_eq_top]
  constructor
  · intro h r hr
    have := h r
    rw [iInf_pos hr] at this
    exact WithTop.coe_ne_top this
  · intro h r
    rw [iInf_neg (h r)]

theorem iInf_nat_attained (p : ℕ → Prop) (h : ∃ r, p r) :
    ∃ r₀, p r₀ ∧ (⨅ (r : ℕ) (_ : p r), (r : WithTop ℕ)) = r₀ := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h,
    le_antisymm (iInf₂_le _ (Nat.find_spec h)) (le_iInf₂ fun r hr => ?_)⟩
  exact_mod_cast Nat.find_min' h hr

/-! ### Characterizations -/

theorem ppWitnessRankZ_eq_top_iff {n : ℕ} (d : ℕ) (A : Set (Fin n → ℕ)) :
    PPWitnessRankZ d A = ⊤ ↔ ¬ WithinPPZ d A := by
  unfold PPWitnessRankZ WithinPPZ
  rw [iInf_nat_eq_top_iff]
  simp only [not_exists]

theorem ppWitnessRankZ_attained {n : ℕ} {d : ℕ} {A : Set (Fin n → ℕ)}
    (h : PPWitnessRankZ d A ≠ ⊤) :
    ∃ r₀, (∃ m, ∃ S : PolySystem n r₀ m, (∀ i, (S i).totalDegree ≤ d) ∧ SystemRepresentsZ S A) ∧
      PPWitnessRankZ d A = r₀ := by
  have hw : WithinPPZ d A := by
    by_contra hno
    exact h ((ppWitnessRankZ_eq_top_iff d A).mpr hno)
  exact iInf_nat_attained _ hw

theorem ppWitnessRankZ_le_coe_iff {n : ℕ} (d r : ℕ) (A : Set (Fin n → ℕ)) :
    PPWitnessRankZ d A ≤ r ↔ ∃ r' ≤ r, ∃ m, ∃ S : PolySystem n r' m,
      (∀ i, (S i).totalDegree ≤ d) ∧ SystemRepresentsZ S A := by
  constructor
  · intro h
    have hne : PPWitnessRankZ d A ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top h
    obtain ⟨r₀, hr₀, hdef⟩ := ppWitnessRankZ_attained hne
    rw [hdef] at h
    exact ⟨r₀, by exact_mod_cast h, hr₀⟩
  · rintro ⟨r', hr', m, S, hS, hrep⟩
    exact le_trans (iInf₂_le r' ⟨m, S, hS, hrep⟩) (by exact_mod_cast hr')

theorem ppWitnessRankZ_le_atomicDegreeRankZ {n : ℕ} (d : ℕ) (A : Set (Fin (n + 1) → ℕ)) :
    PPWitnessRankZ d A ≤ AtomicDegreeRankZ A d := by
  unfold AtomicDegreeRankZ
  refine le_iInf₂ fun r hr => ?_
  obtain ⟨P, hP, hrep⟩ := hr
  refine iInf₂_le r ⟨1, fun _ => P, fun _ => hP, fun a => ?_⟩
  rw [hrep a]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, fun _ => hy⟩
  · rintro ⟨y, hy⟩; exact ⟨y, hy 0⟩

theorem preimageRel_imageRel {n : ℕ} {e : (Fin n → ℕ) → ℕ} (he : Function.Injective e)
    (A : Set (Fin n → ℕ)) : preimageRel e (imageRel e A) = A := by
  ext a
  constructor
  · rintro ⟨a', ha', h⟩
    have : a' = a := he h
    rw [← this]; exact ha'
  · intro ha
    exact ⟨a, ha, rfl⟩

/-! ### Evaluation under renaming -/

theorem evalAt_rename {n r n' r' : ℕ} (φ : Fin n ⊕ Fin r → Fin n' ⊕ Fin r') (P : Poly n r)
    (a : Fin n' → ℕ) (y : Fin r' → ℤ) (a₀ : Fin n → ℕ) (y₀ : Fin r → ℤ)
    (h : ∀ v, Sum.elim (fun i => (a i : ℤ)) y (φ v) = Sum.elim (fun i => (a₀ i : ℤ)) y₀ v) :
    evalAt (rename φ P) a y = evalAt P a₀ y₀ := by
  simp only [evalAt, eval_rename]
  have hf : (Sum.elim (fun i => (a i : ℤ)) y ∘ φ) = Sum.elim (fun i => (a₀ i : ℤ)) y₀ := funext h
  rw [hf]

theorem snoc_mem_graph_iff {n : ℕ} (e : (Fin n → ℕ) → ℕ) (a : Fin n → ℕ) (c : ℕ) :
    Fin.snoc a c ∈ graph e ↔ c = e a := by
  simp only [graph, Set.mem_setOf_eq, Fin.snoc_last, Fin.init_snoc]

theorem exists_toNat_of_sum_four_sq (c : ℤ) (w : Fin 4 → ℤ) (h : c - ∑ j, (w j) ^ 2 = 0) :
    ((c.toNat : ℕ) : ℤ) = c := by
  have hc : 0 ≤ c := by
    rw [sub_eq_zero] at h
    rw [h]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  exact Int.toNat_of_nonneg hc

theorem exists_four_sq (c : ℕ) : ∃ w : Fin 4 → ℤ, ((c : ℕ) : ℤ) - ∑ j, (w j) ^ 2 = 0 := by
  obtain ⟨a, b, c', d, h⟩ := Nat.sum_four_squares c
  refine ⟨![a, b, c', d], ?_⟩
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  rw [sub_eq_zero]
  exact_mod_cast h.symm

/-! ### The preimage fold: witnesses `Fin r ⊕ (c, w₁..w₄) ⊕ Fin q` -/

section Preimage

variable {n r q : ℕ}

def wS (t : Fin r) : Fin (r + 5 + q) := Fin.castAdd q (Fin.castAdd 5 t)
def wC : Fin (r + 5 + q) := Fin.castAdd q (Fin.natAdd r 0)
def wSq (j : Fin 4) : Fin (r + 5 + q) := Fin.castAdd q (Fin.natAdd r j.succ)
def wT (t : Fin q) : Fin (r + 5 + q) := Fin.natAdd (r + 5) t

def φS : Fin (n + 1) ⊕ Fin r → Fin n ⊕ Fin (r + 5 + q)
  | Sum.inl j => Fin.lastCases (Sum.inr (wC (r := r) (q := q))) (fun j' => Sum.inl j') j
  | Sum.inr t => Sum.inr (wS t)

def φT : Fin 1 ⊕ Fin q → Fin n ⊕ Fin (r + 5 + q)
  | Sum.inl _ => Sum.inr (wC (r := r) (q := q))
  | Sum.inr t => Sum.inr (wT t)

noncomputable def sqEq : Poly n (r + 5 + q) :=
  X (Sum.inr wC) - ∑ j : Fin 4, (X (Sum.inr (wSq j))) ^ 2

theorem sqEq_totalDegree : (sqEq (n := n) (r := r) (q := q)).totalDegree ≤ 2 := by
  unfold sqEq
  refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
  · rw [totalDegree_X]; omega
  · refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun j _ => ?_)
    refine le_trans (totalDegree_pow _ _) ?_
    rw [totalDegree_X]

noncomputable def preimageSystem {m k : ℕ} (S : PolySystem (n + 1) r m) (T : PolySystem 1 q k) :
    PolySystem n (r + 5 + q) (m + k + 1) :=
  Fin.append (Fin.append (fun i => rename φS (S i)) (fun i => rename φT (T i)))
    (fun _ : Fin 1 => sqEq)

/-- Witness assembly. -/
def assembleW (yS : Fin r → ℤ) (c : ℤ) (w : Fin 4 → ℤ) (yT : Fin q → ℤ) : Fin (r + 5 + q) → ℤ :=
  Fin.append (Fin.append yS (Fin.cons c w)) yT

theorem assembleW_wS (yS : Fin r → ℤ) (c : ℤ) (w : Fin 4 → ℤ) (yT : Fin q → ℤ) (t : Fin r) :
    assembleW yS c w yT (wS t) = yS t := by
  simp [assembleW, wS, Fin.append_left]

theorem assembleW_wC (yS : Fin r → ℤ) (c : ℤ) (w : Fin 4 → ℤ) (yT : Fin q → ℤ) :
    assembleW yS c w yT wC = c := by
  simp [assembleW, wC, Fin.append_left, Fin.append_right]

theorem assembleW_wSq (yS : Fin r → ℤ) (c : ℤ) (w : Fin 4 → ℤ) (yT : Fin q → ℤ) (j : Fin 4) :
    assembleW yS c w yT (wSq j) = w j := by
  simp [assembleW, wSq, Fin.append_left, Fin.append_right]

theorem assembleW_wT (yS : Fin r → ℤ) (c : ℤ) (w : Fin 4 → ℤ) (yT : Fin q → ℤ) (t : Fin q) :
    assembleW yS c w yT (wT t) = yT t := by
  simp [assembleW, wT, Fin.append_right]

/-- Every witness vector is an assembly of its four blocks. -/
theorem assembleW_eq (y : Fin (r + 5 + q) → ℤ) :
    assembleW (fun t => y (wS t)) (y wC) (fun j => y (wSq j)) (fun t => y (wT t)) = y := by
  funext i
  unfold assembleW
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right]
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero]; rfl
      · rw [Fin.cons_succ]; rfl
  · rw [Fin.append_right]; rfl

theorem evalAt_rename_φS (P : Poly (n + 1) r) (a : Fin n → ℕ) (y : Fin (r + 5 + q) → ℤ)
    (c : ℕ) (hc : y wC = (c : ℤ)) :
    evalAt (rename φS P) a y = evalAt P (Fin.snoc a c) (fun t => y (wS t)) := by
  refine evalAt_rename φS P a y _ _ fun v => ?_
  cases v with
  | inl j =>
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp [φS, Fin.snoc_last, hc]
    · simp [φS, Fin.snoc_castSucc]
  | inr t => rfl

theorem evalAt_rename_φT (P : Poly 1 q) (a : Fin n → ℕ) (y : Fin (r + 5 + q) → ℤ)
    (c : ℕ) (hc : y wC = (c : ℤ)) :
    evalAt (rename φT P) a y = evalAt P (fun _ => c) (fun t => y (wT t)) := by
  refine evalAt_rename φT P a y _ _ fun v => ?_
  cases v with
  | inl j => simp [φT, hc]
  | inr t => rfl

theorem evalAt_sqEq (a : Fin n → ℕ) (y : Fin (r + 5 + q) → ℤ) :
    evalAt (sqEq (n := n) (r := r) (q := q)) a y = y wC - ∑ j, (y (wSq j)) ^ 2 := by
  simp [evalAt, sqEq]

theorem preimageSystem_totalDegree {m k d : ℕ} (hd : 2 ≤ d)
    (S : PolySystem (n + 1) r m) (T : PolySystem 1 q k)
    (hS : ∀ i, (S i).totalDegree ≤ d) (hT : ∀ i, (T i).totalDegree ≤ d) :
    ∀ i, (preimageSystem S T i).totalDegree ≤ d := by
  intro i
  unfold preimageSystem
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact le_trans (totalDegree_rename_le _ _) (hS i)
    · rw [Fin.append_right]; exact le_trans (totalDegree_rename_le _ _) (hT i)
  · rw [Fin.append_right]; exact le_trans sqEq_totalDegree hd

theorem preimageSystem_representsZ {m k : ℕ} (e : (Fin n → ℕ) → ℕ) (B : Set (Fin 1 → ℕ))
    (S : PolySystem (n + 1) r m) (T : PolySystem 1 q k)
    (hS : SystemRepresentsZ S (graph e)) (hT : SystemRepresentsZ T B) :
    SystemRepresentsZ (preimageSystem S T) (preimageRel e B) := by
  intro a
  constructor
  · intro ha
    have hg : Fin.snoc a (e a) ∈ graph e := (snoc_mem_graph_iff e a (e a)).mpr rfl
    obtain ⟨yS, hyS⟩ := (hS _).mp hg
    obtain ⟨yT, hyT⟩ := (hT _).mp ha
    obtain ⟨w, hw⟩ := exists_four_sq (e a)
    refine ⟨assembleW yS ((e a : ℕ) : ℤ) w yT, ?_⟩
    intro i
    unfold preimageSystem
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left, evalAt_rename_φS _ _ _ (e a) (assembleW_wC _ _ _ _)]
        simp only [assembleW_wS]
        exact hyS i
      · rw [Fin.append_right, evalAt_rename_φT _ _ _ (e a) (assembleW_wC _ _ _ _)]
        simp only [assembleW_wT]
        exact hyT i
    · rw [Fin.append_right, evalAt_sqEq]
      simp only [assembleW_wC, assembleW_wSq]
      exact hw
  · rintro ⟨y, hy⟩
    have hsq := hy (Fin.natAdd (m + k) 0)
    unfold preimageSystem at hsq
    rw [Fin.append_right, evalAt_sqEq] at hsq
    have hc : y wC = (((y wC).toNat : ℕ) : ℤ) := (exists_toNat_of_sum_four_sq _ _ hsq).symm
    set c : ℕ := (y wC).toNat with hcdef
    have hSv : ∀ i, evalAt (S i) (Fin.snoc a c) (fun t => y (wS t)) = 0 := by
      intro i
      have := hy (Fin.castAdd 1 (Fin.castAdd k i))
      unfold preimageSystem at this
      rwa [Fin.append_left, Fin.append_left, evalAt_rename_φS _ _ _ c hc] at this
    have hTv : ∀ i, evalAt (T i) (fun _ => c) (fun t => y (wT t)) = 0 := by
      intro i
      have := hy (Fin.castAdd 1 (Fin.natAdd m i))
      unfold preimageSystem at this
      rwa [Fin.append_left, Fin.append_right, evalAt_rename_φT _ _ _ c hc] at this
    have hg : Fin.snoc a c ∈ graph e := (hS _).mpr ⟨_, hSv⟩
    have hce : c = e a := (snoc_mem_graph_iff e a c).mp hg
    have hB : (fun _ : Fin 1 => c) ∈ B := (hT _).mpr ⟨_, hTv⟩
    show (fun _ : Fin 1 => e a) ∈ B
    rw [← hce]; exact hB

end Preimage

theorem ppWitnessRankZ_preimage_le {n d : ℕ} (hd : 2 ≤ d) (e : (Fin n → ℕ) → ℕ)
    (B : Set (Fin 1 → ℕ)) :
    PPWitnessRankZ d (preimageRel e B) ≤ PPWitnessRankZ d (graph e) + 5 + PPWitnessRankZ d B := by
  by_cases hg : PPWitnessRankZ d (graph e) = ⊤
  · rw [hg]; simp
  by_cases hB : PPWitnessRankZ d B = ⊤
  · rw [hB]; simp
  obtain ⟨r, ⟨m, S, hSd, hSrep⟩, hr⟩ := ppWitnessRankZ_attained hg
  obtain ⟨q, ⟨k, T, hTd, hTrep⟩, hq⟩ := ppWitnessRankZ_attained hB
  rw [hr, hq]
  have : PPWitnessRankZ d (preimageRel e B) ≤ ((r + 5 + q : ℕ) : WithTop ℕ) :=
    iInf₂_le _ ⟨_, preimageSystem S T, preimageSystem_totalDegree hd S T hSd hTd,
      preimageSystem_representsZ e B S T hSrep hTrep⟩
  exact_mod_cast this

/-! ### The image fold: witnesses `Fin r ⊕ (a-block ⊕ 4n squares) ⊕ Fin q`, then `5n` by `finCongr` -/

section Image

variable {n r q : ℕ}

def vS (t : Fin r) : Fin (r + (n + n * 4) + q) := Fin.castAdd q (Fin.castAdd (n + n * 4) t)
def vA (x : Fin n) : Fin (r + (n + n * 4) + q) := Fin.castAdd q (Fin.natAdd r (Fin.castAdd (n * 4) x))
def vSq (x : Fin n) (j : Fin 4) : Fin (r + (n + n * 4) + q) :=
  Fin.castAdd q (Fin.natAdd r (Fin.natAdd n (finProdFinEquiv (x, j))))
def vT (t : Fin q) : Fin (r + (n + n * 4) + q) := Fin.natAdd (r + (n + n * 4)) t

def ψS : Fin (n + 1) ⊕ Fin r → Fin 1 ⊕ Fin (r + (n + n * 4) + q)
  | Sum.inl j => Fin.lastCases (Sum.inl 0) (fun x => Sum.inr (vA (r := r) (q := q) x)) j
  | Sum.inr t => Sum.inr (vS t)

def ψT : Fin n ⊕ Fin q → Fin 1 ⊕ Fin (r + (n + n * 4) + q)
  | Sum.inl x => Sum.inr (vA x)
  | Sum.inr t => Sum.inr (vT t)

noncomputable def sqEqs (x : Fin n) : Poly 1 (r + (n + n * 4) + q) :=
  X (Sum.inr (vA x)) - ∑ j : Fin 4, (X (Sum.inr (vSq x j))) ^ 2

theorem sqEqs_totalDegree (x : Fin n) : (sqEqs (r := r) (q := q) x).totalDegree ≤ 2 := by
  unfold sqEqs
  refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
  · rw [totalDegree_X]; omega
  · refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun j _ => ?_)
    refine le_trans (totalDegree_pow _ _) ?_
    rw [totalDegree_X]

noncomputable def imageSystem {m k : ℕ} (S : PolySystem (n + 1) r m) (T : PolySystem n q k) :
    PolySystem 1 (r + (n + n * 4) + q) (m + k + n) :=
  Fin.append (Fin.append (fun i => rename ψS (S i)) (fun i => rename ψT (T i))) (fun x => sqEqs x)

def assembleV (yS : Fin r → ℤ) (a : Fin n → ℤ) (w : Fin n → Fin 4 → ℤ) (yT : Fin q → ℤ) :
    Fin (r + (n + n * 4) + q) → ℤ :=
  Fin.append (Fin.append yS (Fin.append a (fun p => w (finProdFinEquiv.symm p).1
    (finProdFinEquiv.symm p).2))) yT

theorem assembleV_vS (yS : Fin r → ℤ) (a : Fin n → ℤ) (w : Fin n → Fin 4 → ℤ) (yT : Fin q → ℤ)
    (t : Fin r) : assembleV yS a w yT (vS t) = yS t := by
  simp [assembleV, vS, Fin.append_left]

theorem assembleV_vA (yS : Fin r → ℤ) (a : Fin n → ℤ) (w : Fin n → Fin 4 → ℤ) (yT : Fin q → ℤ)
    (x : Fin n) : assembleV yS a w yT (vA x) = a x := by
  simp [assembleV, vA, Fin.append_left, Fin.append_right]

theorem assembleV_vSq (yS : Fin r → ℤ) (a : Fin n → ℤ) (w : Fin n → Fin 4 → ℤ) (yT : Fin q → ℤ)
    (x : Fin n) (j : Fin 4) : assembleV yS a w yT (vSq x j) = w x j := by
  simp only [assembleV, vSq, Fin.append_left, Fin.append_right, Equiv.symm_apply_apply]

theorem assembleV_vT (yS : Fin r → ℤ) (a : Fin n → ℤ) (w : Fin n → Fin 4 → ℤ) (yT : Fin q → ℤ)
    (t : Fin q) : assembleV yS a w yT (vT t) = yT t := by
  simp [assembleV, vT, Fin.append_right]

theorem evalAt_rename_ψS (P : Poly (n + 1) r) (c : Fin 1 → ℕ) (y : Fin (r + (n + n * 4) + q) → ℤ)
    (a : Fin n → ℕ) (ha : ∀ x, y (vA x) = (a x : ℤ)) :
    evalAt (rename ψS P) c y = evalAt P (Fin.snoc a (c 0)) (fun t => y (vS t)) := by
  refine evalAt_rename ψS P c y _ _ fun v => ?_
  cases v with
  | inl j =>
    refine Fin.lastCases ?_ (fun x => ?_) j
    · simp [ψS, Fin.snoc_last]
    · simp [ψS, Fin.snoc_castSucc, ha]
  | inr t => rfl

theorem evalAt_rename_ψT (P : Poly n q) (c : Fin 1 → ℕ) (y : Fin (r + (n + n * 4) + q) → ℤ)
    (a : Fin n → ℕ) (ha : ∀ x, y (vA x) = (a x : ℤ)) :
    evalAt (rename ψT P) c y = evalAt P a (fun t => y (vT t)) := by
  refine evalAt_rename ψT P c y _ _ fun v => ?_
  cases v with
  | inl x => simp [ψT, ha]
  | inr t => rfl

theorem evalAt_sqEqs (x : Fin n) (c : Fin 1 → ℕ) (y : Fin (r + (n + n * 4) + q) → ℤ) :
    evalAt (sqEqs (r := r) (q := q) x) c y = y (vA x) - ∑ j, (y (vSq x j)) ^ 2 := by
  simp [evalAt, sqEqs]

theorem imageSystem_totalDegree {m k d : ℕ} (hd : 2 ≤ d)
    (S : PolySystem (n + 1) r m) (T : PolySystem n q k)
    (hS : ∀ i, (S i).totalDegree ≤ d) (hT : ∀ i, (T i).totalDegree ≤ d) :
    ∀ i, (imageSystem S T i).totalDegree ≤ d := by
  intro i
  unfold imageSystem
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact le_trans (totalDegree_rename_le _ _) (hS i)
    · rw [Fin.append_right]; exact le_trans (totalDegree_rename_le _ _) (hT i)
  · rw [Fin.append_right]; exact le_trans (sqEqs_totalDegree i) hd

theorem imageSystem_representsZ {m k : ℕ} (e : (Fin n → ℕ) → ℕ) (A : Set (Fin n → ℕ))
    (S : PolySystem (n + 1) r m) (T : PolySystem n q k)
    (hS : SystemRepresentsZ S (graph e)) (hT : SystemRepresentsZ T A) :
    SystemRepresentsZ (imageSystem S T) (imageRel e A) := by
  intro c
  constructor
  · rintro ⟨a, ha, hea⟩
    have hg : Fin.snoc a (c 0) ∈ graph e := (snoc_mem_graph_iff e a (c 0)).mpr hea.symm
    obtain ⟨yS, hyS⟩ := (hS _).mp hg
    obtain ⟨yT, hyT⟩ := (hT _).mp ha
    have hw : ∀ x, ∃ w : Fin 4 → ℤ, ((a x : ℕ) : ℤ) - ∑ j, (w j) ^ 2 = 0 :=
      fun x => exists_four_sq (a x)
    choose w hw using hw
    refine ⟨assembleV yS (fun x => (a x : ℤ)) w yT, ?_⟩
    have hva : ∀ x, assembleV yS (fun x => (a x : ℤ)) w yT (vA x) = (a x : ℤ) :=
      fun x => assembleV_vA _ _ _ _ x
    intro i
    unfold imageSystem
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left, evalAt_rename_ψS _ _ _ a hva]
        simp only [assembleV_vS]
        exact hyS i
      · rw [Fin.append_right, evalAt_rename_ψT _ _ _ a hva]
        simp only [assembleV_vT]
        exact hyT i
    · rw [Fin.append_right, evalAt_sqEqs]
      simp only [assembleV_vA, assembleV_vSq]
      exact hw i
  · rintro ⟨y, hy⟩
    have hsq : ∀ x, y (vA x) - ∑ j, (y (vSq x j)) ^ 2 = 0 := by
      intro x
      have := hy (Fin.natAdd (m + k) x)
      unfold imageSystem at this
      rwa [Fin.append_right, evalAt_sqEqs] at this
    set a : Fin n → ℕ := fun x => (y (vA x)).toNat with hadef
    have ha : ∀ x, y (vA x) = (a x : ℤ) :=
      fun x => (exists_toNat_of_sum_four_sq _ _ (hsq x)).symm
    have hSv : ∀ i, evalAt (S i) (Fin.snoc a (c 0)) (fun t => y (vS t)) = 0 := by
      intro i
      have := hy (Fin.castAdd n (Fin.castAdd k i))
      unfold imageSystem at this
      rwa [Fin.append_left, Fin.append_left, evalAt_rename_ψS _ _ _ a ha] at this
    have hTv : ∀ i, evalAt (T i) a (fun t => y (vT t)) = 0 := by
      intro i
      have := hy (Fin.castAdd n (Fin.natAdd m i))
      unfold imageSystem at this
      rwa [Fin.append_left, Fin.append_right, evalAt_rename_ψT _ _ _ a ha] at this
    have hg : Fin.snoc a (c 0) ∈ graph e := (hS _).mpr ⟨_, hSv⟩
    have hce : c 0 = e a := (snoc_mem_graph_iff e a (c 0)).mp hg
    exact ⟨a, (hT _).mpr ⟨_, hTv⟩, hce.symm⟩

/-- Renaming witnesses along an equivalence preserves representation and degree. -/
theorem system_witness_equiv {n r r' m : ℕ} (σ : Fin r ≃ Fin r') (S : PolySystem n r m)
    (A : Set (Fin n → ℕ)) (d : ℕ) (hS : ∀ i, (S i).totalDegree ≤ d) (hrep : SystemRepresentsZ S A) :
    ∃ S' : PolySystem n r' m, (∀ i, (S' i).totalDegree ≤ d) ∧ SystemRepresentsZ S' A := by
  refine ⟨fun i => rename (Sum.map id σ) (S i), fun i => le_trans (totalDegree_rename_le _ _) (hS i),
    fun a => ?_⟩
  rw [hrep a]
  have key : ∀ (y : Fin r' → ℤ) (i : Fin m),
      evalAt (rename (Sum.map id σ) (S i)) a y = evalAt (S i) a (fun t => y (σ t)) := by
    intro y i
    refine evalAt_rename _ _ a y a _ fun v => ?_
    cases v <;> rfl
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨fun t => y (σ.symm t), fun i => ?_⟩
    rw [key]
    simp only [Equiv.symm_apply_apply]
    exact hy i
  · rintro ⟨y, hy⟩
    refine ⟨fun t => y (σ t), fun i => ?_⟩
    simp only [key] at hy
    exact hy i

end Image

theorem ppWitnessRankZ_image_le {n d : ℕ} (hd : 2 ≤ d) (e : (Fin n → ℕ) → ℕ)
    (A : Set (Fin n → ℕ)) :
    PPWitnessRankZ d (imageRel e A) ≤ PPWitnessRankZ d (graph e) + 5 * n + PPWitnessRankZ d A := by
  by_cases hg : PPWitnessRankZ d (graph e) = ⊤
  · rw [hg]; simp
  by_cases hA : PPWitnessRankZ d A = ⊤
  · rw [hA]; simp
  obtain ⟨r, ⟨m, S, hSd, hSrep⟩, hr⟩ := ppWitnessRankZ_attained hg
  obtain ⟨q, ⟨k, T, hTd, hTrep⟩, hq⟩ := ppWitnessRankZ_attained hA
  rw [hr, hq]
  obtain ⟨U, hUd, hUrep⟩ := system_witness_equiv (finCongr (by ring : r + (n + n * 4) + q = r + 5 * n + q))
    (imageSystem S T) (imageRel e A) d (imageSystem_totalDegree hd S T hSd hTd)
    (imageSystem_representsZ e A S T hSrep hTrep)
  have : PPWitnessRankZ d (imageRel e A) ≤ ((r + 5 * n + q : ℕ) : WithTop ℕ) :=
    iInf₂_le _ ⟨_, U, hUd, hUrep⟩
  exact_mod_cast this

/-! ### Theorem F -/

theorem ppArityRankZ_fold {n d r : ℕ} (hd : 2 ≤ d) (e : (Fin n → ℕ) → ℕ)
    (he : Function.Injective e) (hr : PPWitnessRankZ d (graph e) ≤ r) :
    PPArityRankZ d n ≤ PPArityRankZ d 1 + (r + 5) := by
  unfold PPArityRankZ
  refine iSup₂_le fun A hA => ?_
  have hAne : PPWitnessRankZ d A ≠ ⊤ := fun h => (ppWitnessRankZ_eq_top_iff d A).mp h hA
  have himg_le := ppWitnessRankZ_image_le hd e A
  have himg_ne : PPWitnessRankZ d (imageRel e A) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ himg_le
    exact WithTop.add_ne_top.mpr ⟨WithTop.add_ne_top.mpr
      ⟨ne_top_of_le_ne_top WithTop.coe_ne_top hr, WithTop.coe_ne_top⟩, hAne⟩
  have himg_pp : WithinPPZ d (imageRel e A) := by
    by_contra hno
    exact himg_ne ((ppWitnessRankZ_eq_top_iff d _).mpr hno)
  have h1 : PPWitnessRankZ d (imageRel e A) ≤ ⨆ (B : Set (Fin 1 → ℕ)) (_ : WithinPPZ d B),
      PPWitnessRankZ d B :=
    le_iSup₂ (f := fun (B : Set (Fin 1 → ℕ)) (_ : WithinPPZ d B) => PPWitnessRankZ d B)
      (imageRel e A) himg_pp
  have h2 := ppWitnessRankZ_preimage_le hd e (imageRel e A)
  rw [preimageRel_imageRel he] at h2
  calc PPWitnessRankZ d A
      ≤ PPWitnessRankZ d (graph e) + 5 + PPWitnessRankZ d (imageRel e A) := h2
    _ ≤ (r + 5) + (⨆ (B : Set (Fin 1 → ℕ)) (_ : WithinPPZ d B), PPWitnessRankZ d B) :=
        add_le_add (add_le_add_left hr 5) h1
    _ = _ := add_comm _ _

/-! ### Degree 2 -/

theorem ternaryPair_ppWitnessRankZ_le_one : PPWitnessRankZ 2 (graph ternaryPair) ≤ 1 :=
  (ppWitnessRankZ_le_coe_iff 2 1 _).mpr
    ⟨1, le_rfl, 2, ternaryPairSystem, ternaryPairSystem_totalDegree, ternaryPairSystem_representsZ⟩

theorem ppArityRankZ_two_three_le : PPArityRankZ 2 3 ≤ PPArityRankZ 2 1 + 6 := by
  have := ppArityRankZ_fold le_rfl ternaryPair ternaryPair_injective ternaryPair_ppWitnessRankZ_le_one
  norm_num at this
  exact this

theorem ppArityRankZ_two_finite_transfer (h : PPArityRankZ 2 1 ≠ ⊤) :
    ∀ n, PPArityRankZ 2 n ≠ ⊤ := by
  intro n
  obtain ⟨e, he, hpp⟩ := ppQuadratic_graph_all_arity n
  have hne : PPWitnessRankZ 2 (graph e) ≠ ⊤ := fun h' => (ppWitnessRankZ_eq_top_iff 2 _).mp h' hpp
  obtain ⟨r, _, hr⟩ := ppWitnessRankZ_attained hne
  have := ppArityRankZ_fold le_rfl e he (le_of_eq hr)
  refine ne_top_of_le_ne_top ?_ this
  exact WithTop.add_ne_top.mpr ⟨h, WithTop.coe_ne_top⟩

/-! ### Atomic contrast -/

theorem atomicDegreeRankZ_ternary_two_top (e : (Fin 3 → ℕ) → ℕ) (he : Function.Injective e) :
    AtomicDegreeRankZ (graph e) 2 = ⊤ := by
  rw [atomicDegreeRankZ_eq_top_iff]
  intro r ⟨P, hP, hrep⟩
  exact codingDegree_three_exact.2 ⟨r, e, he, r, le_rfl, P, hP, hrep⟩

theorem atomicDegreeRankZ_attained {n : ℕ} {d : ℕ} {A : Set (Fin (n + 1) → ℕ)}
    (h : AtomicDegreeRankZ A d ≠ ⊤) :
    ∃ r₀, (∃ P : Poly (n + 1) r₀, P.totalDegree ≤ d ∧ RepresentsZ P A) ∧
      AtomicDegreeRankZ A d = r₀ := by
  have hw : ∃ r, ∃ P : Poly (n + 1) r, P.totalDegree ≤ d ∧ RepresentsZ P A := by
    by_contra hno
    push Not at hno
    exact h ((atomicDegreeRankZ_eq_top_iff A d).mpr fun r hr => by
      obtain ⟨P, hP, hrep⟩ := hr; exact hno r P hP hrep)
  exact iInf_nat_attained _ hw

/-- Sum of squares: a system of degree ≤ `D` collapses to one equation of degree ≤ `2D`. -/
theorem exists_single_of_system {n r m D : ℕ} (U : PolySystem n r m) (A : Set (Fin n → ℕ))
    (hU : ∀ i, (U i).totalDegree ≤ D) (hrep : SystemRepresentsZ U A) :
    ∃ P : Poly n r, P.totalDegree ≤ 2 * D ∧ RepresentsZ P A := by
  refine ⟨∑ i, (U i) ^ 2, ?_, fun a => ?_⟩
  · refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun i _ => ?_)
    exact le_trans (totalDegree_pow _ _) (Nat.mul_le_mul_left 2 (hU i))
  · rw [hrep a]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [evalAt_sum_sq]
      exact Finset.sum_eq_zero fun i _ => by rw [hy i]; ring
    · rintro ⟨y, hy⟩
      refine ⟨y, fun i => ?_⟩
      rw [evalAt_sum_sq, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at hy
      exact pow_eq_zero_iff (two_ne_zero) |>.mp (hy i (Finset.mem_univ i))

theorem atomicDegreeRankZ_preimage_le {n d : ℕ} (e : (Fin (n + 1) → ℕ) → ℕ)
    (B : Set (Fin 1 → ℕ)) :
    AtomicDegreeRankZ (preimageRel e B) (max (2 * d) 4) ≤
      AtomicDegreeRankZ (graph e) d + 5 + AtomicDegreeRankZ B d := by
  by_cases hg : AtomicDegreeRankZ (graph e) d = ⊤
  · rw [hg]; simp
  by_cases hB : AtomicDegreeRankZ B d = ⊤
  · rw [hB]; simp
  obtain ⟨r, ⟨P, hPd, hPrep⟩, hr⟩ := atomicDegreeRankZ_attained hg
  obtain ⟨q, ⟨Q, hQd, hQrep⟩, hq⟩ := atomicDegreeRankZ_attained hB
  rw [hr, hq]
  have hS : SystemRepresentsZ (fun _ : Fin 1 => P) (graph e) := by
    intro a; rw [hPrep a]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, fun _ => hy⟩, fun ⟨y, hy⟩ => ⟨y, hy 0⟩⟩
  have hT : SystemRepresentsZ (fun _ : Fin 1 => Q) B := by
    intro a; rw [hQrep a]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, fun _ => hy⟩, fun ⟨y, hy⟩ => ⟨y, hy 0⟩⟩
  have hUd := preimageSystem_totalDegree (d := max d 2) (le_max_right d 2)
    (fun _ : Fin 1 => P) (fun _ : Fin 1 => Q)
    (fun _ => le_trans hPd (le_max_left d 2)) (fun _ => le_trans hQd (le_max_left d 2))
  have hUrep := preimageSystem_representsZ e B (fun _ : Fin 1 => P) (fun _ : Fin 1 => Q) hS hT
  obtain ⟨R, hRd, hRrep⟩ := exists_single_of_system _ _ hUd hUrep
  have hRd' : R.totalDegree ≤ max (2 * d) 4 := by
    refine le_trans hRd ?_
    rcases le_total d 2 with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  have : AtomicDegreeRankZ (preimageRel e B) (max (2 * d) 4) ≤ ((r + 5 + q : ℕ) : WithTop ℕ) :=
    iInf₂_le _ ⟨R, hRd', hRrep⟩
  exact_mod_cast this

end DiophCompression

#print axioms DiophCompression.ppArityRankZ_fold
#print axioms DiophCompression.ppArityRankZ_two_three_le
#print axioms DiophCompression.ppArityRankZ_two_finite_transfer
#print axioms DiophCompression.atomicDegreeRankZ_ternary_two_top
#print axioms DiophCompression.atomicDegreeRankZ_preimage_le
