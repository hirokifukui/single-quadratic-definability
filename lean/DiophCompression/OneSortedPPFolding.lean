/-
  DiophCompression/OneSortedPPFolding.lean — APAL r20 Gate 4 (session 22, 2026-08-31, claude.ai direct).
  GPT r19 reply-1 §6 / §10 Gate 4: the standard pp arity-collapse over ℤ. The pp-quadratic fragment is closed under
  image and preimage along the explicit injection intTupleCode : ℤⁿ → ℤ, hence every pp-quadratic relation on ℤⁿ is
  the preimage of a unary pp-quadratic relation (internal tuple coding at degree 2). Degree kept general d ≥ 2.
  Witness overhead is stated, not optimized. Statements frozen in frozen_statements/OneSortedPPFolding_STATEMENTS.lean (md5 bb021f39).
-/
import DiophCompression.OneSortedFragments

namespace DiophCompression

open MvPolynomial MPUP

/-- `e⁻¹(B) ⊆ ℤⁿ` for unary `B ⊆ ℤ¹`. -/
def preimageRelZZ {n : ℕ} (e : (Fin n → ℤ) → ℤ) (B : Set (Fin 1 → ℤ)) : Set (Fin n → ℤ) :=
  {a | (fun _ : Fin 1 => e a) ∈ B}

/-- `e(A) ⊆ ℤ¹` for `A ⊆ ℤⁿ`. -/
def imageRelZZ {n : ℕ} (e : (Fin n → ℤ) → ℤ) (A : Set (Fin n → ℤ)) : Set (Fin 1 → ℤ) :=
  {c | ∃ a ∈ A, c 0 = e a}

theorem mem_preimageRelZZ {n : ℕ} (e : (Fin n → ℤ) → ℤ) (B : Set (Fin 1 → ℤ)) (a : Fin n → ℤ) :
    a ∈ preimageRelZZ e B ↔ (fun _ : Fin 1 => e a) ∈ B := Iff.rfl

theorem mem_imageRelZZ {n : ℕ} (e : (Fin n → ℤ) → ℤ) (A : Set (Fin n → ℤ)) (c : Fin 1 → ℤ) :
    c ∈ imageRelZZ e A ↔ ∃ a ∈ A, c 0 = e a := Iff.rfl

theorem preimageRelZZ_imageRelZZ {n : ℕ} {e : (Fin n → ℤ) → ℤ} (he : Function.Injective e)
    (A : Set (Fin n → ℤ)) : preimageRelZZ e (imageRelZZ e A) = A := by
  ext a
  rw [mem_preimageRelZZ, mem_imageRelZZ]
  constructor
  · rintro ⟨a', ha', heq⟩
    have : a = a' := he heq
    rw [this]; exact ha'
  · intro ha
    exact ⟨a, ha, rfl⟩

/-! ### Evaluation under renaming (one-sorted) -/

theorem evalAtZZ_rename_eq {n r n' r' : ℕ} (φ : Fin n ⊕ Fin r → Fin n' ⊕ Fin r') (P : Poly n r)
    (a : Fin n' → ℤ) (y : Fin r' → ℤ) (a₀ : Fin n → ℤ) (y₀ : Fin r → ℤ)
    (h : ∀ v, Sum.elim a y (φ v) = Sum.elim a₀ y₀ v) :
    evalAtZZ (rename φ P) a y = evalAtZZ P a₀ y₀ := by
  simp only [evalAtZZ, eval_rename]
  have hf : (Sum.elim a y ∘ φ) = Sum.elim a₀ y₀ := funext h
  rw [hf]

/-! ### Preimage: variables `Fin n ⊕ Fin (1 + rG + q)` — witnesses (c, yG, yT) -/

section Preimage

variable (n rG q : ℕ)

def pcIdx : Fin (1 + rG + q) := Fin.castAdd q (Fin.castAdd rG 0)
def pgIdx (t : Fin rG) : Fin (1 + rG + q) := Fin.castAdd q (Fin.natAdd 1 t)
def ptIdx (s : Fin q) : Fin (1 + rG + q) := Fin.natAdd (1 + rG) s

def pφG : Fin (n + 1) ⊕ Fin rG → Fin n ⊕ Fin (1 + rG + q)
  | Sum.inl i => Fin.lastCases (Sum.inr (pcIdx rG q)) (fun j => Sum.inl j) i
  | Sum.inr t => Sum.inr (pgIdx rG q t)

def pφT : Fin 1 ⊕ Fin q → Fin n ⊕ Fin (1 + rG + q)
  | Sum.inl _ => Sum.inr (pcIdx rG q)
  | Sum.inr s => Sum.inr (ptIdx rG q s)

noncomputable def preimageSystemZZ {mG k : ℕ} (G : PolySystem (n + 1) rG mG) (T : PolySystem 1 q k) :
    PolySystem n (1 + rG + q) (mG + k) :=
  Fin.append (fun i => rename (pφG n rG q) (G i)) (fun j => rename (pφT n rG q) (T j))

def passemble (c : ℤ) (yG : Fin rG → ℤ) (yT : Fin q → ℤ) : Fin (1 + rG + q) → ℤ :=
  Fin.append (Fin.append ![c] yG) yT

theorem passemble_c (c : ℤ) (yG : Fin rG → ℤ) (yT : Fin q → ℤ) : passemble rG q c yG yT (pcIdx rG q) = c := by
  simp [passemble, pcIdx, Fin.append_left]
theorem passemble_g (c : ℤ) (yG : Fin rG → ℤ) (yT : Fin q → ℤ) (t : Fin rG) :
    passemble rG q c yG yT (pgIdx rG q t) = yG t := by
  simp [passemble, pgIdx, Fin.append_left, Fin.append_right]
theorem passemble_t (c : ℤ) (yG : Fin rG → ℤ) (yT : Fin q → ℤ) (s : Fin q) :
    passemble rG q c yG yT (ptIdx rG q s) = yT s := by
  simp [passemble, ptIdx, Fin.append_right]

theorem pφG_elim (a : Fin n → ℤ) (y : Fin (1 + rG + q) → ℤ) (v : Fin (n + 1) ⊕ Fin rG) :
    Sum.elim a y (pφG n rG q v)
      = Sum.elim (Fin.snoc a (y (pcIdx rG q))) (fun t => y (pgIdx rG q t)) v := by
  rcases v with i | t
  · induction i using Fin.lastCases with
    | last => simp [pφG, Fin.snoc_last]
    | cast j => simp [pφG, Fin.snoc_castSucc]
  · rfl

theorem pφT_elim (a : Fin n → ℤ) (y : Fin (1 + rG + q) → ℤ) (v : Fin 1 ⊕ Fin q) :
    Sum.elim a y (pφT n rG q v)
      = Sum.elim (fun _ : Fin 1 => y (pcIdx rG q)) (fun s => y (ptIdx rG q s)) v := by
  rcases v with i | s <;> rfl

theorem preimageSystemZZ_totalDegree {mG k d : ℕ} (G : PolySystem (n + 1) rG mG)
    (hGd : ∀ i, (G i).totalDegree ≤ d) (T : PolySystem 1 q k) (hTd : ∀ j, (T j).totalDegree ≤ d) :
    ∀ i, (preimageSystemZZ n rG q G T i).totalDegree ≤ d := by
  intro i
  induction i using Fin.addCases with
  | left i =>
    simp only [preimageSystemZZ, Fin.append_left]
    exact (totalDegree_rename_le _ _).trans (hGd i)
  | right j =>
    simp only [preimageSystemZZ, Fin.append_right]
    exact (totalDegree_rename_le _ _).trans (hTd j)

theorem preimageSystemZZ_representsZZ {mG k : ℕ} (e : (Fin n → ℤ) → ℤ) (G : PolySystem (n + 1) rG mG)
    (hG : SystemRepresentsZZ G (graphZZ e)) (T : PolySystem 1 q k) (B : Set (Fin 1 → ℤ))
    (hT : SystemRepresentsZZ T B) :
    SystemRepresentsZZ (preimageSystemZZ n rG q G T) (preimageRelZZ e B) := by
  intro a
  rw [mem_preimageRelZZ, hT]
  constructor
  · rintro ⟨yT, hyT⟩
    obtain ⟨yG, hyG⟩ := (hG (Fin.snoc a (e a))).1 ((snoc_mem_graphZZ e a (e a)).2 rfl)
    refine ⟨passemble rG q (e a) yG yT, ?_⟩
    intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [preimageSystemZZ, Fin.append_left]
      rw [evalAtZZ_rename_eq _ _ _ _ _ _ (pφG_elim n rG q a _)]
      simp only [passemble_c, passemble_g]
      exact hyG i
    | right j =>
      simp only [preimageSystemZZ, Fin.append_right]
      rw [evalAtZZ_rename_eq _ _ _ _ _ _ (pφT_elim n rG q a _)]
      simp only [passemble_c, passemble_t]
      exact hyT j
  · rintro ⟨y, hy⟩
    have hG' : ∀ i, evalAtZZ (G i) (Fin.snoc a (y (pcIdx rG q))) (fun t => y (pgIdx rG q t)) = 0 := by
      intro i
      have := hy (Fin.castAdd k i)
      simp only [preimageSystemZZ, Fin.append_left] at this
      rwa [evalAtZZ_rename_eq _ _ _ _ _ _ (pφG_elim n rG q a _)] at this
    have hmem := (hG _).2 ⟨_, hG'⟩
    rw [snoc_mem_graphZZ] at hmem
    refine ⟨fun s => y (ptIdx rG q s), fun j => ?_⟩
    have := hy (Fin.natAdd mG j)
    simp only [preimageSystemZZ, Fin.append_right] at this
    rw [evalAtZZ_rename_eq _ _ _ _ _ _ (pφT_elim n rG q a _)] at this
    rw [← hmem]
    exact this

end Preimage

/-! ### Image: variables `Fin 1 ⊕ Fin (n + rG + q)` — witnesses (a, yG, yT) -/

section Image

variable (n rG q : ℕ)

def iaIdx (j : Fin n) : Fin (n + rG + q) := Fin.castAdd q (Fin.castAdd rG j)
def igIdx (t : Fin rG) : Fin (n + rG + q) := Fin.castAdd q (Fin.natAdd n t)
def itIdx (s : Fin q) : Fin (n + rG + q) := Fin.natAdd (n + rG) s

def iφG : Fin (n + 1) ⊕ Fin rG → Fin 1 ⊕ Fin (n + rG + q)
  | Sum.inl i => Fin.lastCases (Sum.inl 0) (fun j => Sum.inr (iaIdx n rG q j)) i
  | Sum.inr t => Sum.inr (igIdx n rG q t)

def iφT : Fin n ⊕ Fin q → Fin 1 ⊕ Fin (n + rG + q)
  | Sum.inl j => Sum.inr (iaIdx n rG q j)
  | Sum.inr s => Sum.inr (itIdx n rG q s)

noncomputable def imageSystemZZ {mG k : ℕ} (G : PolySystem (n + 1) rG mG) (T : PolySystem n q k) :
    PolySystem 1 (n + rG + q) (mG + k) :=
  Fin.append (fun i => rename (iφG n rG q) (G i)) (fun j => rename (iφT n rG q) (T j))

def iassemble (a : Fin n → ℤ) (yG : Fin rG → ℤ) (yT : Fin q → ℤ) : Fin (n + rG + q) → ℤ :=
  Fin.append (Fin.append a yG) yT

theorem iassemble_a (a : Fin n → ℤ) (yG : Fin rG → ℤ) (yT : Fin q → ℤ) (j : Fin n) :
    iassemble n rG q a yG yT (iaIdx n rG q j) = a j := by
  simp [iassemble, iaIdx, Fin.append_left]
theorem iassemble_g (a : Fin n → ℤ) (yG : Fin rG → ℤ) (yT : Fin q → ℤ) (t : Fin rG) :
    iassemble n rG q a yG yT (igIdx n rG q t) = yG t := by
  simp [iassemble, igIdx, Fin.append_left, Fin.append_right]
theorem iassemble_t (a : Fin n → ℤ) (yG : Fin rG → ℤ) (yT : Fin q → ℤ) (s : Fin q) :
    iassemble n rG q a yG yT (itIdx n rG q s) = yT s := by
  simp [iassemble, itIdx, Fin.append_right]

theorem iφG_elim (c : Fin 1 → ℤ) (y : Fin (n + rG + q) → ℤ) (v : Fin (n + 1) ⊕ Fin rG) :
    Sum.elim c y (iφG n rG q v)
      = Sum.elim (Fin.snoc (fun j => y (iaIdx n rG q j)) (c 0)) (fun t => y (igIdx n rG q t)) v := by
  rcases v with i | t
  · induction i using Fin.lastCases with
    | last => simp [iφG, Fin.snoc_last]
    | cast j => simp [iφG, Fin.snoc_castSucc]
  · rfl

theorem iφT_elim (c : Fin 1 → ℤ) (y : Fin (n + rG + q) → ℤ) (v : Fin n ⊕ Fin q) :
    Sum.elim c y (iφT n rG q v)
      = Sum.elim (fun j => y (iaIdx n rG q j)) (fun s => y (itIdx n rG q s)) v := by
  rcases v with j | s <;> rfl

theorem imageSystemZZ_totalDegree {mG k d : ℕ} (G : PolySystem (n + 1) rG mG)
    (hGd : ∀ i, (G i).totalDegree ≤ d) (T : PolySystem n q k) (hTd : ∀ j, (T j).totalDegree ≤ d) :
    ∀ i, (imageSystemZZ n rG q G T i).totalDegree ≤ d := by
  intro i
  induction i using Fin.addCases with
  | left i =>
    simp only [imageSystemZZ, Fin.append_left]
    exact (totalDegree_rename_le _ _).trans (hGd i)
  | right j =>
    simp only [imageSystemZZ, Fin.append_right]
    exact (totalDegree_rename_le _ _).trans (hTd j)

theorem imageSystemZZ_representsZZ {mG k : ℕ} (e : (Fin n → ℤ) → ℤ) (G : PolySystem (n + 1) rG mG)
    (hG : SystemRepresentsZZ G (graphZZ e)) (T : PolySystem n q k) (A : Set (Fin n → ℤ))
    (hT : SystemRepresentsZZ T A) :
    SystemRepresentsZZ (imageSystemZZ n rG q G T) (imageRelZZ e A) := by
  intro c
  rw [mem_imageRelZZ]
  constructor
  · rintro ⟨a, haA, hc⟩
    obtain ⟨yT, hyT⟩ := (hT a).1 haA
    obtain ⟨yG, hyG⟩ := (hG (Fin.snoc a (c 0))).1 ((snoc_mem_graphZZ e a (c 0)).2 hc)
    refine ⟨iassemble n rG q a yG yT, ?_⟩
    intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [imageSystemZZ, Fin.append_left]
      rw [evalAtZZ_rename_eq _ _ _ _ _ _ (iφG_elim n rG q c _)]
      simp only [iassemble_a, iassemble_g]
      exact hyG i
    | right j =>
      simp only [imageSystemZZ, Fin.append_right]
      rw [evalAtZZ_rename_eq _ _ _ _ _ _ (iφT_elim n rG q c _)]
      simp only [iassemble_a, iassemble_t]
      exact hyT j
  · rintro ⟨y, hy⟩
    have hG' : ∀ i, evalAtZZ (G i) (Fin.snoc (fun j => y (iaIdx n rG q j)) (c 0))
        (fun t => y (igIdx n rG q t)) = 0 := by
      intro i
      have := hy (Fin.castAdd k i)
      simp only [imageSystemZZ, Fin.append_left] at this
      rwa [evalAtZZ_rename_eq _ _ _ _ _ _ (iφG_elim n rG q c _)] at this
    have hmem := (hG _).2 ⟨_, hG'⟩
    rw [snoc_mem_graphZZ] at hmem
    have hT' : ∀ j, evalAtZZ (T j) (fun j => y (iaIdx n rG q j)) (fun s => y (itIdx n rG q s)) = 0 := by
      intro j
      have := hy (Fin.natAdd mG j)
      simp only [imageSystemZZ, Fin.append_right] at this
      rwa [evalAtZZ_rename_eq _ _ _ _ _ _ (iφT_elim n rG q c _)] at this
    exact ⟨_, (hT _).2 ⟨_, hT'⟩, hmem⟩

end Image

/-- Preimage preservation with explicit overhead: if `graphZZ e` has an (rG, mG) system and `B` a (q, k) system,
    all of degree ≤ d, then `e⁻¹(B)` has a (1 + rG + q, mG + k) system of degree ≤ d. -/
theorem withinPPZZ_preimage_of_systems {n rG mG q k d : ℕ} (e : (Fin n → ℤ) → ℤ)
    (G : PolySystem (n + 1) rG mG) (hGd : ∀ i, (G i).totalDegree ≤ d) (hG : SystemRepresentsZZ G (graphZZ e))
    (T : PolySystem 1 q k) (hTd : ∀ j, (T j).totalDegree ≤ d) (B : Set (Fin 1 → ℤ))
    (hT : SystemRepresentsZZ T B) :
    ∃ S : PolySystem n (1 + rG + q) (mG + k), (∀ i, (S i).totalDegree ≤ d) ∧
      SystemRepresentsZZ S (preimageRelZZ e B) := ⟨preimageSystemZZ n rG q G T, preimageSystemZZ_totalDegree n rG q G hGd T hTd,
    preimageSystemZZ_representsZZ n rG q e G hG T B hT⟩

/-- Image preservation with explicit overhead: `e(A)` has an (n + rG + q, mG + k) system. -/
theorem withinPPZZ_image_of_systems {n rG mG q k d : ℕ} (e : (Fin n → ℤ) → ℤ)
    (G : PolySystem (n + 1) rG mG) (hGd : ∀ i, (G i).totalDegree ≤ d) (hG : SystemRepresentsZZ G (graphZZ e))
    (T : PolySystem n q k) (hTd : ∀ j, (T j).totalDegree ≤ d) (A : Set (Fin n → ℤ))
    (hT : SystemRepresentsZZ T A) :
    ∃ S : PolySystem 1 (n + rG + q) (mG + k), (∀ i, (S i).totalDegree ≤ d) ∧
      SystemRepresentsZZ S (imageRelZZ e A) := ⟨imageSystemZZ n rG q G T, imageSystemZZ_totalDegree n rG q G hGd T hTd,
    imageSystemZZ_representsZZ n rG q e G hG T A hT⟩

theorem withinPPZZ_preimage_intTupleCode {n d : ℕ} (hd : 2 ≤ d) {B : Set (Fin 1 → ℤ)}
    (hB : WithinPPZZ d B) : WithinPPZZ d (preimageRelZZ (@intTupleCode n) B) := by
  obtain ⟨rG, mG, G, hGd, hG⟩ := graphZZ_intTupleCode_withinPPZZ n
  obtain ⟨q, k, T, hTd, hT⟩ := hB
  obtain ⟨S, hSd, hS⟩ := withinPPZZ_preimage_of_systems intTupleCode G (fun i => (hGd i).trans hd) hG T hTd B hT
  exact ⟨_, _, S, hSd, hS⟩

theorem withinPPZZ_image_intTupleCode {n d : ℕ} (hd : 2 ≤ d) {A : Set (Fin n → ℤ)}
    (hA : WithinPPZZ d A) : WithinPPZZ d (imageRelZZ (@intTupleCode n) A) := by
  obtain ⟨rG, mG, G, hGd, hG⟩ := graphZZ_intTupleCode_withinPPZZ n
  obtain ⟨q, k, T, hTd, hT⟩ := hA
  obtain ⟨S, hSd, hS⟩ := withinPPZZ_image_of_systems intTupleCode G (fun i => (hGd i).trans hd) hG T hTd A hT
  exact ⟨_, _, S, hSd, hS⟩

/-- Internal arity collapse at degree 2: every pp-quadratic relation on ℤⁿ is the preimage under the explicit
    pp-quadratic injection `intTupleCode` of a pp-quadratic relation on ℤ. -/
theorem pp_quadratic_internal_arity_collapse {n : ℕ} {A : Set (Fin n → ℤ)} (hA : WithinPPZZ 2 A) :
    ∃ B : Set (Fin 1 → ℤ), WithinPPZZ 2 B ∧ A = preimageRelZZ (@intTupleCode n) B := ⟨imageRelZZ intTupleCode A, withinPPZZ_image_intTupleCode le_rfl hA,
    (preimageRelZZ_imageRelZZ (intTupleCode_injective n) A).symm⟩

theorem ppFragmentZZ_two_arity_collapse (n : ℕ) :
    ∀ A ∈ PPFragmentZZ 2 n, ∃ B ∈ PPFragmentZZ 2 1, A = preimageRelZZ (@intTupleCode n) B := by
  intro A hA
  obtain ⟨B, hB, hAB⟩ := pp_quadratic_internal_arity_collapse hA
  exact ⟨B, hB, hAB⟩

end DiophCompression

#print axioms DiophCompression.preimageRelZZ_imageRelZZ
#print axioms DiophCompression.withinPPZZ_preimage_of_systems
#print axioms DiophCompression.withinPPZZ_image_of_systems
#print axioms DiophCompression.withinPPZZ_preimage_intTupleCode
#print axioms DiophCompression.withinPPZZ_image_intTupleCode
#print axioms DiophCompression.pp_quadratic_internal_arity_collapse
#print axioms DiophCompression.ppFragmentZZ_two_arity_collapse
