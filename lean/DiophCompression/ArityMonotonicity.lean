/-
  DiophCompression/ArityMonotonicity.lean — r05 必須B (session 5, 2026-08-26, claude.ai direct, no CC).
  Downward closure in the arity: Achievable(n, r, d) → Achievable(m, r, d) for m ≤ n, for the
  specialization (S), graph (G) and universality (U) predicates, ℕ- and ℤ-unknowns.
  Mechanism: parameter padding. The extra parameters i ≥ m are substituted by the constant 0 in the
  polynomial (`padSub`), never folded into coefficients; the coding map is e ∘ pad with pad injective;
  total degree does not increase (substituting variables by variables or by 0). m = 0 and n = 0 are
  instances of the general statement (Fin 0 → ℕ is a singleton; pad is then the constant map).
  Names as prescribed in GPT r04 §6 必須B. Statements frozen 2026-08-26 (draft md5 b99eddc0,
  `frozen statement file `ArityMonotonicity_STATEMENTS.lean``); proofs filled after.
-/
import DiophCompression.Definitions

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Padding of parameter vectors -/

/-- Partial relabelling of parameters: `f i = some j` keeps parameter `i` as parameter `j`,
    `f i = none` fixes parameter `i` to 0. -/
def optPad {m n : ℕ} (f : Fin n → Option (Fin m)) (a : Fin m → ℕ) : Fin n → ℕ :=
  fun i => match f i with
    | some j => a j
    | none => 0

/-- Zero padding `ℕ^m → ℕ^n` (m ≤ n): the first `m` coordinates are kept, the rest are 0. -/
def padMap {m n : ℕ} (h : m ≤ n) : Fin n → Option (Fin m) :=
  fun i => if hi : (i : ℕ) < m then some ⟨i, hi⟩ else none

def pad {m n : ℕ} (h : m ≤ n) : (Fin m → ℕ) → Fin n → ℕ := optPad (padMap h)

theorem pad_apply_lt {m n : ℕ} (h : m ≤ n) (a : Fin m → ℕ) (i : Fin n) (hi : (i : ℕ) < m) :
    pad h a i = a ⟨i, hi⟩ := by
  simp [pad, optPad, padMap, hi]

theorem pad_apply_ge {m n : ℕ} (h : m ≤ n) (a : Fin m → ℕ) (i : Fin n) (hi : ¬ (i : ℕ) < m) :
    pad h a i = 0 := by
  simp [pad, optPad, padMap, hi]

theorem pad_injective {m n : ℕ} (h : m ≤ n) : Function.Injective (pad h) := by
  intro a b hab
  funext i
  have hi : ((Fin.castLE h i : Fin n) : ℕ) < m := by simp
  have := congrFun hab (Fin.castLE h i)
  rw [pad_apply_lt h a _ hi, pad_apply_lt h b _ hi] at this
  simpa using this

/-- Restriction `ℕ^n → ℕ^m` to the first `m` coordinates; left inverse of `pad`. -/
def restrict {m n : ℕ} (h : m ≤ n) (b : Fin n → ℕ) : Fin m → ℕ := fun i => b (Fin.castLE h i)

theorem restrict_pad {m n : ℕ} (h : m ≤ n) (a : Fin m → ℕ) : restrict h (pad h a) = a := by
  funext i
  have hi : ((Fin.castLE h i : Fin n) : ℕ) < m := by simp
  unfold restrict
  rw [pad_apply_lt h a _ hi]
  simp

/-- Padding for the graph layout `Fin (n+1)` (parameters, then the output variable): the output
    variable is kept as the output variable. -/
def padMapLast {m n : ℕ} (h : m ≤ n) : Fin (n + 1) → Option (Fin (m + 1)) :=
  fun i => if hi : (i : ℕ) < m then some ⟨i, by omega⟩
           else if (i : ℕ) = n then some (Fin.last m) else none

theorem optPad_padMapLast_last {m n : ℕ} (h : m ≤ n) (v : Fin (m + 1) → ℕ) :
    optPad (padMapLast h) v (Fin.last n) = v (Fin.last m) := by
  have h1 : ¬ n < m := by omega
  simp [optPad, padMapLast, h1]

theorem init_optPad_padMapLast {m n : ℕ} (h : m ≤ n) (v : Fin (m + 1) → ℕ) :
    Fin.init (optPad (padMapLast h) v) = pad h (Fin.init v) := by
  funext i
  simp only [Fin.init]
  by_cases hi : (i : ℕ) < m
  · rw [pad_apply_lt h _ i hi]
    have hc : ((Fin.castSucc i : Fin (n + 1)) : ℕ) < m := by simpa using hi
    simp only [optPad, padMapLast, hc, dite_true]
    simp [Fin.init]
  · rw [pad_apply_ge h _ i hi]
    have hn : ¬ ((i : ℕ) = n) := Nat.ne_of_lt i.2
    simp [optPad, padMapLast, hi, hn]

/-! ### Substitution of parameters in the polynomial -/

/-- Variable substitution: parameter `i` ↦ `X (inl j)` if `f i = some j`, ↦ `0` if `f i = none`;
    unknowns are kept. -/
noncomputable def optSub {m n : ℕ} (f : Fin n → Option (Fin m)) (σ : Type) :
    (Fin n ⊕ σ) → MvPolynomial (Fin m ⊕ σ) ℤ
  | Sum.inl i => match f i with
      | some j => X (Sum.inl j)
      | none => 0
  | Sum.inr j => X (Sum.inr j)

/-- Substitution never raises the total degree when every variable goes to a variable or to 0. -/
theorem totalDegree_aeval_le_of_le_one {σ τ : Type} (g : σ → MvPolynomial τ ℤ)
    (p : MvPolynomial σ ℤ) (hg : ∀ v, (g v).totalDegree ≤ 1) :
    (aeval g p).totalDegree ≤ p.totalDegree := by
  rw [aeval_def, eval₂_eq]
  apply totalDegree_finsetSum_le
  intro β hβ
  rw [algebraMap_eq]
  calc (C (coeff β p) * ∏ v ∈ β.support, (g v) ^ (β v)).totalDegree
      ≤ (C (coeff β p)).totalDegree + (∏ v ∈ β.support, (g v) ^ (β v)).totalDegree :=
        totalDegree_mul _ _
    _ = (∏ v ∈ β.support, (g v) ^ (β v)).totalDegree := by rw [totalDegree_C]; ring
    _ ≤ ∑ v ∈ β.support, ((g v) ^ (β v)).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ v ∈ β.support, (β v) * 1 := by
        apply Finset.sum_le_sum
        intro v _
        calc ((g v) ^ (β v)).totalDegree ≤ (β v) * (g v).totalDegree := totalDegree_pow _ _
          _ ≤ (β v) * 1 := by apply Nat.mul_le_mul_left; exact hg v
    _ = ∑ v ∈ β.support, β v := by simp
    _ ≤ p.totalDegree := le_totalDegree hβ

theorem optSub_totalDegree_le_one {m n : ℕ} (f : Fin n → Option (Fin m)) (σ : Type) (v : Fin n ⊕ σ) :
    (optSub f σ v).totalDegree ≤ 1 := by
  cases v with
  | inl i =>
    cases hf : f i with
    | some j => simp [optSub, hf, totalDegree_X]
    | none => simp [optSub, hf]
  | inr j => simp [optSub, totalDegree_X]

theorem totalDegree_aeval_optSub_le {m n : ℕ} (f : Fin n → Option (Fin m)) {σ : Type}
    (P : MvPolynomial (Fin n ⊕ σ) ℤ) : (aeval (optSub f σ) P).totalDegree ≤ P.totalDegree :=
  totalDegree_aeval_le_of_le_one _ _ (optSub_totalDegree_le_one f σ)

/-- Evaluation of the substituted polynomial at `a` is evaluation of the original at `optPad f a`. -/
theorem eval_aeval_optSub {m n : ℕ} (f : Fin n → Option (Fin m)) {σ : Type}
    (P : MvPolynomial (Fin n ⊕ σ) ℤ) (a : Fin m → ℕ) (y : σ → ℤ) :
    eval (Sum.elim (fun i => (a i : ℤ)) y) (aeval (optSub f σ) P)
      = eval (Sum.elim (fun i => (optPad f a i : ℤ)) y) P := by
  rw [map_aeval]
  have hcomp : (eval (Sum.elim (fun i => (a i : ℤ)) y)).comp
      (algebraMap ℤ (MvPolynomial (Fin m ⊕ σ) ℤ)) = RingHom.id ℤ := by
    rw [algebraMap_eq]
    ext z
    simp
  rw [hcomp]
  have : (eval₂Hom (RingHom.id ℤ) (fun v => (eval (Sum.elim (fun i => (a i : ℤ)) y)) (optSub f σ v))) P
      = eval (fun v => (eval (Sum.elim (fun i => (a i : ℤ)) y)) (optSub f σ v)) P := rfl
  rw [this]
  apply congrArg (fun ρ => eval ρ P)
  funext v
  cases v with
  | inl i =>
    simp only [Sum.elim_inl, optPad]
    cases hf : f i with
    | some j => simp [optSub, hf]
    | none => simp [optSub, hf]
  | inr j => simp [optSub]

theorem evalAt_aeval_optSub {m n r : ℕ} (f : Fin n → Option (Fin m)) (P : Poly n r)
    (a : Fin m → ℕ) (y : Fin r → ℤ) :
    evalAt (aeval (optSub f (Fin r)) P) a y = evalAt P (optPad f a) y := by
  unfold evalAt
  exact eval_aeval_optSub f P a y

theorem specialize_aeval_optSub {m n : ℕ} (f : Fin n → Option (Fin m)) {σ : Type}
    (P : MvPolynomial (Fin n ⊕ σ) ℤ) (a : Fin m → ℕ) :
    specialize (aeval (optSub f σ) P) a = specialize P (optPad f a) := by
  unfold specialize
  have hcomp : aeval (Sum.elim (fun i => C ((a i : ℕ) : ℤ)) X) (aeval (optSub f σ) P)
      = aeval (fun v => aeval (Sum.elim (fun i => C ((a i : ℕ) : ℤ)) X) (optSub f σ v)) P := by
    have := congrArg (fun φ => φ P)
      (comp_aeval (optSub f σ) (aeval (Sum.elim (fun i => C ((a i : ℕ) : ℤ)) X)))
    simpa using this
  rw [hcomp]
  apply congrArg (fun ρ => aeval ρ P)
  funext v
  cases v with
  | inl i =>
    simp only [Sum.elim_inl, optPad]
    cases hf : f i with
    | some j => simp [optSub, hf]
    | none => simp [optSub, hf]
  | inr j => simp [optSub]

/-! ### Downward closure in the arity (m ≤ n) -/

theorem specialization_arity_downward {m n q d : ℕ} (h : m ≤ n)
    (hS : SpecializationAchievable n q d) : SpecializationAchievable m q d := by
  obtain ⟨P, hP, hinj⟩ := hS
  refine ⟨aeval (optSub (padMap h) (Fin q)) P, le_trans (totalDegree_aeval_optSub_le _ _) hP, ?_⟩
  intro a b hab
  rw [specialize_aeval_optSub, specialize_aeval_optSub] at hab
  exact pad_injective h (hinj hab)

theorem graph_arity_downward_N {m n r d : ℕ} (h : m ≤ n)
    (hG : GraphAchievableN n r d) : GraphAchievableN m r d := by
  obtain ⟨e, he, r', hr', P, hP, hrep⟩ := hG
  refine ⟨fun a => e (pad h a), fun a b hab => pad_injective h (he hab), r', hr',
    aeval (optSub (padMapLast h) (Fin r')) P, le_trans (totalDegree_aeval_optSub_le _ _) hP, ?_⟩
  intro v
  have hg : v ∈ graph (fun a => e (pad h a)) ↔ optPad (padMapLast h) v ∈ graph e := by
    simp only [graph, Set.mem_setOf_eq, optPad_padMapLast_last, init_optPad_padMapLast]
  rw [hg, hrep (optPad (padMapLast h) v)]
  simp only [evalAt_aeval_optSub]

theorem graph_arity_downward_Z {m n r d : ℕ} (h : m ≤ n)
    (hG : GraphAchievableZ n r d) : GraphAchievableZ m r d := by
  obtain ⟨e, he, r', hr', P, hP, hrep⟩ := hG
  refine ⟨fun a => e (pad h a), fun a b hab => pad_injective h (he hab), r', hr',
    aeval (optSub (padMapLast h) (Fin r')) P, le_trans (totalDegree_aeval_optSub_le _ _) hP, ?_⟩
  intro v
  have hg : v ∈ graph (fun a => e (pad h a)) ↔ optPad (padMapLast h) v ∈ graph e := by
    simp only [graph, Set.mem_setOf_eq, optPad_padMapLast_last, init_optPad_padMapLast]
  rw [hg, hrep (optPad (padMapLast h) v)]
  simp only [evalAt_aeval_optSub]

theorem universal_arity_downward_N {m n r d : ℕ} (h : m ≤ n)
    (hU : UniversalAchievableN n r d) : UniversalAchievableN m r d := by
  intro A hA
  -- cylinder A' = {b : ℕ^n | restrict b ∈ A}, Diophantine by renaming
  obtain ⟨t, Q, hQ⟩ := hA
  have hA' : DiophN {b : Fin n → ℕ | restrict h b ∈ A} := by
    refine ⟨t, rename (Sum.map (Fin.castLE h) id) Q, ?_⟩
    intro b
    rw [Set.mem_setOf_eq, hQ (restrict h b)]
    apply exists_congr
    intro y
    unfold evalAt
    rw [eval_rename]
    have hfun : ((Sum.elim (fun i => ((b i : ℕ) : ℤ)) (fun i => ((y i : ℕ) : ℤ)))
        ∘ Sum.map (Fin.castLE h) id)
        = Sum.elim (fun i => ((restrict h b i : ℕ) : ℤ)) (fun i => ((y i : ℕ) : ℤ)) := by
      funext v
      cases v <;> rfl
    rw [hfun]
  obtain ⟨r', hr', P, hP, hrep⟩ := hU _ hA'
  refine ⟨r', hr', aeval (optSub (padMap h) (Fin r')) P,
    le_trans (totalDegree_aeval_optSub_le _ _) hP, ?_⟩
  intro a
  have ha : a ∈ A ↔ pad h a ∈ {b : Fin n → ℕ | restrict h b ∈ A} := by
    simp [restrict_pad]
  rw [ha, hrep (pad h a)]
  simp only [evalAt_aeval_optSub]
  rfl

theorem universal_arity_downward_Z {m n r d : ℕ} (h : m ≤ n)
    (hU : UniversalAchievableZ n r d) : UniversalAchievableZ m r d := by
  intro A hA
  obtain ⟨t, Q, hQ⟩ := hA
  have hA' : DiophN {b : Fin n → ℕ | restrict h b ∈ A} := by
    refine ⟨t, rename (Sum.map (Fin.castLE h) id) Q, ?_⟩
    intro b
    rw [Set.mem_setOf_eq, hQ (restrict h b)]
    apply exists_congr
    intro y
    unfold evalAt
    rw [eval_rename]
    have hfun : ((Sum.elim (fun i => ((b i : ℕ) : ℤ)) (fun i => ((y i : ℕ) : ℤ)))
        ∘ Sum.map (Fin.castLE h) id)
        = Sum.elim (fun i => ((restrict h b i : ℕ) : ℤ)) (fun i => ((y i : ℕ) : ℤ)) := by
      funext v
      cases v <;> rfl
    rw [hfun]
  obtain ⟨r', hr', P, hP, hrep⟩ := hU _ hA'
  refine ⟨r', hr', aeval (optSub (padMap h) (Fin r')) P,
    le_trans (totalDegree_aeval_optSub_le _ _) hP, ?_⟩
  intro a
  have ha : a ∈ A ↔ pad h a ∈ {b : Fin n → ℕ | restrict h b ∈ A} := by
    simp [restrict_pad]
  rw [ha, hrep (pad h a)]
  simp only [evalAt_aeval_optSub]
  rfl

/-- Combined monotonicity: down in arity, up in witnesses and degree. -/
theorem graphAchievableN_mono_all {m n r r' d d' : ℕ} (h : m ≤ n) (hr : r ≤ r') (hd : d ≤ d')
    (hG : GraphAchievableN n r d) : GraphAchievableN m r' d' :=
  graph_arity_downward_N h (graphAchievableN_mono hr hd hG)

theorem universalAchievableN_mono_all {m n r r' d d' : ℕ} (h : m ≤ n) (hr : r ≤ r') (hd : d ≤ d')
    (hU : UniversalAchievableN n r d) : UniversalAchievableN m r' d' :=
  universal_arity_downward_N h (universalAchievableN_mono hr hd hU)

end DiophCompression

#print axioms DiophCompression.pad_injective
#print axioms DiophCompression.totalDegree_aeval_le_of_le_one
#print axioms DiophCompression.eval_aeval_optSub
#print axioms DiophCompression.specialize_aeval_optSub
#print axioms DiophCompression.specialization_arity_downward
#print axioms DiophCompression.graph_arity_downward_N
#print axioms DiophCompression.graph_arity_downward_Z
#print axioms DiophCompression.universal_arity_downward_N
#print axioms DiophCompression.universal_arity_downward_Z
#print axioms DiophCompression.graphAchievableN_mono_all
#print axioms DiophCompression.universalAchievableN_mono_all
