/-
  DiophCompression/FiniteFiberGrowth.lean — APAL Functional-Definability Pivot, Gate 6
  (session 23, 2026-08-31, claude.ai direct, 0 CC).
  GPT r20 必須A: quadratic finite-fiber growth theorem (scalar and vector output); 必須B: quadratic growth of
  single-quadratic-definable total functions ℤⁿ → ℤᵐ and the injective dimension inequality n ≤ 2m.
  Engine: Theorem D (QuadraticProjectionDichotomyZ, all r) applied to the output coordinate and its sign flip —
  the proof of capacity_two_aux_ZZ (OneSorted.lean) with the singleton fiber replaced by a finite fiber; the
  dimension bound is box_counting_bound with output index type Fin m.
  Statements frozen in frozen_statements/FiniteFiberGrowth_STATEMENTS.lean (md5 b9c649ae).
-/
import DiophCompression.OneSorted
import DiophCompression.OneSortedPPFolding

namespace DiophCompression

open MvPolynomial MPUP SemanticQuadraticGeneral

/-! ### Definitions (verbatim from the freeze) -/

/-- The fiber of `P` over the input `a` (output = last coordinate): outputs `c` with an integer witness. -/
def fiberZZ {n r : ℕ} (P : Poly (n + 1) r) (a : Fin n → ℤ) : Set ℤ :=
  {c | ∃ u : Fin r → ℤ, evalAtZZ P (Fin.snoc a c) u = 0}

/-- The fiber of `P` over the first `n` coordinates: output vectors `b ∈ ℤᵐ` with an integer witness. -/
def fiberVecZZ {n m r : ℕ} (P : Poly (n + m) r) (a : Fin n → ℤ) : Set (Fin m → ℤ) :=
  {b | ∃ u : Fin r → ℤ, evalAtZZ P (Fin.append a b) u = 0}

/-- `P` has finite fibers over every input (GPT: FiniteFiberRelationZZ). -/
def FiniteFiberRelationZZ {n m r : ℕ} (P : Poly (n + m) r) : Prop :=
  ∀ a : Fin n → ℤ, (fiberVecZZ P a).Finite

/-- Scalar height bound: on every box `|a_i| ≤ N` (N ≥ 1), every element of a finite fiber has |c| ≤ C·N². -/
def FiberHeightBoundZZ {n r : ℕ} (P : Poly (n + 1) r) (C : ℕ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
    (fiberZZ P a).Finite → ∀ c ∈ fiberZZ P a, |c| ≤ (C : ℤ) * (N : ℤ) ^ 2

/-- Vector height bound: same, coordinatewise on `ℤᵐ`. -/
def FiberHeightBoundVecZZ {n m r : ℕ} (P : Poly (n + m) r) (C : ℕ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
    (fiberVecZZ P a).Finite → ∀ b ∈ fiberVecZZ P a, ∀ j, |b j| ≤ (C : ℤ) * (N : ℤ) ^ 2

/-- Graph of a total function `ℤⁿ → ℤᵐ` as a relation on `ℤⁿ⁺ᵐ` (inputs first). -/
def graphVecZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Set (Fin (n + m) → ℤ) :=
  {v | (fun j => v (Fin.natAdd n j)) = f (fun i => v (Fin.castAdd m i))}

/-- `f : ℤⁿ → ℤᵐ` is defined by a single equation of total degree ≤ 2 with integer witnesses. -/
def SingleQuadraticDefinableFunctionZZ {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop :=
  ∃ r, ∃ P : Poly (n + m) r, P.totalDegree ≤ 2 ∧ RepresentsZZ P (graphVecZZ f)

/-! ### Helpers -/

/-- Evaluation bound on the integer box: |p(a)| ≤ (Σ|coeff|) · N^{deg p} for |a_i| ≤ N, N ≥ 1
    (integer-input version of `eval_abs_le`). -/
theorem eval_abs_le_int {n : ℕ} (p : MvPolynomial (Fin n) ℤ) {N : ℕ} (h1 : 1 ≤ N)
    (a : Fin n → ℤ) (ha : ∀ i, |a i| ≤ N) :
    |eval a p| ≤ (∑ β ∈ p.support, |coeff β p|) * (N : ℤ) ^ p.totalDegree := by
  rw [eval_eq]
  calc |∑ β ∈ p.support, coeff β p * ∏ i ∈ β.support, (a i) ^ β i|
      ≤ ∑ β ∈ p.support, |coeff β p * ∏ i ∈ β.support, (a i) ^ β i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ β ∈ p.support, |coeff β p| * (N : ℤ) ^ p.totalDegree := by
        apply Finset.sum_le_sum
        intro β hβ
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [Finset.abs_prod]
        calc ∏ i ∈ β.support, |(a i) ^ β i| ≤ ∏ i ∈ β.support, (N : ℤ) ^ β i := by
              apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
              intro i _
              rw [abs_pow]
              exact pow_le_pow_left₀ (abs_nonneg _) (ha i) _
          _ = (N : ℤ) ^ (∑ i ∈ β.support, β i) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ (N : ℤ) ^ p.totalDegree :=
              pow_le_pow_right₀ (by exact_mod_cast h1) (le_totalDegree hβ)
    _ = _ := by rw [Finset.sum_mul]

/-- The bound shape `fboundG K (ℓ(a)) (q(a))` is at most `C·N²` on the integer box, with
    `C = K((1+SL)²+SQ)` built from the coefficient ℓ¹-norms of the linear and constant parts. -/
theorem fboundG_box_le {n k : ℕ} (K : ℕ) (ℓ : Fin k → MvPolynomial (Fin n) ℤ)
    (q : MvPolynomial (Fin n) ℤ) (hℓ : ∀ i, (ℓ i).totalDegree ≤ 1) (hq : q.totalDegree ≤ 2) :
    ∃ C : ℕ, ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
      (K : ℤ) * ((1 + ∑ i, |eval a (ℓ i)|) ^ 2 + |eval a q|) ≤ (C : ℤ) * (N : ℤ) ^ 2 := by
  classical
  set SL : ℕ := ∑ i, ∑ β ∈ (ℓ i).support, (coeff β (ℓ i)).natAbs with hSL
  set SQ : ℕ := ∑ β ∈ q.support, (coeff β q).natAbs with hSQ
  refine ⟨K * ((1 + SL) ^ 2 + SQ), ?_⟩
  intro N h1 a ha
  have hSLcast : (SL : ℤ) = ∑ i, ∑ β ∈ (ℓ i).support, |coeff β (ℓ i)| := by
    rw [hSL, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun β _ => Int.natCast_natAbs _
  have hSQcast : (SQ : ℤ) = ∑ β ∈ q.support, |coeff β q| := by
    rw [hSQ, Nat.cast_sum]; exact Finset.sum_congr rfl fun β _ => Int.natCast_natAbs _
  have hNz : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast h1
  have hℓb : ∀ i, |eval a (ℓ i)| ≤ (∑ β ∈ (ℓ i).support, |coeff β (ℓ i)|) * (N : ℤ) := by
    intro i
    have h := eval_abs_le_int (ℓ i) h1 a ha
    calc |eval a (ℓ i)|
        ≤ (∑ β ∈ (ℓ i).support, |coeff β (ℓ i)|) * (N : ℤ) ^ (ℓ i).totalDegree := h
      _ ≤ (∑ β ∈ (ℓ i).support, |coeff β (ℓ i)|) * (N : ℤ) ^ 1 := by
          apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hNz (hℓ i))
          positivity
      _ = (∑ β ∈ (ℓ i).support, |coeff β (ℓ i)|) * (N : ℤ) := by ring
  have hsum : ∑ i, |eval a (ℓ i)| ≤ (SL : ℤ) * (N : ℤ) := by
    rw [hSLcast, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hℓb i
  have hQb : |eval a q| ≤ (SQ : ℤ) * (N : ℤ) ^ 2 := by
    have h := eval_abs_le_int q h1 a ha
    rw [hSQcast]
    calc |eval a q|
        ≤ (∑ β ∈ q.support, |coeff β q|) * (N : ℤ) ^ q.totalDegree := h
      _ ≤ (∑ β ∈ q.support, |coeff β q|) * (N : ℤ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hNz hq)
          rw [← hSQcast]; positivity
  have hnn : (0 : ℤ) ≤ 1 + ∑ i, |eval a (ℓ i)| := by positivity
  have step1 : 1 + ∑ i, |eval a (ℓ i)| ≤ (1 + (SL : ℤ)) * N := by nlinarith [hsum, hNz]
  have step2 : (1 + ∑ i, |eval a (ℓ i)|) ^ 2 ≤ ((1 + (SL : ℤ)) * N) ^ 2 :=
    pow_le_pow_left₀ hnn step1 2
  have hexp : ((1 + (SL : ℤ)) * N) ^ 2 = (1 + (SL : ℤ)) ^ 2 * N ^ 2 := by ring
  rw [hexp] at step2
  have inner : (1 + ∑ i, |eval a (ℓ i)|) ^ 2 + |eval a q| ≤ ((1 + (SL : ℤ)) ^ 2 + SQ) * N ^ 2 := by
    nlinarith [step2, hQb]
  calc (K : ℤ) * ((1 + ∑ i, |eval a (ℓ i)|) ^ 2 + |eval a q|)
      ≤ (K : ℤ) * (((1 + (SL : ℤ)) ^ 2 + SQ) * N ^ 2) :=
        mul_le_mul_of_nonneg_left inner (by positivity)
    _ = ((K * ((1 + SL) ^ 2 + SQ) : ℕ) : ℤ) * (N : ℤ) ^ 2 := by push_cast; ring

/-! ### 必須A — finite-fiber growth (scalar) -/

/-- Scalar finite-fiber growth theorem (Theorem D applied to `c` and `−c`; finiteness only refutes the
    infinite branch of the dichotomy). -/
theorem singleQuadratic_finiteFiber_height_scalar {n r : ℕ} (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) : ∃ C : ℕ, FiberHeightBoundZZ P C := by
  classical
  have hD := SemanticQuadraticSingular.quadraticProjectionDichotomyZ_all r
  obtain ⟨H, ℓ, q, hH, _, hℓ, hq, heval⟩ :=
    normal_form_general_quadratic (r + 1) (rename (relabelG n r) P)
      ((totalDegree_rename_le _ _).trans hP)
  obtain ⟨K₁, hK₁⟩ := hD H hH
  obtain ⟨K₂, hK₂⟩ := hD (flipZero H) (flipZero_isHomogeneous H hH)
  obtain ⟨C, hC⟩ := fboundG_box_le (K₁ + K₂) ℓ q hℓ hq
  refine ⟨C, ?_⟩
  intro N h1 a ha hfin c hc
  let L : Fin (r + 1) → ℤ := fun i => eval a (ℓ i)
  let Q : ℤ := eval a q
  let L' : Fin (r + 1) → ℤ := fun i => if i = 0 then -L i else L i
  have hfib : ∀ (c : ℤ) (u : Fin r → ℤ),
      fiberVal H L Q (Fin.cons c u) = evalAtZZ P (Fin.snoc a c) u := by
    intro c u
    rw [← eval_relabelG_ZZ, heval]
    rfl
  have hsol : ∀ c : ℤ, (∃ u, fiberVal H L Q (Fin.cons c u) = 0) ↔ c ∈ fiberZZ P a := by
    intro c
    show (∃ u, fiberVal H L Q (Fin.cons c u) = 0) ↔ ∃ u, evalAtZZ P (Fin.snoc a c) u = 0
    exact exists_congr fun u => by rw [hfib]
  have hsol' : ∀ m : ℤ, (∃ u, fiberVal (flipZero H) L' Q (Fin.cons m u) = 0) ↔ (-m) ∈ fiberZZ P a := by
    intro m
    rw [← hsol (-m)]
    exact exists_congr fun u => by rw [fiberVal_flip]
  -- the two ℕ-fibers are finite because the ℤ-fiber is
  have hfinN : (fiberSetG H L Q).Finite := by
    have : fiberSetG H L Q = (fun m : ℕ => (m : ℤ)) ⁻¹' fiberZZ P a := by
      ext m
      simp only [fiberSetG, Set.mem_setOf_eq, Set.mem_preimage]
      exact hsol m
    rw [this]
    exact hfin.preimage Nat.cast_injective.injOn
  have hfinN' : (fiberSetG (flipZero H) L' Q).Finite := by
    have : fiberSetG (flipZero H) L' Q = (fun m : ℕ => -(m : ℤ)) ⁻¹' fiberZZ P a := by
      ext m
      simp only [fiberSetG, Set.mem_setOf_eq, Set.mem_preimage]
      exact hsol' m
    rw [this]
    exact hfin.preimage (fun x _ y _ h => by exact_mod_cast neg_inj.mp h)
  -- positive side
  have hpos : c ≤ fboundG K₁ L Q := by
    rcases hK₁ L Q with hinf | hb
    · exact (hinf hfinN).elim
    · rcases le_or_gt 0 c with h0 | h0
      · have hmem : c.toNat ∈ fiberSetG H L Q := by
          obtain ⟨u, hu⟩ := (hsol c).mpr hc
          exact ⟨u, by rw [Int.toNat_of_nonneg h0]; exact hu⟩
        have := hb _ hmem
        rw [Int.toNat_of_nonneg h0] at this
        exact this
      · exact le_trans h0.le (fboundG_nonneg _ _ _)
  -- negative side
  have hneg : -c ≤ fboundG K₂ L Q := by
    rw [← fboundG_flip K₂ L Q]
    rcases hK₂ L' Q with hinf | hb
    · exact (hinf hfinN').elim
    · rcases le_or_gt 0 (-c) with h0 | h0
      · have hmem : (-c).toNat ∈ fiberSetG (flipZero H) L' Q := by
          obtain ⟨u, hu⟩ := (hsol' (-c)).mpr (by rw [neg_neg]; exact hc)
          exact ⟨u, by rw [Int.toNat_of_nonneg h0]; exact hu⟩
        have := hb _ hmem
        rw [Int.toNat_of_nonneg h0] at this
        exact this
      · exact le_trans h0.le (fboundG_nonneg _ _ _)
  have habs : |c| ≤ fboundG (K₁ + K₂) L Q := by
    rw [abs_le]
    constructor
    · have h2 := fboundG_mono_K (by omega : K₂ ≤ K₁ + K₂) L Q
      linarith
    · exact le_trans hpos (fboundG_mono_K (by omega : K₁ ≤ K₁ + K₂) _ _)
  exact le_trans habs (hC N h1 a ha)

/-- The same in GPT's shape: |c| ≤ C·(1 + |a|_∞)², with |a|_∞ = sup_i |a_i| (= 0 for n = 0). -/
theorem singleQuadratic_finiteFiber_height_scalar_sup {n r : ℕ} (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) :
    ∃ C : ℕ, ∀ a : Fin n → ℤ, (fiberZZ P a).Finite → ∀ c ∈ fiberZZ P a,
      |c| ≤ (C : ℤ) * ((1 + Finset.univ.sup (fun i => (a i).natAbs) : ℕ) : ℤ) ^ 2 := by
  classical
  obtain ⟨C, hC⟩ := singleQuadratic_finiteFiber_height_scalar P hP
  refine ⟨C, fun a hfin c hc => ?_⟩
  refine hC (1 + Finset.univ.sup fun i => (a i).natAbs) (by omega) a ?_ hfin c hc
  intro i
  have h1 : (a i).natAbs ≤ Finset.univ.sup fun i => (a i).natAbs :=
    Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ i)
  rw [← Int.natCast_natAbs]
  exact_mod_cast (show (a i).natAbs ≤ 1 + Finset.univ.sup (fun i => (a i).natAbs) by omega)

/-! ### 必須A — vector output -/

/-- Rename making output coordinate `j` the distinguished last input coordinate; the other outputs become
    witnesses (slots `castAdd r k`), the original witnesses move to slots `natAdd m t`; slot `castAdd r j`
    is a dummy. -/
def vecCoordIdx (n m r : ℕ) (j : Fin m) : Fin (n + m) ⊕ Fin r → Fin (n + 1) ⊕ Fin (m + r)
  | Sum.inl v => Fin.addCases (motive := fun _ => Fin (n + 1) ⊕ Fin (m + r))
      (fun i => Sum.inl (Fin.castSucc i))
      (fun k => if k = j then Sum.inl (Fin.last n) else Sum.inr (Fin.castAdd r k)) v
  | Sum.inr t => Sum.inr (Fin.natAdd m t)

/-- The scalar polynomial whose fiber over `a` is the `j`-th coordinate projection of the vector fiber. -/
noncomputable def coordPoly {n m r : ℕ} (P : Poly (n + m) r) (j : Fin m) : Poly (n + 1) (m + r) :=
  rename (vecCoordIdx n m r j) P

theorem evalAtZZ_coordPoly {n m r : ℕ} (P : Poly (n + m) r) (j : Fin m) (a : Fin n → ℤ) (c : ℤ)
    (w : Fin (m + r) → ℤ) :
    evalAtZZ (coordPoly P j) (Fin.snoc a c) w
      = evalAtZZ P (Fin.append a (fun k => if k = j then c else w (Fin.castAdd r k)))
          (fun t => w (Fin.natAdd m t)) := by
  apply evalAtZZ_rename_eq
  intro v
  rcases v with v | t
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) v
    · simp [vecCoordIdx]
    · by_cases hk : k = j
      · subst hk; simp [vecCoordIdx]
      · simp [vecCoordIdx, hk]
  · simp [vecCoordIdx]

theorem mem_fiberZZ_coordPoly {n m r : ℕ} (P : Poly (n + m) r) (j : Fin m) (a : Fin n → ℤ) (c : ℤ) :
    c ∈ fiberZZ (coordPoly P j) a ↔ ∃ b ∈ fiberVecZZ P a, b j = c := by
  constructor
  · rintro ⟨w, hw⟩
    rw [evalAtZZ_coordPoly] at hw
    exact ⟨_, ⟨_, hw⟩, by simp⟩
  · rintro ⟨b, ⟨u, hu⟩, rfl⟩
    refine ⟨Fin.append b u, ?_⟩
    rw [evalAtZZ_coordPoly]
    have hb : (fun k => if k = j then b j else Fin.append b u (Fin.castAdd r k)) = b := by
      funext k
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    have hu' : (fun t => Fin.append b u (Fin.natAdd m t)) = u := by
      funext t; simp
    rw [hb, hu']
    exact hu

/-- Vector finite-fiber growth theorem: each output coordinate is a scalar fiber of a renamed `P`. -/
theorem singleQuadratic_finiteFiber_height_vector {n m r : ℕ} (P : Poly (n + m) r)
    (hP : P.totalDegree ≤ 2) : ∃ C : ℕ, FiberHeightBoundVecZZ P C := by
  classical
  have hdeg : ∀ j, (coordPoly P j).totalDegree ≤ 2 :=
    fun j => (totalDegree_rename_le _ _).trans hP
  choose Cj hCj using fun j => singleQuadratic_finiteFiber_height_scalar (coordPoly P j) (hdeg j)
  refine ⟨Finset.univ.sup Cj, ?_⟩
  intro N h1 a ha hfin b hb j
  have hfinj : (fiberZZ (coordPoly P j) a).Finite := by
    have : fiberZZ (coordPoly P j) a = (fun b => b j) '' fiberVecZZ P a := by
      ext c
      rw [Set.mem_image]
      exact mem_fiberZZ_coordPoly P j a c
    rw [this]
    exact hfin.image _
  have hcj : b j ∈ fiberZZ (coordPoly P j) a :=
    (mem_fiberZZ_coordPoly P j a (b j)).mpr ⟨b, hb, rfl⟩
  calc |b j| ≤ (Cj j : ℤ) * (N : ℤ) ^ 2 := hCj j N h1 a ha hfinj (b j) hcj
    _ ≤ ((Finset.univ.sup Cj : ℕ) : ℤ) * (N : ℤ) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Finset.le_sup (f := Cj) (Finset.mem_univ j)

/-! ### 必須B — definable functions -/

theorem mem_graphVecZZ_append {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) (a : Fin n → ℤ)
    (b : Fin m → ℤ) : Fin.append a b ∈ graphVecZZ f ↔ b = f a := by
  simp [graphVecZZ]

/-- Every single-quadratic-definable total function `ℤⁿ → ℤᵐ` has quadratic growth on boxes. -/
theorem singleQuadratic_function_quadratic_growth {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ))
    (hf : SingleQuadraticDefinableFunctionZZ f) :
    ∃ C : ℕ, ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
      ∀ j, |f a j| ≤ (C : ℤ) * (N : ℤ) ^ 2 := by
  obtain ⟨r, P, hP, hrep⟩ := hf
  obtain ⟨C, hC⟩ := singleQuadratic_finiteFiber_height_vector P hP
  refine ⟨C, fun N h1 a ha j => ?_⟩
  have hfib : fiberVecZZ P a = {f a} := by
    ext b
    rw [Set.mem_singleton_iff]
    show (∃ u, evalAtZZ P (Fin.append a b) u = 0) ↔ b = f a
    rw [← hrep, mem_graphVecZZ_append]
  exact hC N h1 a ha (by rw [hfib]; exact Set.finite_singleton _) (f a)
    (by rw [hfib]; exact Set.mem_singleton _) j

/-- Injective dimension inequality: a single-quadratic-definable injection `ℤⁿ ↪ ℤᵐ` forces `n ≤ 2m`. -/
theorem singleQuadratic_injective_dimension_bound {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ))
    (hf : SingleQuadraticDefinableFunctionZZ f) (hinj : Function.Injective f) : n ≤ 2 * m := by
  classical
  obtain ⟨C, hC⟩ := singleQuadratic_function_quadratic_growth f hf
  have h := box_counting_bound (ι := Fin m) (fun a j => f (fun i => (a i : ℤ)) j) ?inj
    (fun _ => 2) C ?bd
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    omega
  case inj =>
    intro a b hab
    have := hinj hab
    funext i
    exact_mod_cast congrFun this i
  case bd =>
    intro N h1 a ha j
    refine hC N h1 _ (fun i => ?_) j
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast ha i

/-- The one-sorted theorem of Gate 3 (`AtomGraphZZ 2 n → n ≤ 2`) is the case `m = 1` of the dimension bound. -/
theorem atomGraphZZ_le_two_from_dimension_bound : ∀ n, AtomGraphZZ 2 n → n ≤ 2 := by
  intro n h
  obtain ⟨r, e, he, P, hP, hrep⟩ := h
  have hg : graphVecZZ (fun a (_ : Fin 1) => e a) = graphZZ e := by
    ext v
    simp only [graphVecZZ, graphZZ, Set.mem_setOf_eq]
    have h0 : Fin.natAdd n (0 : Fin 1) = Fin.last n := by ext; simp
    constructor
    · intro h
      have := congrFun h 0
      rw [h0] at this
      exact this
    · intro h
      funext j
      rw [Subsingleton.elim j 0, h0]
      exact h
  have hf : SingleQuadraticDefinableFunctionZZ (fun a (_ : Fin 1) => e a) :=
    ⟨r, P, hP, by rw [hg]; exact hrep⟩
  have hinj : Function.Injective (fun a (_ : Fin 1) => e a) := fun a b h => he (congrFun h 0)
  have := singleQuadratic_injective_dimension_bound _ hf hinj
  omega

end DiophCompression

#print axioms DiophCompression.singleQuadratic_finiteFiber_height_scalar
#print axioms DiophCompression.singleQuadratic_finiteFiber_height_scalar_sup
#print axioms DiophCompression.singleQuadratic_finiteFiber_height_vector
#print axioms DiophCompression.singleQuadratic_function_quadratic_growth
#print axioms DiophCompression.singleQuadratic_injective_dimension_bound
#print axioms DiophCompression.atomGraphZZ_le_two_from_dimension_bound
