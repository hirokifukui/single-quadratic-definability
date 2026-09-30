/-
  DiophCompression/SemanticQuadraticGeneral/ProjectionDichotomy.lean — r07 必須C (GPT r06 §7): the abstract
  "projection dichotomy ⇒ graph capacity two" theorem for any number r of integer witnesses, its capacity
  form, the 必須F reduction (dichotomy for every r ⇒ Quadratic Witness Inertia), and the r = 1 instance
  from the r06 leaves. Statements frozen first: frozen statement file `SemanticQuadraticGeneral_STATEMENTS.lean` (md5 65776f2e).
  The proof of the main theorem is Class_D9's box-counting argument with Σ_i ℓ_i in place of (L, M).
  Session 7, 2026-08-27, claude.ai direct.
-/
import DiophCompression.SemanticQuadraticGeneral.NormalForm
import DiophCompression.SemanticQuadratic.FiberDichotomy
import DiophCompression.PolynomialMapCapacity
import DiophCompression.BoundaryCasesZ

namespace DiophCompression.SemanticQuadraticGeneral

open MvPolynomial MPUP

/-- Core: given the dichotomy for r witnesses and an injective `e` whose graph is represented by a
    degree-≤2 polynomial with exactly r integer unknowns, box counting forces `n ≤ 2`. -/
theorem capacity_two_aux {r : ℕ} (hD : QuadraticProjectionDichotomyZ r)
    {n : ℕ} (e : (Fin n → ℕ) → ℕ) (he : Function.Injective e)
    (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2) (hrep : RepresentsZ P (graph e)) :
    n ≤ 2 := by
  classical
  obtain ⟨H, ℓ, q, hH, _, hℓ, hq, heq⟩ := quadratic_normal_form_general P hP
  -- abbreviations for the evaluated linear part
  let ℓa : (Fin n → ℕ) → Fin (r + 1) → ℤ := fun a i => eval (fun j => (a j : ℤ)) (ℓ i)
  let qa : (Fin n → ℕ) → ℤ := fun a => eval (fun j => (a j : ℤ)) q
  -- the fiber set at parameter point a is exactly {e a}
  have hmem : ∀ (a : Fin n → ℕ) (c : ℕ), c ∈ fiberSetG H (ℓa a) (qa a) ↔ c = e a := by
    intro a c
    have hg : (Fin.snoc a c : Fin (n + 1) → ℕ) ∈ graph e ↔ c = e a := by
      simp only [graph, Set.mem_setOf_eq, Fin.snoc_last, Fin.init_snoc]
    simp only [fiberSetG, Set.mem_setOf_eq]
    rw [← hg, hrep (Fin.snoc a c)]
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨u, by rw [heq a c u]; exact hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, by rw [← heq a c u]; exact hu⟩
  obtain ⟨Kd, hK⟩ := hD H hH
  have hbound : ∀ a : Fin n → ℕ, (e a : ℤ) ≤ fboundG Kd (ℓa a) (qa a) := by
    intro a
    rcases hK (ℓa a) (qa a) with hinf | hb
    · exfalso
      have hsub : fiberSetG H (ℓa a) (qa a) ⊆ {e a} := by
        intro c hc; rw [Set.mem_singleton_iff]; exact (hmem a c).mp hc
      exact hinf (Set.Finite.subset (Set.finite_singleton (e a)) hsub)
    · exact hb (e a) ((hmem a (e a)).mpr rfl)
  -- coefficient magnitude sums
  set SL : ℕ := ∑ i, ∑ β ∈ (ℓ i).support, (coeff β (ℓ i)).natAbs with hSL
  set SQ : ℕ := ∑ β ∈ q.support, (coeff β q).natAbs with hSQ
  have hSLcast : (SL : ℤ) = ∑ i, ∑ β ∈ (ℓ i).support, |coeff β (ℓ i)| := by
    rw [hSL, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun β _ => Int.natCast_natAbs _
  have hSQcast : (SQ : ℤ) = ∑ β ∈ q.support, |coeff β q| := by
    rw [hSQ, Nat.cast_sum]; exact Finset.sum_congr rfl fun β _ => Int.natCast_natAbs _
  have hfinalbound : ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℕ, (∀ i, a i ≤ N) →
      (e a : ℤ) ≤ ((Kd * ((1 + SL) ^ 2 + SQ) : ℕ) : ℤ) * (N : ℤ) ^ 2 := by
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
    have hd := hbound a
    simp only [fboundG] at hd
    have hnn : (0 : ℤ) ≤ 1 + ∑ i, |ℓa a i| := by positivity
    have step1 : 1 + ∑ i, |ℓa a i| ≤ (1 + (SL : ℤ)) * N := by nlinarith [hsum, hNz]
    have step2 : (1 + ∑ i, |ℓa a i|) ^ 2 ≤ ((1 + (SL : ℤ)) * N) ^ 2 := pow_le_pow_left₀ hnn step1 2
    have hexp : ((1 + (SL : ℤ)) * N) ^ 2 = (1 + (SL : ℤ)) ^ 2 * N ^ 2 := by ring
    rw [hexp] at step2
    have inner : (1 + ∑ i, |ℓa a i|) ^ 2 + |qa a| ≤ ((1 + (SL : ℤ)) ^ 2 + SQ) * N ^ 2 := by
      nlinarith [step2, hQb]
    calc (e a : ℤ)
        ≤ (Kd : ℤ) * ((1 + ∑ i, |ℓa a i|) ^ 2 + |qa a|) := hd
      _ ≤ (Kd : ℤ) * (((1 + (SL : ℤ)) ^ 2 + SQ) * N ^ 2) :=
          mul_le_mul_of_nonneg_left inner (by positivity)
      _ = ((Kd * ((1 + SL) ^ 2 + SQ) : ℕ) : ℤ) * (N : ℤ) ^ 2 := by push_cast; ring
  have hbc := box_counting_bound (ι := Fin 1) (fun a (_ : Fin 1) => ((e a : ℕ) : ℤ)) ?inj
    (fun _ => 2) (Kd * ((1 + SL) ^ 2 + SQ)) ?bd
  · simpa using hbc
  case inj =>
    intro a b hab
    apply he
    have h0 : ((e a : ℕ) : ℤ) = ((e b : ℕ) : ℤ) := congrFun hab 0
    exact_mod_cast h0
  case bd =>
    intro N h1 a ha j
    rw [abs_of_nonneg (by positivity)]
    exact hfinalbound N h1 a ha

/-- 必須C (GPT's name): the projection dichotomy for r witnesses forces graph capacity ≤ 2. -/
theorem quadraticProjectionDichotomy_implies_capacity_two {r : ℕ}
    (hD : QuadraticProjectionDichotomyZ r) :
    ∀ n, GraphAchievableZ n r 2 → n ≤ 2 := by
  intro n h
  obtain ⟨e, he, r', hr', P, hP, hrep⟩ := h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hr'
  have hrep' : RepresentsZ (weakenUnknowns m P) (graph e) := by
    intro v
    rw [hrep v]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨Fin.append y (fun _ => 0), ?_⟩
      rw [evalAt_weakenUnknowns]
      have : (fun j => Fin.append y (fun _ : Fin m => (0 : ℤ)) (Fin.castAdd m j)) = y := by
        funext j; exact Fin.append_left _ _ _
      rw [this]; exact hy
    · rintro ⟨z, hz⟩
      rw [evalAt_weakenUnknowns] at hz
      exact ⟨_, hz⟩
  have hP' : (weakenUnknowns m P).totalDegree ≤ 2 :=
    (totalDegree_weakenUnknowns_le P).trans hP
  exact capacity_two_aux hD e he (weakenUnknowns m P) hP' hrep'

/-- Capacity form: G_ℤ(r, 2) = 2 under the dichotomy (lower bound from the zero-witness pairing polynomial). -/
theorem graphCapacityZ_two_of_projectionDichotomy {r : ℕ} (hD : QuadraticProjectionDichotomyZ r) :
    graphCapacityZ r 2 = 2 := by
  apply le_antisymm
  · exact quadraticProjectionDichotomy_implies_capacity_two hD _
      ((graphCapacityZ_spec r 2 (by norm_num) _).mpr le_rfl)
  · -- lower bound G_ℤ(r,2) ≥ 2: the zero-witness pairing polynomial (`graph_no_witness_achievable_Z`)
    -- and witness monotonicity; no tree coding (s15, GPT r14 §9).
    exact (graphCapacityZ_spec r 2 (by norm_num) 2).mp
      (graphAchievableZ_mono (Nat.zero_le r) le_rfl (graph_no_witness_achievable_Z 2 (by norm_num)))

/-- 必須F, reduction: dichotomy for every r ⇒ Quadratic Witness Inertia. -/
theorem quadraticWitnessInertiaZ_of_projectionDichotomy
    (hD : ∀ r, QuadraticProjectionDichotomyZ r) : QuadraticWitnessInertiaZ :=
  fun r => graphCapacityZ_two_of_projectionDichotomy (hD r)

/-- A homogeneous binary quadratic form has exactly the three monomials. -/
theorem eval_binary_homogeneous_quadratic (H : MvPolynomial (Fin 2) ℤ) (hH : H.IsHomogeneous 2)
    (x : Fin 2 → ℤ) :
    eval x H = coeff (Finsupp.single 0 2) H * x 0 ^ 2
      + coeff (Finsupp.single 0 1 + Finsupp.single 1 1) H * (x 0 * x 1)
      + coeff (Finsupp.single 1 2) H * x 1 ^ 2 := by
  classical
  rw [eval_eq']
  set T : Finset (Fin 2 →₀ ℕ) :=
    {Finsupp.single 0 2, Finsupp.single 0 1 + Finsupp.single 1 1, Finsupp.single 1 2} with hT
  have hsub : H.support ⊆ T := by
    intro d hd
    have hne : coeff d H ≠ 0 := mem_support_iff.mp hd
    have hdeg : Finsupp.degree d = 2 := by
      by_contra hc
      exact hne (hH.coeff_eq_zero hc)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
    have h0 : d 0 ≤ 2 := by omega
    simp only [hT, Finset.mem_insert, Finset.mem_singleton]
    interval_cases hd0 : d 0
    · right; right
      ext i; fin_cases i <;> simp <;> omega
    · right; left
      ext i; fin_cases i <;> simp <;> omega
    · left
      ext i; fin_cases i <;> simp <;> omega
  have hzero : ∀ d ∈ T, d ∉ H.support → coeff d H * ∏ i, x i ^ d i = 0 := by
    intro d _ hd
    have : coeff d H = 0 := by
      by_contra h
      exact hd (mem_support_iff.mpr h)
    rw [this, zero_mul]
  rw [Finset.sum_subset hsub hzero]
  have h12 : (Finsupp.single (0 : Fin 2) 2) ∉
      ({Finsupp.single 0 1 + Finsupp.single 1 1, Finsupp.single 1 2} : Finset (Fin 2 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro h; have := DFunLike.congr_fun h 0; simp at this
    · intro h; have := DFunLike.congr_fun h 0; simp at this
  have h23 : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1) ∉
      ({Finsupp.single 1 2} : Finset (Fin 2 →₀ ℕ)) := by
    simp only [Finset.mem_singleton]
    intro h; have := DFunLike.congr_fun h 0; simp at this
  rw [hT, Finset.sum_insert h12, Finset.sum_insert h23, Finset.sum_singleton]
  simp only [Fin.prod_univ_two, Finsupp.single_apply, Finsupp.add_apply]
  simp
  ring

/-- r = 1 instance from the r06 leaves: the r06 result is the first case of the general theorem. -/
theorem quadraticProjectionDichotomyZ_one : QuadraticProjectionDichotomyZ 1 := by
  intro H hH
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = coeff (Finsupp.single 0 2) H := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = coeff (Finsupp.single 0 1 + Finsupp.single 1 1) H := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C = coeff (Finsupp.single 1 2) H := ⟨_, rfl⟩
  have hev : ∀ x : Fin 2 → ℤ, eval x H = A * x 0 ^ 2 + B * (x 0 * x 1) + C * x 1 ^ 2 := by
    intro x; rw [eval_binary_homogeneous_quadratic H hH x, hA, hB, hC]
  obtain ⟨K, hK⟩ := SemanticQuadratic.fiber_dichotomy A B C
  refine ⟨K, fun ℓ q => ?_⟩
  have hsum2 : ∀ (f : Fin (1 + 1) → ℤ), ∑ i, f i = f 0 + f 1 := fun f => by
    rw [Fin.sum_univ_succ, Fin.sum_univ_one]; rfl
  have hs1 : ℓ (Fin.succ 0) = ℓ 1 := rfl
  have hset : fiberSetG H ℓ q = SemanticQuadratic.fiberSet A B C (ℓ 0) (ℓ 1) q := by
    ext c
    simp only [fiberSetG, SemanticQuadratic.fiberSet, SemanticQuadratic.fq, Set.mem_setOf_eq,
      fiberVal, hev, Fin.cons_zero, Fin.cons_one]
    constructor
    · rintro ⟨u, hu⟩
      rw [Fin.sum_univ_succ, Fin.sum_univ_one] at hu
      simp only [Fin.cons_zero, Fin.cons_succ, hs1] at hu
      exact ⟨u 0, by linarith [hu]⟩
    · rintro ⟨u, hu⟩
      refine ⟨fun _ => u, ?_⟩
      rw [Fin.sum_univ_succ, Fin.sum_univ_one]
      simp only [Fin.cons_zero, Fin.cons_succ, hs1]
      linarith [hu]
  have hb : fboundG K ℓ q = SemanticQuadratic.fbound K (ℓ 0) (ℓ 1) q := by
    simp only [fboundG, SemanticQuadratic.fbound]
    rw [hsum2 (fun i => |ℓ i|)]; ring
  rw [hset, hb]
  exact hK (ℓ 0) (ℓ 1) q

end DiophCompression.SemanticQuadraticGeneral

#print axioms DiophCompression.SemanticQuadraticGeneral.capacity_two_aux
#print axioms DiophCompression.SemanticQuadraticGeneral.quadraticProjectionDichotomy_implies_capacity_two
#print axioms DiophCompression.SemanticQuadraticGeneral.graphCapacityZ_two_of_projectionDichotomy
#print axioms DiophCompression.SemanticQuadraticGeneral.quadraticWitnessInertiaZ_of_projectionDichotomy
#print axioms DiophCompression.SemanticQuadraticGeneral.eval_binary_homogeneous_quadratic
#print axioms DiophCompression.SemanticQuadraticGeneral.quadraticProjectionDichotomyZ_one

-- Positive control: the r06 headline re-derived through the general theorem.
example : DiophCompression.graphCapacityZ 1 2 = 2 :=
  DiophCompression.SemanticQuadraticGeneral.graphCapacityZ_two_of_projectionDichotomy
    DiophCompression.SemanticQuadraticGeneral.quadraticProjectionDichotomyZ_one
