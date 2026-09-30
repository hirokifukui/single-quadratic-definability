import DiophCompression.SemanticQuadratic.FiberDefs
import DiophCompression.PolynomialMapCapacity
import DiophCompression.WeakenUnknowns

namespace DiophCompression.SemanticQuadratic

open MPUP
open MvPolynomial

/-- Core of D9: given the dichotomy and an injective `e` whose graph is represented by a
    single-unknown polynomial of total degree ≤ 2, box-counting forces `n ≤ 2`. -/
theorem graph_one_witness_aux (hD : ∀ A B C : ℤ, Dichotomy A B C)
    {n : ℕ} (e : (Fin n → ℕ) → ℕ) (he : Function.Injective e)
    (P : Poly (n + 1) 1) (hP : P.totalDegree ≤ 2) (hrep : RepresentsZ P (graph e)) :
    n ≤ 2 := by
  classical
  -- Normal form of the fiber quadratic.
  obtain ⟨A, B, C, L, M, Q, hL, hM, hQ, heq⟩ := quadratic_normal_form_explicit P hP
  -- The fiber set at parameter point `a` is exactly the singleton `{e a}`.
  have hmem : ∀ (a : Fin n → ℕ) (c : ℕ),
      c ∈ fiberSet A B C (eval (fun i => (a i : ℤ)) L) (eval (fun i => (a i : ℤ)) M)
            (eval (fun i => (a i : ℤ)) Q) ↔ c = e a := by
    intro a c
    have key : ∀ u : ℤ,
        fq A B C (eval (fun i => (a i : ℤ)) L) (eval (fun i => (a i : ℤ)) M)
            (eval (fun i => (a i : ℤ)) Q) (↑c) u
          = evalAt P (Fin.snoc a c) (fun _ => u) := by
      intro u; rw [heq a c u]; simp only [fq]
    have hg : (Fin.snoc a c : Fin (n + 1) → ℕ) ∈ graph e ↔ c = e a := by
      simp only [graph, Set.mem_setOf_eq, Fin.snoc_last, Fin.init_snoc]
    simp only [fiberSet, Set.mem_setOf_eq]
    rw [← hg, hrep (Fin.snoc a c)]
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨fun _ => u, by rw [← key u]; exact hu⟩
    · rintro ⟨y, hy⟩
      refine ⟨y 0, ?_⟩
      rw [key]
      have hy' : (fun _ : Fin 1 => y 0) = y := by
        funext j; exact congrArg y (Subsingleton.elim 0 j)
      rw [hy']; exact hy
  -- The dichotomy: since each fiber set is a singleton (finite), the bounded branch holds.
  obtain ⟨Kd, hK⟩ := hD A B C
  have hbound : ∀ a : Fin n → ℕ,
      (e a : ℤ) ≤ fbound Kd (eval (fun i => (a i : ℤ)) L) (eval (fun i => (a i : ℤ)) M)
        (eval (fun i => (a i : ℤ)) Q) := by
    intro a
    rcases hK (eval (fun i => (a i : ℤ)) L) (eval (fun i => (a i : ℤ)) M)
        (eval (fun i => (a i : ℤ)) Q) with hinf | hb
    · exfalso
      have hsub : fiberSet A B C (eval (fun i => (a i : ℤ)) L) (eval (fun i => (a i : ℤ)) M)
          (eval (fun i => (a i : ℤ)) Q) ⊆ {e a} := by
        intro c hc; rw [Set.mem_singleton_iff]; exact (hmem a c).mp hc
      exact hinf (Set.Finite.subset (Set.finite_singleton (e a)) hsub)
    · exact hb (e a) ((hmem a (e a)).mpr rfl)
  -- Coefficient magnitude sums.
  set SL : ℕ := ∑ β ∈ L.support, (coeff β L).natAbs with hSL
  set SM : ℕ := ∑ β ∈ M.support, (coeff β M).natAbs with hSM
  set SQ : ℕ := ∑ β ∈ Q.support, (coeff β Q).natAbs with hSQ
  have hSLcast : (SL : ℤ) = ∑ β ∈ L.support, |coeff β L| := by
    rw [hSL, Nat.cast_sum]; exact Finset.sum_congr rfl fun β _ => Int.natCast_natAbs _
  have hSMcast : (SM : ℤ) = ∑ β ∈ M.support, |coeff β M| := by
    rw [hSM, Nat.cast_sum]; exact Finset.sum_congr rfl fun β _ => Int.natCast_natAbs _
  have hSQcast : (SQ : ℤ) = ∑ β ∈ Q.support, |coeff β Q| := by
    rw [hSQ, Nat.cast_sum]; exact Finset.sum_congr rfl fun β _ => Int.natCast_natAbs _
  -- The box bound: `e a ≤ K' N²` on the box `[0,N]ⁿ`.
  have hfinalbound : ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℕ, (∀ i, a i ≤ N) →
      (e a : ℤ) ≤ ((Kd * ((1 + SL + SM) ^ 2 + SQ) : ℕ) : ℤ) * (N : ℤ) ^ 2 := by
    intro N h1 a ha
    have hNz : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast h1
    have hLb : |eval (fun i => (a i : ℤ)) L| ≤ (SL : ℤ) * (N : ℤ) := by
      have h := eval_abs_le L h1 a ha
      rw [hSLcast]
      calc |eval (fun i => (a i : ℤ)) L|
          ≤ (∑ β ∈ L.support, |coeff β L|) * (N : ℤ) ^ L.totalDegree := h
        _ ≤ (∑ β ∈ L.support, |coeff β L|) * (N : ℤ) ^ 1 := by
            apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hNz hL)
            rw [← hSLcast]; positivity
        _ = (∑ β ∈ L.support, |coeff β L|) * (N : ℤ) := by ring
    have hMb : |eval (fun i => (a i : ℤ)) M| ≤ (SM : ℤ) * (N : ℤ) := by
      have h := eval_abs_le M h1 a ha
      rw [hSMcast]
      calc |eval (fun i => (a i : ℤ)) M|
          ≤ (∑ β ∈ M.support, |coeff β M|) * (N : ℤ) ^ M.totalDegree := h
        _ ≤ (∑ β ∈ M.support, |coeff β M|) * (N : ℤ) ^ 1 := by
            apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hNz hM)
            rw [← hSMcast]; positivity
        _ = (∑ β ∈ M.support, |coeff β M|) * (N : ℤ) := by ring
    have hQb : |eval (fun i => (a i : ℤ)) Q| ≤ (SQ : ℤ) * (N : ℤ) ^ 2 := by
      have h := eval_abs_le Q h1 a ha
      rw [hSQcast]
      calc |eval (fun i => (a i : ℤ)) Q|
          ≤ (∑ β ∈ Q.support, |coeff β Q|) * (N : ℤ) ^ Q.totalDegree := h
        _ ≤ (∑ β ∈ Q.support, |coeff β Q|) * (N : ℤ) ^ 2 := by
            apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hNz hQ)
            rw [← hSQcast]; positivity
    have hd := hbound a
    simp only [fbound] at hd
    -- abbreviations
    have hnn : (0 : ℤ) ≤ 1 + |eval (fun i => (a i : ℤ)) L| + |eval (fun i => (a i : ℤ)) M| := by
      positivity
    have step1 : 1 + |eval (fun i => (a i : ℤ)) L| + |eval (fun i => (a i : ℤ)) M|
        ≤ (1 + (SL : ℤ) + SM) * N := by nlinarith [hLb, hMb, hNz]
    have step2 : (1 + |eval (fun i => (a i : ℤ)) L| + |eval (fun i => (a i : ℤ)) M|) ^ 2
        ≤ ((1 + (SL : ℤ) + SM) * N) ^ 2 := pow_le_pow_left₀ hnn step1 2
    have hexp : ((1 + (SL : ℤ) + SM) * N) ^ 2 = (1 + (SL : ℤ) + SM) ^ 2 * N ^ 2 := by ring
    rw [hexp] at step2
    have inner : (1 + |eval (fun i => (a i : ℤ)) L| + |eval (fun i => (a i : ℤ)) M|) ^ 2
          + |eval (fun i => (a i : ℤ)) Q|
        ≤ ((1 + (SL : ℤ) + SM) ^ 2 + SQ) * N ^ 2 := by nlinarith [step2, hQb]
    calc (e a : ℤ)
        ≤ (Kd : ℤ) * ((1 + |eval (fun i => (a i : ℤ)) L| + |eval (fun i => (a i : ℤ)) M|) ^ 2
            + |eval (fun i => (a i : ℤ)) Q|) := hd
      _ ≤ (Kd : ℤ) * (((1 + (SL : ℤ) + SM) ^ 2 + SQ) * N ^ 2) :=
          mul_le_mul_of_nonneg_left inner (by positivity)
      _ = ((Kd * ((1 + SL + SM) ^ 2 + SQ) : ℕ) : ℤ) * (N : ℤ) ^ 2 := by push_cast; ring
  -- Box-counting.
  have hbc := box_counting_bound (ι := Fin 1) (fun a (_ : Fin 1) => ((e a : ℕ) : ℤ)) ?inj
    (fun _ => 2) (Kd * ((1 + SL + SM) ^ 2 + SQ)) ?bd
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

/-- The frozen D9 statement. -/
theorem graph_one_witness_degree_two_le_two_of_dichotomy (hD : ∀ A B C : ℤ, Dichotomy A B C)
    {n : ℕ} (h : GraphAchievableZ n 1 2) : n ≤ 2 := by
  obtain ⟨e, he, r', hr', P, hP, hrep⟩ := h
  interval_cases r'
  · -- no unknown: pad with one dummy unknown
    have hrep₁ : RepresentsZ (weakenUnknowns 1 P) (graph e) := by
      intro v
      rw [hrep v]
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨fun _ => 0, ?_⟩
        rw [evalAt_weakenUnknowns]
        rwa [Subsingleton.elim (fun j => (fun _ : Fin 1 => (0 : ℤ)) (Fin.castAdd 1 j)) y]
      · rintro ⟨z, hz⟩
        rw [evalAt_weakenUnknowns] at hz
        exact ⟨_, hz⟩
    have hP₁ : (weakenUnknowns 1 P).totalDegree ≤ 2 :=
      le_trans (totalDegree_weakenUnknowns_le P) hP
    exact graph_one_witness_aux hD e he (weakenUnknowns 1 P) hP₁ hrep₁
  · exact graph_one_witness_aux hD e he P hP hrep

end DiophCompression.SemanticQuadratic

#print axioms DiophCompression.SemanticQuadratic.graph_one_witness_degree_two_le_two_of_dichotomy
