/-
  DiophCompression/FiniteFiberCardinality.lean — APAL Structural Theory Gate 1, kernel item 必須B
  (session 24, 2026-08-31, claude.ai direct, 0 CC).
  GPT r21 必須B: cardinality bounds for finite fibers of single-quadratic relations — a finite fiber inside the
  box [-B,B]^m has at most (2B+1)^m integer points, with B = C·N² from the height theorem (same constant C);
  the bundled definition `SingleQuadraticFiniteValuedRelationZZ`; graph/function special cases.
  Statements frozen in frozen_statements/FiniteFiberCardinality_STATEMENTS.lean (md5 recorded in HANDOFF s24).
-/
import DiophCompression.FiniteFiberGrowth

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Definitions -/

/-- Scalar cardinality bound on boxes: a finite fiber over |a_i| ≤ N has at most 2·C·N²+1 elements. -/
def FiberCardBoundZZ {n r : ℕ} (P : Poly (n + 1) r) (C : ℕ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
    (fiberZZ P a).Finite → (fiberZZ P a).ncard ≤ 2 * C * N ^ 2 + 1

/-- Vector cardinality bound on boxes: a finite fiber over |a_i| ≤ N has at most (2·C·N²+1)^m elements. -/
def FiberCardBoundVecZZ {n m r : ℕ} (P : Poly (n + m) r) (C : ℕ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
    (fiberVecZZ P a).Finite → (fiberVecZZ P a).ncard ≤ (2 * C * N ^ 2 + 1) ^ m

/-- A single-quadratic finite-valued relation: `P` has total degree ≤ 2 and every input fiber is finite. -/
def SingleQuadraticFiniteValuedRelationZZ {n m r : ℕ} (P : Poly (n + m) r) : Prop :=
  P.totalDegree ≤ 2 ∧ FiniteFiberRelationZZ P

/-! ### Theorems -/

/-- Any set of integers bounded by `B` in absolute value has at most `2B+1` elements. -/
theorem ncard_le_of_abs_le (S : Set ℤ) (B : ℕ) (hS : ∀ c ∈ S, |c| ≤ (B : ℤ)) :
    S.ncard ≤ 2 * B + 1 := by
  have hsub : S ⊆ ((Finset.Icc (-(B : ℤ)) B : Finset ℤ) : Set ℤ) := by
    intro c hc
    rw [Finset.coe_Icc, Set.mem_Icc]
    exact abs_le.mp (hS c hc)
  calc S.ncard ≤ ((Finset.Icc (-(B : ℤ)) B : Finset ℤ) : Set ℤ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Finset.Icc (-(B : ℤ)) B).card := Set.ncard_coe_finset _
    _ = 2 * B + 1 := by rw [Int.card_Icc]; omega

/-- Any set of integer vectors bounded coordinatewise by `B` has at most `(2B+1)^m` elements. -/
theorem ncard_le_of_abs_le_vec {m : ℕ} (S : Set (Fin m → ℤ)) (B : ℕ)
    (hS : ∀ b ∈ S, ∀ j, |b j| ≤ (B : ℤ)) : S.ncard ≤ (2 * B + 1) ^ m := by
  classical
  let T : Finset (Fin m → ℤ) := Fintype.piFinset (fun _ : Fin m => Finset.Icc (-(B : ℤ)) B)
  have hsub : S ⊆ (T : Set (Fin m → ℤ)) := by
    intro b hb
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_Icc]
    exact abs_le.mp (hS b hb j)
  calc S.ncard ≤ (T : Set (Fin m → ℤ)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = T.card := Set.ncard_coe_finset _
    _ = (2 * B + 1) ^ m := by
        simp only [T]
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
        congr 1
        omega

/-- Height bound ⇒ cardinality bound (scalar), same constant. -/
theorem fiberCardBound_of_fiberHeightBound {n r : ℕ} (P : Poly (n + 1) r) (C : ℕ)
    (h : FiberHeightBoundZZ P C) : FiberCardBoundZZ P C := by
  intro N h1 a ha hfin
  have hb := ncard_le_of_abs_le (fiberZZ P a) (C * N ^ 2) (fun c hc => by
    have := h N h1 a ha hfin c hc
    push_cast
    exact this)
  refine hb.trans (le_of_eq ?_)
  ring

/-- Height bound ⇒ cardinality bound (vector), same constant. -/
theorem fiberCardBoundVec_of_fiberHeightBoundVec {n m r : ℕ} (P : Poly (n + m) r) (C : ℕ)
    (h : FiberHeightBoundVecZZ P C) : FiberCardBoundVecZZ P C := by
  intro N h1 a ha hfin
  have hb := ncard_le_of_abs_le_vec (fiberVecZZ P a) (C * N ^ 2) (fun b hb j => by
    have := h N h1 a ha hfin b hb j
    push_cast
    exact this)
  refine hb.trans (le_of_eq ?_)
  ring

/-- 必須B (scalar): a single quadratic has finite fibers of size ≤ 2·C·N²+1 on the box |a_i| ≤ N. -/
theorem singleQuadratic_finiteFiber_cardinality_scalar {n r : ℕ} (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) : ∃ C : ℕ, FiberHeightBoundZZ P C ∧ FiberCardBoundZZ P C := by
  obtain ⟨C, hC⟩ := singleQuadratic_finiteFiber_height_scalar P hP
  exact ⟨C, hC, fiberCardBound_of_fiberHeightBound P C hC⟩

/-- 必須B (vector): finite fibers of size ≤ (2·C·N²+1)^m on the box, same C as the height bound. -/
theorem singleQuadratic_finiteFiber_cardinality_vector {n m r : ℕ} (P : Poly (n + m) r)
    (hP : P.totalDegree ≤ 2) : ∃ C : ℕ, FiberHeightBoundVecZZ P C ∧ FiberCardBoundVecZZ P C := by
  obtain ⟨C, hC⟩ := singleQuadratic_finiteFiber_height_vector P hP
  exact ⟨C, hC, fiberCardBoundVec_of_fiberHeightBoundVec P C hC⟩

/-- Sup-norm form (scalar): |R_P(a)| ≤ 2·C·(1+|a|_∞)²+1 for every finite fiber. -/
theorem singleQuadratic_finiteFiber_cardinality_scalar_sup {n r : ℕ} (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) :
    ∃ C : ℕ, ∀ a : Fin n → ℤ, (fiberZZ P a).Finite →
      (fiberZZ P a).ncard ≤ 2 * C * (1 + Finset.univ.sup (fun i => (a i).natAbs)) ^ 2 + 1 := by
  classical
  obtain ⟨C, hC⟩ := singleQuadratic_finiteFiber_height_scalar_sup P hP
  refine ⟨C, fun a hfin => ?_⟩
  have hb := ncard_le_of_abs_le (fiberZZ P a)
    (C * (1 + Finset.univ.sup (fun i => (a i).natAbs)) ^ 2) (fun c hc => by
      have := hC a hfin c hc
      push_cast
      exact this)
  refine hb.trans (le_of_eq ?_)
  ring

/-- Sup-norm form (vector): |R_P(a)| ≤ (2·C·(1+|a|_∞)²+1)^m for every finite fiber. -/
theorem singleQuadratic_finiteFiber_cardinality_vector_sup {n m r : ℕ} (P : Poly (n + m) r)
    (hP : P.totalDegree ≤ 2) :
    ∃ C : ℕ, ∀ a : Fin n → ℤ, (fiberVecZZ P a).Finite →
      (fiberVecZZ P a).ncard ≤ (2 * C * (1 + Finset.univ.sup (fun i => (a i).natAbs)) ^ 2 + 1) ^ m := by
  classical
  obtain ⟨C, hC⟩ := singleQuadratic_finiteFiber_height_vector P hP
  refine ⟨C, fun a hfin => ?_⟩
  have hbox : ∀ i, |a i| ≤ ((1 + Finset.univ.sup (fun i => (a i).natAbs) : ℕ) : ℤ) := by
    intro i
    have h1 : (a i).natAbs ≤ Finset.univ.sup fun i => (a i).natAbs :=
      Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ i)
    rw [← Int.natCast_natAbs]
    exact_mod_cast (show (a i).natAbs ≤ 1 + Finset.univ.sup (fun i => (a i).natAbs) by omega)
  have hb := ncard_le_of_abs_le_vec (fiberVecZZ P a)
    (C * (1 + Finset.univ.sup (fun i => (a i).natAbs)) ^ 2) (fun b hb j => by
      have := hC (1 + Finset.univ.sup fun i => (a i).natAbs) (by omega) a hbox hfin b hb j
      push_cast
      exact this)
  refine hb.trans (le_of_eq ?_)
  ring

/-- Bundle: a single-quadratic finite-valued relation has, for one constant C, the height bound and the
    cardinality bound at every input (the finiteness hypothesis of the box forms is discharged globally). -/
theorem singleQuadraticFiniteValuedRelation_bounds {n m r : ℕ} (P : Poly (n + m) r)
    (hR : SingleQuadraticFiniteValuedRelationZZ P) :
    ∃ C : ℕ, ∀ N : ℕ, 1 ≤ N → ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ N) →
      (∀ b ∈ fiberVecZZ P a, ∀ j, |b j| ≤ (C : ℤ) * (N : ℤ) ^ 2) ∧
      (fiberVecZZ P a).ncard ≤ (2 * C * N ^ 2 + 1) ^ m := by
  obtain ⟨hP, hfin⟩ := hR
  obtain ⟨C, hC1, hC2⟩ := singleQuadratic_finiteFiber_cardinality_vector P hP
  exact ⟨C, fun N h1 a ha => ⟨fun b hb j => hC1 N h1 a ha (hfin a) b hb j, hC2 N h1 a ha (hfin a)⟩⟩

/-- Graph special case: the fiber of a representing polynomial of a definable function is the singleton {f a}. -/
theorem fiberVecZZ_eq_singleton_of_represents {n m r : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ))
    (P : Poly (n + m) r) (hrep : RepresentsZZ P (graphVecZZ f)) (a : Fin n → ℤ) :
    fiberVecZZ P a = {f a} := by
  ext b
  rw [Set.mem_singleton_iff]
  show (∃ u, evalAtZZ P (Fin.append a b) u = 0) ↔ b = f a
  rw [← hrep, mem_graphVecZZ_append]

/-- Function special case: the graph relation of a single-quadratic-definable function is a
    single-quadratic finite-valued relation (fibers are singletons). -/
theorem singleQuadraticDefinableFunction_finiteValued {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ))
    (hf : SingleQuadraticDefinableFunctionZZ f) :
    ∃ r, ∃ P : Poly (n + m) r, RepresentsZZ P (graphVecZZ f) ∧ SingleQuadraticFiniteValuedRelationZZ P := by
  obtain ⟨r, P, hP, hrep⟩ := hf
  refine ⟨r, P, hrep, hP, fun a => ?_⟩
  rw [fiberVecZZ_eq_singleton_of_represents f P hrep a]
  exact Set.finite_singleton _

end DiophCompression

#print axioms DiophCompression.ncard_le_of_abs_le
#print axioms DiophCompression.ncard_le_of_abs_le_vec
#print axioms DiophCompression.fiberCardBound_of_fiberHeightBound
#print axioms DiophCompression.fiberCardBoundVec_of_fiberHeightBoundVec
#print axioms DiophCompression.singleQuadratic_finiteFiber_cardinality_scalar
#print axioms DiophCompression.singleQuadratic_finiteFiber_cardinality_vector
#print axioms DiophCompression.singleQuadratic_finiteFiber_cardinality_scalar_sup
#print axioms DiophCompression.singleQuadratic_finiteFiber_cardinality_vector_sup
#print axioms DiophCompression.singleQuadraticFiniteValuedRelation_bounds
#print axioms DiophCompression.fiberVecZZ_eq_singleton_of_represents
#print axioms DiophCompression.singleQuadraticDefinableFunction_finiteValued
