/-
  DiophCompression/QuadraticPPSeparation.lean — APAL Logic Pivot, Gate 1 (session 19, 2026-08-30, claude.ai direct).
  Theorem B (atomic / primitive-positive separation at degree two):
      Atom_2  ⊊  PPQuad  ⊆  Atom_4      on graphs of injections ℕ^n → ℕ.
  Witness of strictness: the ternary scaled-Cantor pairing e(a) = π(π(a₀,a₁),a₂), π(x,y) = (x+y)(x+y+1)+2y,
  whose graph is defined by the quadratic SYSTEM { z = π(a₀,a₁), c = π(z,a₂) } (one ℤ-witness z) but by no
  single quadratic equation with any number of witnesses (Quadratic Witness Inertia).
  PPQuad ⊆ Atom_4: over ℤ, Q₁ = ⋯ = Q_m = 0 ⟺ Σ Q_i² = 0, and degree doubles.
  PPQuad codes every arity: the r18 chain's gate equations X(out_i) − gate_i (β = 1) form a quadratic system.
  Statements frozen in frozen_statements/LogicPivot_STATEMENTS.lean (md5 4b647f55).
-/
import DiophCompression.CodingDegree

namespace DiophCompression

open MvPolynomial MPUP

/-! ### The scaled Cantor pairing (integer coefficients; injective on ℕ²) -/

/-- `π(x,y) = (x+y)(x+y+1) + 2y` — twice the Cantor pairing, hence an integer polynomial. -/
def cantorScaledPair (x y : ℕ) : ℕ := (x + y) * (x + y + 1) + 2 * y

theorem cantorScaledPair_lt_of_sum_lt {x y x' y' : ℕ} (h : x + y < x' + y') :
    cantorScaledPair x y < cantorScaledPair x' y' := by
  unfold cantorScaledPair
  have h1 : (x + y + 1) * (x + y + 2) ≤ (x' + y') * (x' + y' + 1) :=
    Nat.mul_le_mul h (by omega)
  nlinarith

theorem cantorScaledPair_injective :
    Function.Injective (fun p : ℕ × ℕ => cantorScaledPair p.1 p.2) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only at h
  rcases Nat.lt_trichotomy (x + y) (x' + y') with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (cantorScaledPair_lt_of_sum_lt hlt))
  · unfold cantorScaledPair at h
    rw [heq] at h
    have hy : y = y' := by have := Nat.add_left_cancel h; omega
    subst hy
    have hx : x = x' := by omega
    subst hx; rfl
  · exact absurd h (Nat.ne_of_gt (cantorScaledPair_lt_of_sum_lt hgt))

/-- The ternary injection `ℕ^3 → ℕ`. -/
def ternaryPair (a : Fin 3 → ℕ) : ℕ := cantorScaledPair (cantorScaledPair (a 0) (a 1)) (a 2)

theorem ternaryPair_injective : Function.Injective ternaryPair := by
  intro a a' h
  unfold ternaryPair at h
  have h1 := cantorScaledPair_injective (a₁ := (cantorScaledPair (a 0) (a 1), a 2))
    (a₂ := (cantorScaledPair (a' 0) (a' 1), a' 2)) h
  simp only [Prod.mk.injEq] at h1
  have h2 := cantorScaledPair_injective (a₁ := (a 0, a 1)) (a₂ := (a' 0, a' 1)) h1.1
  simp only [Prod.mk.injEq] at h2
  ext i
  fin_cases i
  · exact h2.1
  · exact h2.2
  · exact h1.2

/-! ### The quadratic system defining the ternary graph -/

/-- `π(X_u, X_v)` as a polynomial. -/
noncomputable def pairPolyX {σ : Type} (u v : σ) : MvPolynomial σ ℤ :=
  (X u + X v) * (X u + X v + 1) + (X v + X v)

theorem pairPolyX_totalDegree {σ : Type} (u v : σ) : (pairPolyX u v).totalDegree ≤ 2 := by
  unfold pairPolyX
  have hX : ∀ w : σ, (X w : MvPolynomial σ ℤ).totalDegree ≤ 1 := fun w => by rw [totalDegree_X]
  have hs : (X u + X v : MvPolynomial σ ℤ).totalDegree ≤ 1 :=
    le_trans (totalDegree_add _ _) (max_le (hX u) (hX v))
  have hs1 : (X u + X v + 1 : MvPolynomial σ ℤ).totalDegree ≤ 1 :=
    le_trans (totalDegree_add _ _) (max_le hs (by rw [totalDegree_one]; omega))
  refine le_trans (totalDegree_add _ _) (max_le ?_ ?_)
  · exact le_trans (totalDegree_mul _ _) (by omega)
  · exact le_trans (totalDegree_add _ _) (max_le (by have := hX v; omega) (by have := hX v; omega))

theorem eval_pairPolyX {σ : Type} (f : σ → ℤ) (u v : σ) :
    eval f (pairPolyX u v) = (f u + f v) * (f u + f v + 1) + (f v + f v) := by
  simp [pairPolyX]

theorem cast_cantorScaledPair (x y : ℕ) :
    ((cantorScaledPair x y : ℕ) : ℤ) = ((x : ℤ) + y) * ((x : ℤ) + y + 1) + ((y : ℤ) + y) := by
  unfold cantorScaledPair; push_cast; ring

/-- Variables `Fin 4 ⊕ Fin 1`: inputs `a₀ a₁ a₂`, output `c = inl 3`, witness `z = inr 0`. -/
noncomputable def ternaryPairSystem : PolySystem 4 1 2 :=
  ![X (Sum.inr 0) - pairPolyX (Sum.inl 0) (Sum.inl 1),
    X (Sum.inl 3) - pairPolyX (Sum.inr 0) (Sum.inl 2)]

theorem ternaryPairSystem_totalDegree : ∀ i, (ternaryPairSystem i).totalDegree ≤ 2 := by
  intro i
  fin_cases i <;>
  · simp only [ternaryPairSystem]
    refine le_trans (totalDegree_sub _ _) (max_le ?_ (pairPolyX_totalDegree _ _))
    rw [totalDegree_X]; omega

theorem ternaryPairSystem_representsZ : SystemRepresentsZ ternaryPairSystem (graph ternaryPair) := by
  intro v
  have hev0 : ∀ y : Fin 1 → ℤ, evalAt (ternaryPairSystem 0) v y
      = y 0 - (((v 0 : ℤ) + v 1) * ((v 0 : ℤ) + v 1 + 1) + ((v 1 : ℤ) + v 1)) := by
    intro y
    simp [evalAt, ternaryPairSystem, eval_pairPolyX]
  have hev1 : ∀ y : Fin 1 → ℤ, evalAt (ternaryPairSystem 1) v y
      = (v 3 : ℤ) - ((y 0 + v 2) * (y 0 + v 2 + 1) + ((v 2 : ℤ) + v 2)) := by
    intro y
    simp [evalAt, ternaryPairSystem, eval_pairPolyX]
  have hgraph : v ∈ graph ternaryPair ↔ v 3 = ternaryPair (Fin.init v) := Iff.rfl
  have hinit : ternaryPair (Fin.init v) = cantorScaledPair (cantorScaledPair (v 0) (v 1)) (v 2) := rfl
  rw [hgraph, hinit]
  constructor
  · intro hv
    refine ⟨fun _ => ((cantorScaledPair (v 0) (v 1) : ℕ) : ℤ), Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · rw [hev0, cast_cantorScaledPair]; ring
    · rw [hev1, hv, cast_cantorScaledPair, cast_cantorScaledPair]; ring
  · rintro ⟨y, hy⟩
    have h0 := hy 0
    have h1 := hy 1
    rw [hev0, sub_eq_zero] at h0
    rw [hev1, sub_eq_zero, h0] at h1
    have hcast : ((cantorScaledPair (cantorScaledPair (v 0) (v 1)) (v 2) : ℕ) : ℤ)
        = (((v 0 : ℤ) + v 1) * ((v 0 : ℤ) + v 1 + 1) + ((v 1 : ℤ) + v 1) + v 2)
          * (((v 0 : ℤ) + v 1) * ((v 0 : ℤ) + v 1 + 1) + ((v 1 : ℤ) + v 1) + v 2 + 1)
          + ((v 2 : ℤ) + v 2) := by
      rw [cast_cantorScaledPair, cast_cantorScaledPair]
    exact_mod_cast h1.trans hcast.symm

theorem ternaryPair_withinPPZ : WithinPPZ 2 (graph ternaryPair) :=
  ⟨1, 2, ternaryPairSystem, ternaryPairSystem_totalDegree, ternaryPairSystem_representsZ⟩

/-- Arity 3 is coded in PPQuad (with one witness). -/
theorem ppQuadratic_graph_three : PPQuadraticGraphZ 3 :=
  ⟨ternaryPair, ternaryPair_injective, ternaryPair_withinPPZ⟩

/-! ### PPQuad codes every arity: the gate system of the r18 chain (β = 1) -/

/-- The gate equations `X(out_i) − gate_i(prev_i, block_i)` of the chain, as a system. -/
noncomputable def gateSystem (r β : ℕ) : PolySystem (leafCount r β + 1) r (r + 1) :=
  fun i => X (outVar r β i) - gatePoly r β i

theorem gateSystem_totalDegree (r β : ℕ) : ∀ i, (gateSystem r β i).totalDegree ≤ β + 1 := by
  intro i
  unfold gateSystem
  refine le_trans (totalDegree_sub _ _) (max_le ?_ (gatePoly_totalDegree r β i))
  rw [totalDegree_X]; omega

theorem gateSystem_representsZ (r β : ℕ) :
    SystemRepresentsZ (gateSystem r β) (graph (chainCode r β)) := by
  intro v
  have hev : ∀ (y : Fin r → ℤ) (i : Fin (r + 1)), evalAt (gateSystem r β i) v y
      = val r β v y (outVar r β i) - eval (val r β v y) (gatePoly r β i) := by
    intro y i
    unfold evalAt gateSystem
    rw [map_sub, eval_X]
    rfl
  constructor
  · intro hv
    have hv' : v (Fin.last _) = chainCode r β (Fin.init v) := hv
    refine ⟨fun i => ((chainN β (seed r β v) (blocks r β v) i : ℕ) : ℤ), fun i => ?_⟩
    rw [hev, sub_eq_zero]
    exact ((chain_sol_iff r β v _).mpr ⟨fun i => rfl, by rw [hv', chainCode_init]⟩) i
  · rintro ⟨y, hy⟩
    have h : ∀ i, val r β v y (outVar r β i) = eval (val r β v y) (gatePoly r β i) := fun i => by
      have := hy i
      rw [hev, sub_eq_zero] at this
      exact this
    rw [chain_sol_iff] at h
    show v (Fin.last _) = chainCode r β (Fin.init v)
    rw [chainCode_init]
    exact_mod_cast h.2

/-- Atom_2 ⊆ PPQuad on injective graphs (a single equation is a one-element system). -/
theorem atom_two_implies_pp_quadratic {n : ℕ} (h : AtomGraphZ 2 n) : PPQuadraticGraphZ n := by
  obtain ⟨r, e, he, hw⟩ := h
  exact ⟨e, he, withinPPZ_of_withinZ hw⟩

/-- PPQuad codes every arity: `n ≤ 1` from degree 1, `n ≥ 2` from the gate system with `n − 2`
    witnesses. -/
theorem ppQuadratic_graph_all_arity : ∀ n, PPQuadraticGraphZ n := by
  intro n
  rcases Nat.lt_or_ge n 2 with hn | hn
  · exact atom_two_implies_pp_quadratic
      (atomGraph_mono_degree (by norm_num) (atomGraph_degree_one_iff.mpr (by omega)))
  · have h : PPGraphZ 2 (leafCount (n - 2) 1) :=
      ⟨chainCode (n - 2) 1, chainCode_injective (n - 2) 1, n - 2, (n - 2) + 1, gateSystem (n - 2) 1,
        gateSystem_totalDegree (n - 2) 1, gateSystem_representsZ (n - 2) 1⟩
    have hl : leafCount (n - 2) 1 = n := by unfold leafCount; omega
    rw [hl] at h
    exact h

/-! ### PP_d ⊆ Atom_{2d}: sum of squares -/

theorem evalAt_sum_sq {n r m : ℕ} (S : PolySystem n r m) (a : Fin n → ℕ) (y : Fin r → ℤ) :
    evalAt (∑ i, (S i) ^ 2) a y = ∑ i, (evalAt (S i) a y) ^ 2 := by
  unfold evalAt
  simp only [map_sum, map_pow]

theorem withinZ_of_withinPPZ {n : ℕ} {d : ℕ} {A : Set (Fin n → ℕ)} (h : WithinPPZ d A) :
    ∃ r, WithinZ r (2 * d) A := by
  obtain ⟨r, m, S, hdeg, hrep⟩ := h
  refine ⟨r, r, le_rfl, ∑ i, (S i) ^ 2, ?_, fun a => ?_⟩
  · refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun i _ => ?_)
    exact le_trans (totalDegree_pow _ _) (Nat.mul_le_mul_left 2 (hdeg i))
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

/-- PPQuad ⊆ Atom_4 on injective graphs. -/
theorem pp_quadratic_implies_single_quartic {n : ℕ} (h : PPQuadraticGraphZ n) : AtomGraphZ 4 n := by
  obtain ⟨e, he, hpp⟩ := h
  obtain ⟨r, hr⟩ := withinZ_of_withinPPZ hpp
  exact ⟨r, e, he, hr⟩

/-- Theorem B: Atom_2 ⊊ PPQuad on injective graphs, strict already at arity 3. -/
theorem single_quadratic_strict_pp_quadratic :
    (∀ n, AtomGraphZ 2 n → PPQuadraticGraphZ n) ∧ PPQuadraticGraphZ 3 ∧ ¬ AtomGraphZ 2 3 :=
  ⟨fun _ h => atom_two_implies_pp_quadratic h, ppQuadratic_graph_three, codingDegree_three_exact.2⟩

end DiophCompression

#print axioms DiophCompression.cantorScaledPair_injective
#print axioms DiophCompression.ternaryPair_injective
#print axioms DiophCompression.ternaryPair_withinPPZ
#print axioms DiophCompression.ppQuadratic_graph_three
#print axioms DiophCompression.ppQuadratic_graph_all_arity
#print axioms DiophCompression.atom_two_implies_pp_quadratic
#print axioms DiophCompression.withinZ_of_withinPPZ
#print axioms DiophCompression.pp_quadratic_implies_single_quartic
#print axioms DiophCompression.single_quadratic_strict_pp_quadratic
