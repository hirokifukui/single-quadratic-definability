/-
  DiophCompression/SpectrumTransfer.lean — r06 必須E (session 6, 2026-08-27, claude.ai direct, no CC).
  Statements frozen first: frozen statement file `SpectrumTransfer_STATEMENTS.lean` (md5 be512cbf).
  The ℕ-unknown and ℤ-unknown spectra are equivalent up to explicit distortion:
    WithinZ(r,d) ⇒ WithinN(2r,d)      (z ↦ u − v: `splitUnknowns`, linear substitution, degree preserved)
    WithinN(r,d) ⇒ WithinZ(4r,2d)     (y ↦ x²+y²+z²+w²: `quadUnknowns`, degree ×2, `Nat.sum_four_squares`)
  and hence for G and U, and for the capacities (G via `graphCapacity*_spec`, d ≥ 1; U for all d).
  Generic tool: `totalDegree_aeval_le_mul` — substituting polynomials of degree ≤ k multiplies the total
  degree by at most k (the k = 1 case is `totalDegree_aeval_le_of_le_one`, ArityMonotonicity.lean).
-/
import DiophCompression.CapacityFunctions
import DiophCompression.NatGuardZ

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Degree of a substitution -/

/-- Substituting polynomials of total degree ≤ k multiplies the total degree by at most k. -/
theorem totalDegree_aeval_le_mul {σ τ : Type} (g : σ → MvPolynomial τ ℤ)
    (p : MvPolynomial σ ℤ) (k : ℕ) (hg : ∀ v, (g v).totalDegree ≤ k) :
    (aeval g p).totalDegree ≤ k * p.totalDegree := by
  rw [aeval_def, eval₂_eq]
  apply totalDegree_finsetSum_le
  intro β hβ
  rw [algebraMap_eq]
  calc (C (coeff β p) * ∏ v ∈ β.support, (g v) ^ (β v)).totalDegree
      ≤ (C (coeff β p)).totalDegree + (∏ v ∈ β.support, (g v) ^ (β v)).totalDegree :=
        totalDegree_mul _ _
    _ = (∏ v ∈ β.support, (g v) ^ (β v)).totalDegree := by rw [totalDegree_C]; ring
    _ ≤ ∑ v ∈ β.support, ((g v) ^ (β v)).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ v ∈ β.support, (β v) * k := by
        apply Finset.sum_le_sum
        intro v _
        calc ((g v) ^ (β v)).totalDegree ≤ (β v) * (g v).totalDegree := totalDegree_pow _ _
          _ ≤ (β v) * k := by apply Nat.mul_le_mul_left; exact hg v
    _ = k * ∑ v ∈ β.support, β v := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
    _ ≤ k * p.totalDegree := Nat.mul_le_mul_left k (le_totalDegree hβ)

/-! ### ℤ → ℕ: z ↦ u − v (degree preserved) -/

theorem splitSub_totalDegree_le_one (n r : ℕ) (v : Fin n ⊕ Fin r) : (splitSub n r v).totalDegree ≤ 1 := by
  cases v with
  | inl i => simp [splitSub, totalDegree_X]
  | inr j =>
    simp only [splitSub]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_) <;> rw [totalDegree_X]

theorem splitUnknowns_totalDegree_le {n r : ℕ} (P : Poly n r) :
    (splitUnknowns P).totalDegree ≤ P.totalDegree :=
  totalDegree_aeval_le_of_le_one _ P (splitSub_totalDegree_le_one n r)

theorem withinZ_to_withinN {n : ℕ} {r d : ℕ} {A : Set (Fin n → ℕ)} (h : WithinZ r d A) :
    WithinN (2 * r) d A := by
  obtain ⟨r', hr', P, hP, hrep⟩ := h
  exact ⟨r' + r', by omega, splitUnknowns P, (splitUnknowns_totalDegree_le P).trans hP,
    representsN_splitUnknowns P A hrep⟩

/-! ### ℕ → ℤ: y ↦ x² + y² + z² + w² (degree ×2) -/

/-- Variable map: parameters kept, unknown `j` ↦ Σ_{k<4} X(j,k)², indices via `finProdFinEquiv`. -/
noncomputable def quadSub (n r : ℕ) : (Fin n ⊕ Fin r) → MvPolynomial (Fin n ⊕ Fin (r * 4)) ℤ
  | Sum.inl i => X (Sum.inl i)
  | Sum.inr j => ∑ k : Fin 4, (X (Sum.inr (finProdFinEquiv (j, k)))) ^ 2

theorem quadSub_totalDegree_le_two (n r : ℕ) (v : Fin n ⊕ Fin r) : (quadSub n r v).totalDegree ≤ 2 := by
  cases v with
  | inl i => simp [quadSub, totalDegree_X]
  | inr j =>
    simp only [quadSub]
    apply totalDegree_finsetSum_le
    intro k _
    rw [totalDegree_X_pow]

noncomputable def quadUnknowns {n r : ℕ} (P : Poly n r) : Poly n (r * 4) := aeval (quadSub n r) P

theorem quadUnknowns_totalDegree_le {n r : ℕ} (P : Poly n r) :
    (quadUnknowns P).totalDegree ≤ 2 * P.totalDegree :=
  totalDegree_aeval_le_mul _ P 2 (quadSub_totalDegree_le_two n r)

theorem evalAt_quadUnknowns {n r : ℕ} (P : Poly n r) (a : Fin n → ℕ) (z : Fin (r * 4) → ℤ) :
    evalAt (quadUnknowns P) a z
      = evalAt P a (fun j => ∑ k : Fin 4, (z (finProdFinEquiv (j, k))) ^ 2) := by
  unfold evalAt quadUnknowns
  rw [map_aeval]
  have hcomp : (eval (Sum.elim (fun i => (a i : ℤ)) z)).comp
      (algebraMap ℤ (MvPolynomial (Fin n ⊕ Fin (r * 4)) ℤ)) = RingHom.id ℤ := by
    rw [algebraMap_eq]
    ext x
    simp
  rw [hcomp]
  have : (eval₂Hom (RingHom.id ℤ) (fun v => (eval (Sum.elim (fun i => (a i : ℤ)) z)) (quadSub n r v))) P
      = eval (fun v => (eval (Sum.elim (fun i => (a i : ℤ)) z)) (quadSub n r v)) P := rfl
  rw [this]
  apply congrArg (fun ρ => eval ρ P)
  funext v
  cases v with
  | inl i => simp [quadSub]
  | inr j => simp [quadSub]

theorem representsZ_quadUnknowns {n r : ℕ} (P : Poly n r) (S : Set (Fin n → ℕ))
    (h : RepresentsN P S) : RepresentsZ (quadUnknowns P) S := by
  intro a
  rw [h a]
  constructor
  · rintro ⟨y, hy⟩
    choose x1 x2 x3 x4 hx using fun j => natGuard4_surjective (y j)
    let z : Fin (r * 4) → ℤ := fun idx =>
      ![x1 (finProdFinEquiv.symm idx).1, x2 (finProdFinEquiv.symm idx).1,
        x3 (finProdFinEquiv.symm idx).1, x4 (finProdFinEquiv.symm idx).1] (finProdFinEquiv.symm idx).2
    have hz : ∀ j k, z (finProdFinEquiv (j, k)) = ![x1 j, x2 j, x3 j, x4 j] k := by
      intro j k; simp only [z, Equiv.symm_apply_apply]
    refine ⟨z, ?_⟩
    rw [evalAt_quadUnknowns]
    convert hy using 2
    funext j
    simp only [hz, Fin.sum_univ_four]
    have := hx j
    unfold natGuard4 at this
    simpa using this
  · rintro ⟨z, hz⟩
    rw [evalAt_quadUnknowns] at hz
    refine ⟨fun j => (∑ k : Fin 4, (z (finProdFinEquiv (j, k))) ^ 2).toNat, ?_⟩
    convert hz using 2
    funext j
    exact Int.toNat_of_nonneg (by positivity)

theorem withinN_to_withinZ_fourSquares {n : ℕ} {r d : ℕ} {A : Set (Fin n → ℕ)} (h : WithinN r d A) :
    WithinZ (4 * r) (2 * d) A := by
  obtain ⟨r', hr', P, hP, hrep⟩ := h
  exact ⟨r' * 4, by omega, quadUnknowns P,
    (quadUnknowns_totalDegree_le P).trans (Nat.mul_le_mul_left 2 hP),
    representsZ_quadUnknowns P A hrep⟩

/-! ### Transport to graph and universality achievability -/

theorem graphZ_to_graphN {n r d : ℕ} (h : GraphAchievableZ n r d) : GraphAchievableN n (2 * r) d := by
  obtain ⟨e, he, hw⟩ := h; exact ⟨e, he, withinZ_to_withinN hw⟩

theorem graphN_to_graphZ {n r d : ℕ} (h : GraphAchievableN n r d) : GraphAchievableZ n (4 * r) (2 * d) := by
  obtain ⟨e, he, hw⟩ := h; exact ⟨e, he, withinN_to_withinZ_fourSquares hw⟩

theorem universalZ_to_universalN {n r d : ℕ} (h : UniversalAchievableZ n r d) :
    UniversalAchievableN n (2 * r) d :=
  fun A hA => withinZ_to_withinN (h A hA)

theorem universalN_to_universalZ {n r d : ℕ} (h : UniversalAchievableN n r d) :
    UniversalAchievableZ n (4 * r) (2 * d) :=
  fun A hA => withinN_to_withinZ_fourSquares (h A hA)

/-! ### Capacity inequalities -/

theorem graphCapacityZ_le_graphCapacityN (r d : ℕ) (hd : 1 ≤ d) :
    graphCapacityZ r d ≤ graphCapacityN (2 * r) d :=
  (graphCapacityN_spec _ _ hd _).mp (graphZ_to_graphN ((graphCapacityZ_spec r d hd _).mpr le_rfl))

theorem graphCapacityN_le_graphCapacityZ (r d : ℕ) (hd : 1 ≤ d) :
    graphCapacityN r d ≤ graphCapacityZ (4 * r) (2 * d) :=
  (graphCapacityZ_spec _ _ (by omega) _).mp (graphN_to_graphZ ((graphCapacityN_spec r d hd _).mpr le_rfl))

theorem universalCapacityZ_le_universalCapacityN (r d : ℕ) :
    universalCapacityZ r d ≤ universalCapacityN (2 * r) d :=
  (universalCapacityN_spec _ _ _).mp (universalZ_to_universalN ((universalCapacityZ_spec r d _).mpr le_rfl))

theorem universalCapacityN_le_universalCapacityZ (r d : ℕ) :
    universalCapacityN r d ≤ universalCapacityZ (4 * r) (2 * d) :=
  (universalCapacityZ_spec _ _ _).mp (universalN_to_universalZ ((universalCapacityN_spec r d _).mpr le_rfl))

end DiophCompression

#print axioms DiophCompression.totalDegree_aeval_le_mul
#print axioms DiophCompression.withinZ_to_withinN
#print axioms DiophCompression.withinN_to_withinZ_fourSquares
#print axioms DiophCompression.graphZ_to_graphN
#print axioms DiophCompression.graphN_to_graphZ
#print axioms DiophCompression.universalZ_to_universalN
#print axioms DiophCompression.universalN_to_universalZ
#print axioms DiophCompression.graphCapacityZ_le_graphCapacityN
#print axioms DiophCompression.graphCapacityN_le_graphCapacityZ
#print axioms DiophCompression.universalCapacityZ_le_universalCapacityN
#print axioms DiophCompression.universalCapacityN_le_universalCapacityZ
