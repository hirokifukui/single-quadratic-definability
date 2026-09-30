/-
  DiophCompression/AtomicDegreeRank.lean — APAL Logic Pivot, Gate 1 (session 19, 2026-08-30, claude.ai direct).
  Theorem C (degree-filtered atomic existential rank blow-up). For a relation A ⊆ ℕ^{n+1} and a degree d,
    ρ^atom_d(A) = inf{ r : A is represented by ONE integer equation of total degree ≤ d with r ℤ-witnesses } ∈ ℕ ∪ {∞}.
  For the explicit ternary graph E_3 = graph(6·skolem_3):  ρ^atom_3(E_3) = 0  and  ρ^atom_2(E_3) = ∞.
  This is NOT the DDF existential rank (which counts quantifiers for arbitrary existential formulas over a field);
  it is a single-equation, degree-filtered rank over ℤ-witnesses with ℕ-parameters (ERRATA_r18 E10, E11).
  Statements frozen in frozen_statements/LogicPivot_STATEMENTS.lean (md5 4b647f55).
-/
import DiophCompression.AtomicCodingHierarchy

namespace DiophCompression

open MvPolynomial MPUP

/-- Single-equation, degree-filtered existential rank of `A ⊆ ℕ^{n+1}` (∞ if not single-equation
    definable at degree ≤ `d` with any number of ℤ-witnesses). -/
noncomputable def AtomicDegreeRankZ {n : ℕ} (A : Set (Fin (n + 1) → ℕ)) (d : ℕ) : WithTop ℕ :=
  ⨅ (r : ℕ) (_ : ∃ P : Poly (n + 1) r, P.totalDegree ≤ d ∧ RepresentsZ P A), (r : WithTop ℕ)

theorem atomicDegreeRankZ_eq_top_iff {n : ℕ} (A : Set (Fin (n + 1) → ℕ)) (d : ℕ) :
    AtomicDegreeRankZ A d = ⊤ ↔ ∀ r, ¬ ∃ P : Poly (n + 1) r, P.totalDegree ≤ d ∧ RepresentsZ P A := by
  unfold AtomicDegreeRankZ
  rw [iInf_eq_top]
  constructor
  · intro h r hr
    have := h r
    rw [iInf_pos hr] at this
    exact WithTop.coe_ne_top this
  · intro h r
    rw [iInf_neg (h r)]

theorem atomicDegreeRankZ_eq_zero_iff {n : ℕ} (A : Set (Fin (n + 1) → ℕ)) (d : ℕ) :
    AtomicDegreeRankZ A d = 0 ↔ ∃ P : Poly (n + 1) 0, P.totalDegree ≤ d ∧ RepresentsZ P A := by
  unfold AtomicDegreeRankZ
  constructor
  · intro h
    by_contra hno
    have h1 : (1 : WithTop ℕ) ≤ ⨅ (r : ℕ) (_ : ∃ P : Poly (n + 1) r, P.totalDegree ≤ d ∧ RepresentsZ P A),
        (r : WithTop ℕ) := by
      refine le_iInf₂ fun r hr => ?_
      have hr0 : r ≠ 0 := by rintro rfl; exact hno hr
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr0
    rw [h] at h1
    exact absurd h1 (by decide)
  · intro h
    apply le_antisymm
    · exact le_trans (iInf₂_le 0 h) (by simp)
    · exact bot_le

/-! ### The explicit ternary Skolem graph E_3 -/

/-- The integer cubic injection `ℕ^3 → ℕ`, `a ↦ 3!·skolem(a)` (the raw Skolem tupling has binomial
    denominators; the `e!` scaling is what makes it an integer polynomial, `eval_skolemPoly`). -/
def ternarySkolem (a : Fin 3 → ℕ) : ℕ := Nat.factorial 3 * skolem a

theorem ternarySkolem_injective : Function.Injective ternarySkolem := by
  intro a a' h
  exact skolem_injective (Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos 3) h)

/-- The cubic `c − skolemPoly_3(a)` with no witness (Poly 4 0). -/
noncomputable def ternarySkolemPoly : Poly 4 0 :=
  X (Sum.inl (Fin.last 3)) - rename (Sum.inl ∘ Fin.castSucc) (skolemPoly 3)

theorem ternarySkolemPoly_totalDegree : ternarySkolemPoly.totalDegree ≤ 3 := by
  unfold ternarySkolemPoly
  refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
  · rw [totalDegree_X]; norm_num
  · exact le_trans (totalDegree_rename_le _ _) (skolemPoly_totalDegree 3)

theorem evalAt_ternarySkolemPoly (v : Fin 4 → ℕ) (y : Fin 0 → ℤ) :
    evalAt ternarySkolemPoly v y = (v (Fin.last 3) : ℤ) - ((ternarySkolem (Fin.init v) : ℕ) : ℤ) := by
  unfold evalAt ternarySkolemPoly ternarySkolem
  rw [map_sub, eval_X, eval_rename]
  simp only [Sum.elim_inl]
  congr 1
  have : ((Sum.elim (fun i => ((v i : ℕ) : ℤ)) y) ∘ (Sum.inl ∘ Fin.castSucc) : Fin 3 → ℤ)
      = fun i => ((Fin.init v i : ℕ) : ℤ) := rfl
  rw [this, eval_skolemPoly]

theorem ternarySkolemPoly_representsZ : RepresentsZ ternarySkolemPoly (graph ternarySkolem) := by
  intro v
  constructor
  · intro hv
    have hv' : v (Fin.last 3) = ternarySkolem (Fin.init v) := hv
    exact ⟨Fin.elim0, by rw [evalAt_ternarySkolemPoly, hv']; ring⟩
  · rintro ⟨y, hy⟩
    rw [evalAt_ternarySkolemPoly] at hy
    show v (Fin.last 3) = ternarySkolem (Fin.init v)
    omega

/-- ρ^atom_3(E_3) = 0: the cubic itself defines the graph, no witness. -/
theorem ternarySkolem_atomicRank_three_zero : AtomicDegreeRankZ (graph ternarySkolem) 3 = 0 :=
  (atomicDegreeRankZ_eq_zero_iff _ _).mpr
    ⟨ternarySkolemPoly, ternarySkolemPoly_totalDegree, ternarySkolemPoly_representsZ⟩

/-- ρ^atom_2(E_3) = ∞: lowering the degree from 3 to 2 cannot be compensated by any number of
    ℤ-witnesses (Quadratic Witness Inertia). -/
theorem ternarySkolem_atomicRank_two_top : AtomicDegreeRankZ (graph ternarySkolem) 2 = ⊤ := by
  rw [atomicDegreeRankZ_eq_top_iff]
  rintro r ⟨P, hP, hrep⟩
  have h3 : GraphAchievableZ 3 r 2 := ⟨ternarySkolem, ternarySkolem_injective, r, le_rfl, P, hP, hrep⟩
  have := (SemanticQuadraticSingular.graphAchievableZ_degree_two_iff r 3).mp h3
  omega

end DiophCompression

#print axioms DiophCompression.atomicDegreeRankZ_eq_top_iff
#print axioms DiophCompression.atomicDegreeRankZ_eq_zero_iff
#print axioms DiophCompression.ternarySkolem_injective
#print axioms DiophCompression.ternarySkolem_atomicRank_three_zero
#print axioms DiophCompression.ternarySkolem_atomicRank_two_top
