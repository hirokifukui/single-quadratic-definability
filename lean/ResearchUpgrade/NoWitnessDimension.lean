/-
  NoWitnessDimension.lean — s48.  Gate22 task **G22-T17** (the no-witness theorem into dimension).

  The reviewer asks for the `r = 0`, `m = 1` corner of II-D to be closed FIRST, for arbitrary `n`,
  by connecting the existing `nInputNoWitness_full` to the actual defining function and then
  applying the collision lemma.  Three joints are needed and are supplied here:

   * a COEFFICIENT COMPILER from `QuadraticGraphData n 1 0` to the `Pn` shape
     (`eval_eq_Pn`), so the two vocabularies are the same object and not merely analogous;
   * the identification `fn … = scalarOut f` (`fn` is `Classical.choose`, so this needs
     uniqueness, not just totality);
   * the scalar → `Fin 1` vector normal-form bridge, in the direction the collision lemma wants.

  Result: `dim_le_one_of_noWitness` — an SE₂ graph with ONE output and NO witnesses defines an
  injective function only when `n ≤ 1`.  Unconditional, std-3, no branch hypothesis on the
  quadratic form: this corner does not go through the four-way split at all.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.DimensionFromCoset
import ResearchUpgrade.ExistenceDirection
import ResearchUpgrade.GraphVocabulary
import ResearchUpgrade.NInputNoWitness

namespace DiophCompression.ResearchUpgrade

open Matrix

/-- Scalar → vector normal form at `m = 1`, the direction the collision lemma consumes
(`weakScalarCosetNF_of_weakVector` is the other one). -/
theorem weakVectorCosetNF_of_scalar {n : ℕ} {f : (Fin n → ℤ) → (Fin 1 → ℤ)}
    (h : WeakScalarCosetNF (scalarOut f)) : WeakVectorCosetNF f := by
  obtain ⟨M, ρ, q, hM, hq⟩ := h
  refine ⟨M, ρ, fun _ => q, hM, fun t j => ?_⟩
  have hj : j = 0 := Subsingleton.elim j 0
  subst hj
  exact hq t

namespace QuadraticGraphData

variable {n : ℕ} (D : QuadraticGraphData n 1 0)

/-! ### The coefficient compiler -/

/-- Coefficient of `y²`. -/
def coefA : ℤ := D.P.Q (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inl 0))
/-- Coefficient vector of `xᵢ y`. -/
def coefBeta : Fin n → ℤ := fun i =>
  D.P.Q (Sum.inl i) (Sum.inr (Sum.inl 0)) + D.P.Q (Sum.inr (Sum.inl 0)) (Sum.inl i)
/-- Coefficient of `y`. -/
def coefD : ℤ := D.P.l (Sum.inr (Sum.inl 0))
/-- The input-only quadratic matrix. -/
def coefE : Matrix (Fin n) (Fin n) ℤ := fun i j => D.P.Q (Sum.inl i) (Sum.inl j)
/-- The input-only linear vector. -/
def coefPhi : Fin n → ℤ := fun i => D.P.l (Sum.inl i)
/-- The constant. -/
def coefG : ℤ := D.P.c

/-- **The compiler.**  An `(n, 1, 0)` graph IS a `Pn`, on the nose. -/
theorem eval_eq_Pn (x : Fin n → ℤ) (y : ℤ) (u : Fin 0 → ℤ) :
    D.P.eval (pt x (fun _ => y) u)
      = Pn D.coefA D.coefBeta D.coefD D.coefE D.coefPhi D.coefG x y := by
  rw [D.eval_split x (fun _ => y) u]
  simp only [zQuad, zLin, aPart, Pn, coefA, coefBeta, coefD, coefE, coefPhi, coefG,
    dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_one,
    Finset.univ_eq_empty, Finset.sum_empty, Sum.elim_inl, Sum.elim_inr, add_zero]
  have h1 : ∑ i, x i * (D.P.Q (Sum.inl i) (Sum.inr (Sum.inl 0))
        + D.P.Q (Sum.inr (Sum.inl 0)) (Sum.inl i))
      = ∑ i, (D.P.Q (Sum.inl i) (Sum.inr (Sum.inl 0))
        + D.P.Q (Sum.inr (Sum.inl 0)) (Sum.inl i)) * x i :=
    Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, ∑ j, x i * (D.P.Q (Sum.inl i) (Sum.inl j) * x j)
      = ∑ i, x i * ∑ j, D.P.Q (Sum.inl i) (Sum.inl j) * x j :=
    Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  rw [h1, h2]
  ring

/-! ### Totality and uniqueness from `Defines` -/

theorem rn_of_sol {f : (Fin n → ℤ) → (Fin 1 → ℤ)} (hf : D.Defines f) (x : Fin n → ℤ) :
    Rn D.coefA D.coefBeta D.coefD D.coefE D.coefPhi D.coefG x (f x 0) := by
  obtain ⟨u, hu⟩ : D.Graph x (f x) := (hf x (f x)).mpr rfl
  have hfx : (fun _ => f x 0) = f x := by funext j; have : j = 0 := Subsingleton.elim j 0; simp [this]
  unfold Rn
  rw [← D.eval_eq_Pn x (f x 0) u, hfx]
  exact hu

theorem relTotal_of_defines {f : (Fin n → ℤ) → (Fin 1 → ℤ)} (hf : D.Defines f) :
    RelTotal (Rn D.coefA D.coefBeta D.coefD D.coefE D.coefPhi D.coefG) :=
  fun x => ⟨f x 0, D.rn_of_sol hf x⟩

theorem graph_of_rn {x : Fin n → ℤ} {y : ℤ}
    (hy : Rn D.coefA D.coefBeta D.coefD D.coefE D.coefPhi D.coefG x y) :
    D.Graph x (fun _ => y) := by
  refine ⟨fun i => i.elim0, ?_⟩
  unfold QuadraticGraphData.Sol
  rw [D.eval_eq_Pn x y (fun i => i.elim0)]
  exact hy

theorem relUnique_of_defines {f : (Fin n → ℤ) → (Fin 1 → ℤ)} (hf : D.Defines f) :
    RelUnique (Rn D.coefA D.coefBeta D.coefD D.coefE D.coefPhi D.coefG) := by
  intro x y y' hy hy'
  have h1 := (hf x _).mp (D.graph_of_rn hy)
  have h2 := (hf x _).mp (D.graph_of_rn hy')
  have := h1.trans h2.symm
  exact congrFun this 0

/-- `fn` is extracted by `Classical.choose`, so identifying it with the defined function needs
uniqueness, not merely totality. -/
theorem fn_eq_scalarOut {f : (Fin n → ℤ) → (Fin 1 → ℤ)} (hf : D.Defines f) :
    fn D.coefA D.coefBeta D.coefD D.coefE D.coefPhi D.coefG (D.relTotal_of_defines hf)
      = scalarOut f := by
  funext x
  have hspec := Classical.choose_spec ((D.relTotal_of_defines hf) x)
  exact D.relUnique_of_defines hf x _ _ hspec (D.rn_of_sol hf x)

/-! ### G22-T17 — the `r = 0`, `m = 1` corner, all `n` -/

/-- Every `(n, 1, 0)` graph puts its defined function in the weak vector coset normal form. -/
theorem weakVectorCosetNF_of_defines {f : (Fin n → ℤ) → (Fin 1 → ℤ)} (hf : D.Defines f) :
    WeakVectorCosetNF f := by
  refine weakVectorCosetNF_of_scalar ?_
  rw [← D.fn_eq_scalarOut hf]
  exact nInputNoWitness_weak D.coefA D.coefBeta D.coefD D.coefE D.coefPhi D.coefG
    (D.relTotal_of_defines hf) (D.relUnique_of_defines hf)

/-- **G22-T17.**  One output, no witnesses: an SE₂ graph defines an injective function only when
`n ≤ 1`.  Arbitrary `n`, unconditional, and with NO hypothesis on the quadratic form — this corner
of II-D does not use the four-way branch split at all. -/
theorem dim_le_one_of_noWitness {f : (Fin n → ℤ) → (Fin 1 → ℤ)}
    (hf : D.Defines f) (hinj : Function.Injective f) : n ≤ 1 := by
  by_contra hcon
  have h1 : 1 < n := by omega
  exact not_injective_of_weakVectorCosetNF h1 f (D.weakVectorCosetNF_of_defines hf) hinj

/-! ### Controls -/

/-- POSITIVE control: the bound is attained.  `idGraph 1` is an `(1, 1, 0)` graph defining an
injective function, so `n ≤ 1` cannot be improved to `n ≤ 0`. -/
theorem dim_le_one_sharp :
    ∃ (D' : QuadraticGraphData 1 1 0) (f : (Fin 1 → ℤ) → (Fin 1 → ℤ)),
      D'.Defines f ∧ Function.Injective f :=
  ⟨idGraph 1, id, idGraph_defines 1, Function.injective_id⟩

end QuadraticGraphData

/-- NEGATIVE control (regression control 11): the normal form genuinely needs a COSET.  `⌈x/2⌉`
has the weak scalar coset form but is NOT a single global polynomial of degree ≤ 2, so
`weakVectorCosetNF_of_defines` may not be strengthened to `GlobalQuadratic` and the collision
lemma must be applied on a coset, not on all of `ℤⁿ`. -/
theorem coset_not_global_control :
    WeakScalarCosetNF ceilHalf1 ∧ ¬ GlobalQuadratic ceilHalf1 :=
  ⟨WeakScalarCosetNF.of_full ceilHalf1_full, ceilHalf1_not_global⟩

end DiophCompression.ResearchUpgrade
