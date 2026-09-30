/-
  LinearBranchDimension.lean — s48.  Gate22 tasks **G22-T16** (witness coefficients vanish in the
  linear fibre) and the `Q = 0` half of **G22-T19/T20** (witness removal into the no-witness
  theorem).

  In the `Q = 0` branch the equation is linear in `z`, every vector is radical, and G21-T19 already
  gives `m ≤ 1` together with `c₀ = ℓ_a(e_out) ≠ 0`.  What was missing is the step the reviewer's
  §7 describes: for each witness coordinate `k`, the vector

      e = c_k · e_out − c₀ · e_witness

  is killed by `ℓ_a`, so `ker ℓ ⊆ ker π` forces `π(e) = c_k = 0`.  **Every witness coefficient
  vanishes**, at every input.  The equation then no longer mentions the witnesses at all, so it IS
  a `Pn`, and G22-T17 applies: `n ≤ 1`.

  The witnesses are removed WITHOUT constructing a new `QuadraticGraphData` — the compiler goes
  straight to `Pn`, which is what both routes have to reach anyway.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.ExistenceDirection
import ResearchUpgrade.GraphVocabulary
import ResearchUpgrade.LinearFibre
import ResearchUpgrade.NInputNoWitness
import ResearchUpgrade.NoWitnessDimension
import ResearchUpgrade.RadicalBridge
import ResearchUpgrade.RadicalDrift

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadraticGraphData

variable {n r : ℕ} (D : QuadraticGraphData n 1 r)

/-! ### Coefficients (the same six as `coefA…`, at arbitrary witness arity) -/

def lbA : ℤ := D.P.Q (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inl 0))
def lbBeta : Fin n → ℤ := fun i =>
  D.P.Q (Sum.inl i) (Sum.inr (Sum.inl 0)) + D.P.Q (Sum.inr (Sum.inl 0)) (Sum.inl i)
def lbD : ℤ := D.P.l (Sum.inr (Sum.inl 0))
def lbE : Matrix (Fin n) (Fin n) ℤ := fun i j => D.P.Q (Sum.inl i) (Sum.inl j)
def lbPhi : Fin n → ℤ := fun i => D.P.l (Sum.inl i)
def lbG : ℤ := D.P.c

/-! ### G22-T16 — every witness coefficient vanishes -/

/-- The quadratic coefficient of the output vanishes in the linear branch. -/
theorem lbA_eq_zero (hpol : ∀ v w : OutWit 1 r → ℤ, D.zPolar v w = 0) : D.lbA = 0 := by
  have h := D.zQuad_of_radical (e := Pi.single (Sum.inl 0) (1 : ℤ)) (fun w => hpol _ w)
  simpa [zQuad, lbA, Fintype.sum_sum_type, Fin.sum_univ_one, Pi.single_apply] using h

/-- **G22-T16.**  With a vanishing quadratic part and output uniqueness, every witness
coefficient of `ℓ_a` is zero. -/
theorem witnessCoeff_eq_zero (hpol : ∀ v w : OutWit 1 r → ℤ, D.zPolar v w = 0)
    (hOU : D.OutputUnique) {x : Fin n → ℤ} {z₀ : OutWit 1 r → ℤ} (hz : D.SolZ x z₀)
    (k : Fin r) : D.zLin x (Sum.inr k) = 0 := by
  obtain ⟨hc0, -⟩ := D.m_le_one_of_linear hpol hOU hz (by norm_num : 0 < 1)
  set i0 : Fin 1 := ⟨0, by norm_num⟩ with hi0
  set c0 : ℤ := D.zLin x (Sum.inl i0) with hc0def
  set ck : ℤ := D.zLin x (Sum.inr k) with hckdef
  set e : OutWit 1 r → ℤ :=
    ck • Pi.single (Sum.inl i0) (1 : ℤ) + (-c0) • Pi.single (Sum.inr k) (1 : ℤ) with hedef
  have hlin : D.zLinEval x e = 0 := by
    rw [hedef, D.zLinEval_add, D.zLinEval_smul, D.zLinEval_smul,
      D.zLinEval_single, D.zLinEval_single]
    ring
  have hp := D.kerLin_subset_kerProj hpol hOU hz hlin
  have hval := congrFun hp i0
  simp only [outProj, hedef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    Pi.single_apply, reduceCtorEq, if_true, if_false, mul_one, mul_zero,
    add_zero] at hval
  exact hval

/-! ### The compiler in the linear branch -/

/-- With the witness coefficients gone and `Q = 0`, the value of the polynomial does not depend on
the witnesses at all, and the graph IS a `Pn`. -/
theorem eval_eq_Pn_of_linear (hpol : ∀ v w : OutWit 1 r → ℤ, D.zPolar v w = 0)
    {x : Fin n → ℤ} (hwit : ∀ k : Fin r, D.zLin x (Sum.inr k) = 0) (y : ℤ) (u : Fin r → ℤ) :
    D.P.eval (pt x (fun _ => y) u) = Pn D.lbA D.lbBeta D.lbD D.lbE D.lbPhi D.lbG x y := by
  have hQ0 : D.zQuad (Sum.elim (fun _ => y) u) = 0 :=
    D.zQuad_of_radical (fun w => hpol _ w)
  have hA := D.lbA_eq_zero hpol
  rw [D.eval_split x (fun _ => y) u, hQ0]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr,
    hwit, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  simp only [Pn, zLin, aPart, lbA, lbBeta, lbD, lbE, lbPhi, lbG,
    dotProduct, Matrix.mulVec] at hA ⊢
  rw [hA]
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

/-! ### G22-T19 / T20 (the `Q = 0` half) — dimension in the linear branch -/

theorem rn_of_sol_linear (hpol : ∀ v w : OutWit 1 r → ℤ, D.zPolar v w = 0)
    {f : (Fin n → ℤ) → (Fin 1 → ℤ)} (hf : D.Defines f) (x : Fin n → ℤ) :
    Rn D.lbA D.lbBeta D.lbD D.lbE D.lbPhi D.lbG x (f x 0) := by
  obtain ⟨u, hu⟩ : D.Graph x (f x) := (hf x (f x)).mpr rfl
  have hsol : D.SolZ x (Sum.elim (f x) u) := hu
  have hwit := D.witnessCoeff_eq_zero hpol (D.outputUnique_of_defines hf) hsol
  have hfx : (fun _ => f x 0) = f x := by
    funext j; have : j = 0 := Subsingleton.elim j 0; simp [this]
  unfold Rn
  rw [← D.eval_eq_Pn_of_linear hpol hwit (f x 0) u, hfx]
  exact hu

theorem graph_of_rn_linear (hpol : ∀ v w : OutWit 1 r → ℤ, D.zPolar v w = 0)
    {f : (Fin n → ℤ) → (Fin 1 → ℤ)} (hf : D.Defines f) {x : Fin n → ℤ} {y : ℤ}
    (hy : Rn D.lbA D.lbBeta D.lbD D.lbE D.lbPhi D.lbG x y) : D.Graph x (fun _ => y) := by
  obtain ⟨u, hu⟩ : D.Graph x (f x) := (hf x (f x)).mpr rfl
  have hsol : D.SolZ x (Sum.elim (f x) u) := hu
  have hwit := D.witnessCoeff_eq_zero hpol (D.outputUnique_of_defines hf) hsol
  refine ⟨u, ?_⟩
  unfold QuadraticGraphData.Sol
  rw [D.eval_eq_Pn_of_linear hpol hwit y u]
  exact hy

/-- **The `Q = 0` branch of II-D.**  A vanishing output/witness quadratic part forces `n ≤ 1` for
any injective function the graph defines — the witnesses are removed by G22-T16 and the rest is
G22-T17.  `m ≤ 1` is not an extra hypothesis: it is G21-T19's conclusion, which is why the
statement is written at `m = 1`. -/
theorem dim_le_one_of_linearBranch (hpol : ∀ v w : OutWit 1 r → ℤ, D.zPolar v w = 0)
    {f : (Fin n → ℤ) → (Fin 1 → ℤ)} (hf : D.Defines f) (hinj : Function.Injective f) :
    n ≤ 1 := by
  have hT : RelTotal (Rn D.lbA D.lbBeta D.lbD D.lbE D.lbPhi D.lbG) :=
    fun x => ⟨f x 0, D.rn_of_sol_linear hpol hf x⟩
  have hU : RelUnique (Rn D.lbA D.lbBeta D.lbD D.lbE D.lbPhi D.lbG) := by
    intro x y y' hy hy'
    have h1 := (hf x _).mp (D.graph_of_rn_linear hpol hf hy)
    have h2 := (hf x _).mp (D.graph_of_rn_linear hpol hf hy')
    exact congrFun (h1.trans h2.symm) 0
  have hfn : fn D.lbA D.lbBeta D.lbD D.lbE D.lbPhi D.lbG hT = scalarOut f := by
    funext x
    exact hU x _ _ (Classical.choose_spec (hT x)) (D.rn_of_sol_linear hpol hf x)
  have hNF : WeakVectorCosetNF f := by
    refine weakVectorCosetNF_of_scalar ?_
    rw [← hfn]
    exact nInputNoWitness_weak D.lbA D.lbBeta D.lbD D.lbE D.lbPhi D.lbG hT hU
  by_contra hcon
  have h1 : 1 < n := by omega
  exact not_injective_of_weakVectorCosetNF h1 f hNF hinj

/-! ### Controls -/

/-- POSITIVE control: the branch is inhabited and the bound is attained.  `idGraph 1` at `n = 1`
has `m = 1`, `r = 0` and defines an injective function; the linear branch therefore does not prove
`n ≤ 0`. -/
theorem linearBranch_sharp :
    ∃ (D' : QuadraticGraphData 1 1 0) (f : (Fin 1 → ℤ) → (Fin 1 → ℤ)),
      D'.Defines f ∧ Function.Injective f :=
  ⟨idGraph 1, id, idGraph_defines 1, Function.injective_id⟩

/-- NEGATIVE control: `hpol` is load-bearing.  If some vector is NOT radical then `Q ≠ 0`, the
branch hypothesis fails, and `witnessCoeff_eq_zero` is unavailable — the witness coefficients may
then be anything, which is exactly the situation `P = (b − a)²` (a free witness) exhibits. -/
theorem not_linear_of_zQuad_ne_zero {v : OutWit 1 r → ℤ} (hv : D.zQuad v ≠ 0) :
    ¬ (∀ v w : OutWit 1 r → ℤ, D.zPolar v w = 0) := by
  intro hpol
  exact hv (D.zQuad_of_radical (fun w => hpol v w))

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
