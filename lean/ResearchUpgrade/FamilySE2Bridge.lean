/-
  FamilySE2Bridge.lean — s52.  R41-D1: the four-square family compiles to an honest SE2 datum.

  Given a family F and an EXPLICIT witness that its residual is an integer quadratic
  (hR : forall a, F.R a = PR.eval a), `familyData` builds a real `QuadraticGraphData n m 4`
  whose evaluation is the left minus the right side of `Family.Sol`, whose graph coincides
  with the family's, and across which `Total`, `OutputUnique` and `Defines` transport.
  Degree <= 2 is structural: the object IS an `IntQuad`.

  The hypothesis is not optional.  `Family.R` is an ARBITRARY function, so no family is SE2
  unconditionally; `hR` is what buys the bridge.  The k = 3, R = 1 example is put through it.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.FourSquareSlack

namespace DiophCompression.ResearchUpgrade.FourSquareSlack
namespace Family

open Matrix DiophCompression.ResearchUpgrade

variable {n m : ℕ} (F : Family n m) (PR : IntQuad (Fin n))

/-- **R41-D1 — the SE₂ compiler for the four-square family.**  Given a witness that the residual
is an integer quadratic, build the actual `QuadraticGraphData n m 4`. -/
def familyData : QuadraticGraphData n m 4 where
  P :=
    { c := (∑ j, F.c j ^ 2) - PR.c
      l := fun v => match v with
        | Sum.inl i => 2 * (∑ j, F.c j * F.B j i) - PR.l i
        | Sum.inr (Sum.inl j) => -2 * F.k * F.c j
        | Sum.inr (Sum.inr _) => 0
      Q := fun p q => match p, q with
        | Sum.inl i, Sum.inl i' => (∑ j, F.B j i * F.B j i') - PR.Q i i'
        | Sum.inr (Sum.inl j), Sum.inr (Sum.inl j') => if j = j' then F.k ^ 2 else 0
        | Sum.inr (Sum.inl j), Sum.inl i => -2 * F.k * F.B j i
        | Sum.inr (Sum.inr i), Sum.inr (Sum.inr i') => if i = i' then 1 else 0
        | _, _ => 0 }

theorem familyData_zQuad (z : OutWit m 4 → ℤ) :
    (F.familyData PR).zQuad z
      = F.k ^ 2 * (∑ j, z (Sum.inl j) ^ 2) + ∑ i, z (Sum.inr i) ^ 2 := by
  simp only [QuadraticGraphData.zQuad, familyData, Fintype.sum_sum_type]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq, Finset.mul_sum, sq]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem familyData_zLin_out (a : Fin n → ℤ) (j : Fin m) :
    (F.familyData PR).zLin a (Sum.inl j) = -2 * F.k * F.lin a j := by
  simp only [QuadraticGraphData.zLin, familyData, Family.lin]
  rw [mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem familyData_zLin_wit (a : Fin n → ℤ) (i : Fin 4) :
    (F.familyData PR).zLin a (Sum.inr i) = 0 := by
  simp [QuadraticGraphData.zLin, familyData]

theorem familyData_aPart (a : Fin n → ℤ) :
    (F.familyData PR).aPart a = (∑ j, F.lin a j ^ 2) - PR.eval a := by
  have e1 : ∀ j : Fin m, F.lin a j ^ 2
      = F.c j ^ 2 + 2 * F.c j * (∑ i, F.B j i * a i)
        + (∑ i, F.B j i * a i) * (∑ i, F.B j i * a i) := by
    intro j; simp only [Family.lin]; ring
  have h2 : ∑ j, 2 * F.c j * (∑ i, F.B j i * a i)
      = ∑ i, (2 * ∑ j, F.c j * F.B j i) * a i := by
    have e : ∀ j : Fin m, 2 * F.c j * (∑ i, F.B j i * a i)
        = ∑ i, 2 * (F.c j * F.B j i) * a i := by
      intro j; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_mul, Finset.mul_sum]
  have h3 : ∑ j, (∑ i, F.B j i * a i) * (∑ i, F.B j i * a i)
      = ∑ i, ∑ i', a i * ((∑ j, F.B j i * F.B j i') * a i') := by
    have e : ∀ j : Fin m, (∑ i, F.B j i * a i) * (∑ i, F.B j i * a i)
        = ∑ i, ∑ i', (F.B j i * a i) * (F.B j i' * a i') := by
      intro j
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsq : (∑ j, F.lin a j ^ 2)
      = (∑ j, F.c j ^ 2) + (∑ i, (2 * ∑ j, F.c j * F.B j i) * a i)
        + ∑ i, ∑ i', a i * ((∑ j, F.B j i * F.B j i') * a i') := by
    rw [Finset.sum_congr rfl fun j _ => e1 j, Finset.sum_add_distrib, Finset.sum_add_distrib,
      h2, h3]
  rw [hsq]
  simp only [QuadraticGraphData.aPart, familyData, IntQuad.eval, dotProduct, Matrix.mulVec]
  have hl : ∑ i, (2 * (∑ j, F.c j * F.B j i) - PR.l i) * a i
      = (∑ i, (2 * ∑ j, F.c j * F.B j i) * a i) - ∑ i, PR.l i * a i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hq : ∑ i, ∑ i', a i * (((∑ j, F.B j i * F.B j i') - PR.Q i i') * a i')
      = (∑ i, ∑ i', a i * ((∑ j, F.B j i * F.B j i') * a i'))
        - ∑ i, a i * ∑ i', PR.Q i i' * a i' := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i' _ => by ring
  rw [hl, hq]
  ring


theorem familyData_eval (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin 4 → ℤ) :
    (F.familyData PR).P.eval (pt a b u)
      = ((∑ j, (F.k * b j - F.lin a j) ^ 2) + (∑ i, u i ^ 2)) - PR.eval a := by
  rw [QuadraticGraphData.eval_split, familyData_zQuad, familyData_aPart]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    F.familyData_zLin_out PR a, F.familyData_zLin_wit PR a, zero_mul, Finset.sum_const_zero,
    add_zero]
  have hexp : ∑ j, (F.k * b j - F.lin a j) ^ 2
      = F.k ^ 2 * (∑ j, b j ^ 2) + (∑ j, -2 * F.k * F.lin a j * b j) + ∑ j, F.lin a j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp]
  ring

/-- The residual is an integer quadratic: the hypothesis R41-D1 asks to be made explicit. -/
theorem familyData_sol_iff (hR : ∀ a, F.R a = PR.eval a)
    (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin 4 → ℤ) :
    (F.familyData PR).Sol a b u ↔ F.Sol a b u := by
  show (F.familyData PR).P.eval (pt a b u) = 0 ↔ _
  rw [F.familyData_eval PR a b u, sub_eq_zero, ← hR a]
  rfl

theorem familyData_graph_iff (hR : ∀ a, F.R a = PR.eval a)
    (a : Fin n → ℤ) (b : Fin m → ℤ) :
    (F.familyData PR).Graph a b ↔ F.Graph a b :=
  exists_congr fun u => F.familyData_sol_iff PR hR a b u

theorem familyData_total (hR : ∀ a, F.R a = PR.eval a) (hT : F.Total) :
    (F.familyData PR).Total := fun a => by
  obtain ⟨b, hb⟩ := hT a
  exact ⟨b, (F.familyData_graph_iff PR hR a b).mpr hb⟩

theorem familyData_outputUnique (hR : ∀ a, F.R a = PR.eval a) (hU : F.OutputUnique) :
    (F.familyData PR).OutputUnique := fun a b b' hb hb' =>
  hU a b b' ((F.familyData_graph_iff PR hR a b).mp hb)
    ((F.familyData_graph_iff PR hR a b').mp hb')

theorem familyData_defines (hR : ∀ a, F.R a = PR.eval a)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : ∀ a b, F.Graph a b ↔ b = f a) :
    (F.familyData PR).Defines f := fun a b =>
  (F.familyData_graph_iff PR hR a b).trans (hf a b)

end Family

/-! ### The `k = 3`, `R = 1` example through the bridge (R41-D1's required control) -/

/-- The residual of `Ex` as an explicit integer quadratic: the constant `1`. -/
def ExResidual : IntQuad (Fin 1) := { c := 1, l := 0, Q := 0 }

theorem ExResidual_eval (a : Fin 1 → ℤ) : ExResidual.eval a = 1 := by
  simp [ExResidual, IntQuad.eval, dotProduct, Matrix.mulVec]

theorem Ex_hR : ∀ a, Ex.R a = ExResidual.eval a := fun a => by
  rw [ExResidual_eval]; rfl

/-- `Ex` compiles to an honest `QuadraticGraphData 1 1 4` with the same graph. -/
theorem Ex_bridge (a b : Fin 1 → ℤ) :
    (Ex.familyData ExResidual).Graph a b ↔ Ex.Graph a b :=
  Ex.familyData_graph_iff ExResidual Ex_hR a b

/-- …and therefore the compiled datum defines `a ↦ ⌊(a+1)/3⌋` on the nose. -/
theorem Ex_bridge_value (a b : Fin 1 → ℤ) :
    (Ex.familyData ExResidual).Graph a b ↔ b 0 = (a 0 + 1) / 3 :=
  (Ex_bridge a b).trans (Ex_value a b)

end DiophCompression.ResearchUpgrade.FourSquareSlack
