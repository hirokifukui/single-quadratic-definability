/-
  FamilySealedBridge.lean — s53.  R41-D1 completed: the four-square family reaches the SEALED
  predicate `DiophCompression.SingleQuadraticDefinableFunctionZZ`, not only a `QuadraticGraphData`.

  * `QuadraticGraphData.singleQuadraticDefinable_of_defines`: the converse of FidelityBridge's
    `graphData_of_singleQuadraticDefinable` — any datum that defines f gives the sealed predicate
    (polynomial `rename split (toMv P)`, total degree ≤ 2).
  * `familyData_totalDegree_le_two`; `singleQuadraticDefinable_of_family` (under the explicit hR).
  * `Ex_singleQuadraticDefinable`: the k = 3, R = 1 example, a ↦ ⌊(a+1)/3⌋, in the sealed sense.

  No SE₂ property is attached to an arbitrary residual R: hR stays a hypothesis.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.FamilySE2Bridge
import ResearchUpgrade.FidelityBridge
import ResearchUpgrade.ReverseCompiler

namespace DiophCompression.ResearchUpgrade

/-- The sealed predicate from any `QuadraticGraphData` that defines `f` (converse of
`graphData_of_singleQuadraticDefinable`). -/
theorem QuadraticGraphData.singleQuadraticDefinable_of_defines {n m r : ℕ}
    (D : QuadraticGraphData n m r) {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    DiophCompression.SingleQuadraticDefinableFunctionZZ f := by
  classical
  let split : Vars n m r → Fin (n + m) ⊕ Fin r :=
    Sum.elim (fun i => Sum.inl (Fin.castAdd m i))
      (Sum.elim (fun j => Sum.inl (Fin.natAdd n j)) Sum.inr)
  refine ⟨r, MvPolynomial.rename split D.P.toMv,
    le_trans (MvPolynomial.totalDegree_rename_le _ _) D.P.totalDegree_toMv, ?_⟩
  intro v
  have hv : ∀ y : Fin r → ℤ,
      DiophCompression.evalAtZZ (MvPolynomial.rename split D.P.toMv) v y
        = D.P.eval (pt (fun i => v (Fin.castAdd m i)) (fun j => v (Fin.natAdd n j)) y) := by
    intro y
    unfold DiophCompression.evalAtZZ
    rw [MvPolynomial.eval_rename, D.P.eval_toMv]
    congr 1
    funext x
    rcases x with i | j | k <;> rfl
  show (fun j => v (Fin.natAdd n j)) = f (fun i => v (Fin.castAdd m i)) ↔ _
  rw [← hf]
  simp only [hv]
  rfl

namespace FourSquareSlack
namespace Family

variable {n m : ℕ} (F : Family n m) (PR : IntQuad (Fin n))

theorem familyData_totalDegree_le_two :
    ∃ P : MvPolynomial (Vars n m 4) ℤ, P.totalDegree ≤ 2 ∧
      ∀ x, MvPolynomial.eval x P = (F.familyData PR).P.eval x :=
  (intQuad_iff_totalDegree_le_two _).mp ⟨_, fun _ => rfl⟩

theorem singleQuadraticDefinable_of_family (hR : ∀ a, F.R a = PR.eval a)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : ∀ a b, F.Graph a b ↔ b = f a) :
    DiophCompression.SingleQuadraticDefinableFunctionZZ f :=
  (F.familyData PR).singleQuadraticDefinable_of_defines (F.familyData_defines PR hR hf)

end Family

/-- The `k = 3`, `R = 1` example is definable in the SEALED sense. -/
theorem Ex_singleQuadraticDefinable :
    DiophCompression.SingleQuadraticDefinableFunctionZZ
      (fun a : Fin 1 → ℤ => fun _ : Fin 1 => (a 0 + 1) / 3) := by
  refine Ex.singleQuadraticDefinable_of_family ExResidual Ex_hR fun a b => ?_
  refine (Ex_value a b).trans ⟨fun h => ?_, fun h => ?_⟩
  · funext i
    rw [Subsingleton.elim i 0]
    exact h
  · rw [h]

end FourSquareSlack
end DiophCompression.ResearchUpgrade
