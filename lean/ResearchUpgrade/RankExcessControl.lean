/-
  RankExcessControl.lean — s53.  The R41-C2 control `(b − a)² + (u₀ + u₁)² = 0`
  (n = m = 1, r = 2), as asked by the reviewer.

  * `exD_polarRank`: d = 2 (the radical is the line through (b,u₀,u₁) = (0,1,−1)), so the
    generic compiler's presentation carries d − m = 1 witness (`exD_compiled_witnessCount`,
    `exD_rankExcess`).
  * `UEx`: the explicit change u₀ = v + w, u₁ = −w (determinant −1) takes r = 2 to the
    one-witness presentation `(b − a)² + v² = 0` (`exD_graph_iff_oneWit`).
  * `noWitD`: `b − a = 0` defines the same graph with r = 0.
  * `sameGraph_three_witnessCounts`: one graph, presentations with 2, 1 and 0 witnesses —
    the compiled count is not a semantic minimum.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.RankExcessCompiler

namespace DiophCompression.ResearchUpgrade
namespace RankExcessControl

open QuadraticGraphData

/-- `s·x = b − a`. -/
def sEx : Vars 1 1 2 → ℤ := Sum.elim (fun _ => -1) (Sum.elim (fun _ => 1) (fun _ => 0))
/-- `t·x = u₀ + u₁`. -/
def tEx : Vars 1 1 2 → ℤ := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1))

/-- **The GPT control** `(b − a)² + (u₀ + u₁)² = 0`: `n = m = 1`, `r = 2`. -/
def exD : QuadraticGraphData 1 1 2 where
  P := { c := 0, l := 0, Q := fun i j => sEx i * sEx j + tEx i * tEx j }

theorem exD_eval (a : Fin 1 → ℤ) (b : Fin 1 → ℤ) (u : Fin 2 → ℤ) :
    exD.P.eval (pt a b u) = (b 0 - a 0) ^ 2 + (u 0 + u 1) ^ 2 := by
  simp [exD, IntQuad.eval, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two,
    sEx, tEx, pt]
  ring

theorem exD_graph_iff (a b : Fin 1 → ℤ) : exD.Graph a b ↔ b = a := by
  constructor
  · rintro ⟨u, hu⟩
    have h := hu
    unfold Sol at h
    rw [exD_eval] at h
    have h1 : b 0 - a 0 = 0 := by nlinarith [sq_nonneg (b 0 - a 0), sq_nonneg (u 0 + u 1)]
    funext i; rw [Subsingleton.elim i 0]; omega
  · rintro rfl
    exact ⟨0, by unfold Sol; rw [exD_eval]; simp⟩

theorem exD_defines : exD.Defines id := fun a b => exD_graph_iff a b

theorem exD_zQuad_ne_zero : ∃ v : OutWit 1 2 → ℤ, exD.zQuad v ≠ 0 :=
  ⟨Sum.elim (fun _ => 1) (fun _ => 0), by
    simp [zQuad, exD, Fintype.sum_sum_type, sEx, tEx]⟩

theorem exD_zPolarQ (v w : OutWit 1 2 → ℚ) :
    exD.zPolarQ v w = 2 * (v (Sum.inl 0) * w (Sum.inl 0))
      + 2 * ((v (Sum.inr 0) + v (Sum.inr 1)) * (w (Sum.inr 0) + w (Sum.inr 1))) := by
  simp [zPolarQ, exD, Fintype.sum_sum_type, Fin.sum_univ_two, sEx, tEx]
  ring

/-- The radical direction `(b, u₀, u₁) = (0, 1, −1)`. -/
def eRad : OutWit 1 2 → ℚ := Sum.elim (fun _ => 0) ![1, -1]

theorem exD_ker_eq : LinearMap.ker exD.polarMapQ = ℚ ∙ eRad := by
  apply le_antisymm
  · intro v hv
    have hrad := exD.mem_ker_polarMapQ.mp hv
    have hb := hrad (Sum.elim (fun _ => 1) (fun _ => 0))
    have hu := hrad (Sum.elim (fun _ => 0) (fun _ => 1))
    rw [exD_zPolarQ] at hb hu
    simp at hb hu
    rw [Submodule.mem_span_singleton]
    refine ⟨v (Sum.inr 0), ?_⟩
    funext x
    rcases x with j | t
    · rw [Subsingleton.elim j 0]; simp [eRad, hb]
    · fin_cases t
      · simp [eRad]
      · simp [eRad]; linarith
  · rw [Submodule.span_le]
    rintro _ rfl
    refine exD.mem_ker_polarMapQ.mpr fun w => ?_
    rw [exD_zPolarQ]
    simp [eRad]

/-- `d = 2`. -/
theorem exD_polarRank : exD.polarRank = 2 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker exD.polarMapQ
  rw [exD_ker_eq, finrank_span_singleton, finrank_outWit] at h1
  · unfold polarRank; omega
  · intro h
    have := congrFun h (Sum.inr 0)
    simp [eRad] at this

/-- The generic compiler applies, and its presentation carries `d − m = 1` witness. -/
theorem exD_compiled_witnessCount : exD.polarRank - 1 = 1 := by
  rw [exD_polarRank]

theorem exD_rankExcess :
    ∃ U, exD.WitnessCompiler U ∧
      (∀ a b, exD.Graph a b ↔ (exD.compiledData U).Graph a b) ∧
      (exD.compiledData U).Defines id := by
  obtain ⟨-, -, U, hU, hG, hD, -⟩ :=
    exD.rankExcess_compiler Nat.one_pos exD_defines exD_zQuad_ne_zero
  exact ⟨U, hU, hG, hD⟩

/-- An explicit witness-only change: `u₀ = v + w`, `u₁ = −w` (determinant `−1`). -/
def UEx : ((Fin 1 ⊕ Fin 1) → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := ![x (Sum.inl 0) + x (Sum.inr 0), -x (Sum.inr 0)]
  invFun u := Sum.elim (fun _ => u 0 + u 1) (fun _ => -u 1)
  map_add' x y := by funext i; fin_cases i <;> (simp; try ring)
  map_smul' c x := by funext i; fin_cases i <;> (simp; try ring)
  left_inv x := by
    funext y
    rcases y with j | j <;> rw [Subsingleton.elim j 0] <;> simp
  right_inv u := by
    funext i; fin_cases i <;> simp

theorem exD_eval_UEx (a b : Fin 1 → ℤ) (v w : Fin 1 → ℤ) :
    exD.P.eval (pt a b (UEx (Sum.elim v w))) = (b 0 - a 0) ^ 2 + (v 0) ^ 2 := by
  rw [exD_eval]
  simp [UEx]

/-- The one-witness presentation `(b − a)² + v² = 0`. -/
def oneWitD : QuadraticGraphData 1 1 1 where
  P := { c := 0, l := 0,
         Q := fun i j =>
           (Sum.elim (fun _ => -1) (Sum.elim (fun _ => 1) (fun _ => 0)) i : ℤ)
             * Sum.elim (fun _ => -1) (Sum.elim (fun _ => 1) (fun _ => 0)) j
           + (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1)) i : ℤ)
             * Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1)) j }

theorem oneWitD_eval (a b v : Fin 1 → ℤ) :
    oneWitD.P.eval (pt a b v) = (b 0 - a 0) ^ 2 + (v 0) ^ 2 := by
  simp [oneWitD, IntQuad.eval, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, pt]
  ring

/-- `r = 2 → 1`: the explicit change carries the original graph onto the one-witness one. -/
theorem exD_graph_iff_oneWit (a b : Fin 1 → ℤ) : exD.Graph a b ↔ oneWitD.Graph a b := by
  constructor
  · rintro ⟨u, hu⟩
    set x := UEx.symm u
    refine ⟨fun _ => x (Sum.inl 0), ?_⟩
    have hx : UEx (Sum.elim (fun _ => x (Sum.inl 0)) (fun _ => x (Sum.inr 0))) = u := by
      have : (Sum.elim (fun _ => x (Sum.inl 0)) (fun _ => x (Sum.inr 0)) :
          Fin 1 ⊕ Fin 1 → ℤ) = x := by
        funext y; rcases y with j | j <;> rw [Subsingleton.elim j 0] <;> rfl
      rw [this, LinearEquiv.apply_symm_apply]
    unfold Sol at hu ⊢
    rw [← hx, exD_eval_UEx] at hu
    rw [oneWitD_eval]
    exact hu
  · rintro ⟨v, hv⟩
    refine ⟨UEx (Sum.elim v 0), ?_⟩
    unfold Sol at hv ⊢
    rw [exD_eval_UEx]
    rw [oneWitD_eval] at hv
    exact hv

/-- The zero-witness presentation `b − a = 0`. -/
def noWitD : QuadraticGraphData 1 1 0 where
  P := { c := 0, l := Sum.elim (fun _ => -1) (Sum.elim (fun _ => 1) Fin.elim0), Q := 0 }

theorem noWitD_eval (a b : Fin 1 → ℤ) (u : Fin 0 → ℤ) :
    noWitD.P.eval (pt a b u) = b 0 - a 0 := by
  simp [noWitD, IntQuad.eval, dotProduct, Fintype.sum_sum_type, pt]
  ring

theorem noWitD_graph_iff (a b : Fin 1 → ℤ) : noWitD.Graph a b ↔ b = a := by
  constructor
  · rintro ⟨u, hu⟩
    unfold Sol at hu
    rw [noWitD_eval] at hu
    funext i; rw [Subsingleton.elim i 0]; omega
  · rintro rfl
    exact ⟨Fin.elim0, by unfold Sol; rw [noWitD_eval]; simp⟩

/-- **The control's point.**  One graph, three presentations with `2`, `1` and `0` witnesses:
the compiler's `d − m = 1` is the count of ITS presentation, not a semantic minimum. -/
theorem sameGraph_three_witnessCounts (a b : Fin 1 → ℤ) :
    (exD.Graph a b ↔ oneWitD.Graph a b) ∧ (exD.Graph a b ↔ noWitD.Graph a b) := by
  refine ⟨exD_graph_iff_oneWit a b, ?_⟩
  rw [exD_graph_iff, noWitD_graph_iff]

end RankExcessControl
end DiophCompression.ResearchUpgrade
