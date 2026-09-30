/-
  FullNFControls.lean — s57.  GPT R45 D3 (GATE27): boundary controls for the isotropic branch, stated as NEGATED over-claims.

  * `rank_hypothesis_needed` — `b(2u+1) = 0`: split polar rank 2, centre `(0, −1/2)`, residual 0, output `b = 0` unique, the
    integer solution `(0,0)` is off-radical and `e_b` is a non-radical isotropic vector.  So the rank ≥ 3 impossibility
    (`false_of_offRadical_of_three_le_polarRank`) is false without `3 ≤ polarRank`.
  * `residual_zero_not_forced` — `(4b+1)(4u+1) = 1`: the only integer solution is `(0,0)`, centre `(−1/4, −1/4)`, residual 1.
    So the constant-residual theorem in polar rank ≤ 2 (`constResidual_of_isotropic_polarRank_le_two`) cannot be strengthened
    to residual 0.

  Statements frozen before proof (`~/lean/s57_evidence/freeze/F6_FREEZE_s57.lean` `f685a227`).  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.GeneralFullNF

namespace DiophCompression.ResearchUpgrade

namespace FullNFControls

open QuadraticGraphData

/-- `b(2u+1) = 0`: no input, one output `b`, one witness `u`. -/
def split1 : QuadraticGraphData 0 1 1 where
  P :=
    { c := 0
      l := fun p => match p with
        | Sum.inr (Sum.inl _) => 1
        | _ => 0
      Q := fun p q => match p, q with
        | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => 1
        | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => 1
        | _, _ => 0 }

/-- `(4b+1)(4u+1) − 1 = 16bu + 4b + 4u = 0`: no input, one output `b`, one witness `u`. -/
def split2 : QuadraticGraphData 0 1 1 where
  P :=
    { c := 0
      l := fun p => match p with
        | Sum.inr _ => 4
        | _ => 0
      Q := fun p q => match p, q with
        | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => 8
        | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => 8
        | _, _ => 0 }

theorem split1_eval (a : Fin 0 → ℤ) (b : Fin 1 → ℤ) (u : Fin 1 → ℤ) :
    split1.P.eval (pt a b u) = b 0 * (2 * u 0 + 1) := by
  simp [IntQuad.eval, split1, pt, dotProduct, Matrix.mulVec, Fintype.sum_sum_type]
  ring

theorem split2_eval (a : Fin 0 → ℤ) (b : Fin 1 → ℤ) (u : Fin 1 → ℤ) :
    split2.P.eval (pt a b u) = (4 * b 0 + 1) * (4 * u 0 + 1) - 1 := by
  simp [IntQuad.eval, split2, pt, dotProduct, Matrix.mulVec, Fintype.sum_sum_type]
  ring

theorem split1_defines : split1.Defines (fun _ => 0) := by
  intro a b
  constructor
  · rintro ⟨u, hu⟩
    have h : b 0 * (2 * u 0 + 1) = 0 := by rw [← split1_eval a b u]; exact hu
    have h2 : (2 * u 0 + 1) ≠ 0 := by omega
    have hb : b 0 = 0 := (mul_eq_zero.mp h).resolve_right h2
    funext i; fin_cases i; simpa using hb
  · rintro rfl
    refine ⟨fun _ => 0, ?_⟩
    show split1.P.eval (pt a _ _) = 0
    rw [split1_eval]; simp

theorem split2_defines : split2.Defines (fun _ => 0) := by
  intro a b
  constructor
  · rintro ⟨u, hu⟩
    have h : (4 * b 0 + 1) * (4 * u 0 + 1) = 1 := by
      have := hu; unfold QuadraticGraphData.Sol at this; rw [split2_eval] at this; linarith
    have hb : b 0 = 0 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one h with h1 | h1 <;> omega
    funext i; fin_cases i; simpa using hb
  · rintro rfl
    refine ⟨fun _ => 0, ?_⟩
    show split2.P.eval (pt a _ _) = 0
    rw [split2_eval]; simp

theorem split1_zPolarQ (v w : OutWit 1 1 → ℚ) :
    split1.zPolarQ v w = 2 * (v (Sum.inl 0) * w (Sum.inr 0) + v (Sum.inr 0) * w (Sum.inl 0)) := by
  simp [QuadraticGraphData.zPolarQ, split1, Fintype.sum_sum_type]
  ring

theorem split2_zPolarQ (v w : OutWit 1 1 → ℚ) :
    split2.zPolarQ v w = 16 * (v (Sum.inl 0) * w (Sum.inr 0) + v (Sum.inr 0) * w (Sum.inl 0)) := by
  simp [QuadraticGraphData.zPolarQ, split2, Fintype.sum_sum_type]
  ring

theorem split1_zQuadQ (v : OutWit 1 1 → ℚ) : split1.zQuadQ v = 2 * v (Sum.inl 0) * v (Sum.inr 0) := by
  simp [QuadraticGraphData.zQuadQ, split1, Fintype.sum_sum_type]
  ring

theorem split2_zQuadQ (v : OutWit 1 1 → ℚ) : split2.zQuadQ v = 16 * v (Sum.inl 0) * v (Sum.inr 0) := by
  simp [QuadraticGraphData.zQuadQ, split2, Fintype.sum_sum_type]
  ring

theorem split1_zLinQ (a : Fin 0 → ℤ) (w : OutWit 1 1 → ℚ) : split1.zLinQ a w = w (Sum.inl 0) := by
  simp [QuadraticGraphData.zLinQ, QuadraticGraphData.zLin, split1, Fintype.sum_sum_type]

theorem split2_zLinQ (a : Fin 0 → ℤ) (w : OutWit 1 1 → ℚ) :
    split2.zLinQ a w = 4 * w (Sum.inl 0) + 4 * w (Sum.inr 0) := by
  simp [QuadraticGraphData.zLinQ, QuadraticGraphData.zLin, split2, Fintype.sum_sum_type]

/-- The isotropic output direction `e_b`. -/
def eb : OutWit 1 1 → ℚ := fun k => match k with
  | Sum.inl _ => 1
  | Sum.inr _ => 0

/-- The witness direction `e_u`. -/
def eu : OutWit 1 1 → ℚ := fun k => match k with
  | Sum.inl _ => 0
  | Sum.inr _ => 1

end FullNFControls

open FullNFControls in
theorem rank_hypothesis_needed :
    ¬ (∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (a : Fin n → ℤ) (c : OutWit m r → ℚ) (z : OutWit m r → ℤ)
        (e₀ : OutWit m r → ℚ), 0 < m → D.OutputUnique → D.IsCentre a c → D.SolZ a z → ¬ D.InRadicalQ (toQ z - c) →
        D.zQuadQ e₀ = 0 → ¬ D.InRadicalQ e₀ → False) := by
  intro H
  let c : OutWit 1 1 → ℚ := fun k => match k with
    | Sum.inl _ => 0
    | Sum.inr _ => -1/2
  have hc : split1.IsCentre (fun i => i.elim0) c := by
    intro w
    rw [split1_zPolarQ, split1_zLinQ]
    simp [c]
    ring
  have hz : split1.SolZ (fun i => i.elim0) (0 : OutWit 1 1 → ℤ) := by
    show split1.P.eval (Sum.elim _ (0 : OutWit 1 1 → ℤ)) = 0
    have := split1_eval (fun i => i.elim0) 0 0
    have e : (Sum.elim (0 : Fin 1 → ℤ) (0 : Fin 1 → ℤ) : OutWit 1 1 → ℤ) = 0 := by
      funext k; rcases k with k | k <;> rfl
    simp only [pt] at this
    rw [e] at this
    rw [this]; simp
  have hx : ¬ split1.InRadicalQ (toQ (0 : OutWit 1 1 → ℤ) - c) := by
    intro h
    have := h eb
    rw [split1_zPolarQ] at this
    simp [toQ, c, eb] at this
  have he : split1.zQuadQ eb = 0 := by rw [split1_zQuadQ]; simp [eb]
  have hne : ¬ split1.InRadicalQ eb := by
    intro h
    have := h eu
    rw [split1_zPolarQ] at this
    simp [eb, eu] at this
  exact H 0 1 1 split1 _ c 0 eb Nat.one_pos (split1.outputUnique_of_defines split1_defines) hc hz hx he hne

open FullNFControls in
theorem residual_zero_not_forced :
    ¬ (∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)) (c₀ : OutWit m r → ℚ)
        (cs : Fin n → OutWit m r → ℚ), 0 < m → D.Defines f → (∃ x : OutWit m r → ℚ, D.zQuadQ x = 0 ∧ ¬ D.InRadicalQ x) →
        D.polarRank ≤ 2 → (∀ a, D.IsCentre a (centreFamily c₀ cs a)) → ∀ a, D.residual a (centreFamily c₀ cs a) = 0) := by
  intro H
  let c₀ : OutWit 1 1 → ℚ := fun _ => -1/4
  let cs : Fin 0 → OutWit 1 1 → ℚ := fun i => i.elim0
  have hcf : ∀ a : Fin 0 → ℤ, centreFamily c₀ cs a = c₀ := by
    intro a; simp [centreFamily]
  have hiso : ∃ x : OutWit 1 1 → ℚ, split2.zQuadQ x = 0 ∧ ¬ split2.InRadicalQ x := by
    refine ⟨eb, by rw [split2_zQuadQ]; simp [eb], fun h => ?_⟩
    have := h eu
    rw [split2_zPolarQ] at this
    simp [eb, eu] at this
  have hrank : split2.polarRank ≤ 2 := by
    calc split2.polarRank = Module.finrank ℚ (LinearMap.range split2.polarMapQ) := rfl
      _ ≤ Module.finrank ℚ (OutWit 1 1 → ℚ) := LinearMap.finrank_range_le _
      _ = 2 := by simp
  have hcen : ∀ a, split2.IsCentre a (centreFamily c₀ cs a) := by
    intro a w
    rw [hcf, split2_zPolarQ, split2_zLinQ]
    simp [c₀]
    ring
  have h0 := H 0 1 1 split2 (fun _ => 0) c₀ cs Nat.one_pos split2_defines hiso hrank hcen (fun i => i.elim0)
  rw [hcf] at h0
  simp only [QuadraticGraphData.residual, split2_zQuadQ] at h0
  simp [QuadraticGraphData.aPart, split2, c₀] at h0

end DiophCompression.ResearchUpgrade
