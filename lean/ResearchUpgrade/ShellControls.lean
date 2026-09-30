/-
  ShellControls.lean — s55.  R43 C4 Step 5 (GATE25 #69): the `n = 0` and empty-shell controls for
  the finite criterion of `DefiniteShell`.

  * `ctlN0`: `9b² + (u + b)² + v² = 1` with no input — centre 0, residual 1, `f = 0`; the single
    residue passes the output-image criterion at `M = 1` while its residue shell has four points.
  * `ctlNeg`: the same form with residual `−1` — every residue shell is empty and the graph is not
    total.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.DefiniteShell

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace ShellControl

def ctlN0 : QuadraticGraphData 0 1 2 where
  P :=
    { c := -1
      l := 0
      Q := fun p q => match p, q with
        | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 10
        | Sum.inr (Sum.inl _), Sum.inr (Sum.inr i) => if (i : ℕ) = 0 then 2 else 0
        | Sum.inr (Sum.inr i), Sum.inr (Sum.inr i') => if i = i' then 1 else 0
        | _, _ => 0 }

def ctlNeg : QuadraticGraphData 0 1 2 where
  P :=
    { c := 1
      l := 0
      Q := fun p q => match p, q with
        | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 10
        | Sum.inr (Sum.inl _), Sum.inr (Sum.inr i) => if (i : ℕ) = 0 then 2 else 0
        | Sum.inr (Sum.inr i), Sum.inr (Sum.inr i') => if i = i' then 1 else 0
        | _, _ => 0 }

theorem sc_N0_zQuadQ (u : OutWit 1 2 → ℚ) :
    ctlN0.zQuadQ u = 9 * u (Sum.inl 0) ^ 2 + (u (Sum.inr 0) + u (Sum.inl 0)) ^ 2
      + u (Sum.inr 1) ^ 2 := by
  simp [QuadraticGraphData.zQuadQ, ctlN0, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem sc_Neg_zQuadQ (u : OutWit 1 2 → ℚ) :
    ctlNeg.zQuadQ u = 9 * u (Sum.inl 0) ^ 2 + (u (Sum.inr 0) + u (Sum.inl 0)) ^ 2
      + u (Sum.inr 1) ^ 2 := by
  simp [QuadraticGraphData.zQuadQ, ctlNeg, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem sc_N0_eval (a : Fin 0 → ℤ) (b : Fin 1 → ℤ) (u : Fin 2 → ℤ) :
    ctlN0.P.eval (pt a b u) = 9 * b 0 ^ 2 + (u 0 + b 0) ^ 2 + u 1 ^ 2 - 1 := by
  simp [ctlN0, IntQuad.eval, pt, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem sc_Neg_eval (a : Fin 0 → ℤ) (b : Fin 1 → ℤ) (u : Fin 2 → ℤ) :
    ctlNeg.P.eval (pt a b u) = 9 * b 0 ^ 2 + (u 0 + b 0) ^ 2 + u 1 ^ 2 + 1 := by
  simp [ctlNeg, IntQuad.eval, pt, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem sc_posForm (u : OutWit 1 2 → ℚ) (hu : u ≠ 0) :
    0 < 9 * u (Sum.inl 0) ^ 2 + (u (Sum.inr 0) + u (Sum.inl 0)) ^ 2 + u (Sum.inr 1) ^ 2 := by
  by_contra hle
  push Not at hle
  have e1 : u (Sum.inl 0) ^ 2 = 0 := by
    nlinarith [sq_nonneg (u (Sum.inl 0)), sq_nonneg (u (Sum.inr 0) + u (Sum.inl 0)),
      sq_nonneg (u (Sum.inr 1))]
  have e2 : (u (Sum.inr 0) + u (Sum.inl 0)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (u (Sum.inl 0)), sq_nonneg (u (Sum.inr 0) + u (Sum.inl 0)),
      sq_nonneg (u (Sum.inr 1))]
  have e3 : u (Sum.inr 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (u (Sum.inl 0)), sq_nonneg (u (Sum.inr 0) + u (Sum.inl 0)),
      sq_nonneg (u (Sum.inr 1))]
  have f1 : u (Sum.inl 0) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e1
  have f3 : u (Sum.inr 1) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e3
  have f2 : u (Sum.inr 0) = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e2
    rw [f1] at this
    simpa using this
  apply hu
  funext k
  rcases k with k | k
  · fin_cases k
    exact f1
  · fin_cases k
    · exact f2
    · exact f3

theorem ctlN0_centre_residual :
    (∀ a, ctlN0.IsCentre a (QuadraticGraphData.centreAt 0 0 a)) ∧
    (∀ a, ctlN0.residual a (QuadraticGraphData.centreAt 0 0 a) = 1) := by
  have h0 : ∀ a : Fin 0 → ℤ, QuadraticGraphData.centreAt (0 : OutWit 1 2 → ℚ) 0 a = 0 := by
    intro a; funext k; simp [QuadraticGraphData.centreAt]
  refine ⟨fun a w => ?_, fun a => ?_⟩
  · rw [h0]
    simp [QuadraticGraphData.zPolarQ, QuadraticGraphData.zLinQ, QuadraticGraphData.zLin, ctlN0]
  · rw [h0]
    simp [QuadraticGraphData.residual, QuadraticGraphData.zQuadQ, QuadraticGraphData.aPart, ctlN0]

theorem ctlN0_posDef : ∀ u : OutWit 1 2 → ℚ, u ≠ 0 → 0 < ctlN0.zQuadQ u := by
  intro u hu
  rw [sc_N0_zQuadQ]
  exact sc_posForm u hu

theorem ctlN0_defines : ctlN0.Defines (fun _ _ => 0) := by
  intro a b
  have hb : b = (fun _ => 0 : Fin 1 → ℤ) ↔ b 0 = 0 := by
    constructor
    · intro h; rw [h]
    · intro h
      funext j
      fin_cases j
      exact h
  simp only
  rw [hb]
  constructor
  · rintro ⟨u, hu⟩
    have h := hu
    unfold QuadraticGraphData.Sol at h
    rw [sc_N0_eval] at h
    by_contra hne
    have hp : 0 < (b 0) ^ 2 := by positivity
    have h1 : 0 + 1 ≤ (b 0) ^ 2 := Int.add_one_le_iff.mpr hp
    nlinarith [sq_nonneg (u 0 + b 0), sq_nonneg (u 1)]
  · intro hb0
    refine ⟨![1, 0], ?_⟩
    unfold QuadraticGraphData.Sol
    rw [sc_N0_eval, hb0]
    simp

theorem sc_N0_box (y : OutWit 1 2 → ℤ) (hy : ctlN0.zQuadQ (toQ y) = ((1 : ℕ) : ℚ) ^ 2 * 1)
    (k : OutWit 1 2) : |y k| ≤ ((1 : ℕ) : ℤ) := by
  have hy1 : ctlN0.zQuadQ (toQ y) = 1 := by rw [hy]; norm_num
  rw [sc_N0_zQuadQ] at hy1
  have hy' : 9 * (y (Sum.inl 0)) ^ 2 + (y (Sum.inr 0) + y (Sum.inl 0)) ^ 2
      + (y (Sum.inr 1)) ^ 2 = 1 := by
    have : ((9 * (y (Sum.inl 0)) ^ 2 + (y (Sum.inr 0) + y (Sum.inl 0)) ^ 2
      + (y (Sum.inr 1)) ^ 2 : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
      push_cast
      simpa [toQ] using hy1
    exact_mod_cast this
  have hb : y (Sum.inl 0) = 0 := by
    by_contra hne
    have hp : 0 < (y (Sum.inl 0)) ^ 2 := by positivity
    have h1 : 0 + 1 ≤ (y (Sum.inl 0)) ^ 2 := Int.add_one_le_iff.mpr hp
    nlinarith [sq_nonneg (y (Sum.inr 0) + y (Sum.inl 0)), sq_nonneg (y (Sum.inr 1))]
  rw [hb] at hy'
  have c2 : -1 ≤ y (Sum.inr 0) ∧ y (Sum.inr 0) ≤ 1 :=
    ⟨by nlinarith [sq_nonneg (y (Sum.inr 1))], by nlinarith [sq_nonneg (y (Sum.inr 1))]⟩
  have c3 : -1 ≤ y (Sum.inr 1) ∧ y (Sum.inr 1) ≤ 1 :=
    ⟨by nlinarith [sq_nonneg (y (Sum.inr 0))], by nlinarith [sq_nonneg (y (Sum.inr 0))]⟩
  push_cast
  rw [abs_le]
  rcases k with k | k
  · obtain rfl : k = 0 := Subsingleton.elim _ _
    rw [hb]; norm_num
  · fin_cases k
    · exact c2
    · exact c3

theorem ctlN0_shellImage (ρ : Fin 0 → Fin 1) :
    ((ctlN0.residueShell 1 1 1 0 0 (fun i => ((ρ i : ℕ) : ℤ))).image outProj).card = 1 := by
  have hdata := ctlN0_centre_residual
  have H := ctlN0.shellImage_eq_value ctlN0_posDef 0 0 1 hdata.1 hdata.2 1 le_rfl 0 0
    (by intro k; simp) (by intro k i; simp) 1 sc_N0_box ctlN0_defines (fun i => ((ρ i : ℕ) : ℤ))
  have hT : ((1 : ℕ) : ℚ) ^ 2 * 1 = 1 := by norm_num
  have hρ : (fun i => ((fun i => ((ρ i : ℕ) : ℤ)) i) % ((1 : ℕ) : ℤ)) = fun i => ((ρ i : ℕ) : ℤ) :=
    funext fun i => i.elim0
  rw [hT, hρ] at H
  rw [H]
  exact Finset.card_singleton _

theorem ctlN0_residueShell_card : (ctlN0.residueShell 1 1 1 0 0 (fun _ => 0)).card = 4 := by
  have hS : ctlN0.residueShell 1 1 1 0 0 (fun _ => 0) =
      ({Sum.elim (0 : Fin 1 → ℤ) (![1, 0] : Fin 2 → ℤ),
        Sum.elim (0 : Fin 1 → ℤ) (![-1, 0] : Fin 2 → ℤ),
        Sum.elim (0 : Fin 1 → ℤ) (![0, 1] : Fin 2 → ℤ),
        Sum.elim (0 : Fin 1 → ℤ) (![0, -1] : Fin 2 → ℤ)} : Finset (OutWit 1 2 → ℤ)) := by
    ext y
    obtain ⟨b, u, rfl⟩ : ∃ b u, y = Sum.elim b u :=
      ⟨fun i => y (Sum.inl i), fun i => y (Sum.inr i), by funext k; cases k <;> rfl⟩
    simp only [QuadraticGraphData.residueShell, QuadraticGraphData.shellFinset, Finset.mem_filter,
      Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
      DefiniteShellControl.c4_elim_eq_iff, Pi.zero_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Nat.cast_one, one_dvd, implies_true, and_true]
    have hq : ctlN0.zQuadQ (toQ (Sum.elim b u)) = 1 ↔
        9 * (b 0) ^ 2 + (u 0 + b 0) ^ 2 + (u 1) ^ 2 = 1 := by
      rw [sc_N0_zQuadQ]
      constructor
      · intro h
        have : ((9 * (b 0) ^ 2 + (u 0 + b 0) ^ 2 + (u 1) ^ 2 : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
          push_cast; simpa [toQ] using h
        exact_mod_cast this
      · intro h
        have : ((9 * (b 0) ^ 2 + (u 0 + b 0) ^ 2 + (u 1) ^ 2 : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
          exact_mod_cast h
        push_cast at this
        simpa [toQ] using this
    rw [hq]
    constructor
    · rintro ⟨-, h⟩
      have hb : b 0 = 0 := by
        by_contra hne
        have hp : 0 < (b 0) ^ 2 := by positivity
        have h1 : 0 + 1 ≤ (b 0) ^ 2 := Int.add_one_le_iff.mpr hp
        nlinarith [sq_nonneg (u 0 + b 0), sq_nonneg (u 1)]
      rw [hb] at h
      have p1 : -1 ≤ u 0 := by nlinarith [sq_nonneg (u 1)]
      have p2 : u 0 ≤ 1 := by nlinarith [sq_nonneg (u 1)]
      have q1 : -1 ≤ u 1 := by nlinarith [sq_nonneg (u 0)]
      have q2 : u 1 ≤ 1 := by nlinarith [sq_nonneg (u 0)]
      generalize u 0 = p at *
      generalize u 1 = q at *
      interval_cases p <;> interval_cases q <;> simp_all
    · intro hmem
      have hvals : b 0 = 0 ∧ ((u 0 = 1 ∧ u 1 = 0) ∨ (u 0 = -1 ∧ u 1 = 0) ∨
          (u 0 = 0 ∧ u 1 = 1) ∨ (u 0 = 0 ∧ u 1 = -1)) := by
        rcases hmem with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
          simp_all
      obtain ⟨hb0, hu⟩ := hvals
      have hq1 : 9 * (b 0) ^ 2 + (u 0 + b 0) ^ 2 + (u 1) ^ 2 = 1 := by
        rw [hb0]
        rcases hu with ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> rw [h2, h3] <;> norm_num
      refine ⟨fun k => ?_, hq1⟩
      have hbox := sc_N0_box (Sum.elim b u) (by rw [(hq).mpr hq1]; norm_num) k
      push_cast at hbox
      exact abs_le.mp hbox
  rw [hS]
  decide

theorem ctlNeg_centre_residual :
    (∀ a, ctlNeg.IsCentre a (QuadraticGraphData.centreAt 0 0 a)) ∧
    (∀ a, ctlNeg.residual a (QuadraticGraphData.centreAt 0 0 a) = -1) := by
  have h0 : ∀ a : Fin 0 → ℤ, QuadraticGraphData.centreAt (0 : OutWit 1 2 → ℚ) 0 a = 0 := by
    intro a; funext k; simp [QuadraticGraphData.centreAt]
  refine ⟨fun a w => ?_, fun a => ?_⟩
  · rw [h0]
    simp [QuadraticGraphData.zPolarQ, QuadraticGraphData.zLinQ, QuadraticGraphData.zLin, ctlNeg]
  · rw [h0]
    simp [QuadraticGraphData.residual, QuadraticGraphData.zQuadQ, QuadraticGraphData.aPart, ctlNeg]

theorem ctlNeg_residueShell_empty (B : ℕ) :
    ctlNeg.residueShell B (-1) 1 0 0 (fun _ => 0) = ∅ := by
  ext y
  simp only [QuadraticGraphData.residueShell, QuadraticGraphData.shellFinset, Finset.mem_filter,
    Finset.notMem_empty, iff_false, not_and]
  intro h _
  have hq := h.2
  rw [sc_Neg_zQuadQ] at hq
  nlinarith [sq_nonneg (toQ y (Sum.inl 0)), sq_nonneg (toQ y (Sum.inr 0) + toQ y (Sum.inl 0)),
    sq_nonneg (toQ y (Sum.inr 1))]

theorem ctlNeg_not_total : ¬ ctlNeg.Total := by
  have hdata := ctlNeg_centre_residual
  exact ctlNeg.not_total_of_negResidual (fun u hu => by rw [sc_Neg_zQuadQ]; exact sc_posForm u hu)
    0 0 (-1) hdata.1 hdata.2 (by norm_num)

end ShellControl

end DiophCompression.ResearchUpgrade
