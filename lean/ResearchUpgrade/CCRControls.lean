/-
  CCRControls.lean — s56.  GPT R44 D1 (GATE26 #86): boundary controls on the CCR predicate.

  * `ccr_false_without_output` — with no output (`m = 0`) CCR is false: `u² + v² = a²` is total,
    trivially output-unique, positive definite of polar rank two, with residual `a²`.
  * `ccr_false_rank_one` — with polar rank one CCR is false: the R41-D3 datum
    `(2b − a)(2b + 3a − 1) = 0`, residual `(4a − 1)²/4`.
  * `rotation_without_congruence_not_integral` — the A3 rotation with `a = b = 1`, `K = 3` gives
    `w' = (−4/5, 3/5)` of the same norm; the change from `w/3` is not integral.
  * `integer_nonneg_not_real_nonneg` — `t(t − 1)`.
  * `threeSquares24_no_rational_affine_section` — `x² + y² + z² = 1 + 24a²` has no rational affine
    section on any input coset: a section gives `P·P = 1`, `P·g = 0`, `g·g = 24`; with `h = P × g`,
    `g_k² + h_k² = 24(1 − P_k²)`, and a sum of two rational squares cannot be `24` times a nonzero
    sum of two squares (3-adic descent, `sq_add_sq_eq_24_aux`).  Totality of this family is the
    three-square theorem, which is not in mathlib at the pin and is NOT claimed.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.SectionRigidity
import ResearchUpgrade.N4Control
import Mathlib.Data.ZMod.Basic

namespace DiophCompression.ResearchUpgrade

open Matrix

/-! ### D1 controls -/

namespace CCRControls

open QuadraticGraphData

/-- `u² + v² − a² = 0`: one input, no output, two witnesses. -/
def noOut : QuadraticGraphData 1 0 2 where
  P :=
    { c := 0
      l := fun _ => 0
      Q := fun p q => match p, q with
        | Sum.inl _, Sum.inl _ => -1
        | Sum.inr (Sum.inr i), Sum.inr (Sum.inr j) => if i = j then 1 else 0
        | _, _ => 0 }

theorem noOut_zQuadQ (u : OutWit 0 2 → ℚ) :
    noOut.zQuadQ u = u (Sum.inr 0) ^ 2 + u (Sum.inr 1) ^ 2 := by
  simp [QuadraticGraphData.zQuadQ, noOut, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem noOut_pos : ∀ u : OutWit 0 2 → ℚ, u ≠ 0 → 0 < noOut.zQuadQ u := by
  intro u hu
  rw [noOut_zQuadQ]
  by_contra h
  push_neg at h
  have h0 : u (Sum.inr 0) = 0 := by nlinarith [sq_nonneg (u (Sum.inr 0)), sq_nonneg (u (Sum.inr 1))]
  have h1 : u (Sum.inr 1) = 0 := by nlinarith [sq_nonneg (u (Sum.inr 0)), sq_nonneg (u (Sum.inr 1))]
  apply hu
  funext k
  rcases k with k | k
  · exact k.elim0
  · fin_cases k
    · simpa using h0
    · simpa using h1

theorem noOut_eval (a : Fin 1 → ℤ) (b : Fin 0 → ℤ) (u : Fin 2 → ℤ) :
    noOut.P.eval (pt a b u) = u 0 ^ 2 + u 1 ^ 2 - a 0 ^ 2 := by
  simp [IntQuad.eval, noOut, pt, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem noOut_aPart (a : Fin 1 → ℤ) : noOut.aPart a = -(a 0) ^ 2 := by
  simp [QuadraticGraphData.aPart, noOut]
  ring

theorem noOut_centre (a : Fin 1 → ℤ) :
    noOut.IsCentre a (centreAt (0 : OutWit 0 2 → ℚ) (0 : Matrix (OutWit 0 2) (Fin 1) ℚ) a) := by
  intro w
  simp [QuadraticGraphData.zPolarQ, QuadraticGraphData.zLinQ, QuadraticGraphData.zLin, noOut, centreAt,
    Fintype.sum_sum_type]

theorem noOut_residual (a : Fin 1 → ℤ) :
    noOut.residual a (centreAt (0 : OutWit 0 2 → ℚ) (0 : Matrix (OutWit 0 2) (Fin 1) ℚ) a)
      = ((a 0 : ℤ) : ℚ) ^ 2 := by
  have hc : centreAt (0 : OutWit 0 2 → ℚ) (0 : Matrix (OutWit 0 2) (Fin 1) ℚ) a = 0 := by
    funext k; simp [centreAt]
  rw [hc]
  simp only [QuadraticGraphData.residual, noOut_aPart]
  simp [QuadraticGraphData.zQuadQ]

theorem ccr_false_without_output :
    ∃ (D : QuadraticGraphData 1 0 2) (c0 : OutWit 0 2 → ℚ) (C : Matrix (OutWit 0 2) (Fin 1) ℚ),
      (∀ u : OutWit 0 2 → ℚ, u ≠ 0 → 0 < D.zQuadQ u) ∧ 2 ≤ D.polarRank ∧
      (∀ a, D.IsCentre a (QuadraticGraphData.centreAt c0 C a)) ∧ D.Total ∧ D.OutputUnique ∧
      ¬ ∃ R0 : ℚ, ∀ a, D.residual a (QuadraticGraphData.centreAt c0 C a) = R0 := by
  refine ⟨noOut, 0, 0, noOut_pos, ?_, noOut_centre, ?_, outputUnique_of_m_zero noOut, ?_⟩
  · rw [noOut.sr_polarRank_eq noOut_pos]
  · intro a
    refine ⟨fun i => i.elim0, fun j => if j = 0 then a 0 else 0, ?_⟩
    show noOut.P.eval _ = 0
    rw [noOut_eval]
    simp
  · rintro ⟨R0, hR⟩
    have h0 := hR (fun _ => 0)
    have h1 := hR (fun _ => 1)
    rw [noOut_residual] at h0 h1
    norm_num at h0 h1
    linarith

/-- The R41-D3 datum in the CCR vocabulary. -/
theorem D3_zQuadQ (u : OutWit 1 0 → ℚ) : N4Control.D3.zQuadQ u = 4 * u (Sum.inl 0) ^ 2 := by
  simp [QuadraticGraphData.zQuadQ, N4Control.D3, Fintype.sum_sum_type]
  ring

theorem D3_pos : ∀ u : OutWit 1 0 → ℚ, u ≠ 0 → 0 < N4Control.D3.zQuadQ u := by
  intro u hu
  rw [D3_zQuadQ]
  have : u (Sum.inl 0) ≠ 0 := by
    intro h0
    apply hu
    funext k
    rcases k with k | k
    · fin_cases k; simpa using h0
    · exact k.elim0
  positivity

theorem ccr_false_rank_one :
    ∃ (c0 : OutWit 1 0 → ℚ) (C : Matrix (OutWit 1 0) (Fin 1) ℚ),
      (∀ u : OutWit 1 0 → ℚ, u ≠ 0 → 0 < N4Control.D3.zQuadQ u) ∧ N4Control.D3.polarRank = 1 ∧
      (∀ a, N4Control.D3.IsCentre a (QuadraticGraphData.centreAt c0 C a)) ∧
      N4Control.D3.Total ∧ N4Control.D3.OutputUnique ∧
      ¬ ∃ R0 : ℚ, ∀ a, N4Control.D3.residual a (QuadraticGraphData.centreAt c0 C a) = R0 := by
  refine ⟨fun _ => 1 / 4, fun _ _ => -1 / 2, D3_pos, ?_, ?_, N4Control.D3_total,
    N4Control.D3_outputUnique, ?_⟩
  · rw [N4Control.D3.sr_polarRank_eq D3_pos]
  · intro a w
    simp [QuadraticGraphData.zPolarQ, QuadraticGraphData.zLinQ, QuadraticGraphData.zLin,
      N4Control.D3, centreAt, Fintype.sum_sum_type]
    ring
  · rintro ⟨R0, hR⟩
    have h0 := hR (fun _ => 0)
    have h1 := hR (fun _ => 1)
    simp [QuadraticGraphData.residual, QuadraticGraphData.zQuadQ, QuadraticGraphData.aPart,
      N4Control.D3, centreAt, Fintype.sum_sum_type] at h0 h1
    norm_num at h0 h1
    linarith

theorem rotation_without_congruence_not_integral :
    ((-4 / 5 : ℚ) ^ 2 + (3 / 5 : ℚ) ^ 2 = 1) ∧
    (-4 / 5 : ℚ) = ((1 - 1 * 1 * 3 ^ 2) * 1 + 2 * 1 * 3 * 0) / (1 + 1 * 1 * 3 ^ 2) ∧
    (3 / 5 : ℚ) = ((1 - 1 * 1 * 3 ^ 2) * 0 + 2 * 1 * 3 * 1) / (1 + 1 * 1 * 3 ^ 2) ∧
    ¬ ∃ z : Fin 2 → ℤ, (z 0 : ℚ) = ((-4 / 5 : ℚ) - 1) / 3 ∧ (z 1 : ℚ) = ((3 / 5 : ℚ) - 0) / 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  rintro ⟨z, h0, _⟩
  have h : (5 : ℚ) * (z 0 : ℚ) = -3 := by rw [h0]; norm_num
  have h' : (5 : ℤ) * z 0 = -3 := by exact_mod_cast h
  omega

theorem integer_nonneg_not_real_nonneg :
    (∀ t : ℤ, 0 ≤ t * (t - 1)) ∧ ∃ t : ℚ, t * (t - 1) < 0 := by
  refine ⟨fun t => ?_, ⟨1 / 2, by norm_num⟩⟩
  rcases le_or_gt t 0 with h | h
  · nlinarith
  · nlinarith

/-- Descent at 3: a sum of two integer squares equal to 24 times a sum of two squares forces the latter to vanish. -/
theorem sq_add_sq_eq_24_aux : ∀ (N : ℕ) (A B C D : ℤ), C.natAbs + D.natAbs ≤ N →
    A ^ 2 + B ^ 2 = 24 * (C ^ 2 + D ^ 2) → C = 0 ∧ D = 0 := by
  have mod3 : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
  have dvd3 : ∀ x y : ℤ, (3 : ℤ) ∣ x ^ 2 + y ^ 2 → (3 : ℤ) ∣ x ∧ (3 : ℤ) ∣ y := by
    intro x y h
    have h' : ((x ^ 2 + y ^ 2 : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h
    push_cast at h'
    obtain ⟨hx, hy⟩ := mod3 _ _ h'
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp hx, (ZMod.intCast_zmod_eq_zero_iff_dvd y 3).mp hy⟩
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro A B C D hN h
    by_cases hz : C = 0 ∧ D = 0
    · exact hz
    exfalso
    obtain ⟨⟨A', rfl⟩, ⟨B', rfl⟩⟩ := dvd3 A B ⟨8 * (C ^ 2 + D ^ 2), by linarith⟩
    have h2 : 3 * (A' ^ 2 + B' ^ 2) = 8 * (C ^ 2 + D ^ 2) := by linarith
    have h3 : (3 : ℤ) ∣ C ^ 2 + D ^ 2 := by
      have : (3 : ℤ) ∣ 8 * (C ^ 2 + D ^ 2) := ⟨A' ^ 2 + B' ^ 2, by linarith⟩
      exact (Int.Prime.dvd_mul' (by norm_num) this).resolve_left (by norm_num)
    obtain ⟨⟨C', rfl⟩, ⟨D', rfl⟩⟩ := dvd3 C D h3
    have h4 : A' ^ 2 + B' ^ 2 = 24 * (C' ^ 2 + D' ^ 2) := by linarith
    have hlt : C'.natAbs + D'.natAbs < N := by
      have hC : (3 * C').natAbs = 3 * C'.natAbs := by rw [Int.natAbs_mul]; rfl
      have hD : (3 * D').natAbs = 3 * D'.natAbs := by rw [Int.natAbs_mul]; rfl
      rw [hC, hD] at hN
      have : C'.natAbs + D'.natAbs ≠ 0 := by
        intro h0
        apply hz
        constructor <;> omega
      omega
    obtain ⟨h5, h6⟩ := ih _ hlt A' B' C' D' le_rfl h4
    exact hz ⟨by rw [h5]; ring, by rw [h6]; ring⟩

theorem sq_add_sq_eq_24_rat (a b c d : ℚ) (h : a ^ 2 + b ^ 2 = 24 * (c ^ 2 + d ^ 2)) :
    c = 0 ∧ d = 0 := by
  set L : ℤ := ((a.den * b.den * c.den * d.den : ℕ) : ℤ) with hL
  have hL0 : (L : ℚ) ≠ 0 := by
    rw [hL]; push_cast
    have := a.den_nz; have := b.den_nz; have := c.den_nz; have := d.den_nz
    positivity
  have hint : ∀ x : ℚ, x.den ∣ (a.den * b.den * c.den * d.den) → ∃ X : ℤ, (X : ℚ) = L * x := by
    intro x hx
    obtain ⟨k, hk⟩ := hx
    refine ⟨x.num * k, ?_⟩
    have hk' : ((a.den : ℚ) * b.den * c.den * d.den) = (x.den : ℚ) * k := by exact_mod_cast hk
    rw [hL]; push_cast
    rw [hk', ← Rat.mul_den_eq_num]
    ring
  obtain ⟨A, hA⟩ := hint a ⟨b.den * c.den * d.den, by ring⟩
  obtain ⟨B, hB⟩ := hint b ⟨a.den * c.den * d.den, by ring⟩
  obtain ⟨C, hC⟩ := hint c ⟨a.den * b.den * d.den, by ring⟩
  obtain ⟨D, hD⟩ := hint d ⟨a.den * b.den * c.den, by ring⟩
  have hE : A ^ 2 + B ^ 2 = 24 * (C ^ 2 + D ^ 2) := by
    have : (A : ℚ) ^ 2 + (B : ℚ) ^ 2 = 24 * ((C : ℚ) ^ 2 + (D : ℚ) ^ 2) := by
      rw [hA, hB, hC, hD]; linear_combination (L : ℚ) ^ 2 * h
    exact_mod_cast this
  obtain ⟨hC0, hD0⟩ := sq_add_sq_eq_24_aux _ A B C D le_rfl hE
  rw [hC0] at hC; rw [hD0] at hD
  push_cast at hC hD
  exact ⟨(mul_eq_zero.mp hC.symm).resolve_left hL0, (mul_eq_zero.mp hD.symm).resolve_left hL0⟩

theorem threeSquares24_no_rational_affine_section :
    ¬ ∃ (M : ℕ) (ρ : ℤ) (x0 x1 : Fin 3 → ℚ), 1 ≤ M ∧
      ∀ t : ℤ, ∑ i, (x0 i + (t : ℚ) * x1 i) ^ 2 = 1 + 24 * ((ρ : ℚ) + (M : ℚ) * t) ^ 2 := by
  rintro ⟨M, ρ, x0, x1, hM, h⟩
  have hM1 : (1 : ℚ) ≤ M := by exact_mod_cast hM
  have hM0 : (M : ℚ) ≠ 0 := by linarith
  have e0 := h 0
  have e1 := h 1
  have e2 := h (-1)
  simp only [Fin.sum_univ_three] at e0 e1 e2
  push_cast at e0 e1 e2
  -- P = x0 - (ρ/M) x1, g = x1 / M
  set P0 := x0 0 - (ρ : ℚ) / M * x1 0
  set P1 := x0 1 - (ρ : ℚ) / M * x1 1
  set P2 := x0 2 - (ρ : ℚ) / M * x1 2
  set g0 := x1 0 / M
  set g1 := x1 1 / M
  set g2 := x1 2 / M
  have hS11 : x1 0 ^ 2 + x1 1 ^ 2 + x1 2 ^ 2 = 24 * (M : ℚ) ^ 2 := by linear_combination (e1 + e2 - 2 * e0) / 2
  have hS01 : x0 0 * x1 0 + x0 1 * x1 1 + x0 2 * x1 2 = 24 * (ρ : ℚ) * M := by
    linear_combination (e1 - e2) / 4
  have hPP : P0 ^ 2 + P1 ^ 2 + P2 ^ 2 = 1 := by
    simp only [P0, P1, P2]
    field_simp
    linear_combination (M : ℚ) ^ 2 * e0 - 2 * (ρ : ℚ) * M * hS01 + (ρ : ℚ) ^ 2 * hS11
  have hPg : P0 * g0 + P1 * g1 + P2 * g2 = 0 := by
    simp only [P0, P1, P2, g0, g1, g2]
    field_simp
    linear_combination (M : ℚ) * hS01 - (ρ : ℚ) * hS11
  have hgg : g0 ^ 2 + g1 ^ 2 + g2 ^ 2 = 24 := by
    simp only [g0, g1, g2]
    field_simp
    linear_combination hS11
  -- cross product h = P × g and the column identities
  have k0 : g0 ^ 2 + (P1 * g2 - P2 * g1) ^ 2 = 24 * (P1 ^ 2 + P2 ^ 2) := by
    linear_combination (g1 ^ 2 + g2 ^ 2) * hPP + (P0 * g0 - P1 * g1 - P2 * g2) * hPg
      + (1 - P0 ^ 2) * hgg - 24 * hPP
  have k1 : g1 ^ 2 + (P2 * g0 - P0 * g2) ^ 2 = 24 * (P0 ^ 2 + P2 ^ 2) := by
    linear_combination (g0 ^ 2 + g2 ^ 2) * hPP + (-P0 * g0 + P1 * g1 - P2 * g2) * hPg
      + (1 - P1 ^ 2) * hgg - 24 * hPP
  obtain ⟨hP1, hP2⟩ := sq_add_sq_eq_24_rat _ _ _ _ k0
  obtain ⟨hP0, _⟩ := sq_add_sq_eq_24_rat _ _ _ _ k1
  rw [hP0, hP1, hP2] at hPP
  norm_num at hPP

end CCRControls

end DiophCompression.ResearchUpgrade
