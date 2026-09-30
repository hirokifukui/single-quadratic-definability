/-
  DiophCompression/SemanticQuadratic/PellFiberOrbit.lean — APAL Structural Theory Gate 5, 必須F step 2
  (leaf D7, membership) (s28, 2026-09-02, claude.ai direct).

  The last piece of the Pell leaf: every stage of the orbit is a fibre point. The sealed proof of
  `dichotomy_pell` applies `pell_step_identity` ONCE per step inside an existence argument; here it is
  applied along the orbit `pellOrbit D P Q X₀ Y₀`, so the whole family — outputs, witnesses and their
  Pell coordinates — is produced at once. With `PellOrbitCore` (recurrence, norm, growth, congruence,
  integral affine output) this supplies every field `PellUnitOrbitRealization` asks for. No sorry; std-3.
-/
import DiophCompression.SemanticQuadratic.Class_D7
import DiophCompression.PellOrbitCore

namespace DiophCompression.SemanticQuadratic

open MPUP

/-- Every stage of the Pell orbit over a fibre point is again a fibre point, with its output and witness
    read off the orbit coordinates: `X k = 2D·c + β` and `Y k = 2(2C·u + B·c + m)`. -/
theorem pell_fiber_orbit_mem (A B C l m q D P Q σ M : ℤ) (c₀ u₀ : ℤ)
    (hD : D = B ^ 2 - 4 * A * C) (hunit : P ^ 2 - D * Q ^ 2 = 1) (hσ : σ * C = |C|)
    (hM : M = 8 * D * |C|) (hPd : M ∣ P - 1) (hQd : M ∣ Q) (hDC : 16 * D * C ≠ 0)
    (h₀ : fq A B C l m q c₀ u₀ = 0) (k : ℕ) :
    ∃ c u : ℤ, fq A B C l m q c u = 0 ∧
      2 * D * c + (2 * B * m - 4 * C * l)
        = (DiophCompression.pellOrbit D P Q (2 * D * c₀ + (2 * B * m - 4 * C * l))
            (2 * (2 * C * u₀ + B * c₀ + m)) k).1 ∧
      2 * (2 * C * u + B * c + m)
        = (DiophCompression.pellOrbit D P Q (2 * D * c₀ + (2 * B * m - 4 * C * l))
            (2 * (2 * C * u₀ + B * c₀ + m)) k).2 := by
  have hMσ : M = 8 * D * σ * C := by rw [hM, ← hσ]; ring
  induction k with
  | zero => exact ⟨c₀, u₀, h₀, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨c, u, hfq, hX, hY⟩ := ih
    have hdX : M ∣ (DiophCompression.pellOrbit D P Q (2 * D * c₀ + (2 * B * m - 4 * C * l))
        (2 * (2 * C * u₀ + B * c₀ + m)) (k + 1)).1
        - (DiophCompression.pellOrbit D P Q (2 * D * c₀ + (2 * B * m - 4 * C * l))
            (2 * (2 * C * u₀ + B * c₀ + m)) k).1 := by
      rw [DiophCompression.pellOrbit_succ_fst]
      have e : ∀ x y : ℤ, x * P + D * y * Q - x = x * (P - 1) + D * y * Q := by intro x y; ring
      rw [e]
      exact dvd_add (Dvd.dvd.mul_left hPd _) (Dvd.dvd.mul_left hQd _)
    have hdY : M ∣ (DiophCompression.pellOrbit D P Q (2 * D * c₀ + (2 * B * m - 4 * C * l))
        (2 * (2 * C * u₀ + B * c₀ + m)) (k + 1)).2
        - (DiophCompression.pellOrbit D P Q (2 * D * c₀ + (2 * B * m - 4 * C * l))
            (2 * (2 * C * u₀ + B * c₀ + m)) k).2 := by
      rw [DiophCompression.pellOrbit_succ_snd]
      have e : ∀ x y : ℤ, x * Q + y * P - y = x * Q + y * (P - 1) := by intro x y; ring
      rw [e]
      exact dvd_add (Dvd.dvd.mul_left hQd _) (Dvd.dvd.mul_left hPd _)
    obtain ⟨a, ha⟩ := hdX
    obtain ⟨b, hb⟩ := hdY
    rw [DiophCompression.pellOrbit_succ_fst] at ha
    rw [DiophCompression.pellOrbit_succ_snd] at hb
    have ha' : (2 * D * c + (2 * B * m - 4 * C * l)) * P + D * (2 * (2 * C * u + B * c + m)) * Q
        - (2 * D * c + (2 * B * m - 4 * C * l)) = 8 * D * σ * C * a := by
      rw [hX, hY, ha, hMσ]
    have hb' : (2 * D * c + (2 * B * m - 4 * C * l)) * Q + (2 * (2 * C * u + B * c + m)) * P
        - 2 * (2 * C * u + B * c + m) = 8 * D * σ * C * b := by
      rw [hX, hY, hb, hMσ]
    have hid := pell_step_identity A B C l m q D c u P Q a b σ hD hunit hfq ha' hb'
    refine ⟨c + 4 * σ * C * a, u + 2 * σ * (D * b - B * a), ?_, ?_, ?_⟩
    · rcases mul_eq_zero.mp hid with h | h
      · exact absurd h hDC
      · exact h
    · rw [DiophCompression.pellOrbit_succ_fst]
      linear_combination hX - ha - a * hMσ
    · rw [DiophCompression.pellOrbit_succ_snd]
      linear_combination hY - hb - b * hMσ

end DiophCompression.SemanticQuadratic

#print axioms DiophCompression.SemanticQuadratic.pell_fiber_orbit_mem
