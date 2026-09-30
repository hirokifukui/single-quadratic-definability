/-
  ResidualReduction.lean — s55.  R43 D2 (GATE25 #71): the general weak normal form is equivalent to
  its residual-reflection obstruction case.

  * `ResidualReflectionObstructionNF` — positive definite, at least one output, polar rank at least
    three, an affine centre whose residual is not constant and whose doubled centre is integral at
    no input.
  * `generalWeakNF_iff_residualReflectionObstructionNF` — via `generalWeakNF_iff_definiteWeakNF`,
    the low-rank theorem (rank ≤ 2), `constResidual_fullVectorCosetNF` (constant residual) and
    `centreReflect_weakVectorCosetNF` (a reflectable input); `definite_exists_centreAt`.

  Not claimed: the general weak normal form itself.  The obstruction case is open.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.CentreReflection
import ResearchUpgrade.AffineSection
import ResearchUpgrade.DefiniteReduction

namespace DiophCompression.ResearchUpgrade

open Matrix

def ResidualReflectionObstructionNF : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ))
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ),
    0 < m → (∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) → 3 ≤ D.polarRank →
      (∀ a, D.IsCentre a (QuadraticGraphData.centreAt c0 C a)) →
      (¬ ∃ R0 : ℚ, ∀ a, D.residual a (QuadraticGraphData.centreAt c0 C a) = R0) →
      (∀ a, ¬ ∃ h : OutWit m r → ℤ, toQ h = 2 • QuadraticGraphData.centreAt c0 C a) →
      D.Defines f → WeakVectorCosetNF f

namespace QuadraticGraphData

theorem definite_exists_centreAt {n m r : ℕ} (D : QuadraticGraphData n m r)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) :
    ∃ (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ),
      ∀ a, D.IsCentre a (centreAt c0 C a) := by
  have hnd : D.NondegQ := fun v hv => ⟨v, by
    rw [D.zPolarQ_self]
    have := hpos v hv
    linarith⟩
  obtain ⟨c₀, cs, hc⟩ := D.exists_affine_centre_of_nondegQ hnd
  refine ⟨c₀, Matrix.of fun k i => cs i k, fun a => ?_⟩
  have heq : centreAt c₀ (Matrix.of fun k i => cs i k) a = c₀ + ∑ i, (a i : ℚ) • cs i := by
    funext k
    simp only [centreAt, Matrix.of_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  exact hc a

end QuadraticGraphData

theorem generalWeakNF_iff_residualReflectionObstructionNF :
    GeneralWeakNF ↔ ResidualReflectionObstructionNF := by
  constructor
  · intro hG n m r D f c0 C _ _ _ _ _ _ hf
    exact hG n m r D f hf
  · intro hO
    rw [generalWeakNF_iff_definiteWeakNF]
    intro n m r D f hm hpos hf
    obtain ⟨c0, C, hcen⟩ := D.definite_exists_centreAt hpos
    by_cases hr : D.polarRank ≤ 2
    · have hQ : ∃ v, D.zQuad v ≠ 0 := by
        refine ⟨Pi.single (Sum.inl ⟨0, hm⟩) 1, fun h0 => ?_⟩
        have hne : toQ (Pi.single (Sum.inl ⟨0, hm⟩) (1 : ℤ) : OutWit m r → ℤ) ≠ 0 := by
          intro h
          have := congrFun h (Sum.inl ⟨0, hm⟩)
          simp [toQ] at this
        have := hpos _ hne
        rw [D.zQuadQ_toQ, h0] at this
        simp at this
      exact lowRankSemidefiniteWeakNF_allM_holds n m r D f hQ
        (Or.inl (D.sc_zQuadQ_nonneg hpos)) hr hf
    · by_cases hc : ∃ R0 : ℚ, ∀ a, D.residual a (QuadraticGraphData.centreAt c0 C a) = R0
      · obtain ⟨R0, hR⟩ := hc
        exact weakVectorCosetNF_of_fullVectorCosetNF
          (D.constResidual_fullVectorCosetNF c0 C R0 hcen hR hf)
      · by_cases hrefl : ∃ a, ∃ h : OutWit m r → ℤ,
            toQ h = 2 • QuadraticGraphData.centreAt c0 C a
        · obtain ⟨a0, h0⟩ := hrefl
          exact D.centreReflect_weakVectorCosetNF c0 C hcen hf a0 h0
        · exact hO n m r D f c0 C hm hpos (by omega) hcen hc (fun a ha => hrefl ⟨a, ha⟩) hf

end DiophCompression.ResearchUpgrade
