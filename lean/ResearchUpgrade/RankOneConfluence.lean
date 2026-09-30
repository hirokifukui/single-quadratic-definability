/-
  RankOneConfluence.lean — s52.  R41-B3: polar rank one, Q not identically zero, total and
  output-unique ⇒ the defined function has the FULL-residue vector coset normal form, with one
  modulus common to every residue class.

  `m ≤ 1` is DERIVED here (m_le_one_of_polarRankOne), not assumed; `m = 0` is discharged by the
  trivial wrapper.  The `m = 1` half runs through the compiler of B2: the witness block is
  removed, and the witness-free datum is fed to nInputNoWitness_full.

  With this, rank one is a closed endpoint: witness-radical (B3 of r41), evaluation invariance
  (B1, s52), an actual witness-free presentation (B2, s52), and the normal form here.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.NoWitnessCompiler
import ResearchUpgrade.AffineNormalForm
import ResearchUpgrade.RankOne

namespace DiophCompression.ResearchUpgrade

open Matrix

/-- Scalar → vector, in the FULL-residue form.  Companion of `weakVectorCosetNF_of_scalar`. -/
theorem fullVectorCosetNF_of_scalar {n : ℕ} {f : (Fin n → ℤ) → (Fin 1 → ℤ)}
    (h : FullCosetNF (scalarOut f)) : FullVectorCosetNF f := by
  obtain ⟨M, hM, hq⟩ := h
  refine ⟨M, hM, fun ρ => ?_⟩
  obtain ⟨q, hq'⟩ := hq ρ
  refine ⟨fun _ => q, fun t j => ?_⟩
  have hj : j = 0 := Subsingleton.elim j 0
  subst hj
  exact hq' t

namespace QuadraticGraphData

/-- Every `(n, 1, 0)` graph puts its defined function in the FULL vector coset normal form. -/
theorem fullVectorCosetNF_of_defines {n : ℕ} (D : QuadraticGraphData n 1 0)
    {f : (Fin n → ℤ) → (Fin 1 → ℤ)} (hf : D.Defines f) : FullVectorCosetNF f := by
  refine fullVectorCosetNF_of_scalar ?_
  rw [← D.fn_eq_scalarOut hf]
  exact nInputNoWitness_full D.coefA D.coefBeta D.coefD D.coefE D.coefPhi D.coefG
    (D.relTotal_of_defines hf) (D.relUnique_of_defines hf)

/-- **R41-B3 — the rank-one confluence.**  Polar rank one, `Q ≠ 0`, total and output-unique:
the defined function has the FULL-residue vector coset normal form, with a modulus common to
every residue class.  `m ≤ 1` is derived, not assumed; `m = 0` is the trivial wrapper. -/
theorem fullVectorCosetNF_of_polarRankOne {n m r : ℕ} (D : QuadraticGraphData n m r)
    (hOU : D.OutputUnique) (hT : D.Total)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {a₀ : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hz : D.SolZ a₀ z₀)
    {w₀ : OutWit m r → ℚ}
    (hcodim : ∀ x : OutWit m r → ℚ, ∃ t : ℚ, D.InRadicalQ (x - t • w₀))
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    FullVectorCosetNF f := by
  have hm1 : m ≤ 1 := D.m_le_one_of_polarRankOne hOU hQ hz hcodim
  interval_cases m
  · exact fullVectorCosetNF_of_m_zero f
  · have hrad : ∀ x : OutWit 1 r → ℚ, (∀ j : Fin 1, x (Sum.inl j) = 0) → D.InRadicalQ x :=
      fun x hx => D.witnessDir_inRadicalQ Nat.one_pos hOU hQ hz hcodim hx
    exact (D.noWitnessData).fullVectorCosetNF_of_defines
      (D.noWitnessData_defines hOU hT hQ hrad hf)

end QuadraticGraphData
end DiophCompression.ResearchUpgrade
