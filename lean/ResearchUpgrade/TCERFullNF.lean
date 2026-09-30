/-
  TCERFullNF.lean — s56.  GPT R44 C3 step 3 in its own scope: TCER ⇒ full-residue NF for EVERY non-zero
  semidefinite datum (either sign) with an output.  Polar rank 1 is the unconditional R42 theorem
  `fullVectorCosetNF_of_polarRank_eq_one`; polar rank ≥ 2 is `semidefiniteFullNF_of_TCER` (TCERCapstones).
  Statement frozen before proof (`~/lean/s56_evidence/freeze/C3b_FREEZE_s56.lean`, Dr. Fukui 2026-09-25 15:51);
  frozen = installed by `#check` output, planted control caught.
  Not claimed: the general (indefinite / isotropic) full NF — Packet D2 records that residue.
  Claim tags: [C] (conditional on TCER; std-3 otherwise).
-/
import ResearchUpgrade.TCERCapstones
import ResearchUpgrade.R42Completion
namespace DiophCompression.ResearchUpgrade

/-- **C3.3, all ranks.**  TCER ⇒ full-residue NF for every non-zero semidefinite datum (either sign) with an output
that defines `f`.  Polar rank 1 is unconditional (R42); polar rank ≥ 2 uses `semidefiniteFullNF_of_TCER`. -/
theorem semidefiniteFullNF_allRanks_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) →
      ((∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) ∨ (∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0)) →
      D.Defines f → FullVectorCosetNF f := by
  intro n m r D f hm hQ hsemi hf
  have hmle : m ≤ D.polarRank := D.m_le_polarRank hm hf hQ
  by_cases h1 : D.polarRank = 1
  · exact D.fullVectorCosetNF_of_polarRank_eq_one hQ h1 hf
  · exact semidefiniteFullNF_of_TCER hT n m r D f hm hQ hsemi (by omega) hf

end DiophCompression.ResearchUpgrade
