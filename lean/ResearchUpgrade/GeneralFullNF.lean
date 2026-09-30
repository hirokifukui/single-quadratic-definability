/-
  GeneralFullNF.lean — s57.  GPT R45 Packets D1/D2 (GATE27): the confluence.

  * `isotropicBranchFullNF_holds` (D1, unconditional) — polar rank ≤ 2 (`SplitRankTwo`) or ≥ 3 (`IsotropicEichler`).
  * `generalFullNF_iff_semidefiniteFullNF` (unconditional) — with A3/A4 (`FullNFExtraction`) only the semidefinite branch
    remains.
  * `generalFullNF_of_TCER`, `sealedFullNF_of_TCER` (D2) — TCER is an explicit hypothesis (never an axiom); the sealed form
    is on the ORIGINAL class `SingleQuadraticDefinableFunctionZZ`, with one modulus for every residue class.

  Statements frozen before proof (`~/lean/s57_evidence/freeze/F5_FREEZE_s57.lean` `ba934ea9`, ruling of Dr. Fukui
  2026-09-25 21:23).  Claim tags: [P] (std-3) for the first two; the last two are [C] (TCER as an explicit hypothesis).
-/
import ResearchUpgrade.SplitRankTwo

namespace DiophCompression.ResearchUpgrade

/-- **D1.**  The isotropic branch has the full-residue NF (unconditional). -/
theorem isotropicBranchFullNF_holds : IsotropicBranchFullNF := by
  intro n m r D f hm hiso hf
  rcases Nat.lt_or_ge 2 D.polarRank with h | h
  · exact isotropicBranchFullNF_of_three_le_polarRank n m r D f hm hiso h hf
  · exact isotropicBranchFullNF_of_polarRank_le_two n m r D f hm hiso h hf

/-- **D2, exact.**  General full NF ⟺ the semidefinite branch (unconditional). -/
theorem generalFullNF_iff_semidefiniteFullNF : GeneralFullNF ↔ SemidefiniteFullNF := by
  rw [generalFullNF_iff_isotropic_and_semidefinite]
  exact ⟨fun h => h.2, fun h => ⟨isotropicBranchFullNF_holds, h⟩⟩

/-- **D2 with TCER.**  TCER ⇒ the general full-residue NF. -/
theorem generalFullNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) : GeneralFullNF :=
  generalFullNF_iff_semidefiniteFullNF.mpr (semidefiniteFullNF_allRanks_of_TCER hT)

/-- **D2, sealed.**  TCER ⇒ every function in the ORIGINAL sealed class has a full vector coset normal form. -/
theorem sealedFullNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f → FullVectorCosetNF f := by
  intro n m f hf
  obtain ⟨r, D, hD⟩ := graphData_of_singleQuadraticDefinable hf
  exact generalFullNF_of_TCER hT n m r D f hD

end DiophCompression.ResearchUpgrade
