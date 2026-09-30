/-
  FullNFBranches.lean — s56.  GPT R44 Packet D2 (GATE26): the general full-residue NF cut exactly into branches.

  * `GeneralFullNF` (OPEN) and four branch propositions following `branch_exhaustive`:
    `LinearBranchFullNF` (Q ≡ 0), `IsotropicBranchFullNF` (a non-radical isotropic vector),
    `AnisotropicIndefiniteFullNF` (quotient-anisotropic, indefinite), `SemidefiniteFullNF` (non-zero semidefinite,
    either sign).  The first three are OPEN; each has a proved WEAK NF (`weakVectorCosetNF_of_linearBranch_general`,
    `weakVectorCosetNF_of_isotropicBranch`, `weakVectorCosetNF_of_quotientAnisotropicBranch`).  The semidefinite one
    is unconditional in polar rank 1 (R42) and 2 (s56) and conditional on TCER in polar rank ≥ 3.
  * `generalFullNF_iff_branches` — `GeneralFullNF` ⟺ the four branches (unconditional; `m = 0` is automatic).
  * `generalFullNF_iff_of_TCER` — with TCER, ⟺ the three non-semidefinite branches.
  The missing statement in each open branch is exactly "one modulus for all residue classes" (full), since the
  weak one-coset form is already proved there.

  Statements frozen before proof (`~/lean/s56_evidence/freeze/D2_FREEZE_s56.lean`, Dr. Fukui 2026-09-25 15:51);
  frozen = installed by `#check`/`#print` output, planted control caught.
  Claim tags: [P] for `generalFullNF_iff_branches`; [C] (TCER) for `generalFullNF_iff_of_TCER`.
-/
import ResearchUpgrade.TCERFullNF
import ResearchUpgrade.BranchSplit
import ResearchUpgrade.DimensionII_D
namespace DiophCompression.ResearchUpgrade

/-- The general full-residue target.  OPEN. -/
def GeneralFullNF : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
    D.Defines f → FullVectorCosetNF f

/-- Branch Q ≡ 0 (the equation is linear in the outputs and witnesses).  OPEN (weak NF proved:
`weakVectorCosetNF_of_linearBranch_general`). -/
def LinearBranchFullNF : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
    0 < m → (∀ x : OutWit m r → ℚ, D.zQuadQ x = 0) → D.Defines f → FullVectorCosetNF f

/-- Branch: a non-radical isotropic vector.  OPEN (weak NF proved: `weakVectorCosetNF_of_isotropicBranch`). -/
def IsotropicBranchFullNF : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
    0 < m → (∃ x : OutWit m r → ℚ, D.zQuadQ x = 0 ∧ ¬ D.InRadicalQ x) → D.Defines f → FullVectorCosetNF f

/-- Branch: quotient-anisotropic and indefinite.  OPEN (weak NF proved:
`weakVectorCosetNF_of_quotientAnisotropicBranch`). -/
def AnisotropicIndefiniteFullNF : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
    0 < m → (∀ x : OutWit m r → ℚ, D.zQuadQ x = 0 → D.InRadicalQ x) →
      (∃ p : OutWit m r → ℚ, 0 < D.zQuadQ p) → (∃ q : OutWit m r → ℚ, D.zQuadQ q < 0) →
      D.Defines f → FullVectorCosetNF f

/-- Branch: non-zero semidefinite (either sign).  Unconditional in polar rank 1 (R42) and 2 (s56);
conditional on TCER in polar rank ≥ 3 (`semidefiniteFullNF_allRanks_of_TCER`). -/
def SemidefiniteFullNF : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
    0 < m → (∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) →
    ((∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) ∨ (∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0)) →
    D.Defines f → FullVectorCosetNF f

/-- **D2.4** (exact reduction, unconditional).  The general full NF is equivalent to the conjunction of the four
branch propositions. -/
theorem generalFullNF_iff_branches :
    GeneralFullNF ↔
      LinearBranchFullNF ∧ IsotropicBranchFullNF ∧ AnisotropicIndefiniteFullNF ∧ SemidefiniteFullNF := by
  constructor
  · intro h
    exact ⟨fun n m r D f _ _ hf => h n m r D f hf, fun n m r D f _ _ hf => h n m r D f hf,
      fun n m r D f _ _ _ _ hf => h n m r D f hf, fun n m r D f _ _ _ hf => h n m r D f hf⟩
  · rintro ⟨hL, hI, hA, hS⟩ n m r D f hf
    by_cases hm0 : m = 0
    · subst hm0
      exact fullVectorCosetNF_of_m_zero f
    have hm : 0 < m := Nat.pos_of_ne_zero hm0
    rcases D.branch_exhaustive with hz | hiso | ⟨hqa, hcase⟩
    · exact hL n m r D f hm hz hf
    · exact hI n m r D f hm hiso hf
    · rcases hcase with hpos | hneg | ⟨hp, hq⟩
      · by_cases hz : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0
        · exact hL n m r D f hm hz hf
        · exact hS n m r D f hm (D.exists_int_zQuad_ne_zero hz) (Or.inl hpos) hf
      · by_cases hz : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0
        · exact hL n m r D f hm hz hf
        · exact hS n m r D f hm (D.exists_int_zQuad_ne_zero hz) (Or.inr hneg) hf
      · exact hA n m r D f hm hqa hp hq hf

/-- **D2, with TCER.**  Given TCER, the general full NF is equivalent to the three non-semidefinite branches. -/
theorem generalFullNF_iff_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    GeneralFullNF ↔ LinearBranchFullNF ∧ IsotropicBranchFullNF ∧ AnisotropicIndefiniteFullNF := by
  rw [generalFullNF_iff_branches]
  constructor
  · rintro ⟨h1, h2, h3, -⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3, semidefiniteFullNF_allRanks_of_TCER hT⟩

end DiophCompression.ResearchUpgrade
