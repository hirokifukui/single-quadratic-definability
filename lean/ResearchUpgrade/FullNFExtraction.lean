/-
  FullNFExtraction.lean — s57.  GPT R45 Packets A3/A4 (GATE27): two branches of the general full-residue NF are
  closed by EXISTING proofs, and the general full NF is cut down to the isotropic branch.

  * `linearBranchFullNF_holds` (A3) — the `Q ≡ 0` branch.  At `m = 1` the scalar relation built in
    `weakVectorCosetNF_of_linearBranch` is fed to `nInputNoWitness_full` (of which `nInputNoWitness_weak` was only a
    corollary) and `fullVectorCosetNF_of_scalar`; `m ≥ 2` is impossible (`m_le_one_of_linear`).
  * `anisotropicIndefiniteFullNF_holds` (A4) — the quotient-anisotropic indefinite branch.  The off-centre radicality
    `hrad` built in `weakVectorCosetNF_of_quotientAnisotropicBranch` is passed to `fullVectorCosetNF_of_offCentre_radical`
    directly.  (NB: `fullVectorCosetNF_of_isotropic_fallback`, used there, returns only the WEAK NF despite its name.)
  * `generalFullNF_iff_isotropic_and_semidefinite` (unconditional), `generalFullNF_iff_isotropic_of_TCER`.

  Statements frozen before proof (`~/lean/s57_evidence/freeze/F1_FREEZE_s57.lean` `d61dd15c`, ruling of Dr. Fukui
  2026-09-25 21:23).  Claim tags: [P] (std-3) for the first three; the last is [C] (TCER as an explicit hypothesis).
-/
import ResearchUpgrade.FullNFBranches
import ResearchUpgrade.Reduction
import ResearchUpgrade.RankOneConfluence

namespace DiophCompression.ResearchUpgrade

/-- **A3.**  The `Q ≡ 0` branch has the full-residue NF (unconditional). -/
theorem linearBranchFullNF_holds : LinearBranchFullNF := by
  intro n m r D f hm hz hf
  have hpol : ∀ v w : OutWit m r → ℤ, D.zPolar v w = 0 := D.zPolar_eq_zero_of_zQuadQ_zero hz
  match m, D, f, hf, hpol, hm with
  | 0, _, _, _, _, hm => exact absurd hm (lt_irrefl 0)
  | 1, D₁, f, hf, hpol, _ =>
      have hT : RelTotal (Rn D₁.lbA D₁.lbBeta D₁.lbD D₁.lbE D₁.lbPhi D₁.lbG) :=
        fun x => ⟨f x 0, D₁.rn_of_sol_linear hpol hf x⟩
      have hU : RelUnique (Rn D₁.lbA D₁.lbBeta D₁.lbD D₁.lbE D₁.lbPhi D₁.lbG) := by
        intro x y y' hy hy'
        have h1 := (hf x _).mp (D₁.graph_of_rn_linear hpol hf hy)
        have h2 := (hf x _).mp (D₁.graph_of_rn_linear hpol hf hy')
        exact congrFun (h1.trans h2.symm) 0
      have hfn : fn D₁.lbA D₁.lbBeta D₁.lbD D₁.lbE D₁.lbPhi D₁.lbG hT = scalarOut f := by
        funext x
        exact hU x _ _ (Classical.choose_spec (hT x)) (D₁.rn_of_sol_linear hpol hf x)
      refine fullVectorCosetNF_of_scalar ?_
      rw [← hfn]
      exact nInputNoWitness_full D₁.lbA D₁.lbBeta D₁.lbD D₁.lbE D₁.lbPhi D₁.lbG hT hU
  | (k + 2), D, f, hf, hpol, _ =>
      exfalso
      obtain ⟨z, hz⟩ := D.exists_solZ_of_defines hf 0
      obtain ⟨-, hle⟩ := D.m_le_one_of_linear hpol (D.outputUnique_of_defines hf) hz (by omega)
      omega

/-- **A4.**  The quotient-anisotropic indefinite branch has the full-residue NF, indeed a global affine form
(unconditional). -/
theorem anisotropicIndefiniteFullNF_holds : AnisotropicIndefiniteFullNF := by
  classical
  intro n m r D f hm hqa hp hq hf
  obtain ⟨pp, hpp⟩ := hp
  obtain ⟨qq, hqq⟩ := hq
  have hQ : ∃ x : OutWit m r → ℤ, D.zQuad x ≠ 0 :=
    D.exists_int_zQuad_ne_zero (fun h => by have := h pp; linarith)
  have hOU := D.outputUnique_of_defines hf
  have hall : ∀ (a : Fin n → ℤ) (e : OutWit m r → ℚ), D.InRadicalQ e → D.zLinQ a e = 0 := by
    intro a e he
    obtain ⟨z, hz⟩ := D.exists_solZ_of_defines hf a
    exact D.zLinQ_radicalQ_eq_zero hm hOU hz hQ he
  obtain ⟨c₀, cs, hcen⟩ := D.exists_affine_centre_of_all_inputs hall
  have hcen' : ∀ a : Fin n → ℤ, D.IsCentre a (centreFamily c₀ cs a) := hcen
  have hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
      D.InRadicalQ (toQ z - centreFamily c₀ cs a) := by
    intro a z hz
    by_contra hcon
    have hQv : D.zQuadQ (toQ z - centreFamily c₀ cs a) ≠ 0 :=
      D.zQuadQ_ne_zero_of_nonradical hqa hcon
    obtain ⟨u, hu⟩ := D.exists_opposite_sign hpp hqq hQv
    obtain ⟨w, hperp, hsign, hvis⟩ := D.exists_visible_orthogonal hm hu
    exact D.pell_branch_contradiction hf hqa hz (hcen' a) rfl hperp hsign hvis
  exact D.fullVectorCosetNF_of_offCentre_radical hm hQ hf hrad

/-- **A4, one branch left** (unconditional).  General full NF ⟺ isotropic branch ∧ semidefinite branch. -/
theorem generalFullNF_iff_isotropic_and_semidefinite :
    GeneralFullNF ↔ IsotropicBranchFullNF ∧ SemidefiniteFullNF := by
  rw [generalFullNF_iff_branches]
  constructor
  · rintro ⟨-, hI, -, hS⟩
    exact ⟨hI, hS⟩
  · rintro ⟨hI, hS⟩
    exact ⟨linearBranchFullNF_holds, hI, anisotropicIndefiniteFullNF_holds, hS⟩

/-- **A4 with TCER.**  Given TCER, general full NF ⟺ the isotropic branch. -/
theorem generalFullNF_iff_isotropic_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    GeneralFullNF ↔ IsotropicBranchFullNF := by
  rw [generalFullNF_iff_isotropic_and_semidefinite]
  exact ⟨fun h => h.1, fun h => ⟨h, semidefiniteFullNF_allRanks_of_TCER hT⟩⟩

end DiophCompression.ResearchUpgrade
