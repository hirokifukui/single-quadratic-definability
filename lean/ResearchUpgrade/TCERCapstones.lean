/-
  TCERCapstones.lean — s56.  GPT R44 Packets C3 and C4 (GATE26): the TCER-conditional capstones.
  EVERY theorem here carries `hT : TCERBridge.TernaryCosetEventualRepresentation` as an explicit hypothesis.
  TCER is not proved in this library (see TCERBridge.lean and C1_TCER_CROSSWALK); nothing here is unconditional.

  * `lineCollision_rankThree_of_TCER` (C3a) — polar rank ≥ 3, non-zero discriminant: B1 `fixedCoset_slice` +
    C2 `ternaryCosetCollision_of_TCER` give one input with two integer solutions of different output.
  * `ccr_of_TCER` (C3.1) — constant-residual rigidity for all `n, m, r`: rank 2 by the unconditional
    `rankTwo_CCR`; rank ≥ 3 by a line with positive leading coefficient (`residual_line_of_nonconstant`),
    re-centred at a point of positive residual among t = 0, 1, 2, then discriminant zero
    (`discriminantZero_line_const`) or non-zero (C3a).
  * `definiteCommonSlopeNF_of_TCER` (C3.2) — positive definite, polar rank ≥ 2: one integer slope on all
    residue classes (`constResidual_commonSlopeIntNF`).
  * `semidefiniteFullNF_of_TCER` (C3.3) — non-zero semidefinite (either sign), polar rank ≥ 2: full-residue NF,
    via `definite_reduction` and the sign flip `negGraph`.  Polar rank 1 is the unconditional
    `fullVectorCosetNF_of_polarRank_eq_one` (R42); the two are combined in `TCERFullNF.lean`.
  * `definiteShellCriterion_of_TCER` (C3.4) — positive definite, polar rank ≥ 2, m ≥ 1, actual centre:
    total ∧ output-unique ⟺ constant residual and every residue shell (box-bounded) has a one-point output image.
    No complexity claim for the finite check.
  * `generalWeakNF_of_TCER` (C4) — `GeneralWeakNF`, through `generalWeakNF_iff_residualReflectionObstructionNF`:
    the obstruction case assumes a non-constant residual, which CCR excludes.
  * `sealedWeakNF_of_TCER` (C4, sealed) — the same for the ORIGINAL sealed class
    `DiophCompression.SingleQuadraticDefinableFunctionZZ` (via `graphData_of_singleQuadraticDefinable`).

  Statements frozen before proof (`~/lean/s56_evidence/freeze/C3_FREEZE_s56.lean`, Dr. Fukui 2026-09-25 15:51
  "全て承認する"); frozen = installed by `#check` output, planted control caught.

  Claim tags: [C] (conditional on TCER; std-3 otherwise).
-/
import ResearchUpgrade.TCERSlice
import ResearchUpgrade.DefiniteShell
import ResearchUpgrade.ResidualReduction
import ResearchUpgrade.FidelityBridge
namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadraticGraphData

variable {n m r : ℕ}

/-- **C3a** (verbatim from C3a_DRAFT_s56.lean).  Polar rank ≥ 3, non-zero discriminant: one input on the line with
two actual integer solutions whose output `j₀` differs. -/
theorem lineCollision_rankThree_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation)
    (D : QuadraticGraphData n m r) (j0 : Fin m)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (hrank : 3 ≤ D.polarRank)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a))
    (a0 v : Fin n → ℤ) (z0 : OutWit m r → ℤ) (hz0 : D.SolZ a0 z0)
    (hR0 : 0 < D.residual a0 (centreAt c0 C a0)) (Aq Bq : ℚ)
    (hline : ∀ t : ℤ, D.residual (a0 + t • v) (centreAt c0 C (a0 + t • v))
        = Aq * (t : ℚ) ^ 2 + Bq * t + D.residual a0 (centreAt c0 C a0))
    (hA : 0 < Aq) (hdisc : Bq ^ 2 - 4 * Aq * D.residual a0 (centreAt c0 C a0) ≠ 0) :
    ∃ (t : ℤ) (z z' : OutWit m r → ℤ), D.SolZ (a0 + t • v) z ∧ D.SolZ (a0 + t • v) z' ∧
      z (Sum.inl j0) ≠ z' (Sum.inl j0) := by
  obtain ⟨S, d, M, p, A, B, α, β, γ, hS, hSpos, hd, hM, hp, hA', hdisc', hβ, hret⟩ :=
    fixedCoset_slice D j0 hpos hrank c0 C hc a0 v z0 hz0 hR0 Aq Bq hline hA hdisc
  obtain ⟨k, x, x', hx, hx', hne⟩ :=
    TCERBridge.ternaryCosetCollision_of_TCER hT S hS hSpos d hd p hp A B hA' hdisc' M hM
  obtain ⟨z, hz, hzj⟩ := hret k x hx
  obtain ⟨z', hz', hzj'⟩ := hret k x' hx'
  refine ⟨(M : ℤ) * k, z, z', hz, hz', ?_⟩
  intro heq
  apply hne
  have h1 : ((z (Sum.inl j0) : ℤ) : ℚ) = z' (Sum.inl j0) := by rw [heq]
  rw [hzj, hzj'] at h1
  have h2 : β * ((p ⬝ᵥ (TCERBridge.e1 + (d : ℤ) • x) : ℤ) : ℚ)
      = β * ((p ⬝ᵥ (TCERBridge.e1 + (d : ℤ) • x') : ℤ) : ℚ) := by linarith
  exact_mod_cast mul_left_cancel₀ hβ h2

end QuadraticGraphData

/-- **C3.1** (general CCR, conditional).  TCER ⇒ constant-residual rigidity for every `n, m, r`. -/
theorem ccr_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) : ConstantResidualRigidity := by
  intro n m r D c0 C hm hpos hrank hc hTot hOU
  have hpr := D.sr_polarRank_eq hpos
  by_cases h2 : D.polarRank = 2
  · have hcard : Fintype.card (OutWit m r) = 2 := by simp; omega
    exact D.rankTwo_CCR (Fintype.equivFinOfCardEq hcard) hm hpos c0 C hc hTot hOU
  · by_contra hnc
    obtain ⟨a0, v, A, B, hA, hl⟩ := D.residual_line_of_nonconstant hpos c0 C hc hTot hnc
    have hnn : ∀ t : ℤ, 0 ≤ A * (t : ℚ) ^ 2 + B * t + D.residual a0 (QuadraticGraphData.centreAt c0 C a0) := by
      intro t
      rw [← hl t]
      obtain ⟨z, hz⟩ := D.sr_solZ_of_total hTot (a0 + t • v)
      have := D.sr_zQuadQ_nonneg hpos (toQ z - QuadraticGraphData.centreAt c0 C (a0 + t • v))
      rwa [(D.sr_solZ_iff (hc _) z).mp hz] at this
    obtain ⟨t1, ht1⟩ : ∃ t1 : ℤ,
        0 < A * (t1 : ℚ) ^ 2 + B * t1 + D.residual a0 (QuadraticGraphData.centreAt c0 C a0) := by
      by_contra H
      push_neg at H
      have h0 := le_antisymm (H 0) (hnn 0)
      have h1 := le_antisymm (H 1) (hnn 1)
      have h2' := le_antisymm (H 2) (hnn 2)
      push_cast at h0 h1 h2'
      linarith
    obtain ⟨a1, ha1⟩ : ∃ a1 : Fin n → ℤ, a1 = a0 + t1 • v := ⟨_, rfl⟩
    have hR1eq : D.residual a1 (QuadraticGraphData.centreAt c0 C a1)
        = A * (t1 : ℚ) ^ 2 + B * t1 + D.residual a0 (QuadraticGraphData.centreAt c0 C a0) := by
      rw [ha1]; exact hl t1
    have hla : ∀ s : ℤ, D.residual (a1 + s • v) (QuadraticGraphData.centreAt c0 C (a1 + s • v))
        = A * (s : ℚ) ^ 2 + (B + 2 * A * t1) * s + D.residual a1 (QuadraticGraphData.centreAt c0 C a1) := by
      intro s
      have e : a1 + s • v = a0 + (t1 + s) • v := by rw [ha1, add_smul, add_assoc]
      rw [e, hl, hR1eq]
      push_cast
      ring
    have hR1 : 0 < D.residual a1 (QuadraticGraphData.centreAt c0 C a1) := by rw [hR1eq]; exact ht1
    obtain ⟨z1, hz1⟩ := D.sr_solZ_of_total hTot a1
    by_cases hd : (B + 2 * A * t1) ^ 2 - 4 * A * D.residual a1 (QuadraticGraphData.centreAt c0 C a1) = 0
    · have := D.discriminantZero_line_const hm hpos hrank hOU c0 C hc a1 v z1 hz1 hR1 A (B + 2 * A * t1)
        hla (by linarith)
      linarith [this.1]
    · obtain ⟨t, z, z', hz, hz', hne⟩ := D.lineCollision_rankThree_of_TCER hT ⟨0, hm⟩ hpos (by omega) c0 C hc
        a1 v z1 hz1 hR1 A (B + 2 * A * t1) hla hA hd
      have := hOU _ _ _ (D.graph_of_solZ hz) (D.graph_of_solZ hz')
      exact hne (by simpa [outProj] using congrFun this ⟨0, hm⟩)

namespace QuadraticGraphData

variable {n m r : ℕ}

/-- **C3.4** (finite recognition).  Positive definite, polar rank ≥ 2, at least one output, an actual affine centre:
total and output-unique iff the residual is a constant `R₀` and, for an integral rescaling `M` of the centre and a
box bound `B` containing the shell `Q(y) = M²R₀`, every one of the `Mⁿ` residue shells has a one-point output
image. -/
theorem definiteShellCriterion_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation)
    (D : QuadraticGraphData n m r) (hm : 0 < m)
    (hpos : ∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) (hrank : 2 ≤ D.polarRank)
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hc : ∀ a, D.IsCentre a (centreAt c0 C a)) :
    (D.Total ∧ D.OutputUnique) ↔
      ∃ R0 : ℚ, (∀ a, D.residual a (centreAt c0 C a) = R0) ∧
        ∃ (M : ℕ) (e0 : OutWit m r → ℤ) (E : Matrix (OutWit m r) (Fin n) ℤ) (B : ℕ), 1 ≤ M ∧
          (∀ k, (e0 k : ℚ) = (M : ℚ) * c0 k) ∧ (∀ k i, (E k i : ℚ) = (M : ℚ) * C k i) ∧
          (∀ y : OutWit m r → ℤ, D.zQuadQ (toQ y) = (M : ℚ) ^ 2 * R0 → ∀ k, |y k| ≤ B) ∧
          ∀ ρ : Fin n → Fin M,
            ((D.residueShell B ((M : ℚ) ^ 2 * R0) M e0 E (fun i => ((ρ i : ℕ) : ℤ))).image
              outProj).card = 1 := by
  classical
  have hMpos_of : ∀ M : ℕ, 1 ≤ M → (0 : ℤ) < M := fun M hM => by exact_mod_cast (show 0 < M by omega)
  constructor
  · rintro ⟨hTot, hOU⟩
    obtain ⟨R0, hR⟩ := ccr_of_TCER hT n m r D c0 C hm hpos hrank hc hTot hOU
    obtain ⟨M, e0, E, hM, he0, hE, -⟩ := D.shellEquiv c0 C R0 hc hR
    obtain ⟨h, h0, hh⟩ := D.definite_coord_sq_le hpos
    have hB : ∀ y : OutWit m r → ℤ, D.zQuadQ (toQ y) = (M : ℚ) ^ 2 * R0 →
        ∀ k, |y k| ≤ ((⌈h * max ((M : ℚ) ^ 2 * R0) 0⌉₊ + 1 : ℕ) : ℤ) :=
      fun y hy k => D.definiteShell_bound h0 hh _ hy k
    refine ⟨R0, hR, M, e0, E, ⌈h * max ((M : ℚ) ^ 2 * R0) 0⌉₊ + 1, hM, he0, hE, hB, fun ρ => ?_⟩
    obtain ⟨f, hf⟩ := (D.exists_defines_iff).mpr ⟨hTot, hOU⟩
    have hrepr : (fun i => ((ρ i : ℕ) : ℤ)) = (fun i => ((fun i => ((ρ i : ℕ) : ℤ)) i) % M) := by
      funext i
      exact (Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (ρ i).isLt)).symm
    rw [hrepr, D.shellImage_eq_value hpos c0 C R0 hc hR M hM e0 E he0 hE _ hB hf]
    exact Finset.card_singleton _
  · rintro ⟨R0, hR, M, e0, E, B, hM, he0, hE, hB, hcard⟩
    have hMpos := hMpos_of M hM
    have key : ∀ a : Fin n → ℤ, ∃ ρ : Fin n → Fin M,
        (fun i => ((ρ i : ℕ) : ℤ)) = fun i => a i % M := by
      intro a
      refine ⟨fun i => ⟨(a i % M).toNat, ?_⟩, ?_⟩
      · have h1 := Int.emod_lt_of_pos (a i) hMpos
        have h2 := Int.emod_nonneg (a i) (ne_of_gt hMpos)
        omega
      · funext i
        exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hMpos))
    have hsol : ∀ a : Fin n → ℤ, ∃ v, (D.residueShell B ((M : ℚ) ^ 2 * R0) M e0 E
        (fun i => a i % M)).image outProj = {v} := by
      intro a
      obtain ⟨ρ, hρ⟩ := key a
      have hc' := hcard ρ
      rw [hρ] at hc'
      exact Finset.card_eq_one.mp hc'
    refine ⟨fun a => ?_, fun a b b' hb hb' => ?_⟩
    · obtain ⟨v, hv⟩ := hsol a
      have hvm : v ∈ (D.residueShell B ((M : ℚ) ^ 2 * R0) M e0 E
          (fun i => a i % M)).image outProj := by rw [hv]; exact Finset.mem_singleton_self _
      obtain ⟨y, hy, -⟩ := Finset.mem_image.mp hvm
      simp only [residueShell, shellFinset, Finset.mem_filter] at hy
      obtain ⟨⟨_, hq⟩, hd⟩ := hy
      obtain ⟨e, -, -⟩ := D.shellEquiv_of c0 C R0 hc hR M hM e0 E he0 hE a
      have hz := (e.symm ⟨y, hq, (sc_cong M e0 E a y).mp hd⟩).2
      exact ⟨_, D.graph_of_solZ hz⟩
    · obtain ⟨v, hv⟩ := hsol a
      obtain ⟨e, he, -⟩ := D.shellEquiv_of c0 C R0 hc hR M hM e0 E he0 hE a
      have img : ∀ (c : Fin m → ℤ), D.Graph a c →
          (fun j => (M : ℤ) * c j - (e0 + E *ᵥ a) (Sum.inl j)) = v := by
        intro c hc'
        obtain ⟨u, hu⟩ := hc'
        have hz : D.SolZ a (Sum.elim c u) := (D.solZ_iff_sol a c u).mpr hu
        have hmem : outProj (e ⟨_, hz⟩).1 ∈ (D.residueShell B ((M : ℚ) ^ 2 * R0) M e0 E
            (fun i => a i % M)).image outProj := by
          refine Finset.mem_image.mpr ⟨(e ⟨_, hz⟩).1, ?_, rfl⟩
          simp only [residueShell, shellFinset, Finset.mem_filter, Fintype.mem_piFinset,
            Finset.mem_Icc]
          exact ⟨⟨fun k => abs_le.mp (hB _ (e ⟨_, hz⟩).2.1 k), (e ⟨_, hz⟩).2.1⟩,
            (sc_cong M e0 E a _).mpr (e ⟨_, hz⟩).2.2⟩
        rw [hv, Finset.mem_singleton, he] at hmem
        rw [← hmem]
        funext j
        simp [outProj]
      have e1 := img b hb
      have e2 := img b' hb'
      funext j
      have := congrFun (e1.trans e2.symm) j
      have hM0 : (M : ℤ) ≠ 0 := ne_of_gt hMpos
      exact mul_left_cancel₀ hM0 (by linarith)

end QuadraticGraphData

/-- **C3.2** (positive definite, common slope).  TCER ⇒ every positive definite datum of polar rank ≥ 2 with an
output that defines `f` gives `f` one integer slope on all residue classes of one modulus. -/
theorem definiteCommonSlopeNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) → 2 ≤ D.polarRank → D.Defines f →
        CommonSlopeIntNF f := by
  intro n m r D f hm hpos hrank hf
  obtain ⟨c0, C, hcen⟩ := D.definite_exists_centreAt hpos
  have hTot : D.Total := fun a => ⟨f a, (hf a (f a)).mpr rfl⟩
  obtain ⟨R0, hR⟩ := ccr_of_TCER hT n m r D c0 C hm hpos hrank hcen hTot (D.outputUnique_of_defines hf)
  exact D.constResidual_commonSlopeIntNF c0 C R0 hcen hR hf

/-- **C3.3** (semidefinite full NF, polar rank ≥ 2, either sign, conditional). -/
theorem semidefiniteFullNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) →
      ((∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) ∨ (∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0)) →
      2 ≤ D.polarRank → D.Defines f → FullVectorCosetNF f := by
  intro n m r D f hm hQ hsemi hrank hf
  have key : ∀ (D : QuadraticGraphData n m r), (∃ v, D.zQuad v ≠ 0) → (∀ u, 0 ≤ D.zQuadQ u) →
      2 ≤ D.polarRank → D.Defines f → FullVectorCosetNF f := by
    intro D hQ hnn hrank hf
    obtain ⟨U, hU, hdef, hpr, hpd⟩ := D.definite_reduction hm hf hQ hnn
    exact fullVectorCosetNF_of_commonSlope
      (definiteCommonSlopeNF_of_TCER hT n m _ (D.compiledData U) f hm hpd (by rw [hpr]; exact hrank) hdef)
  rcases hsemi with hnn | hnp
  · exact key D hQ hnn hrank hf
  · refine key D.negGraph ?_ ?_ ?_ (D.negGraph_defines hf)
    · obtain ⟨v, hv⟩ := hQ; exact ⟨v, by rw [D.negGraph_zQuad]; omega⟩
    · intro u; rw [D.negGraph_zQuadQ]; linarith [hnp u]
    · rw [D.negGraph_polarRank]; exact hrank

/-- **C4** (general weak NF, conditional).  TCER ⇒ `GeneralWeakNF`. -/
theorem generalWeakNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) : GeneralWeakNF := by
  rw [generalWeakNF_iff_residualReflectionObstructionNF]
  intro n m r D f c0 C hm hpos hrank hcen hnc _ hf
  exact absurd (ccr_of_TCER hT n m r D c0 C hm hpos (by omega) hcen
    (fun a => ⟨f a, (hf a (f a)).mpr rfl⟩) (D.outputUnique_of_defines hf)) hnc

/-- **C4, sealed.**  TCER ⇒ every function in the ORIGINAL sealed class `SingleQuadraticDefinableFunctionZZ`
(any number of witnesses, total degree ≤ 2) has a weak vector coset normal form. -/
theorem sealedWeakNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      DiophCompression.SingleQuadraticDefinableFunctionZZ f → WeakVectorCosetNF f := by
  intro n m f hf
  obtain ⟨r, D, hD⟩ := graphData_of_singleQuadraticDefinable hf
  exact generalWeakNF_of_TCER hT n m r D f hD

end DiophCompression.ResearchUpgrade
