/-
  CommonSlopeForward.lean — s58.  GPT R46 Packets A4 and B1–B4 (GATE28): the forward direction of the multi-output
  classification.  For m ≥ 2, TCER ⇒ every SE₂ function has ONE integer slope on all residue classes.

  * `false_of_isotropic_of_three_le_polarRank` (A4) — isotropic, polar rank ≥ 3: an input with an actual centre has no
    integer solution at all (the s57 off-radical theorem, extended to the radical side by a shift `z + N e₀`).
  * `isotropic_three_le_polarRank_not_defines` — hence that branch is empty for functions with an output.
  * `intAffine_of_ratAffine`, `commonSlopeIntNF_of_ratAffine`, `commonSlopeIntNF_of_offCentre_radical` (B3) — a rational
    global affine form of an integer-valued f has integer coefficients f 0, f eᵢ − f 0.
  * `isotropicRankTwoCommonSlope_holds` (B2), `anisotropicIndefiniteCommonSlope_holds` (B3): unconditional.
  * `semidefiniteCommonSlopeNF_of_TCER` (B1), `commonSlopeNF_of_TCER_of_two_le`, `sealedCommonSlopeNF_of_TCER` (B4): [C].

  Statements frozen before proof (`~/lean/s58_evidence/freeze/G1_FREEZE_s58.lean`, ruling of Dr. Fukui
  2026-09-26 13:07).  Claim tags: [P] (std-3) except the last three, [C] (TCER as an explicit hypothesis).
-/
import ResearchUpgrade.GeneralFullNF
import ResearchUpgrade.FullNFExtraction
import ResearchUpgrade.IsotropicEichler
import ResearchUpgrade.TCERCapstones
import ResearchUpgrade.RankExcessCompiler
import ResearchUpgrade.LinearFibre
import ResearchUpgrade.BranchSplit

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- **A4.**  Isotropic, polar rank ≥ 3, an output coordinate, output uniqueness and an actual centre at the input `a`:
the input `a` has NO integer solution. -/
theorem false_of_isotropic_of_three_le_polarRank (hm : 0 < m) (hOU : D.OutputUnique)
    {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    {z : OutWit m r → ℤ} (hz : D.SolZ a z)
    {e₀ : OutWit m r → ℚ} (he₀q : D.zQuadQ e₀ = 0) (he₀ : ¬ D.InRadicalQ e₀)
    (hrank : 3 ≤ D.polarRank) : False := by
  by_cases hx : D.InRadicalQ (toQ z - c)
  · obtain ⟨N, hN, hg⟩ := cr_exists_common_den e₀
    choose g hg using hg
    have e1 : toQ (z + g) - c = (toQ z - c) + (N : ℚ) • e₀ := by
      funext k
      simp only [toQ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add, hg k]
      ring
    have hpol : D.zPolarQ (toQ z - c) e₀ = 0 := hx e₀
    have hQ : D.zQuadQ (toQ (z + g) - c) = D.zQuadQ (toQ z - c) := by
      rw [e1, D.zQuadQ_add_smul, hpol, he₀q]; ring
    have hz' : D.SolZ a (z + g) := by
      rw [D.sr_solZ_iff hc, hQ]; exact (D.sr_solZ_iff hc z).mp hz
    have hx' : ¬ D.InRadicalQ (toQ (z + g) - c) := by
      intro h
      apply he₀
      intro w
      have h1 := h w
      rw [e1, D.zPolarQ_add_left, hx w, D.zPolarQ_smul_left, zero_add] at h1
      have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      exact (mul_eq_zero.mp h1).resolve_left hN0
    exact D.false_of_offRadical_of_three_le_polarRank hm hOU hc hz' hx' he₀q he₀ hrank
  · exact D.false_of_offRadical_of_three_le_polarRank hm hOU hc hz hx he₀q he₀ hrank

end QuadraticGraphData

/-- **B3, integral coefficients.**  A rational global affine form of an integer-valued `f` has integer
coefficients: the intercept is `f 0` and the `i`-th column is `f eᵢ − f 0`. -/
theorem intAffine_of_ratAffine {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (c₀ : Fin m → ℚ) (cs : Fin n → Fin m → ℚ)
    (h : ∀ (a : Fin n → ℤ) (j : Fin m), ((f a j : ℤ) : ℚ) = c₀ j + ∑ i, (a i : ℚ) * cs i j) :
    (∀ j, ((f 0 j : ℤ) : ℚ) = c₀ j) ∧
    (∀ i j, ((f (Pi.single i 1) j - f 0 j : ℤ) : ℚ) = cs i j) ∧
    ∀ a : Fin n → ℤ, f a = f 0 + (Matrix.of fun j i => f (Pi.single i 1) j - f 0 j) *ᵥ a := by
  have h0 : ∀ j, ((f 0 j : ℤ) : ℚ) = c₀ j := by
    intro j; simpa using h 0 j
  have h1 : ∀ i j, ((f (Pi.single i 1) j - f 0 j : ℤ) : ℚ) = cs i j := by
    intro i j
    have := h (Pi.single i 1) j
    push_cast
    rw [this, h0 j]
    simp [Pi.single_apply]
  refine ⟨h0, h1, fun a => ?_⟩
  funext j
  have key : ((f a j : ℤ) : ℚ)
      = (((f 0 + (Matrix.of fun j i => f (Pi.single i 1) j - f 0 j) *ᵥ a) j : ℤ) : ℚ) := by
    rw [h a j]
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Int.cast_add, Int.cast_sum,
      Int.cast_mul]
    rw [h0 j]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 i j]
    ring
  exact_mod_cast key

/-- **B3, packaged.**  A rational global affine form gives `CommonSlopeIntNF` with modulus 1. -/
theorem commonSlopeIntNF_of_ratAffine {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (c₀ : Fin m → ℚ) (cs : Fin n → Fin m → ℚ)
    (h : ∀ (a : Fin n → ℤ) (j : Fin m), ((f a j : ℤ) : ℚ) = c₀ j + ∑ i, (a i : ℚ) * cs i j) :
    CommonSlopeIntNF f := by
  obtain ⟨-, -, hA⟩ := intAffine_of_ratAffine c₀ cs h
  refine ⟨1, Matrix.of fun j i => f (Pi.single i 1) j - f 0 j, le_refl 1, fun a t => ?_⟩
  rw [hA (a + ((1 : ℕ) : ℤ) • t), hA a]
  simp [Matrix.mulVec_add, add_assoc]

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- **B3, branch form.**  Every solution off-centre radical ⇒ one integer slope with modulus 1. -/
theorem commonSlopeIntNF_of_offCentre_radical
    (hm : 0 < m) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
      D.InRadicalQ (toQ z - centreFamily c₀ cs a)) :
    CommonSlopeIntNF f :=
  commonSlopeIntNF_of_ratAffine (fun j => c₀ (Sum.inl j)) (fun i j => cs i (Sum.inl j))
    (D.affine_of_offCentre_radical hm hQ hf hrad)

end QuadraticGraphData

/-- **A4, consequence.**  In the isotropic branch of polar rank ≥ 3 no datum with an output coordinate defines a
function: the branch is empty. -/
theorem isotropic_three_le_polarRank_not_defines :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ x : OutWit m r → ℚ, D.zQuadQ x = 0 ∧ ¬ D.InRadicalQ x) → 3 ≤ D.polarRank →
      ¬ D.Defines f := by
  classical
  intro n m r D f hm ⟨e₀, he₀q, he₀⟩ hrank hf
  have hQ : ∃ x : OutWit m r → ℤ, D.zQuad x ≠ 0 := by
    refine D.exists_int_zQuad_ne_zero (fun h => he₀ (fun w => ?_))
    have := D.zQuadQ_add e₀ w
    rw [h, h, h] at this
    linarith
  have hOU := D.outputUnique_of_defines hf
  have hall : ∀ (a : Fin n → ℤ) (e : OutWit m r → ℚ), D.InRadicalQ e → D.zLinQ a e = 0 := by
    intro a e he
    obtain ⟨z, hz⟩ := D.exists_solZ_of_defines hf a
    exact D.zLinQ_radicalQ_eq_zero hm hOU hz hQ he
  obtain ⟨c₀, cs, hcen⟩ := D.exists_affine_centre_of_all_inputs hall
  obtain ⟨z, hz⟩ := D.exists_solZ_of_defines hf 0
  exact D.false_of_isotropic_of_three_le_polarRank hm hOU (hcen 0) hz he₀q he₀ hrank

/-- **B2.**  Split isotropic branch, polar rank ≤ 2: one integer slope on all residue classes (unconditional). -/
theorem isotropicRankTwoCommonSlope_holds :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ x : OutWit m r → ℚ, D.zQuadQ x = 0 ∧ ¬ D.InRadicalQ x) → D.polarRank ≤ 2 →
      D.Defines f → CommonSlopeIntNF f := by
  classical
  intro n m r D f hm ⟨e₀, he₀q, he₀⟩ hrank hf
  have hQ : ∃ x : OutWit m r → ℤ, D.zQuad x ≠ 0 := by
    refine D.exists_int_zQuad_ne_zero (fun h => he₀ (fun w => ?_))
    have := D.zQuadQ_add e₀ w
    rw [h, h, h] at this
    linarith
  have hOU := D.outputUnique_of_defines hf
  have hall : ∀ (a : Fin n → ℤ) (e : OutWit m r → ℚ), D.InRadicalQ e → D.zLinQ a e = 0 := by
    intro a e he
    obtain ⟨z, hz⟩ := D.exists_solZ_of_defines hf a
    exact D.zLinQ_radicalQ_eq_zero hm hOU hz hQ he
  obtain ⟨c₀, cs, hcen⟩ := D.exists_affine_centre_of_all_inputs hall
  have hcen' : ∀ a : Fin n → ℤ, D.IsCentre a (centreFamily c₀ cs a) := hcen
  obtain ⟨R0, hR⟩ := D.constResidual_of_isotropic_polarRank_le_two hm hf he₀q he₀ hrank c₀ cs hcen'
  let C : Matrix (OutWit m r) (Fin n) ℚ := fun k i => cs i k
  have hCF : ∀ a, centreFamily c₀ cs a = QuadraticGraphData.centreAt c₀ C a := by
    intro a; funext k
    simp [centreFamily, QuadraticGraphData.centreAt, C, Finset.sum_apply, mul_comm]
  exact D.constResidual_commonSlopeIntNF c₀ C R0 (fun a => by rw [← hCF]; exact hcen' a)
    (fun a => by rw [← hCF]; exact hR a) hf

/-- **B3, the quotient-anisotropic indefinite branch.**  One integer slope, modulus 1 (unconditional). -/
theorem anisotropicIndefiniteCommonSlope_holds :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∀ x : OutWit m r → ℚ, D.zQuadQ x = 0 → D.InRadicalQ x) →
      (∃ p, 0 < D.zQuadQ p) → (∃ q, D.zQuadQ q < 0) → D.Defines f → CommonSlopeIntNF f := by
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
  exact D.commonSlopeIntNF_of_offCentre_radical hm hQ hf hrad

/-- **B1.**  TCER ⇒ non-zero semidefinite (either sign), polar rank ≥ 2: one integer slope on all residue classes. -/
theorem semidefiniteCommonSlopeNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      0 < m → (∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) →
      ((∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) ∨ (∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0)) →
      2 ≤ D.polarRank → D.Defines f → CommonSlopeIntNF f := by
  intro n m r D f hm hQ hsemi hrank hf
  have key : ∀ (D : QuadraticGraphData n m r), (∃ v, D.zQuad v ≠ 0) → (∀ u, 0 ≤ D.zQuadQ u) →
      2 ≤ D.polarRank → D.Defines f → CommonSlopeIntNF f := by
    intro D hQ hnn hrank hf
    obtain ⟨U, hU, hdef, hpr, hpd⟩ := D.definite_reduction hm hf hQ hnn
    exact definiteCommonSlopeNF_of_TCER hT n m _ (D.compiledData U) f hm hpd (by rw [hpr]; exact hrank) hdef
  rcases hsemi with hnn | hnp
  · exact key D hQ hnn hrank hf
  · refine key D.negGraph ?_ ?_ ?_ (D.negGraph_defines hf)
    · obtain ⟨v, hv⟩ := hQ; exact ⟨v, by rw [D.negGraph_zQuad]; omega⟩
    · intro u; rw [D.negGraph_zQuadQ]; linarith [hnp u]
    · rw [D.negGraph_polarRank]; exact hrank

/-- **B4, data form.**  TCER ⇒ for m ≥ 2 every datum that defines `f` gives `CommonSlopeIntNF f`. -/
theorem commonSlopeNF_of_TCER_of_two_le (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
      2 ≤ m → D.Defines f → CommonSlopeIntNF f := by
  intro n m r D f hm2 hf
  have hm : 0 < m := by omega
  by_cases hz : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0
  · exfalso
    have hpol := D.zPolar_eq_zero_of_zQuadQ_zero hz
    obtain ⟨z, hz0⟩ := D.exists_solZ_of_defines hf 0
    obtain ⟨-, hle⟩ := D.m_le_one_of_linear hpol (D.outputUnique_of_defines hf) hz0 hm
    omega
  have hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0 := D.exists_int_zQuad_ne_zero hz
  have hrank : 2 ≤ D.polarRank := le_trans hm2 (D.m_le_polarRank hm hf hQ)
  rcases D.branch_exhaustive with h1 | ⟨x, hx0, hxr⟩ | ⟨hqa, hsd | hsd' | ⟨hp, hq⟩⟩
  · exact absurd h1 hz
  · rcases Nat.lt_or_ge 2 D.polarRank with h3 | h2
    · exact absurd hf (isotropic_three_le_polarRank_not_defines n m r D f hm ⟨x, hx0, hxr⟩ h3)
    · exact isotropicRankTwoCommonSlope_holds n m r D f hm ⟨x, hx0, hxr⟩ h2 hf
  · exact semidefiniteCommonSlopeNF_of_TCER hT n m r D f hm hQ (Or.inl hsd) hrank hf
  · exact semidefiniteCommonSlopeNF_of_TCER hT n m r D f hm hQ (Or.inr hsd') hrank hf
  · exact anisotropicIndefiniteCommonSlope_holds n m r D f hm hqa hp hq hf

/-- **B4, sealed.**  TCER ⇒ every function `ℤⁿ → ℤᵐ`, m ≥ 2, in the ORIGINAL class `SingleQuadraticDefinableFunctionZZ`
has one modulus `M` and one integer matrix `B` with `f (a + M t) = f a + B t` for all `a, t`. -/
theorem sealedCommonSlopeNF_of_TCER (hT : TCERBridge.TernaryCosetEventualRepresentation) :
    ∀ (n m : ℕ) (f : (Fin n → ℤ) → (Fin m → ℤ)), 2 ≤ m →
      DiophCompression.SingleQuadraticDefinableFunctionZZ f → CommonSlopeIntNF f := by
  intro n m f hm2 hf
  obtain ⟨r, D, hD⟩ := graphData_of_singleQuadraticDefinable hf
  exact commonSlopeNF_of_TCER_of_two_le hT n m r D f hm2 hD

end DiophCompression.ResearchUpgrade
