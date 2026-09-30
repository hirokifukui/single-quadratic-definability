/-
  B2 (R40-B2) — the general weak vector normal form, reduced to the semidefinite residue.

  What is proved here is a REDUCTION, not the general conjecture.  `GeneralWeakNF` (every graph
  that defines a function has a weak vector coset normal form) is shown EQUIVALENT to
  `SemidefiniteWeakNF`, its restriction to `0 ≤ Q` with `Q ≠ 0` and `m ≥ 1`.  Both directions:

  * forward — trivial, the semidefinite statement is a special case;
  * backward — the branches of `branch_exhaustive` are discharged as follows.
      `Q ≡ 0`                     `weakVectorCosetNF_of_linearBranch_general`  (existing)
      isotropic, off-centre       `weakVectorCosetNF_of_isotropic`             (existing)
      isotropic, all radical      `fullVectorCosetNF_of_offCentre_radical`     (B1, s51)
      quotient-anisotropic        `fullVectorCosetNF_of_offCentre_radical`     (B1, s51)
      `Q ≤ 0`                     `negGraph`, then the semidefinite hypothesis
      `0 ≤ Q`, `Q ≠ 0`            the hypothesis itself
      `m = 0`                     `weakVectorCosetNF_of_m_zero`                (existing)

  Two branches that r40 sent LEFT (to `LinearGrowth`) now land RIGHT, and that is exactly what
  B1 bought: the information was already inside those proofs.  `LinearGrowth → WeakNF` is NOT
  used anywhere and is not true in general (the `⌊√2 x⌋` control of Packet D).

  SCOPE.  This says nothing about the FULL-residue normal form.  The isotropic branch still
  returns ONE coset, so the uniform all-classes statement is a different question and is not
  reduced here.  Any wrapper assuming `SemidefiniteWeakNF` is CONDITIONAL: the general conjecture
  remains open.

  s51.
-/
import ResearchUpgrade.Summit
import ResearchUpgrade.DimensionII_D
import ResearchUpgrade.AffineNormalForm

namespace DiophCompression.ResearchUpgrade

/-- The general target: every quadratic graph that defines a function has a weak vector coset
normal form.  OPEN. -/
def GeneralWeakNF : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
    D.Defines f → WeakVectorCosetNF f

/-- The residue: the same statement for a semidefinite, non-zero form with at least one output.
OPEN. -/
def SemidefiniteWeakNF : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
    0 < m → (∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) →
    (∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) → D.Defines f → WeakVectorCosetNF f

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- The isotropic branch, landing RIGHT in BOTH sub-cases.  r40 sent the radical fallback LEFT;
B1 shows it carries an affine normal form with modulus 1. -/
theorem weakVectorCosetNF_of_isotropicBranch
    (hm : 0 < m) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {e₀ : OutWit m r → ℚ} (he₀q : D.zQuadQ e₀ = 0) (he₀ : ¬ D.InRadicalQ e₀)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    WeakVectorCosetNF f := by
  classical
  have hOU := D.outputUnique_of_defines hf
  have hall : ∀ (a : Fin n → ℤ) (e : OutWit m r → ℚ), D.InRadicalQ e → D.zLinQ a e = 0 := by
    intro a e he
    obtain ⟨z₀, hz⟩ := D.exists_solZ_of_defines hf a
    exact D.zLinQ_radicalQ_eq_zero hm hOU hz hQ he
  obtain ⟨c₀, cs, hcen⟩ := D.exists_affine_centre_of_all_inputs hall
  have hcen' : ∀ a : Fin n → ℤ, D.IsCentre a (centreFamily c₀ cs a) := hcen
  by_cases hcase : ∃ (a₀ : Fin n → ℤ) (z₀ : OutWit m r → ℤ),
      D.SolZ a₀ z₀ ∧ ¬ D.InRadicalQ (toQ z₀ - centreFamily c₀ cs a₀)
  · obtain ⟨a₀, z₀, hz₀, hv₀⟩ := hcase
    obtain ⟨e, he, hb⟩ := D.exists_isotropic_nonorthogonal_of_nonradical he₀q he₀ hv₀
    exact D.weakVectorCosetNF_of_isotropic hf hcen' hz₀ he hb
  · have hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
        D.InRadicalQ (toQ z - centreFamily c₀ cs a) := by
      intro a z hz
      by_contra hcon
      exact hcase ⟨a, z, hz, hcon⟩
    exact D.fullVectorCosetNF_of_isotropic_fallback hm hQ hf hrad

/-- The quotient-anisotropic (Pell) branch, landing RIGHT, for the same reason. -/
theorem weakVectorCosetNF_of_quotientAnisotropicBranch
    (hm : 0 < m) (hQ : ∃ x : OutWit m r → ℤ, D.zQuad x ≠ 0)
    (hqa : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0 → D.InRadicalQ x)
    {pp qq : OutWit m r → ℚ} (hpp : 0 < D.zQuadQ pp) (hqq : D.zQuadQ qq < 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    WeakVectorCosetNF f := by
  classical
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
  exact D.fullVectorCosetNF_of_isotropic_fallback hm hQ hf hrad

/-- **B2, the reduction.**  CONDITIONAL on `SemidefiniteWeakNF`. -/
theorem weakVectorCosetNF_of_semidefiniteWeakNF (H : SemidefiniteWeakNF)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : WeakVectorCosetNF f := by
  classical
  by_cases hm0 : m = 0
  · subst hm0
    exact weakVectorCosetNF_of_m_zero
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  by_cases hz : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0
  · exact D.weakVectorCosetNF_of_linearBranch_general
      (D.zPolar_eq_zero_of_zQuadQ_zero hz) hf
  have hQ := D.exists_int_zQuad_ne_zero hz
  rcases D.branch_exhaustive with hz' | ⟨x, hx0, hxr⟩ | ⟨hqa, hcase⟩
  · exact absurd hz' hz
  · exact D.weakVectorCosetNF_of_isotropicBranch hmpos hQ hx0 hxr hf
  · rcases hcase with hpos | hneg | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    · exact H n m r D f hmpos hQ hpos hf
    · have hpos' : ∀ u : OutWit m r → ℚ, 0 ≤ D.negGraph.zQuadQ u := by
        intro u
        rw [D.negGraph_zQuadQ]
        linarith [hneg u]
      have hQ' : ∃ v : OutWit m r → ℤ, D.negGraph.zQuad v ≠ 0 := by
        obtain ⟨v, hv⟩ := hQ
        exact ⟨v, by rw [D.negGraph_zQuad]; omega⟩
      exact H n m r D.negGraph f hmpos hQ' hpos' (D.negGraph_defines hf)
    · exact D.weakVectorCosetNF_of_quotientAnisotropicBranch hmpos hQ hqa hp hq hf

end QuadraticGraphData

/-- **B2.**  The general weak vector normal form and its semidefinite restriction are EQUIVALENT.
Neither side is proved here; what is proved is that the open problem is exactly the semidefinite
one.  The other branches are closed unconditionally. -/
theorem generalWeakNF_iff_semidefiniteWeakNF : GeneralWeakNF ↔ SemidefiniteWeakNF := by
  constructor
  · intro H n m r D f _ _ _ hf
    exact H n m r D f hf
  · intro H n m r D f hf
    exact D.weakVectorCosetNF_of_semidefiniteWeakNF H hf

end DiophCompression.ResearchUpgrade
