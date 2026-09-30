/-
  IsotropicBranch.lean — s48.  The isotropic branch of II-D, made SELF-CONTAINED.

  `dim_le_of_isotropic` (G22-T12) takes the centre family, the integer solution and the visible
  isotropic direction as inputs.  Each is now available: the centre from
  `exists_affine_centre_of_all_inputs` (G22-T06 §3.1 + G22-T04), the direction from
  `exists_isotropic_nonorthogonal_of_nonradical` (G22-T10).  What was missing is the case analysis
  the reviewer's §5.2 ends with, and it is not a formality:

   * if SOME integer solution has a non-radical off-centre part, the isotropic machinery applies;
   * if EVERY off-centre part is radical, then `π` kills it (G22-T04) and `f = π∘h` is AFFINE,
     hence of linear growth, and the counting theorem closes it directly.

  Note that the second case does NOT use the branch condition at all, and that `Q(v) = 0` would
  NOT be enough in its place — isotropic is weaker than radical, which is exactly why the
  quotient-anisotropic branch exists as a separate case.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.IsotropicCoset
import ResearchUpgrade.IsotropicSection
import ResearchUpgrade.LinearGrowthDimension
import ResearchUpgrade.OutputGrowth
import ResearchUpgrade.PolarAnnihilator

namespace DiophCompression.ResearchUpgrade

/-- A uniform rational bound on the output gives `LinearGrowth`.  Extracted so that the affine
case below does not have to repeat the cast bookkeeping of G22-T08. -/
theorem linearGrowth_of_bound {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)} (C : ℚ)
    (h : ∀ (a : Fin n → ℤ) (j : Fin m), |((f a j : ℤ) : ℚ)| ≤ C * growthArg a) :
    LinearGrowth f := by
  refine ⟨⌈C⌉₊, fun a => ?_⟩
  have hN0 := growthArg_nonneg a
  simp only [supNorm]
  refine Finset.sup_le fun j _ => ?_
  have h1 : ((f a j).natAbs : ℚ) = |((f a j : ℤ) : ℚ)| := by
    have h0 := congrArg (fun t : ℤ => (t : ℚ)) (Int.natCast_natAbs (f a j))
    push_cast at h0
    simpa using h0
  have h5 : ((⌈C⌉₊ * (1 + supNorm a) : ℕ) : ℚ) = (⌈C⌉₊ : ℚ) * growthArg a := by
    simp only [growthArg]
    push_cast
    ring
  have hq : ((f a j).natAbs : ℚ) ≤ ((⌈C⌉₊ * (1 + supNorm a) : ℕ) : ℚ) := by
    rw [h1, h5]
    have h3 : C ≤ (⌈C⌉₊ : ℚ) := Nat.le_ceil _
    have h4 := mul_le_mul_of_nonneg_right h3 hN0
    linarith [h a j]
  exact_mod_cast hq

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- **The affine case.**  If every integer solution sits at a radical distance from the centre,
the output IS the centre's output — affine in the input — so `f` has linear growth. -/
theorem linearGrowth_of_offCentre_radical
    (hm : 0 < m) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
      D.InRadicalQ (toQ z - centreFamily c₀ cs a)) :
    LinearGrowth f := by
  have hOU := D.outputUnique_of_defines hf
  refine linearGrowth_of_bound (centreCoeffSum c₀ cs) ?_
  intro a j
  obtain ⟨u, hu⟩ : D.Graph a (f a) := (hf a (f a)).mpr rfl
  have hz : D.SolZ a (Sum.elim (f a) u) := hu
  have he := hrad a (Sum.elim (f a) u) hz
  have hzero := D.outCoordQ_radicalQ_eq_zero hm hOU hz hQ he j
  have hval : ((f a j : ℤ) : ℚ) = (centreFamily c₀ cs a) (Sum.inl j) := by
    have h2 : ((f a j : ℤ) : ℚ) - (centreFamily c₀ cs a) (Sum.inl j) = 0 := hzero
    linarith
  rw [hval]
  exact abs_centre_le c₀ cs a (Sum.inl j)

/-- **The isotropic branch of II-D, self-contained.**  `0 < m`, `Q ≠ 0`, and the branch condition
(a non-radical isotropic vector exists) give `n ≤ m` for any injective function the graph defines.
The centre family, the visible isotropic direction, the section, the modulus and the normal form
are all produced inside. -/
theorem dim_le_of_isotropic_defines
    (hm : 0 < m) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {e₀ : OutWit m r → ℚ} (he₀q : D.zQuadQ e₀ = 0) (he₀ : ¬ D.InRadicalQ e₀)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (hinj : Function.Injective f) :
    n ≤ m := by
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
    exact D.dim_le_of_isotropic hf hinj hcen' hz₀ he hb
  · have hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
        D.InRadicalQ (toQ z - centreFamily c₀ cs a) := by
      intro a z hz
      by_contra hcon
      exact hcase ⟨a, z, hz, hcon⟩
    exact dim_le_of_linearGrowth_injective
      (D.linearGrowth_of_offCentre_radical hm hQ hf hrad) hinj

/-! ### Controls -/

/-- POSITIVE control: the affine case is reachable and not vacuous — `idGraph n` has every
solution AT the centre (its output is determined outright), so the second case of the split is
inhabited. -/
theorem linearGrowth_id (n : ℕ) : LinearGrowth (id : (Fin n → ℤ) → (Fin n → ℤ)) := by
  refine ⟨1, fun a => ?_⟩
  simp only [id]
  omega

/-- NEGATIVE control, and the reason the quotient-anisotropic branch has to exist separately:
`Q(v) = 0` does NOT imply `v ∈ rad(Q)`.  So the case split above cannot be made on the value of the
form; it has to be made on radicality. -/
theorem isotropic_not_radical_possible :
    ∃ (D' : QuadraticGraphData 1 1 1) (v : OutWit 1 1 → ℚ),
      D'.zQuadQ v = 0 ∧ ¬ D'.InRadicalQ v := by
  classical
  refine ⟨⟨⟨0, 0, fun x y =>
      match x, y with
      | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => 1
      | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => 1
      | _, _ => 0⟩⟩,
    fun k => match k with | Sum.inl _ => 1 | Sum.inr _ => 0, ?_, ?_⟩
  · simp [QuadraticGraphData.zQuadQ, Fintype.sum_sum_type]
  · intro hcon
    have := hcon (fun k => match k with | Sum.inl _ => 0 | Sum.inr _ => 1)
    simp [QuadraticGraphData.zPolarQ, Fintype.sum_sum_type] at this

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
