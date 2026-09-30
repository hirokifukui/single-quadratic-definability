/-
  Summit.lean — s48.  **G22-T20, partial**: the summit disjunction
  `LinearGrowth f ∨ WeakVectorCosetNF f`.

  `dim_le_of_defines` splits into five branches and reaches `n ≤ m` in each.  The reviewer asks
  for the shape ONE level below that: each branch should land in one of the two disjuncts, and the
  dimension bound should then follow from the disjunction alone.  What is assembled here is that
  landing, for the branches whose piece exists:

    * `Q ≡ 0`                                     → RIGHT (`WeakVectorCosetNF`) — new here
    * `0 ≤ Q`  (semidefinite)                     → LEFT  (`LinearGrowth`)
    * `Q ≤ 0`  (negative semidefinite)            → LEFT, via `negGraph` — new here
    * every off-centre part radical (Pell branch) → LEFT
    * an isotropic direction seen from a centre   → RIGHT (`WeakVectorCosetNF`)

  and `dim_le_of_summit`, which closes `n ≤ m` from the disjunction — the left disjunct by T09's
  counting, the right by the same counting after the coset normal form.

  WHAT IS NOT HERE, and is named rather than hidden:
    * the isotropic and Pell branches are stated here with their DATA as hypotheses; the
      constructions that produce that data from `Defines f` alone live inside
      `dim_le_of_isotropic_defines` and `dim_le_of_quotientAnisotropic_defines` and have not been
      factored out.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.BranchSplit
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.DimensionFromCoset
import ResearchUpgrade.DimensionII_D
import ResearchUpgrade.IsotropicBranch
import ResearchUpgrade.IsotropicCoset
import ResearchUpgrade.LinearBranchDimension
import ResearchUpgrade.LinearGrowthDimension
import ResearchUpgrade.PellBranch
import ResearchUpgrade.RadicalBridge

namespace DiophCompression.ResearchUpgrade

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- **The negative-semidefinite branch lands LEFT.**  Same zero set, opposite form: apply the
semidefinite theorem to `negGraph`. -/
theorem linearGrowth_of_negSemidefinite_defines
    (hm : 0 < m) (hneg : ∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : LinearGrowth f := by
  have hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.negGraph.zQuadQ u := by
    intro u; rw [D.negGraph_zQuadQ]; linarith [hneg u]
  have hQ' : ∃ v : OutWit m r → ℤ, D.negGraph.zQuad v ≠ 0 := by
    obtain ⟨v, hv⟩ := hQ
    exact ⟨v, by rw [D.negGraph_zQuad]; omega⟩
  exact D.negGraph.linearGrowth_of_semidefinite_defines hm hpos hQ' (D.negGraph_defines hf)

/-- **The `Q ≡ 0` branch at `m = 1` lands RIGHT.**  The coset normal form was already built inside
`dim_le_one_of_linearBranch`; it is factored out here so the summit can use it. -/
theorem weakVectorCosetNF_of_linearBranch {n' r' : ℕ} (D₁ : QuadraticGraphData n' 1 r')
    (hpol : ∀ v w : OutWit 1 r' → ℤ, D₁.zPolar v w = 0)
    {f : (Fin n' → ℤ) → (Fin 1 → ℤ)} (hf : D₁.Defines f) : WeakVectorCosetNF f := by
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
  refine weakVectorCosetNF_of_scalar ?_
  rw [← hfn]
  exact nInputNoWitness_weak D₁.lbA D₁.lbBeta D₁.lbD D₁.lbE D₁.lbPhi D₁.lbG hT hU

/-- With no output coordinates the coset normal form is vacuous. -/
theorem weakVectorCosetNF_of_m_zero {n' : ℕ} {f : (Fin n' → ℤ) → (Fin 0 → ℤ)} :
    WeakVectorCosetNF f :=
  ⟨1, 0, fun j => j.elim0, le_refl 1, fun _ j => j.elim0⟩

/-- **The `Q ≡ 0` branch lands RIGHT at every `m`.**  `m = 0` is vacuous, `m = 1` is the theorem
above, and `m ≥ 2` is impossible in this branch. -/
theorem weakVectorCosetNF_of_linearBranch_general
    (hpol : ∀ v w : OutWit m r → ℤ, D.zPolar v w = 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) : WeakVectorCosetNF f := by
  classical
  match m, D, f, hf with
  | 0, _, _, _ => exact weakVectorCosetNF_of_m_zero
  | 1, D, f, hf => exact D.weakVectorCosetNF_of_linearBranch hpol hf
  | (k + 2), D, f, hf =>
      exfalso
      obtain ⟨z, hz⟩ := D.exists_solZ_of_defines hf 0
      obtain ⟨-, hle⟩ :=
        D.m_le_one_of_linear hpol (D.outputUnique_of_defines hf) hz (by omega)
      omega

/-! ### The five landings -/

theorem summit_of_qZero
    (hpol : ∀ v w : OutWit m r → ℤ, D.zPolar v w = 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    LinearGrowth f ∨ WeakVectorCosetNF f :=
  Or.inr (D.weakVectorCosetNF_of_linearBranch_general hpol hf)


theorem summit_of_semidefinite
    (hm : 0 < m) (hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    LinearGrowth f ∨ WeakVectorCosetNF f :=
  Or.inl (D.linearGrowth_of_semidefinite_defines hm hpos hQ hf)

theorem summit_of_negSemidefinite
    (hm : 0 < m) (hneg : ∀ u : OutWit m r → ℚ, D.zQuadQ u ≤ 0)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    LinearGrowth f ∨ WeakVectorCosetNF f :=
  Or.inl (D.linearGrowth_of_negSemidefinite_defines hm hneg hQ hf)

theorem summit_of_offCentre_radical
    (hm : 0 < m) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
      D.InRadicalQ (toQ z - centreFamily c₀ cs a)) :
    LinearGrowth f ∨ WeakVectorCosetNF f :=
  Or.inl (D.linearGrowth_of_offCentre_radical hm hQ hf hrad)

theorem summit_of_isotropic
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    (hcen : ∀ a : Fin n → ℤ, D.IsCentre a (centreFamily c₀ cs a))
    {a₀ : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hz₀ : D.SolZ a₀ z₀)
    {e : OutWit m r → ℚ} (he : D.zQuadQ e = 0)
    (hb : D.zPolarQ (toQ z₀ - centreFamily c₀ cs a₀) e ≠ 0) :
    LinearGrowth f ∨ WeakVectorCosetNF f :=
  Or.inr (D.weakVectorCosetNF_of_isotropic hf hcen hz₀ he hb)

/-! ### The two branch-data constructions, factored out

`summit_of_isotropic` and `summit_of_offCentre_radical` take their data as hypotheses.  The
constructions that produce that data from `Defines f` alone were buried inside
`dim_le_of_isotropic_defines` and `dim_le_of_quotientAnisotropic_defines`; they are mirrored here,
ending at the disjunct instead of at `n ≤ m`. -/

/-- **The isotropic branch, self-contained, landing in the disjunction.** -/
theorem summit_of_isotropicBranch
    (hm : 0 < m) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {e₀ : OutWit m r → ℚ} (he₀q : D.zQuadQ e₀ = 0) (he₀ : ¬ D.InRadicalQ e₀)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    LinearGrowth f ∨ WeakVectorCosetNF f := by
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
    exact Or.inr (D.weakVectorCosetNF_of_isotropic hf hcen' hz₀ he hb)
  · have hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
        D.InRadicalQ (toQ z - centreFamily c₀ cs a) := by
      intro a z hz
      by_contra hcon
      exact hcase ⟨a, z, hz, hcon⟩
    exact Or.inl (D.linearGrowth_of_offCentre_radical hm hQ hf hrad)

/-- **The quotient-anisotropic (Pell) branch, self-contained, landing in the disjunction.** -/
theorem summit_of_quotientAnisotropicBranch
    (hm : 0 < m) (hQ : ∃ x : OutWit m r → ℤ, D.zQuad x ≠ 0)
    (hqa : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0 → D.InRadicalQ x)
    {pp qq : OutWit m r → ℚ} (hpp : 0 < D.zQuadQ pp) (hqq : D.zQuadQ qq < 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    LinearGrowth f ∨ WeakVectorCosetNF f := by
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
  exact Or.inl (D.linearGrowth_of_offCentre_radical hm hQ hf hrad)

/-- **G22-T20, the summit.**  Every quadratic graph that defines a function lands in one of the
two disjuncts — no branch hypothesis, no nondegeneracy, no bound on the witnesses, arbitrary
`n, m, r`.  The five branches of `branch_exhaustive` are exhaustive but NOT pairwise
exclusive (`Q ≡ 0` satisfies the semidefinite conditions as well), and they land as:
`Q ≡ 0` RIGHT; the isotropic branch RIGHT when some solution lies off the centre family
and LEFT otherwise, through `summit_of_isotropicBranch`; `0 ≤ Q` LEFT, `Q ≤ 0` LEFT,
quotient-anisotropic LEFT. -/
theorem summit_of_defines {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    LinearGrowth f ∨ WeakVectorCosetNF f := by
  classical
  by_cases hm0 : m = 0
  · subst hm0
    exact Or.inr weakVectorCosetNF_of_m_zero
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  by_cases hz : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0
  · exact D.summit_of_qZero (D.zPolar_eq_zero_of_zQuadQ_zero hz) hf
  have hQ := D.exists_int_zQuad_ne_zero hz
  rcases D.branch_exhaustive with hz' | ⟨x, hx0, hxr⟩ | ⟨hqa, hcase⟩
  · exact absurd hz' hz
  · exact D.summit_of_isotropicBranch hmpos hQ hx0 hxr hf
  · rcases hcase with hpos | hneg | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    · exact Or.inl (D.linearGrowth_of_semidefinite_defines hmpos hpos hQ hf)
    · exact Or.inl (D.linearGrowth_of_negSemidefinite_defines hmpos hneg hQ hf)
    · exact D.summit_of_quotientAnisotropicBranch hmpos hQ hqa hp hq hf

end QuadraticGraphData

/-- **The summit closes the dimension bound.**  Either disjunct gives `n ≤ m` for an injective
`f`, so the disjunction is a sufficient intermediate — which is the reviewer's point in asking for
this shape. -/
theorem dim_le_of_summit {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hsum : LinearGrowth f ∨ WeakVectorCosetNF f) (hinj : Function.Injective f) : n ≤ m := by
  rcases hsum with h | h
  · exact dim_le_of_linearGrowth_injective h hinj
  · by_contra hcon
    exact not_injective_of_weakVectorCosetNF (by omega) f h hinj

/-- NEGATIVE control on the missing branch: **`Q ≡ 0` cannot land LEFT.**  `b − a² = 0` has
`Q ≡ 0` (no `b²` term) and defines `f a = a²`, which has no linear bound — so the missing branch
must go RIGHT, and any proof that routed it through `LinearGrowth` would be wrong.  The witness is
the existing `not_linearGrowth_sq`; it is restated here so the summit file carries its own
counterexample. -/
theorem qZeroBranch_cannot_go_left :
    ¬ LinearGrowth (fun a : Fin 1 → ℤ => ![a 0 ^ 2]) := not_linearGrowth_sq

/-- POSITIVE control, and a SECOND PROOF of II-D: `n ≤ m` factors through the summit.  The two
routes assemble the same five-branch split differently — `dim_le_of_defines` closes each branch at
`n ≤ m`, this one closes each branch at a disjunct and counts once at the end — and they agree. -/
theorem dim_le_of_defines_via_summit {n m r : ℕ} (D : QuadraticGraphData n m r)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (hinj : Function.Injective f) : n ≤ m :=
  dim_le_of_summit (D.summit_of_defines hf) hinj

end DiophCompression.ResearchUpgrade
