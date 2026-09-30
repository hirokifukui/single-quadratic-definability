/-
  AffineCentre.lean — s48.  Gate22 task **G22-T06 §3.1** — the AFFINE centre family.

  G22-T05 produces a centre for ONE input at a time.  That is not enough downstream: the isotropic
  section must be a polynomial of degree ≤ 2 in `a`, and the output-only growth bound needs `π h`
  to be affine in `a`.  Choosing `h` input by input gives neither — `∀ a, ∃ h_a` has no dependence
  at all.  The reviewer's §3.1 fixes this by solving FINITELY many linear systems once:

      polar(h₀, ·) = −ℓ₀ ,   polar(hᵢ, ·) = −ℓᵢ ,   h(a) = h₀ + Σᵢ aᵢ hᵢ.

  Since `zLin` is affine in `a` by construction (`zLin a k = l(inr k) + Σᵢ aᵢ·Cᵢₖ`, T02), the
  decomposition `ℓ_a = ℓ₀ + Σᵢ aᵢ ℓᵢ` is exact, and `h(a)` is then a centre for EVERY `a`, with
  the affine dependence VISIBLE IN THE TYPE (the conclusion is stated as `h₀ + Σ aᵢ • hᵢ`, not as
  `∀ a, ∃ h`).  The denominators are those of finitely many fixed vectors — no input-dependent
  "denominator growth" is needed anywhere.

  Entry point: `exists_affine_centre_of_all_inputs`, whose single hypothesis is exactly what
  G21-T05 (`zLinEval_radical_eq_zero`) supplies under output uniqueness — `ℓ_a` kills the radical
  at every input.  The `a = 0` and `a = eᵢ` specialisations are done inside the proof.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.GraphVocabulary
import ResearchUpgrade.OutputCoercivity
import ResearchUpgrade.PolarAnnihilator
import ResearchUpgrade.RationalCentre

namespace DiophCompression.ResearchUpgrade

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-! ### The representation lemma in general form (G22-T05, packaged) -/

/-- Any functional annihilating the radical is `polar(c, ·)` for some `c`. -/
theorem exists_polar_rep {ℓ : Module.Dual ℚ (OutWit m r → ℚ)}
    (hann : ∀ e : OutWit m r → ℚ, D.InRadicalQ e → ℓ e = 0) :
    ∃ c : OutWit m r → ℚ, ∀ w, D.zPolarQ c w = ℓ w := by
  have hmem : ℓ ∈ (LinearMap.ker D.polarMapQ).dualAnnihilator := by
    refine Submodule.mem_dualAnnihilator _ |>.mpr ?_
    intro e he
    exact hann e (D.mem_ker_polarMapQ.mp he)
  rw [← D.range_polarMapQ_eq_dualAnnihilator_ker] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, fun w => ?_⟩
  have := congrArg (fun f : Module.Dual ℚ (OutWit m r → ℚ) => f w) hc
  simpa using this

/-! ### The two constituents of `ℓ_a` -/

/-- The `a`-independent part of `ℓ_a`, over ℚ. -/
def linQ0 : Module.Dual ℚ (OutWit m r → ℚ) where
  toFun z := ∑ k, (D.P.l (Sum.inr k) : ℚ) * z k
  map_add' := by
    intro z₁ z₂
    simp only [Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' := by
    intro c z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The coefficient functional of the input `aᵢ` in `ℓ_a`, over ℚ. -/
def linQcoeff (i : Fin n) : Module.Dual ℚ (OutWit m r → ℚ) where
  toFun z := ∑ k, ((D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i) : ℤ) : ℚ) * z k
  map_add' := by
    intro z₁ z₂
    simp only [Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' := by
    intro c z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)

@[simp] theorem linQ0_apply (z : OutWit m r → ℚ) :
    D.linQ0 z = ∑ k, (D.P.l (Sum.inr k) : ℚ) * z k := rfl

@[simp] theorem linQcoeff_apply (i : Fin n) (z : OutWit m r → ℚ) :
    D.linQcoeff i z
      = ∑ k, ((D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i) : ℤ) : ℚ) * z k :=
  rfl

/-- **`ℓ_a` is affine in `a`, exactly.**  This is not an approximation: `zLin` is defined with an
`a`-independent term and a term linear in `a` (T02), so the identity is an equality of rationals
for every `a` and every `z`. -/
theorem zLinQ_affine (a : Fin n → ℤ) (z : OutWit m r → ℚ) :
    D.zLinQ a z = D.linQ0 z + ∑ i, (a i : ℚ) * D.linQcoeff i z := by
  have hterm : ∀ k : OutWit m r,
      ((D.zLin a k : ℤ) : ℚ) * z k
        = (D.P.l (Sum.inr k) : ℚ) * z k
          + ∑ i, (a i : ℚ) *
              (((D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i) : ℤ) : ℚ) * z k) := by
    intro k
    simp only [zLin]
    push_cast
    rw [add_mul, Finset.sum_mul]
    refine congrArg _ (Finset.sum_congr rfl (fun i _ => by ring))
  simp only [zLinQ, hterm, Finset.sum_add_distrib]
  refine congrArg _ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [linQcoeff_apply, Finset.mul_sum]

theorem zLinQ_zero (z : OutWit m r → ℚ) : D.zLinQ (fun _ => (0 : ℤ)) z = D.linQ0 z := by
  rw [D.zLinQ_affine]
  simp

theorem zLinQ_single (i : Fin n) (z : OutWit m r → ℚ) :
    D.zLinQ (Pi.single i (1 : ℤ)) z = D.linQ0 z + D.linQcoeff i z := by
  rw [D.zLinQ_affine]
  refine congrArg _ ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### G22-T06 §3.1 — the affine centre family -/

/-- **G22-T06 §3.1.**  One choice of `h₀` and of `h₁, …, hₙ` makes `h(a) = h₀ + Σ aᵢ hᵢ` a centre
for EVERY integer input.  The affine dependence is in the type, not in the prose. -/
theorem exists_affine_centre
    (h0 : ∀ e : OutWit m r → ℚ, D.InRadicalQ e → D.linQ0 e = 0)
    (hc : ∀ (i : Fin n) (e : OutWit m r → ℚ), D.InRadicalQ e → D.linQcoeff i e = 0) :
    ∃ (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ),
      ∀ a : Fin n → ℤ, D.IsCentre a (c₀ + ∑ i, (a i : ℚ) • cs i) := by
  obtain ⟨c₀, hc₀⟩ : ∃ c, ∀ w, D.zPolarQ c w = (-D.linQ0) w := by
    refine D.exists_polar_rep ?_
    intro e he
    simp [h0 e he]
  have hcs : ∀ i : Fin n, ∃ c, ∀ w, D.zPolarQ c w = (-D.linQcoeff i) w := by
    intro i
    refine D.exists_polar_rep ?_
    intro e he
    simp [hc i e he]
  choose cs hcs using hcs
  refine ⟨c₀, cs, fun a w => ?_⟩
  have hmap : D.polarMapQ (c₀ + ∑ i, (a i : ℚ) • cs i)
      = D.polarMapQ c₀ + ∑ i, (a i : ℚ) • D.polarMapQ (cs i) := by
    rw [map_add, map_sum]
    exact congrArg _ (Finset.sum_congr rfl (fun i _ => map_smul _ _ _))
  have hval := congrArg (fun f : Module.Dual ℚ (OutWit m r → ℚ) => f w) hmap
  simp only [LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, polarMapQ_apply] at hval
  rw [hval, D.zLinQ_affine]
  have h₀w : D.zPolarQ c₀ w = -D.linQ0 w := by simpa using hc₀ w
  have hiw : ∀ i, D.zPolarQ (cs i) w = -D.linQcoeff i w := by
    intro i; simpa using hcs i w
  rw [h₀w]
  simp only [hiw, mul_neg]
  rw [Finset.sum_neg_distrib]
  ring

/-- The entry point actually used downstream: ONE hypothesis, and it is exactly what G21-T05
supplies — `ℓ_a` kills the radical at every integer input.  The `a = 0` and `a = eᵢ`
specialisations of the reviewer's §3.1 are performed here. -/
theorem exists_affine_centre_of_all_inputs
    (hall : ∀ (a : Fin n → ℤ) (e : OutWit m r → ℚ), D.InRadicalQ e → D.zLinQ a e = 0) :
    ∃ (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ),
      ∀ a : Fin n → ℤ, D.IsCentre a (c₀ + ∑ i, (a i : ℚ) • cs i) := by
  have h0 : ∀ e : OutWit m r → ℚ, D.InRadicalQ e → D.linQ0 e = 0 := by
    intro e he
    rw [← D.zLinQ_zero e]
    exact hall _ e he
  refine D.exists_affine_centre h0 ?_
  intro i e he
  have h1 := hall (Pi.single i (1 : ℤ)) e he
  rw [D.zLinQ_single i e, h0 e he, zero_add] at h1
  exact h1

/-- What T08 consumes: the OUTPUT of the centre is affine in the input, coordinatewise. -/
theorem outCoord_affine_centre (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ)
    (a : Fin n → ℤ) (j : Fin m) :
    (c₀ + ∑ i, (a i : ℚ) • cs i) (Sum.inl j)
      = c₀ (Sum.inl j) + ∑ i, (a i : ℚ) * cs i (Sum.inl j) := by
  simp [Finset.sum_apply]

/-! ### Controls -/

/-- POSITIVE control: with a nondegenerate form the radical is trivial, both hypotheses are free,
and an affine centre family exists outright.  So the statement is not vacuous. -/
theorem exists_affine_centre_of_nondegQ (hnd : D.NondegQ) :
    ∃ (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ),
      ∀ a : Fin n → ℤ, D.IsCentre a (c₀ + ∑ i, (a i : ℚ) • cs i) := by
  refine D.exists_affine_centre_of_all_inputs ?_
  intro a e he
  by_cases h0 : e = 0
  · subst h0; simp [zLinQ]
  · obtain ⟨w, hw⟩ := hnd e h0
    exact absurd (he w) hw

/-- NEGATIVE control: if `ℓ_a` fails to kill the radical at even ONE input, no centre exists there,
so no affine family can exist either.  The hypothesis of `exists_affine_centre_of_all_inputs` is
therefore load-bearing at every input, not only at `a = 0`. -/
theorem not_exists_affine_centre_of_lin_ne_zero {a : Fin n → ℤ} {e : OutWit m r → ℚ}
    (he : D.InRadicalQ e) (hne : D.zLinQ a e ≠ 0) :
    ¬ ∃ (c₀ : OutWit m r → ℚ) (cs : Fin n → OutWit m r → ℚ),
        ∀ a' : Fin n → ℤ, D.IsCentre a' (c₀ + ∑ i, (a' i : ℚ) • cs i) := by
  rintro ⟨c₀, cs, hfam⟩
  exact D.not_isCentre_of_lin_ne_zero_on_radical he hne _ (hfam a)

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
