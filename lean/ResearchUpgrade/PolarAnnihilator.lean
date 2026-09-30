/-
  PolarAnnihilator.lean — s48.  Gate22 task **G22-T05**, and with it the named open leaf
  `exists_centre_of_lin_annihilates_radical` recorded in RationalCentre.lean.

  Over ℚ the image of the polar map is the annihilator of the radical:

      range (v ↦ polar(v, ·))  =  (rad Q).dualAnnihilator.

  `≤` is symmetry of the polar form.  `≥` is rank–nullity twice: both sides have codimension
  `finrank (rad Q)` inside the dual.  No positivity, no nondegeneracy, no basis, no complement —
  the degenerate case is included, which is the whole point.

  Consequence (`isCentre_iff_lin_annihilates_radical`): a centre for the input `a` exists **iff**
  `ℓ_a` vanishes on the radical.  Under output uniqueness that hypothesis is exactly what T05
  (`zLinEval_radical_eq_zero`, RadicalDrift.lean) already proves, so the centre — and therefore
  `completeSquare` / `offCentre_norm` — becomes unconditional on that branch.

  The statement is an iff, so it carries its own negative control: when `ℓ_a` does NOT kill the
  radical, no centre exists at all (`not_isCentre_of_lin_ne_zero_on_radical`).

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import ResearchUpgrade.RationalCentre

namespace DiophCompression.ResearchUpgrade

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-! ### Left linearity of the polar form (the right-hand versions are in RationalCentre) -/

theorem zPolarQ_add_left (v₁ v₂ w : OutWit m r → ℚ) :
    D.zPolarQ (v₁ + v₂) w = D.zPolarQ v₁ w + D.zPolarQ v₂ w := by
  rw [D.zPolarQ_symm, D.zPolarQ_add_right, D.zPolarQ_symm w v₁, D.zPolarQ_symm w v₂]

theorem zPolarQ_smul_left (lam : ℚ) (v w : OutWit m r → ℚ) :
    D.zPolarQ (lam • v) w = lam * D.zPolarQ v w := by
  rw [D.zPolarQ_symm, D.zPolarQ_smul_right, D.zPolarQ_symm w v]

theorem zLinQ_add (a : Fin n → ℤ) (z₁ z₂ : OutWit m r → ℚ) :
    D.zLinQ a (z₁ + z₂) = D.zLinQ a z₁ + D.zLinQ a z₂ := by
  simp only [zLinQ, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem zLinQ_smul (a : Fin n → ℤ) (lam : ℚ) (z : OutWit m r → ℚ) :
    D.zLinQ a (lam • z) = lam * D.zLinQ a z := by
  simp only [zLinQ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ### The radical, and the two linear maps -/

/-- `v` lies in the radical of the polar form, over ℚ. -/
def InRadicalQ (v : OutWit m r → ℚ) : Prop := ∀ w, D.zPolarQ v w = 0

/-- `ℓ_a` as an element of the dual space. -/
def linDual (a : Fin n → ℤ) : Module.Dual ℚ (OutWit m r → ℚ) where
  toFun z := D.zLinQ a z
  map_add' := D.zLinQ_add a
  map_smul' := by intro c z; simpa using D.zLinQ_smul a c z

@[simp] theorem linDual_apply (a : Fin n → ℤ) (z : OutWit m r → ℚ) :
    D.linDual a z = D.zLinQ a z := rfl

/-- The polar map `p : v ↦ polar(v, ·)` into the dual. -/
def polarMapQ : (OutWit m r → ℚ) →ₗ[ℚ] Module.Dual ℚ (OutWit m r → ℚ) where
  toFun v :=
    { toFun := fun w => D.zPolarQ v w
      map_add' := D.zPolarQ_add_right v
      map_smul' := by intro c w; simpa using D.zPolarQ_smul_right c v w }
  map_add' := by
    intro v₁ v₂
    refine LinearMap.ext fun w => ?_
    simpa using D.zPolarQ_add_left v₁ v₂ w
  map_smul' := by
    intro c v
    refine LinearMap.ext fun w => ?_
    simpa using D.zPolarQ_smul_left c v w

@[simp] theorem polarMapQ_apply (v w : OutWit m r → ℚ) :
    D.polarMapQ v w = D.zPolarQ v w := rfl

theorem mem_ker_polarMapQ {v : OutWit m r → ℚ} :
    v ∈ LinearMap.ker D.polarMapQ ↔ D.InRadicalQ v := by
  constructor
  · intro h w
    have h' : D.polarMapQ v = 0 := LinearMap.mem_ker.mp h
    calc D.zPolarQ v w = D.polarMapQ v w := rfl
      _ = 0 := by rw [h']; rfl
  · intro h
    refine LinearMap.mem_ker.mpr (LinearMap.ext fun w => ?_)
    simpa using h w

/-! ### G22-T05 — the image of the polar map IS the annihilator of the radical -/

/-- Symmetry gives the easy inclusion, with no finiteness. -/
theorem range_polarMapQ_le :
    LinearMap.range D.polarMapQ ≤ (LinearMap.ker D.polarMapQ).dualAnnihilator := by
  rintro _ ⟨v, rfl⟩
  refine Submodule.mem_dualAnnihilator _ |>.mpr ?_
  intro e he
  have hev : D.zPolarQ e v = 0 := (D.mem_ker_polarMapQ.mp he) v
  calc D.polarMapQ v e = D.zPolarQ v e := rfl
    _ = D.zPolarQ e v := D.zPolarQ_symm v e
    _ = 0 := hev

/-- **G22-T05.**  `im(p) = Ann(rad Q)` over ℚ.  Equality, not merely `≤`: the two subspaces have
the same finrank by rank–nullity, and one is contained in the other.  No hypothesis whatsoever on
the form — in particular the radical may be nonzero. -/
theorem range_polarMapQ_eq_dualAnnihilator_ker :
    LinearMap.range D.polarMapQ = (LinearMap.ker D.polarMapQ).dualAnnihilator := by
  refine Submodule.eq_of_le_of_finrank_eq D.range_polarMapQ_le ?_
  have h1 : Module.finrank ℚ (LinearMap.range D.polarMapQ)
      + Module.finrank ℚ (LinearMap.ker D.polarMapQ)
      = Module.finrank ℚ (OutWit m r → ℚ) :=
    LinearMap.finrank_range_add_finrank_ker D.polarMapQ
  have h2 : Module.finrank ℚ (LinearMap.ker D.polarMapQ)
      + Module.finrank ℚ ((LinearMap.ker D.polarMapQ).dualAnnihilator)
      = Module.finrank ℚ (OutWit m r → ℚ) :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.ker D.polarMapQ)
  omega

/-! ### The named leaf: existence of a centre -/

/-- **`exists_centre_of_lin_annihilates_radical`, in iff form.**  A centre for the input `a`
exists exactly when `ℓ_a` vanishes on the radical of the polar form.  The forward direction is the
negative control (the hypothesis is not decorative); the backward direction is the leaf that
RationalCentre.lean left open, and it discharges `completeSquare`'s hypothesis. -/
theorem isCentre_iff_lin_annihilates_radical (a : Fin n → ℤ) :
    (∃ c : OutWit m r → ℚ, D.IsCentre a c) ↔ ∀ e, D.InRadicalQ e → D.zLinQ a e = 0 := by
  constructor
  · rintro ⟨c, hc⟩ e he
    have h := hc e
    have hce : D.zPolarQ c e = 0 := by
      rw [D.zPolarQ_symm c e]; exact he c
    linarith [h, hce]
  · intro hann
    have hmem : -D.linDual a ∈ (LinearMap.ker D.polarMapQ).dualAnnihilator := by
      refine Submodule.mem_dualAnnihilator _ |>.mpr ?_
      intro e he
      have : D.zLinQ a e = 0 := hann e (D.mem_ker_polarMapQ.mp he)
      simp [this]
    rw [← D.range_polarMapQ_eq_dualAnnihilator_ker] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, fun w => ?_⟩
    have := congrArg (fun f : Module.Dual ℚ (OutWit m r → ℚ) => f w) hc
    simp only [LinearMap.neg_apply, linDual_apply, polarMapQ_apply] at this
    linarith [this]

/-- The leaf in the shape RationalCentre.lean asks for. -/
theorem exists_centre_of_lin_annihilates_radical {a : Fin n → ℤ}
    (hann : ∀ e, D.InRadicalQ e → D.zLinQ a e = 0) :
    ∃ c : OutWit m r → ℚ, D.IsCentre a c :=
  (D.isCentre_iff_lin_annihilates_radical a).mpr hann

/-- NEGATIVE control, read off the iff: if some radical vector is seen by `ℓ_a`, there is no
centre at all — so `completeSquare` genuinely cannot be applied there. -/
theorem not_isCentre_of_lin_ne_zero_on_radical {a : Fin n → ℤ} {e : OutWit m r → ℚ}
    (he : D.InRadicalQ e) (hne : D.zLinQ a e ≠ 0) (c : OutWit m r → ℚ) :
    ¬ D.IsCentre a c := by
  intro hc
  exact hne ((D.isCentre_iff_lin_annihilates_radical a).mp ⟨c, hc⟩ e he)

/-- POSITIVE control: the radical is always annihilated by `ℓ_a` when the form is nondegenerate
(the radical is then trivial), so a centre exists with no further input. -/
theorem exists_centre_of_nondegQ {a : Fin n → ℤ} (hnd : D.NondegQ) :
    ∃ c : OutWit m r → ℚ, D.IsCentre a c := by
  refine D.exists_centre_of_lin_annihilates_radical ?_
  intro e he
  by_cases h0 : e = 0
  · subst h0; simp [zLinQ]
  · obtain ⟨w, hw⟩ := hnd e h0
    exact absurd (he w) hw

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
