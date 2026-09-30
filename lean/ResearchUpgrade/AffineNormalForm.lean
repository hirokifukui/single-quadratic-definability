/-
  B1 (R40-B1) — the affine normal form that `linearGrowth_of_offCentre_radical` derives and
  then discards.

  Inside that proof the line

      hval : ((f a j : ℤ) : ℚ) = (centreFamily c₀ cs a) (Sum.inl j)

  holds for EVERY input `a`, and `centreFamily c₀ cs a = c₀ + ∑ i, a i • cs i` is affine in `a`
  by construction.  The theorem then throws that identity into an absolute-value bound and
  concludes `LinearGrowth`, which is strictly weaker: it keeps the growth and forgets the
  coefficients.  Here the identity is kept as the conclusion, and the modulus is 1, so it is a
  normal form on EVERY residue class, not on one coset.

  s51 (R40-B1).  Statement fixed by claude.ai; nothing delegated.  The axiom footprint is
  checked by audit_ru.sh in the clean room, not by a #print in the library.
-/
import ResearchUpgrade.IsotropicBranch

namespace DiophCompression.ResearchUpgrade

open Matrix

/-- Full-residue VECTOR normal form: one modulus `M` works for EVERY coset `ρ + M ℤⁿ` and for all
`m` output coordinates at once.  `FullCosetNF` is the scalar version; `WeakVectorCosetNF` is the
one-coset version. -/
def FullVectorCosetNF {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop :=
  ∃ M : ℕ, 1 ≤ M ∧ ∀ ρ : Fin n → ℤ, ∃ q : Fin m → QuadForm n,
    ∀ (t : Fin n → ℤ) (j : Fin m), (f (ρ + (M : ℤ) • t) j : ℚ) = (q j).eval (castQ t)

/-- The full-residue form implies the one-coset form (take `ρ = 0`). -/
theorem weakVectorCosetNF_of_fullVectorCosetNF {n m : ℕ}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (h : FullVectorCosetNF f) : WeakVectorCosetNF f := by
  obtain ⟨M, hM, h⟩ := h
  obtain ⟨q, hq⟩ := h 0
  exact ⟨M, 0, q, hM, hq⟩

/-- `m = 0`: the trivial wrapper.  There is no output coordinate to constrain. -/
theorem fullVectorCosetNF_of_m_zero {n : ℕ} (f : (Fin n → ℤ) → (Fin 0 → ℤ)) :
    FullVectorCosetNF f :=
  ⟨1, le_refl 1, fun _ => ⟨fun j => j.elim0, fun _ j => j.elim0⟩⟩

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- **B1, the extraction.**  Under the hypotheses of `linearGrowth_of_offCentre_radical`, the
value of `f` at every input is the affine expression read off the centre family:
`f a j = c₀(inl j) + ∑ i, a i · cs i (inl j)`.  The coefficients do not depend on `a`. -/
theorem affine_of_offCentre_radical
    (hm : 0 < m) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
      D.InRadicalQ (toQ z - centreFamily c₀ cs a)) :
    ∀ (a : Fin n → ℤ) (j : Fin m),
      ((f a j : ℤ) : ℚ) = c₀ (Sum.inl j) + ∑ i, (a i : ℚ) * cs i (Sum.inl j) := by
  have hOU := D.outputUnique_of_defines hf
  intro a j
  obtain ⟨u, hu⟩ : D.Graph a (f a) := (hf a (f a)).mpr rfl
  have hz : D.SolZ a (Sum.elim (f a) u) := hu
  have he := hrad a (Sum.elim (f a) u) hz
  have hzero := D.outCoordQ_radicalQ_eq_zero hm hOU hz hQ he j
  have hval : ((f a j : ℤ) : ℚ) = (centreFamily c₀ cs a) (Sum.inl j) := by
    have h2 : ((f a j : ℤ) : ℚ) - (centreFamily c₀ cs a) (Sum.inl j) = 0 := hzero
    linarith
  rw [hval, centreFamily]
  simp [Finset.sum_apply, smul_eq_mul]

/-- **B1, packaged.**  The same hypotheses give a normal form on every residue class with
modulus 1: `f` is globally affine with rational coefficients. -/
theorem fullVectorCosetNF_of_offCentre_radical
    (hm : 0 < m) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
      D.InRadicalQ (toQ z - centreFamily c₀ cs a)) :
    FullVectorCosetNF f := by
  have key := D.affine_of_offCentre_radical hm hQ hf hrad
  refine ⟨1, le_refl 1, fun ρ => ?_⟩
  refine ⟨fun j => ⟨c₀ (Sum.inl j) + ∑ i, (ρ i : ℚ) * cs i (Sum.inl j),
                    fun i => cs i (Sum.inl j), 0⟩, ?_⟩
  intro t j
  have h1 : ρ + ((1 : ℕ) : ℤ) • t = ρ + t := by simp
  rw [h1, key (ρ + t) j]
  have hsplit : ∀ i : Fin n, (((ρ + t) i : ℤ) : ℚ) * cs i (Sum.inl j)
      = (ρ i : ℚ) * cs i (Sum.inl j) + cs i (Sum.inl j) * ((t i : ℤ) : ℚ) := by
    intro i
    simp only [Pi.add_apply, Int.cast_add]
    ring
  simp only [QuadForm.eval]
  simp only [zero_mulVec, dotProduct_zero, add_zero]
  simp only [dotProduct, castQ]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib]
  ring

/-- **The isotropic fallback, restated.**  This is the branch that `summit_of_isotropicBranch`
sends LEFT: when every solution lies in the radical of the centre family, the conclusion is not
merely linear growth but a full-residue affine normal form. -/
theorem fullVectorCosetNF_of_isotropic_fallback
    (hm : 0 < m) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {c₀ : OutWit m r → ℚ} {cs : Fin n → OutWit m r → ℚ}
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hrad : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ), D.SolZ a z →
      D.InRadicalQ (toQ z - centreFamily c₀ cs a)) :
    WeakVectorCosetNF f :=
  weakVectorCosetNF_of_fullVectorCosetNF
    (D.fullVectorCosetNF_of_offCentre_radical hm hQ hf hrad)

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
