/-
  SaturatedLattice.lean — s52.  R41-C1 core: for a SATURATED sublattice of Z^r every Smith
  normal form diagonal entry is a unit.

  This is the step clearing denominators does not give.  A rational basis scaled to integrality
  spans a finite-index sublattice, not the intersection lattice; saturation is what forces the
  diagonal to be +-1, hence the change of basis to be unimodular and a basis of the sublattice
  to extend to a basis of Z^r.

  mathlib used (all #check'd against the working-zone mathlib d46bd45 (the release pin; not d568c8c — corrected s53) before use, see s52_evidence/C1_mathlib_coverage_s52.md):
  Submodule.smithNormalForm, Module.Basis.SmithNormalForm (NOT Basis.SmithNormalForm — that name
  does not exist at this pin), Module.Basis.repr_self, Module.Basis.sum_repr.

  Claim tags: [P] (std-3).
-/
import Mathlib.LinearAlgebra.FreeModule.PID

namespace DiophCompression.ResearchUpgrade.SaturatedLattice

variable {r : ℕ}

/-- A sublattice is **saturated** when a nonzero multiple lying in it forces membership.
For `L = K ∩ ℤ^r` with `K` a rational subspace this holds by construction. -/
def Saturated (N : Submodule ℤ (Fin r → ℤ)) : Prop :=
  ∀ (c : ℤ) (x : Fin r → ℤ), c ≠ 0 → c • x ∈ N → x ∈ N

/-- **R41-C1, the core.**  For a saturated sublattice every Smith diagonal entry is a unit.
This is exactly what clearing denominators does NOT give: it is the step that turns a basis of
the sublattice into part of a basis of the whole lattice. -/
theorem smith_isUnit_of_saturated {N : Submodule ℤ (Fin r → ℤ)} (hsat : Saturated N)
    {n : ℕ} (snf : Module.Basis.SmithNormalForm N (Fin r) n) (i : Fin n) :
    IsUnit (snf.a i) := by
  have ha0 : snf.a i ≠ 0 := by
    intro h
    have hb := snf.snf i
    rw [h, zero_smul] at hb
    exact snf.bN.ne_zero i (Submodule.coe_eq_zero.mp hb)
  have hmem : snf.bM (snf.f i) ∈ N := by
    refine hsat (snf.a i) _ ha0 ?_
    rw [← snf.snf i]
    exact (snf.bN i).2
  set y : ↥N := ⟨snf.bM (snf.f i), hmem⟩ with hy
  have hsum : ∑ j, snf.bN.repr y j • ((snf.bN j : Fin r → ℤ))
      = snf.bM (snf.f i) := by
    have h := snf.bN.sum_repr y
    have h2 := congrArg N.subtype h
    simp only [map_sum, map_smul, Submodule.subtype_apply] at h2
    exact h2
  have hsum' : ∑ j, (snf.bN.repr y j * snf.a j) • snf.bM (snf.f j)
      = snf.bM (snf.f i) := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun j _ => by rw [snf.snf j, smul_smul]
  have key := congrArg (fun z => snf.bM.repr z (snf.f i)) hsum'
  simp only [map_sum, map_smul, Module.Basis.repr_self, mul_one, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply,
    snf.f.injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true] at key
  -- read `key` with trace_state before closing (s52: three blind guesses failed here first)
  have key2 : snf.bN.repr y i * snf.a i = 1 := by
    rw [← key]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.single_apply, snf.f.injective.eq_iff,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' key2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    exact Int.isUnit_iff.mpr (by omega)

end DiophCompression.ResearchUpgrade.SaturatedLattice
