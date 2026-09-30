/-
  DimensionII_D.lean — s48.  **The glue**: the five branch capstones assembled along
  `branch_exhaustive`.

  Every clause of the split now has a discharged capstone, so what remains is bookkeeping of three
  kinds, and it is worth naming each because each was a place the argument could have quietly
  failed:

    * **ℚ → ℤ.**  The semidefinite capstones want an INTEGER vector on which the form is non-zero;
      the split only says the form is not identically zero over `ℚ`.  Clearing denominators turns
      `Q(x) ≠ 0` into `Q(V) = d²·Q(x) ≠ 0`.
    * **`m = 0`.**  Nothing about the form is needed: an injective map into `Fin 0 → ℤ` forces
      `n = 0`, because the codomain has exactly one element.
    * **`m = 1`.**  `dim_le_one_of_linearBranch` is stated at `m = 1`; general `m` in the linear
      branch is `m ≤ 1` (G21-T19) plus the `m = 0` case, and the reduction is by `interval_cases`
      on `m`, not by a cast.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Ring.Int.Defs
import ResearchUpgrade.BranchSplit
import ResearchUpgrade.ExistenceDirection
import ResearchUpgrade.LinearBranchDimension
import ResearchUpgrade.RadicalBridge

namespace DiophCompression.ResearchUpgrade

/-- With no outputs, injectivity alone forces no inputs: the codomain has one element. -/
theorem dim_le_of_m_zero {n : ℕ} {f : (Fin n → ℤ) → (Fin 0 → ℤ)}
    (hinj : Function.Injective f) : n ≤ 0 := by
  by_contra hcon
  have hn : 0 < n := by omega
  have heq : f 0 = f (Pi.single ⟨0, hn⟩ 1) := funext (fun j => j.elim0)
  have hz := hinj heq
  have h0 := congrFun hz ⟨0, hn⟩
  simp at h0

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- **ℚ → ℤ.**  If the form does not vanish identically over `ℚ`, some INTEGER vector already
witnesses that — clearing denominators multiplies the value by `d²`. -/
theorem exists_int_zQuad_ne_zero (h : ¬ ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0) :
    ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : OutWit m r → ℚ, D.zQuadQ x ≠ 0 := by
    by_contra hc
    exact h (fun x => by by_contra hne; exact hc ⟨x, hne⟩)
  obtain ⟨V, d, hd, hV⟩ := exists_int_clear x
  refine ⟨V, ?_⟩
  intro hzero
  have hVQ : toQ V = (d : ℚ) • x := by funext k; exact hV k
  have h1 : D.zQuadQ (toQ V) = (d : ℚ) ^ 2 * D.zQuadQ x := by
    rw [hVQ, D.zQuadQ_smul]
  rw [D.zQuadQ_toQ, hzero] at h1
  have hdQ : ((d : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : (d : ℚ) ^ 2 * D.zQuadQ x = 0 := by rw [← h1]; norm_num
  rcases mul_eq_zero.mp this with h2 | h2
  · exact hdQ (by nlinarith [h2])
  · exact hx h2

/-- **`m = 1` reduction.**  The linear branch at arbitrary `m`. -/
theorem dim_le_of_linearBranch_general
    (hpol : ∀ v w : OutWit m r → ℤ, D.zPolar v w = 0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) (hinj : Function.Injective f) :
    n ≤ m := by
  classical
  match m, D, f, hf, hinj with
  | 0, _, _, _, hinj => exact dim_le_of_m_zero hinj
  | 1, D, f, hf, hinj => exact D.dim_le_one_of_linearBranch hpol hf hinj
  | (k + 2), D, f, hf, hinj =>
      exfalso
      obtain ⟨z, hz⟩ := D.exists_solZ_of_defines hf 0
      obtain ⟨-, hle⟩ :=
        D.m_le_one_of_linear hpol (D.outputUnique_of_defines hf) hz (by omega)
      omega

/-- **II-D.**  The integer non-compression dimension theorem: a quadratic graph that DEFINES an
injective function cannot compress.  No branch hypothesis, no nondegeneracy, no bound on the
witnesses, no normal form assumed — arbitrary `n, m, r`. -/
theorem dim_le_of_defines {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hinj : Function.Injective f) : n ≤ m := by
  classical
  by_cases hm0 : m = 0
  · subst hm0
    exact dim_le_of_m_zero hinj
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  by_cases hz : ∀ x : OutWit m r → ℚ, D.zQuadQ x = 0
  · exact D.dim_le_of_linearBranch_general (D.zPolar_eq_zero_of_zQuadQ_zero hz) hf hinj
  have hQ := D.exists_int_zQuad_ne_zero hz
  rcases D.branch_exhaustive with hz' | ⟨x, hx0, hxr⟩ | ⟨hqa, hcase⟩
  · exact absurd hz' hz
  · exact D.dim_le_of_isotropic_defines hmpos hQ hx0 hxr hf hinj
  · rcases hcase with hpos | hneg | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    · exact D.dim_le_of_semidefinite_defines hmpos hpos hQ hf hinj
    · exact D.dim_le_of_negSemidefinite_defines hmpos hneg hQ hf hinj
    · exact D.dim_le_of_quotientAnisotropic_defines hmpos hQ hqa hp hq hf hinj

/-- **Statement-fidelity check against the recorded sharpest specialisation** (TARGETS, T35
addendum): "every integer polynomial of total degree ≤ 2 fails to be injective on `ℤ²`".  That is
`(n,m,r) = (2,1,0)`, and it falls straight out of II-D.  Note that the ℤ-side literature
(arXiv:2102.03392) covers this case only under a non-degeneracy hypothesis and only at `r = 0`,
`m = 1`; `dim_le_of_defines` has neither restriction. -/
theorem not_injective_of_two_one_zero (D : QuadraticGraphData 2 1 0)
    {f : (Fin 2 → ℤ) → (Fin 1 → ℤ)} (hf : D.Defines f) : ¬ Function.Injective f := by
  intro hinj
  have := D.dim_le_of_defines hf hinj
  omega

/-! ### Controls -/

/-- POSITIVE control: the bound is ATTAINED — the identity graph at `n = m` defines an injective
function, so II-D cannot be improved to `n < m` or to `n ≤ m − 1`. -/
theorem dim_le_of_defines_sharp (n : ℕ) :
    (idGraph n).Defines id ∧ Function.Injective (id : (Fin n → ℤ) → (Fin n → ℤ)) :=
  ⟨idGraph_defines n, Function.injective_id⟩

/-- NEGATIVE control: `Defines` is load-bearing and cannot be weakened to `Total`.  With `m = 0`
the graph `P = 0` relates every input to the unique output, so it is total, yet the function it
"defines" is constant and not injective — the theorem says nothing about such graphs, and must
not. -/
theorem dim_le_of_defines_needs_injective {n : ℕ} (hn : 0 < n)
    {f : (Fin n → ℤ) → (Fin 0 → ℤ)} : ¬ Function.Injective f := by
  intro hinj
  have := dim_le_of_m_zero hinj
  omega

end QuadraticGraphData

end DiophCompression.ResearchUpgrade
