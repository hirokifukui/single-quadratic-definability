/-
  DiophCompression/SummitReduction.lean — APAL Structural Theory Gate 5, 必須F step 1 (s28, 2026-09-02,
  claude.ai direct).

  What is actually left of the summit. The strong target `UniformQuadraticFiberStructureZZ` (必須B) asks for
  ONE constant valid at every parameter point; the finite-fibre theorem already supplies such a constant
  (`singleQuadratic_finiteFiber_height_scalar_sup`). Hence, for a quadratic `P`, the strong target is
  EQUIVALENT to the certificate supply on the infinite side alone:

      UniformQuadraticFiberStructureZZ P  ↔  (∀ a, fibre infinite → structured certificate).

  This settles GPT Gate-4 §3 exactly: nothing is lost by the uniform form — the uniformity is free, and the
  whole remaining obligation is the infinite side. Together with the output-negation layer (必須C) the
  obligation reduces further to the NONNEGATIVE half of the fibre of `P` and of its flip. What is not yet
  proved is precisely that supply, branch by branch (必須D packagers + 必須E exhaustion). No sorry; std-3.
-/
import DiophCompression.GSInputCompiler

namespace DiophCompression

open MvPolynomial MPUP Matrix

variable {n r : ℕ}

/-- The remaining obligation of the summit: every infinite fibre carries a structured certificate. -/
def InfiniteFiberStructured (P : Poly (n + 1) r) : Prop :=
  ∀ a : Fin n → ℤ, (fiberZZ P a).Infinite → Nonempty (StructuredCertificate P a)

/-- The uniform constant is free: it comes from the finite-fibre theorem. -/
theorem uniformQuadraticFiberStructureZZ_of_infiniteFiberStructured (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) (h : InfiniteFiberStructured P) :
    UniformQuadraticFiberStructureZZ P := by
  classical
  obtain ⟨C, hC⟩ := singleQuadratic_finiteFiber_height_scalar_sup P hP
  refine ⟨C, fun a => ?_⟩
  by_cases hfin : (fiberZZ P a).Finite
  · exact Or.inl (fun c hc => hC a hfin c hc)
  · exact Or.inr (h a (Set.not_finite.mp hfin))

/-- Conversely the strong target gives the certificate supply: on an infinite fibre the bounded branch is
    impossible. -/
theorem infiniteFiberStructured_of_uniformQuadraticFiberStructureZZ (P : Poly (n + 1) r)
    (h : UniformQuadraticFiberStructureZZ P) : InfiniteFiberStructured P := by
  obtain ⟨C, hC⟩ := h
  intro a hinf
  rcases hC a with hB | hcert
  · exact absurd (fiber_finite_of_bounded P a (C * (1 + paramSup a) ^ 2) (fun c hc => by
      have := hB c hc
      push_cast
      push_cast at this
      linarith)) hinf
  · exact hcert

/-- 必須F, step 1: for a quadratic `P` the strong summit target and the infinite-side certificate supply
    are the SAME statement. The uniformity GPT asks for is not an extra burden; the burden is the
    infinite side, and only that. -/
theorem uniformQuadraticFiberStructureZZ_iff_infiniteFiberStructured (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) :
    UniformQuadraticFiberStructureZZ P ↔ InfiniteFiberStructured P :=
  ⟨infiniteFiberStructured_of_uniformQuadraticFiberStructureZZ P,
    uniformQuadraticFiberStructureZZ_of_infiniteFiberStructured P hP⟩

/-- 必須C ∘ 必須F: it suffices to certify the NONNEGATIVE half of the fibre, for `P` and for its output
    flip. The negative half is transported back by `structuredCertificate_of_flipZero`, kind-preservingly. -/
theorem infiniteFiberStructured_of_nonneg_halves (P : Poly (n + 1) r)
    (hpos : ∀ a : Fin n → ℤ, {c ∈ fiberZZ P a | 0 ≤ c}.Infinite →
      Nonempty (StructuredCertificate P a))
    (hneg : ∀ a : Fin n → ℤ, {c ∈ fiberZZ (negOutputPoly P) a | 0 ≤ c}.Infinite →
      Nonempty (StructuredCertificate (negOutputPoly P) a)) :
    InfiniteFiberStructured P := by
  intro a hinf
  rcases infinite_integer_fiber_pos_or_neg P a hinf with h1 | h2
  · exact hpos a h1
  · exact (hneg a h2).elim (fun cert => ⟨structuredCertificate_of_flipZero cert⟩)

/-- The same reduction stated for the strong target directly. -/
theorem uniformQuadraticFiberStructureZZ_of_nonneg_halves (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2)
    (hpos : ∀ a : Fin n → ℤ, {c ∈ fiberZZ P a | 0 ≤ c}.Infinite →
      Nonempty (StructuredCertificate P a))
    (hneg : ∀ a : Fin n → ℤ, {c ∈ fiberZZ (negOutputPoly P) a | 0 ≤ c}.Infinite →
      Nonempty (StructuredCertificate (negOutputPoly P) a)) :
    UniformQuadraticFiberStructureZZ P :=
  uniformQuadraticFiberStructureZZ_of_infiniteFiberStructured P hP
    (infiniteFiberStructured_of_nonneg_halves P hpos hneg)

/-- Negative control for the summit target (GPT 宿題群6-1): the WEAK per-point form cannot replace the
    strong one silently — but not because it is vacuous. On a finite fibre the weak form is trivially
    satisfied by the fibre's own bound, whereas the strong form still asserts the uniform quadratic
    height. This theorem exhibits the trivial bound, so the difference is on the record. -/
theorem weak_target_trivial_on_finite_fibre (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (hfin : (fiberZZ P a).Finite) : ∃ B : ℕ, ∀ c ∈ fiberZZ P a, |c| ≤ B := by
  classical
  obtain ⟨s, hs⟩ := hfin.exists_finset_coe
  refine ⟨(s.sup fun c => c.natAbs), fun c hc => ?_⟩
  have hcs : c ∈ s := by rw [← Finset.mem_coe, hs]; exact hc
  have : c.natAbs ≤ s.sup fun c => c.natAbs := Finset.le_sup (f := fun c => c.natAbs) hcs
  calc |c| = (c.natAbs : ℤ) := (Int.abs_eq_natAbs c)
    _ ≤ ((s.sup fun c => c.natAbs : ℕ) : ℤ) := by exact_mod_cast this

end DiophCompression

#print axioms DiophCompression.uniformQuadraticFiberStructureZZ_of_infiniteFiberStructured
#print axioms DiophCompression.infiniteFiberStructured_of_uniformQuadraticFiberStructureZZ
#print axioms DiophCompression.uniformQuadraticFiberStructureZZ_iff_infiniteFiberStructured
#print axioms DiophCompression.infiniteFiberStructured_of_nonneg_halves
#print axioms DiophCompression.uniformQuadraticFiberStructureZZ_of_nonneg_halves
#print axioms DiophCompression.weak_target_trivial_on_finite_fibre
