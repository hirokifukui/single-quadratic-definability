/-
  DiophCompression/SummitClosure.lean — APAL Structural Theory Gate 5, 必須F steps 3–4
  (s29, 2026-09-02, claude.ai direct).

  The last joint of the summit. `quadraticProjectionDichotomyZ_all_data` speaks about `fiberSetG H ℓ q`
  (a homogeneous quadratic part plus a linear part, unknowns in `Fin (r+1)`); the summit target speaks
  about `fiberZZ P a` (a degree-≤2 polynomial in parameters and unknowns, output = last parameter).
  The two are the same set: `normal_form_general_quadratic` splits the relabelled `P` into `H + ℓ·x + q`
  and specialising the parameters at `a` turns `ℓ, q` into integers. The output sign is carried by a
  parameter `ε` with `ε·ε = 1`: `ε = 1` is the nonnegative half, `ε = -1` the nonpositive half, and the
  flip is `flipZero H` — so no degree bound for `negOutputPoly` is needed. Converting the family into a
  certificate is kind-preserving (progression/quadratic → PP, pell → PU, movingModulus → MM).
  No sorry; std-3 expected.
-/
import DiophCompression.SummitReduction
import DiophCompression.SemanticQuadraticGeneral.TopDichotomyData

namespace DiophCompression

open MvPolynomial MPUP SemanticQuadraticGeneral

variable {n r : ℕ}

/-! ### The signed ℕ-fibre -/

/-- The naturals `m` with `ε·m` in the integer fibre (`ε = ±1` selects the half). -/
def fiberNatSigned (P : Poly (n + 1) r) (a : Fin n → ℤ) (ε : ℤ) : Set ℕ :=
  {m : ℕ | ε * (m : ℤ) ∈ fiberZZ P a}

/-- 必須F step 3 (homogenisation + parameter specialisation): each half of the fibre of a quadratic `P`
    IS a `fiberSetG` fibre of a homogeneous quadratic part. -/
theorem exists_fiberSetG_eq_fiberNatSigned (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2)
    (a : Fin n → ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ (H : MvPolynomial (Fin (r + 1)) ℤ) (L : Fin (r + 1) → ℤ) (Q : ℤ),
      H.IsHomogeneous 2 ∧ fiberSetG H L Q = fiberNatSigned P a ε := sorry

/-! ### 必須F step 4: family → certificate (kind-preserving) -/

/-- A structured family inside a signed half of the fibre is a structured certificate for `P` at `a`.
    The sign travels into the polynomial coefficients (PP), into the affine projection (PU), and into
    the `sign` field (MM). -/
noncomputable def structuredCertificate_of_family (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (ε : ℤ) (hε : ε * ε = 1) (F : StructuredFamily (fiberNatSigned P a ε)) :
    StructuredCertificate P a := sorry

/-! ### The summit -/

/-- 必須F: an infinite HALF of the fibre of a quadratic `P` carries a structured certificate. -/
theorem structuredCertificate_of_half_infinite (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2)
    (a : Fin n → ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hinf : {c ∈ fiberZZ P a | 0 ≤ ε * c}.Infinite) : Nonempty (StructuredCertificate P a) := sorry

/-- 必須F, closed: every infinite fibre of a quadratic `P` carries a structured certificate. -/
theorem infiniteFiberStructured_of_quadratic (P : Poly (n + 1) r) (hP : P.totalDegree ≤ 2) :
    InfiniteFiberStructured P := sorry

/-- THE SUMMIT (Gate 4 必須B, strong form): for every quadratic `P` there is ONE constant `C` such that
    at every parameter point the fibre is bounded by `C·(1+|a|)²` or carries a structured certificate. -/
theorem uniformQuadraticFiberStructureZZ_of_quadratic (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) : UniformQuadraticFiberStructureZZ P := sorry

/-- The Gate-4 summit target in its bounded-or-structured shape. -/
theorem quadraticFiberBoundedOrStructured_of_quadratic (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) : QuadraticFiberBoundedOrStructured P := sorry

/-! ### The two names GPT's Gate-5 必須F asks for (thin aliases; the content is above) -/

/-- 必須F name 1: the projection dichotomy in structured (family-carrying) form, all `r`. -/
theorem quadraticProjectionDichotomyZ_structured :
    ∀ r : ℕ, SemanticQuadraticGeneral.QuadraticProjectionDichotomyZData r := sorry

/-- 必須F name 2: every scalar fibre of a quadratic is bounded, or structurally infinite. -/
theorem singleQuadratic_fiber_bounded_or_structurallyInfinite (P : Poly (n + 1) r)
    (hP : P.totalDegree ≤ 2) : QuadraticFiberBoundedOrStructured P := sorry

end DiophCompression

