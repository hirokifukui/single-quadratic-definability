/-
  frozen_statements/SummitTarget_STATEMENTS.lean — statement freeze (s28) of DiophCompression/SummitTarget.lean — APAL Structural Theory Gate 5, 必須B (s28, 2026-09-02, claude.ai direct).

  The STRONG summit target. GPT Gate-4 §3 / Q1: the r25 predicate `QuadraticFiberBoundedOrStructured`
  ("for every a the fibre is bounded, or carries a structured certificate") is not vacuous — an infinite
  subset of ℤ is unbounded, so it says exactly "infinite fibre ⇒ certificate" — but it LOSES the uniformity
  that the finite side already has: the finite-fibre theorem gives one constant C_P with
  |c| ≤ C_P·(1 + |a|_∞)² for every parameter point. The strong target below keeps that constant and is
  therefore the statement that unifies the finite and the infinite side. The weak predicate is proved to
  be a corollary (`uniformQuadraticFiberStructureZZ_implies_boundedOrStructured`), i.e. demoted.
  No sorry; std-3.
-/
import DiophCompression.LeafExtraction

namespace DiophCompression

open MvPolynomial MPUP Matrix

variable {n r : ℕ}

/-- `|a|_∞` as a natural number (`0` when `n = 0`), the height used by the finite-fibre theorem. -/
def paramSup (a : Fin n → ℤ) : ℕ := Finset.univ.sup (fun i => (a i).natAbs)

/-- 必須B: the strong summit target — ONE constant `C`, valid at every parameter point: either the whole
    fibre obeys the uniform quadratic height bound, or it carries a structured certificate. -/
def UniformQuadraticFiberStructureZZ (P : Poly (n + 1) r) : Prop :=
  ∃ C : ℕ, ∀ a : Fin n → ℤ,
    (∀ c ∈ fiberZZ P a, |c| ≤ (C : ℤ) * ((1 + paramSup a : ℕ) : ℤ) ^ 2)
      ∨ Nonempty (StructuredCertificate P a)

/-- A uniform quadratic bound and a structured certificate cannot hold at the same parameter point. -/
theorem uniform_bound_certificate_exclusive (P : Poly (n + 1) r) (a : Fin n → ℤ) (C : ℕ)
    (hB : ∀ c ∈ fiberZZ P a, |c| ≤ (C : ℤ) * ((1 + paramSup a : ℕ) : ℤ) ^ 2)
    (cert : StructuredCertificate P a) : False := by
  sorry

/-- DEMOTION (GPT Gate-4 §3): the r25 target is a corollary of the strong one. -/
theorem uniformQuadraticFiberStructureZZ_implies_boundedOrStructured (P : Poly (n + 1) r)
    (h : UniformQuadraticFiberStructureZZ P) : QuadraticFiberBoundedOrStructured P := by
  sorry

/-- The strong target implies the finite-fibre height bound with the SAME constant: on a finite fibre the
    certificate branch is impossible, so the uniform quadratic bound holds. -/
theorem uniformQuadraticFiberStructureZZ_implies_finiteFiberHeight (P : Poly (n + 1) r)
    (h : UniformQuadraticFiberStructureZZ P) :
    ∃ C : ℕ, ∀ a : Fin n → ℤ, (fiberZZ P a).Finite → ∀ c ∈ fiberZZ P a,
      |c| ≤ (C : ℤ) * ((1 + paramSup a : ℕ) : ℤ) ^ 2 := by
  sorry

/-- The strong target implies the clean phase statement: every fibre is either inside the uniform
    quadratic box or infinite. -/
theorem uniformQuadraticFiberStructureZZ_implies_boundedOrInfinite (P : Poly (n + 1) r)
    (h : UniformQuadraticFiberStructureZZ P) :
    ∃ C : ℕ, ∀ a : Fin n → ℤ,
      (∀ c ∈ fiberZZ P a, |c| ≤ (C : ℤ) * ((1 + paramSup a : ℕ) : ℤ) ^ 2) ∨ (fiberZZ P a).Infinite := by
  sorry

/-! ### Compatibility with the output-negation layer (必須C) -/

/-- Transport in the other direction: a solution of `P` is a solution of the flipped polynomial with the
    negated output. -/
theorem negOutputPoly_solution_transport (P : Poly (n + 1) r) (a : Fin n → ℤ) :
    ∀ (c : ℤ) (u : Fin r → ℤ), evalAtZZ P (Fin.snoc a c) u = 0 →
      evalAtZZ (negOutputPoly P) (Fin.snoc a (-c)) (id u) = 0 := by
  sorry

/-- The strong summit target is invariant under output negation: proving it for `P` proves it for the
    flipped polynomial, so the negative half of every integer fibre is covered by the same statement. -/
theorem uniformQuadraticFiberStructureZZ_negOutputPoly (P : Poly (n + 1) r)
    (h : UniformQuadraticFiberStructureZZ P) :
    UniformQuadraticFiberStructureZZ (negOutputPoly P) := by
  sorry

/-- Kind is preserved by that transport (the taxonomy does not degenerate on the negative side). -/
theorem uniformQuadraticFiberStructureZZ_negOutputPoly_kind (P : Poly (n + 1) r) (a : Fin n → ℤ)
    (cert : StructuredCertificate P a) :
    (cert.negOutput id (negOutputPoly_solution_transport P a)).kind = cert.kind := by
  sorry

end DiophCompression
