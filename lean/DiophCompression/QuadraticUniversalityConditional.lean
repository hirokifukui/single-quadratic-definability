/-
  DiophCompression/QuadraticUniversalityConditional.lean — r13 mandatory A
  (session 13, 2026-08-28, claude.ai direct, no CC).

  Conditional determination of the quadratic universality capacity:
      U_Z(r,2) = 0  and  U_N(r,2) = 0  for all r,
  conditional on two named external inputs, each stated as an explicit
  hypothesis of the theorems (no axiom; see METHODOLOGY §5):

  (H) `QuadraticSolvabilityDecidableZ/N` — for every FIXED integer polynomial
      of total degree ≤ 2 in n parameters and r unknowns, the parametrized
      solvability predicate (in the parameters) is a computable predicate.
      Mathematical source: Grunewald–Segal 1981 (MPCPS 89, 1–5; effective
      procedure for integer solvability of an arbitrary rational quadratic)
      and Grunewald–Segal 2004 (Crelle 569, 13–45; algorithm for positive
      integers and for regions cut by rational affine hyperplanes — hence
      both the ℤ- and ℕ-unknown forms). See
      literature/QUADRATIC_DECIDABILITY_AUDIT.md. This per-polynomial form
      is weaker than the uniform GS algorithm: no uniformity in the
      polynomial is assumed, only that each fixed P yields a decider — the
      "hard-coded polynomial" reading, which is exactly what the DPRM
      contradiction consumes.

  (Hh) `HardDiophantineSetExists` — some Diophantine A ⊆ ℕ^1 (project DiophN,
      ℕ-unknowns as in the AFP) is not a computable predicate. Mathematical
      source: DPRM/MRDP (every r.e. set is Diophantine) + the halting problem.
      Machine-verified externally (Isabelle AFP DPRM_Theorem); not yet in
      mathlib, hence a hypothesis here, never a bare axiom.

  With the unconditional G_Z(r,2) = 2 (SingularAssembly) and S(2,r+1) = r+3,
  these theorems close the three-level classification
      U = 0 < G = 2 < S = r+3   (conditional on (H), (Hh)).
-/
import DiophCompression.CapacityFunctions
import Mathlib.Computability.Halting

namespace DiophCompression

open MPUP

/-- Solvability set of a fixed polynomial with ℤ-unknowns: the parameters for
    which some integer witness vector zeroes `P`. -/
def solvableSetZ {n r : ℕ} (P : Poly n r) : Set (Fin n → ℕ) :=
  {a | ∃ y : Fin r → ℤ, evalAt P a y = 0}

/-- Solvability set of a fixed polynomial with ℕ-unknowns. -/
def solvableSetN {n r : ℕ} (P : Poly n r) : Set (Fin n → ℕ) :=
  {a | ∃ y : Fin r → ℕ, evalAt P a (fun i => (y i : ℤ)) = 0}

/-- Grunewald–Segal decidability, ℤ-unknowns, per-polynomial form: every fixed
    quadratic yields a computable parametrized solvability predicate. -/
def QuadraticSolvabilityDecidableZ : Prop :=
  ∀ (n r : ℕ) (P : Poly n r), P.totalDegree ≤ 2 → ComputablePred (· ∈ solvableSetZ P)

/-- Grunewald–Segal decidability, ℕ-unknowns (GS 2004 positive-integer /
    hyperplane-region algorithm), per-polynomial form. -/
def QuadraticSolvabilityDecidableN : Prop :=
  ∀ (n r : ℕ) (P : Poly n r), P.totalDegree ≤ 2 → ComputablePred (· ∈ solvableSetN P)

/-- DPRM + halting: some Diophantine arity-1 set is not computable. -/
def HardDiophantineSetExists : Prop :=
  ∃ A : Set (Fin 1 → ℕ), DiophN A ∧ ¬ComputablePred (· ∈ A)

/-- Any set represented within degree 2 and ℤ-unknowns is a computable
    predicate, given the GS hypothesis. -/
theorem withinZ_degree_two_is_decidable (H : QuadraticSolvabilityDecidableZ)
    {n ν : ℕ} {A : Set (Fin n → ℕ)} (hA : WithinZ ν 2 A) :
    ComputablePred (· ∈ A) := by
  obtain ⟨r, -, P, hdeg, hrep⟩ := hA
  have hset : A = solvableSetZ P := Set.ext fun a => hrep a
  rw [hset]
  exact H n r P hdeg

/-- Any set represented within degree 2 and ℕ-unknowns is a computable
    predicate, given the GS hypothesis (ℕ form). -/
theorem withinN_degree_two_is_decidable (H : QuadraticSolvabilityDecidableN)
    {n ν : ℕ} {A : Set (Fin n → ℕ)} (hA : WithinN ν 2 A) :
    ComputablePred (· ∈ A) := by
  obtain ⟨r, -, P, hdeg, hrep⟩ := hA
  have hset : A = solvableSetN P := Set.ext fun a => hrep a
  rw [hset]
  exact H n r P hdeg

/-- No quadratic one-parameter universality with ℤ-witnesses, conditionally:
    a universal quadratic pair would make every Diophantine arity-1 set
    computable, contradicting `HardDiophantineSetExists`. No uniform
    algorithm over Diophantine sets is needed — the single hard set's fixed
    representing polynomial suffices. -/
theorem not_universalAchievableZ_one_degree_two
    (H : QuadraticSolvabilityDecidableZ) (Hh : HardDiophantineSetExists) (r : ℕ) :
    ¬ UniversalAchievableZ 1 r 2 := by
  intro hU
  obtain ⟨A, hD, hnc⟩ := Hh
  exact hnc (withinZ_degree_two_is_decidable H (hU A hD))

/-- No quadratic one-parameter universality with ℕ-witnesses, conditionally. -/
theorem not_universalAchievableN_one_degree_two
    (H : QuadraticSolvabilityDecidableN) (Hh : HardDiophantineSetExists) (r : ℕ) :
    ¬ UniversalAchievableN 1 r 2 := by
  intro hU
  obtain ⟨A, hD, hnc⟩ := Hh
  exact hnc (withinN_degree_two_is_decidable H (hU A hD))

/-- Conditional exact quadratic universality capacity, ℤ-witnesses:
    U_Z(r,2) = 0 for every r. Completes U = 0 < G = 2 < S = r+3. -/
theorem universalCapacityZ_degree_two_eq_zero
    (H : QuadraticSolvabilityDecidableZ) (Hh : HardDiophantineSetExists) (r : ℕ) :
    universalCapacityZ r 2 = 0 := by
  by_contra h
  exact not_universalAchievableZ_one_degree_two H Hh r
    ((universalCapacityZ_spec r 2 1).mpr (Nat.one_le_iff_ne_zero.mpr h))

/-- Conditional exact quadratic universality capacity, ℕ-witnesses. -/
theorem universalCapacityN_degree_two_eq_zero
    (H : QuadraticSolvabilityDecidableN) (Hh : HardDiophantineSetExists) (r : ℕ) :
    universalCapacityN r 2 = 0 := by
  by_contra h
  exact not_universalAchievableN_one_degree_two H Hh r
    ((universalCapacityN_spec r 2 1).mpr (Nat.one_le_iff_ne_zero.mpr h))

end DiophCompression

#print axioms DiophCompression.withinZ_degree_two_is_decidable
#print axioms DiophCompression.withinN_degree_two_is_decidable
#print axioms DiophCompression.not_universalAchievableZ_one_degree_two
#print axioms DiophCompression.not_universalAchievableN_one_degree_two
#print axioms DiophCompression.universalCapacityZ_degree_two_eq_zero
#print axioms DiophCompression.universalCapacityN_degree_two_eq_zero
