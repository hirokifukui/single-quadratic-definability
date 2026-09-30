/-
  frozen_statements/OneSortedPPFolding_STATEMENTS.lean — APAL r20 Gate 4 (session 22, 2026-08-31, claude.ai direct).
  GPT r19 reply-1 §6 / §10 Gate 4: the standard pp arity-collapse over ℤ. The pp-quadratic fragment is closed under
  image and preimage along the explicit injection intTupleCode : ℤⁿ → ℤ, hence every pp-quadratic relation on ℤⁿ is
  the preimage of a unary pp-quadratic relation (internal tuple coding at degree 2). Degree kept general d ≥ 2.
  Witness overhead is stated, not optimized. Statements only; sorry bodies.
-/
import DiophCompression.OneSortedFragments

namespace DiophCompression

open MvPolynomial MPUP

/-- `e⁻¹(B) ⊆ ℤⁿ` for unary `B ⊆ ℤ¹`. -/
def preimageRelZZ {n : ℕ} (e : (Fin n → ℤ) → ℤ) (B : Set (Fin 1 → ℤ)) : Set (Fin n → ℤ) :=
  {a | (fun _ : Fin 1 => e a) ∈ B}

/-- `e(A) ⊆ ℤ¹` for `A ⊆ ℤⁿ`. -/
def imageRelZZ {n : ℕ} (e : (Fin n → ℤ) → ℤ) (A : Set (Fin n → ℤ)) : Set (Fin 1 → ℤ) :=
  {c | ∃ a ∈ A, c 0 = e a}

theorem mem_preimageRelZZ {n : ℕ} (e : (Fin n → ℤ) → ℤ) (B : Set (Fin 1 → ℤ)) (a : Fin n → ℤ) :
    a ∈ preimageRelZZ e B ↔ (fun _ : Fin 1 => e a) ∈ B := by sorry

theorem mem_imageRelZZ {n : ℕ} (e : (Fin n → ℤ) → ℤ) (A : Set (Fin n → ℤ)) (c : Fin 1 → ℤ) :
    c ∈ imageRelZZ e A ↔ ∃ a ∈ A, c 0 = e a := by sorry

theorem preimageRelZZ_imageRelZZ {n : ℕ} {e : (Fin n → ℤ) → ℤ} (he : Function.Injective e)
    (A : Set (Fin n → ℤ)) : preimageRelZZ e (imageRelZZ e A) = A := by sorry

/-- Preimage preservation with explicit overhead: if `graphZZ e` has an (rG, mG) system and `B` a (q, k) system,
    all of degree ≤ d, then `e⁻¹(B)` has a (1 + rG + q, mG + k) system of degree ≤ d. -/
theorem withinPPZZ_preimage_of_systems {n rG mG q k d : ℕ} (e : (Fin n → ℤ) → ℤ)
    (G : PolySystem (n + 1) rG mG) (hGd : ∀ i, (G i).totalDegree ≤ d) (hG : SystemRepresentsZZ G (graphZZ e))
    (T : PolySystem 1 q k) (hTd : ∀ j, (T j).totalDegree ≤ d) (B : Set (Fin 1 → ℤ))
    (hT : SystemRepresentsZZ T B) :
    ∃ S : PolySystem n (1 + rG + q) (mG + k), (∀ i, (S i).totalDegree ≤ d) ∧
      SystemRepresentsZZ S (preimageRelZZ e B) := by sorry

/-- Image preservation with explicit overhead: `e(A)` has an (n + rG + q, mG + k) system. -/
theorem withinPPZZ_image_of_systems {n rG mG q k d : ℕ} (e : (Fin n → ℤ) → ℤ)
    (G : PolySystem (n + 1) rG mG) (hGd : ∀ i, (G i).totalDegree ≤ d) (hG : SystemRepresentsZZ G (graphZZ e))
    (T : PolySystem n q k) (hTd : ∀ j, (T j).totalDegree ≤ d) (A : Set (Fin n → ℤ))
    (hT : SystemRepresentsZZ T A) :
    ∃ S : PolySystem 1 (n + rG + q) (mG + k), (∀ i, (S i).totalDegree ≤ d) ∧
      SystemRepresentsZZ S (imageRelZZ e A) := by sorry

theorem withinPPZZ_preimage_intTupleCode {n d : ℕ} (hd : 2 ≤ d) {B : Set (Fin 1 → ℤ)}
    (hB : WithinPPZZ d B) : WithinPPZZ d (preimageRelZZ (@intTupleCode n) B) := by sorry

theorem withinPPZZ_image_intTupleCode {n d : ℕ} (hd : 2 ≤ d) {A : Set (Fin n → ℤ)}
    (hA : WithinPPZZ d A) : WithinPPZZ d (imageRelZZ (@intTupleCode n) A) := by sorry

/-- Internal arity collapse at degree 2: every pp-quadratic relation on ℤⁿ is the preimage under the explicit
    pp-quadratic injection `intTupleCode` of a pp-quadratic relation on ℤ. -/
theorem pp_quadratic_internal_arity_collapse {n : ℕ} {A : Set (Fin n → ℤ)} (hA : WithinPPZZ 2 A) :
    ∃ B : Set (Fin 1 → ℤ), WithinPPZZ 2 B ∧ A = preimageRelZZ (@intTupleCode n) B := by sorry

theorem ppFragmentZZ_two_arity_collapse (n : ℕ) :
    ∀ A ∈ PPFragmentZZ 2 n, ∃ B ∈ PPFragmentZZ 2 1, A = preimageRelZZ (@intTupleCode n) B := by sorry

end DiophCompression
