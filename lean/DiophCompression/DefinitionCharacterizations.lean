/-
  DiophCompression/DefinitionCharacterizations.lean — s18 (2026-08-30, claude.ai direct; GPT r17 §8 / APAL-D 4).
  Kernel-checked characterization theorems for the twelve load-bearing definitions displayed in
  manuscript §2, plus DichotomyG and QuadraticProjectionDichotomyZ. Each theorem unfolds the
  definition to the formula printed in the paper; every proof is `Iff.rfl` or `rfl`, so the
  theorem is a definitional restatement and cannot drift from the `def` without failing to compile.
  No production definition is modified; this file only imports.
-/
import DiophCompression.SemanticQuadraticGeneral.Defs

namespace DiophCompression

open MvPolynomial MPUP Classical

/-! ## Representation and bounded resources (MPUP.Spec) -/

theorem representsZ_iff {n r : ℕ} (P : Poly n r) (A : Set (Fin n → ℕ)) :
    RepresentsZ P A ↔ ∀ a, a ∈ A ↔ ∃ y : Fin r → ℤ, evalAt P a y = 0 := Iff.rfl

theorem representsN_iff {n r : ℕ} (P : Poly n r) (A : Set (Fin n → ℕ)) :
    RepresentsN P A ↔ ∀ a, a ∈ A ↔ ∃ y : Fin r → ℕ, evalAt P a (fun i => (y i : ℤ)) = 0 := Iff.rfl

theorem diophN_iff {n : ℕ} (A : Set (Fin n → ℕ)) :
    DiophN A ↔ ∃ r : ℕ, ∃ P : Poly n r, RepresentsN P A := Iff.rfl

theorem withinZ_iff {n : ℕ} (ν δ : ℕ) (A : Set (Fin n → ℕ)) :
    WithinZ ν δ A ↔ ∃ r ≤ ν, ∃ P : Poly n r, P.totalDegree ≤ δ ∧ RepresentsZ P A := Iff.rfl

theorem withinN_iff {n : ℕ} (ν δ : ℕ) (A : Set (Fin n → ℕ)) :
    WithinN ν δ A ↔ ∃ r ≤ ν, ∃ P : Poly n r, P.totalDegree ≤ δ ∧ RepresentsN P A := Iff.rfl

theorem graph_iff {n : ℕ} (e : (Fin n → ℕ) → ℕ) (v : Fin (n + 1) → ℕ) :
    v ∈ graph e ↔ v (Fin.last n) = e (Fin.init v) := Iff.rfl

/-! ## The three achievability predicates (Definitions) -/

theorem specializationAchievable_iff (n q d : ℕ) :
    SpecializationAchievable n q d ↔
      ∃ P : MvPolynomial (Fin n ⊕ Fin q) ℤ, P.totalDegree ≤ d ∧ Function.Injective (specialize P) :=
  Iff.rfl

theorem graphAchievableZ_iff (n r d : ℕ) :
    GraphAchievableZ n r d ↔ ∃ e : (Fin n → ℕ) → ℕ, Function.Injective e ∧ WithinZ r d (graph e) :=
  Iff.rfl

theorem universalAchievableZ_iff (n r d : ℕ) :
    UniversalAchievableZ n r d ↔ ∀ A : Set (Fin n → ℕ), DiophN A → WithinZ r d A := Iff.rfl

/-! ## Capacity functions (CapacityFunctions) -/

theorem capBound_eq (r d : ℕ) : capBound r d = (d + r + 1).choose (r + 2) := rfl

theorem graphCapacityZ_eq (r d : ℕ) :
    graphCapacityZ r d = Nat.findGreatest (fun n => GraphAchievableZ n r d) (capBound r d) := rfl

theorem universalCapacityZ_eq (r d : ℕ) :
    universalCapacityZ r d =
      Nat.findGreatest (fun n => UniversalAchievableZ n r d) (capBound r d + 1) := rfl

/-! ## Fiber sets and the projection dichotomy (SemanticQuadraticGeneral.Defs) -/

namespace SemanticQuadraticGeneral

theorem fiberSetG_iff {r : ℕ} (H : MvPolynomial (Fin (r + 1)) ℤ) (ℓ : Fin (r + 1) → ℤ) (q : ℤ)
    (c : ℕ) :
    c ∈ fiberSetG H ℓ q ↔ ∃ u : Fin r → ℤ, fiberVal H ℓ q (Fin.cons (c : ℤ) u) = 0 := Iff.rfl

theorem fboundG_eq {r : ℕ} (K : ℕ) (ℓ : Fin (r + 1) → ℤ) (q : ℤ) :
    fboundG K ℓ q = (K : ℤ) * ((1 + ∑ i, |ℓ i|) ^ 2 + |q|) := rfl

theorem dichotomyG_iff {r : ℕ} (H : MvPolynomial (Fin (r + 1)) ℤ) :
    DichotomyG H ↔ ∃ K : ℕ, ∀ (ℓ : Fin (r + 1) → ℤ) (q : ℤ),
      (fiberSetG H ℓ q).Infinite ∨ ∀ c ∈ fiberSetG H ℓ q, (c : ℤ) ≤ fboundG K ℓ q := Iff.rfl

theorem quadraticProjectionDichotomyZ_iff (r : ℕ) :
    QuadraticProjectionDichotomyZ r ↔
      ∀ H : MvPolynomial (Fin (r + 1)) ℤ, H.IsHomogeneous 2 → DichotomyG H := Iff.rfl

end SemanticQuadraticGeneral

end DiophCompression

#print axioms DiophCompression.representsZ_iff
#print axioms DiophCompression.representsN_iff
#print axioms DiophCompression.diophN_iff
#print axioms DiophCompression.withinZ_iff
#print axioms DiophCompression.withinN_iff
#print axioms DiophCompression.graph_iff
#print axioms DiophCompression.specializationAchievable_iff
#print axioms DiophCompression.graphAchievableZ_iff
#print axioms DiophCompression.universalAchievableZ_iff
#print axioms DiophCompression.capBound_eq
#print axioms DiophCompression.graphCapacityZ_eq
#print axioms DiophCompression.universalCapacityZ_eq
#print axioms DiophCompression.SemanticQuadraticGeneral.fiberSetG_iff
#print axioms DiophCompression.SemanticQuadraticGeneral.fboundG_eq
#print axioms DiophCompression.SemanticQuadraticGeneral.dichotomyG_iff
#print axioms DiophCompression.SemanticQuadraticGeneral.quadraticProjectionDichotomyZ_iff
