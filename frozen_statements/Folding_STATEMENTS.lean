/-
  frozen_statements/Folding_STATEMENTS.lean — APAL Logic Pivot, Gate 2 (session 20, 2026-08-30, claude.ai direct).
  THE BRIDGE (desk r19 §1, §7.2; Dr. Fukui ruling s20 option (1)).
  Standard quantity: DDF (arXiv:2102.06941v5) Definition 1.3 / 2.12 — rk∃,n(R) = sup over sets D
  definable with n free variables of the least number of existential quantifiers defining D — here
  RESTRICTED to the degree-≤ d primitive-positive fragment on ℕ-traces (parameters in ℕ, witnesses in ℤ,
  the frozen Spec). DDF Lemma 8.19 mechanism: an injective polynomial pairing folds all arities into arity 1.
  Gate 2 states the degree-bounded, witness-costing form of that mechanism (Theorem F), and the two facts
  that decide its hypothesis at degree 2: PP_2 has an injective ternary graph with ONE witness (Theorem B),
  the single-equation fragment Atom_2 has none (Theorem A(2)).
  Statements only; sorry bodies; frozen before delegation/proof.
-/
import DiophCompression.QuadraticPPSeparation
import DiophCompression.AtomicDegreeRank

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Degree-bounded existential rank on ℕ-traces (pp fragment) -/

/-- Witness rank of `A ⊆ ℕ^n` in the degree-≤ `d` primitive-positive fragment: the least number of
    ℤ-witnesses over all finite systems of integer equations of total degree ≤ `d` representing `A`;
    `⊤` iff `A ∉ PP_d`. (DDF Definition 1.3 quantifier count, degree-bounded, ℕ-traces.) -/
noncomputable def PPWitnessRankZ {n : ℕ} (d : ℕ) (A : Set (Fin n → ℕ)) : WithTop ℕ :=
  ⨅ (r : ℕ) (_ : ∃ m, ∃ S : PolySystem n r m, (∀ i, (S i).totalDegree ≤ d) ∧ SystemRepresentsZ S A),
    (r : WithTop ℕ)

/-- Degree-bounded arity-`n` existential rank: `sup` of `PPWitnessRankZ d` over all `A ∈ PP_d` of
    arity `n`. (DDF Definition 2.12 `rk∃,n`, degree-bounded, pp fragment, ℕ-traces.) -/
noncomputable def PPArityRankZ (d n : ℕ) : WithTop ℕ :=
  ⨆ (A : Set (Fin n → ℕ)) (_ : WithinPPZ d A), PPWitnessRankZ d A

/-- Preimage of a unary relation `B ⊆ ℕ` under `e : ℕ^n → ℕ`. -/
def preimageRel {n : ℕ} (e : (Fin n → ℕ) → ℕ) (B : Set (Fin 1 → ℕ)) : Set (Fin n → ℕ) :=
  {a | (fun _ => e a) ∈ B}

/-- Image of `A ⊆ ℕ^n` under `e : ℕ^n → ℕ`, as a unary relation. -/
def imageRel {n : ℕ} (e : (Fin n → ℕ) → ℕ) (A : Set (Fin n → ℕ)) : Set (Fin 1 → ℕ) :=
  {c | ∃ a ∈ A, e a = c 0}

/-! ### Characterizations (audit surface) -/

theorem ppWitnessRankZ_eq_top_iff {n : ℕ} (d : ℕ) (A : Set (Fin n → ℕ)) :
    PPWitnessRankZ d A = ⊤ ↔ ¬ WithinPPZ d A := by
  sorry

theorem ppWitnessRankZ_le_coe_iff {n : ℕ} (d r : ℕ) (A : Set (Fin n → ℕ)) :
    PPWitnessRankZ d A ≤ r ↔ ∃ r' ≤ r, ∃ m, ∃ S : PolySystem n r' m,
      (∀ i, (S i).totalDegree ≤ d) ∧ SystemRepresentsZ S A := by
  sorry

/-- A single equation is a one-element system: pp witness rank ≤ atomic degree rank. -/
theorem ppWitnessRankZ_le_atomicDegreeRankZ {n : ℕ} (d : ℕ) (A : Set (Fin (n + 1) → ℕ)) :
    PPWitnessRankZ d A ≤ AtomicDegreeRankZ A d := by
  sorry

theorem preimageRel_imageRel {n : ℕ} {e : (Fin n → ℕ) → ℕ} (he : Function.Injective e)
    (A : Set (Fin n → ℕ)) : preimageRel e (imageRel e A) = A := by
  sorry

/-! ### Theorem F — folding in the degree-bounded pp fragment (DDF Lemma 8.19, witness-costing form)

The output of `e` becomes a witness; a ℤ-witness that must range over ℕ costs four squares
(one equation of degree 2, four witnesses) — the constant 5 = 1 + 4 is the ℕ-trace price of folding. -/

theorem ppWitnessRankZ_preimage_le {n d : ℕ} (hd : 2 ≤ d) (e : (Fin n → ℕ) → ℕ)
    (B : Set (Fin 1 → ℕ)) :
    PPWitnessRankZ d (preimageRel e B) ≤ PPWitnessRankZ d (graph e) + 5 + PPWitnessRankZ d B := by
  sorry

theorem ppWitnessRankZ_image_le {n d : ℕ} (hd : 2 ≤ d) (e : (Fin n → ℕ) → ℕ)
    (A : Set (Fin n → ℕ)) :
    PPWitnessRankZ d (imageRel e A) ≤ PPWitnessRankZ d (graph e) + 5 * n + PPWitnessRankZ d A := by
  sorry

/-- Theorem F. An injective graph of witness rank ≤ `r` in `PP_d` (`d ≥ 2`) folds every arity-`n`
    relation of the fragment into arity 1 at the price `r + 5`. -/
theorem ppArityRankZ_fold {n d r : ℕ} (hd : 2 ≤ d) (e : (Fin n → ℕ) → ℕ)
    (he : Function.Injective e) (hr : PPWitnessRankZ d (graph e) ≤ r) :
    PPArityRankZ d n ≤ PPArityRankZ d 1 + (r + 5) := by
  sorry

/-! ### Degree 2: the hypothesis of Theorem F holds in `PP_2` (Theorem B) ... -/

theorem ternaryPair_ppWitnessRankZ_le_one : PPWitnessRankZ 2 (graph ternaryPair) ≤ 1 := by
  sorry

theorem ppArityRankZ_two_three_le : PPArityRankZ 2 3 ≤ PPArityRankZ 2 1 + 6 := by
  sorry

theorem ppArityRankZ_two_finite_transfer (h : PPArityRankZ 2 1 ≠ ⊤) :
    ∀ n, PPArityRankZ 2 n ≠ ⊤ := by
  sorry

/-! ### ... and fails in the single-equation fragment `Atom_2` (Theorem A(2)); the atomic fold costs degree -/

/-- No injective ternary graph has finite atomic rank at degree 2 (Theorem A(2) in rank form). -/
theorem atomicDegreeRankZ_ternary_two_top (e : (Fin 3 → ℕ) → ℕ) (he : Function.Injective e) :
    AtomicDegreeRankZ (graph e) 2 = ⊤ := by
  sorry

/-- Atomic folding (sum of squares of the three equations) exists only at degree `max (2d) 4`. -/
theorem atomicDegreeRankZ_preimage_le {n d : ℕ} (e : (Fin (n + 1) → ℕ) → ℕ)
    (B : Set (Fin 1 → ℕ)) :
    AtomicDegreeRankZ (preimageRel e B) (max (2 * d) 4) ≤
      AtomicDegreeRankZ (graph e) d + 5 + AtomicDegreeRankZ B d := by
  sorry

end DiophCompression
