/-
  frozen_statements/LeafDataD3D6_STATEMENTS.lean — statement freeze (s28) of
  DiophCompression/SemanticQuadratic/LeafDataD3D6.lean (必須F step 2 pilot: leaves D3, D4, D6 in data form).
-/
import DiophCompression.SemanticQuadratic.FiberDefs
import DiophCompression.SemanticQuadratic.Class_D4

namespace DiophCompression.SemanticQuadratic

open MPUP

structure LinearFiberFamily (A B C l m q : ℤ) where
  c₀ : ℕ
  s : ℕ
  s_pos : 1 ≤ s
  ut : ℕ → ℤ
  fam : ∀ t : ℕ, fq A B C l m q ((c₀ + s * t : ℕ) : ℤ) (ut t) = 0

theorem linearFamily_nonempty (A B C l m q : ℤ) (c₀ : ℕ) (s : ℕ) (hs : 1 ≤ s)
    (ut : ℕ → ℤ) (hfam : ∀ t : ℕ, fq A B C l m q ((c₀ + s * t : ℕ) : ℤ) (ut t) = 0) :
    Nonempty (LinearFiberFamily A B C l m q) := by
  sorry

theorem fiberSet_infinite_of_linearFamily {A B C l m q : ℤ} (F : LinearFiberFamily A B C l m q) :
    (fiberSet A B C l m q).Infinite := by
  sorry

def DichotomyLinearData (A B C : ℤ) : Prop :=
  ∃ K : ℕ, ∀ l m q : ℤ, Nonempty (LinearFiberFamily A B C l m q) ∨
    ∀ c ∈ fiberSet A B C l m q, (c : ℤ) ≤ fbound K l m q

theorem dichotomy_of_dichotomyLinearData {A B C : ℤ} (h : DichotomyLinearData A B C) :
    Dichotomy A B C := by
  sorry

theorem dichotomy_degenerate_C_zero_data (A B C : ℤ) (h : disc A B C = 0) (hC : C = 0) :
    DichotomyLinearData A B C := by
  sorry

theorem dichotomy_square_C_zero_data (A B C : ℤ) (h : 0 < disc A B C) (hC : C = 0) :
    DichotomyLinearData A B C := by
  sorry

theorem dichotomy_square_C_ne_data (A B C : ℤ) (h : 0 < disc A B C) (hs : IsSquare (disc A B C)) (hC : C ≠ 0) :
    DichotomyLinearData A B C := by
  sorry

theorem dichotomy_degenerate_C_zero_of_data (A B C : ℤ) (h : disc A B C = 0) (hC : C = 0) :
    Dichotomy A B C := by
  sorry

theorem dichotomy_square_C_zero_of_data (A B C : ℤ) (h : 0 < disc A B C) (hC : C = 0) :
    Dichotomy A B C := by
  sorry

theorem dichotomy_square_C_ne_of_data (A B C : ℤ) (h : 0 < disc A B C) (hs : IsSquare (disc A B C))
    (hC : C ≠ 0) : Dichotomy A B C := by
  sorry

end DiophCompression.SemanticQuadratic
