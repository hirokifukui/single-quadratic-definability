/-
  frozen_statements/PeriodicProgressionCore_STATEMENTS.lean — statement freeze (s28) of
  DiophCompression/PeriodicProgressionCore.lean.
-/
import Mathlib

namespace DiophCompression

structure PeriodicProgression (S : Set ℕ) where
  c₀ : ℕ
  T : ℕ
  T_pos : 1 ≤ T
  mem : ∀ t : ℕ, c₀ + t * T ∈ S

theorem infinite_of_periodicProgression {S : Set ℕ} (F : PeriodicProgression S) : S.Infinite := by
  sorry

theorem periodicProgression_or_empty (S : Set ℕ) (M : ℕ) (hM : 1 ≤ M)
    (h : ∀ c, c ∈ S ↔ c + M ∈ S) : Nonempty (PeriodicProgression S) ∨ S = ∅ := by
  sorry

theorem periodic_infinite_or_empty_of_data (S : Set ℕ) (M : ℕ) (hM : 1 ≤ M)
    (h : ∀ c, c ∈ S ↔ c + M ∈ S) : S.Infinite ∨ S = ∅ := by
  sorry

end DiophCompression
