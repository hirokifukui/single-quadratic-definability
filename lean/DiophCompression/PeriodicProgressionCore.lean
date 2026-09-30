/-
  DiophCompression/PeriodicProgressionCore.lean — APAL Structural Theory Gate 5, 必須F step 2
  (s28, 2026-09-02, claude.ai direct).

  The periodic family pattern in DATA-CARRYING form, generic in the set and with NO project imports, so
  that every leaf that is periodic (A3 in `fiberSetM`, B3 in `fiberSetSG`, B1b in `fiberSet2`) can use it
  without an import cycle. `periodic_infinite_or_empty` builds the progression `c₀ + t·T` internally and
  then discards it; here it is kept. No sorry; std-3.
-/
import Mathlib

namespace DiophCompression

/-- An explicit arithmetic progression inside a set of naturals: base `c₀`, period `T ≥ 1`. -/
structure PeriodicProgression (S : Set ℕ) where
  c₀ : ℕ
  T : ℕ
  T_pos : 1 ≤ T
  mem : ∀ t : ℕ, c₀ + t * T ∈ S

/-- Soundness: such a progression makes the set infinite. -/
theorem infinite_of_periodicProgression {S : Set ℕ} (F : PeriodicProgression S) : S.Infinite := by
  apply Set.infinite_of_not_bddAbove
  intro ⟨b, hb⟩
  have := hb (F.mem (b + 1))
  have := F.T_pos
  nlinarith

/-- Data-carrying twin of `periodic_infinite_or_empty`, with the SAME argument order. -/
theorem periodicProgression_or_empty (S : Set ℕ) (M : ℕ) (hM : 1 ≤ M)
    (h : ∀ c, c ∈ S ↔ c + M ∈ S) : Nonempty (PeriodicProgression S) ∨ S = ∅ := by
  by_cases hS : S = ∅
  · exact Or.inr hS
  · left
    obtain ⟨c₀, hc₀⟩ := Set.nonempty_iff_ne_empty.mpr hS
    have hmem : ∀ t : ℕ, c₀ + t * M ∈ S := by
      intro t
      induction t with
      | zero => simpa using hc₀
      | succ t ih =>
        have := (h (c₀ + t * M)).mp ih
        convert this using 1; ring
    exact ⟨⟨c₀, M, hM, hmem⟩⟩

/-- The sealed lemma is a consequence: nothing is lost by strengthening. -/
theorem periodic_infinite_or_empty_of_data (S : Set ℕ) (M : ℕ) (hM : 1 ≤ M)
    (h : ∀ c, c ∈ S ↔ c + M ∈ S) : S.Infinite ∨ S = ∅ := by
  rcases periodicProgression_or_empty S M hM h with hF | hE
  · exact Or.inl (hF.elim fun F => infinite_of_periodicProgression F)
  · exact Or.inr hE

end DiophCompression

#print axioms DiophCompression.infinite_of_periodicProgression
#print axioms DiophCompression.periodicProgression_or_empty
#print axioms DiophCompression.periodic_infinite_or_empty_of_data
