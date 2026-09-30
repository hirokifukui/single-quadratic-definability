/-
  DiophCompression/UnifiedLower.lean — r06 必須F (session 6, 2026-08-27, claude.ai direct, no CC).
  Statements frozen first: frozen statement file `UnifiedLower_STATEMENTS.lean` (md5 cd87945c).
  For d ≥ 2 the two known constructions are joined: the no-witness Skolem bound G(0,d) = d transported to
  r witnesses by witness monotonicity, and the chain bound G(r, 2b) ≥ (b−1)(r+1)+1 at b = ⌊d/2⌋ transported
  to degree d by degree monotonicity (2⌊d/2⌋ ≤ d). Result: ℓ(r,d) = max{d, (⌊d/2⌋−1)(r+1)+1} ≤ G_R(r,d),
  in both rings, next to the syntactic upper bound C(d+r+1, r+2) (`*_known_region`).
-/
import DiophCompression.CapacityFunctions
import DiophCompression.TreeCoding

namespace DiophCompression

open MPUP

/-- The unified lower bound ℓ(r,d) = max{d, (⌊d/2⌋−1)(r+1)+1}. -/
def unifiedLower (r d : ℕ) : ℕ := max d ((d / 2 - 1) * (r + 1) + 1)

/-- ℤ twin of `graph_achievable_tree_form`. -/
theorem graph_achievable_tree_form_Z (r b : ℕ) (hb : 1 ≤ b) :
    GraphAchievableZ ((b - 1) * (r + 1) + 1) r (2 * b) := by
  have h := chain_graph_achievable_Z r (b - 1)
  rw [show 2 * (b - 1 + 1) = 2 * b by omega] at h
  rw [show (b - 1) * (r + 1) + 1 = leafCount r (b - 1) by unfold leafCount; ring]
  exact h

theorem graph_unified_lower_achievable_N (r d : ℕ) (hd : 2 ≤ d) :
    GraphAchievableN (unifiedLower r d) r d := by
  have h1 : GraphAchievableN d r d :=
    graphAchievableN_mono (Nat.zero_le r) le_rfl (graph_no_witness_achievable d (by omega))
  have h2 : GraphAchievableN ((d / 2 - 1) * (r + 1) + 1) r d :=
    graphAchievableN_mono le_rfl (by omega) (graph_achievable_tree_form r (d / 2) (by omega))
  unfold unifiedLower
  rcases le_total d ((d / 2 - 1) * (r + 1) + 1) with h | h
  · rw [max_eq_right h]; exact h2
  · rw [max_eq_left h]; exact h1

theorem graph_unified_lower_achievable_Z (r d : ℕ) (hd : 2 ≤ d) :
    GraphAchievableZ (unifiedLower r d) r d := by
  have h1 : GraphAchievableZ d r d :=
    graphAchievableZ_mono (Nat.zero_le r) le_rfl (graph_no_witness_achievable_Z d (by omega))
  have h2 : GraphAchievableZ ((d / 2 - 1) * (r + 1) + 1) r d :=
    graphAchievableZ_mono le_rfl (by omega) (graph_achievable_tree_form_Z r (d / 2) (by omega))
  unfold unifiedLower
  rcases le_total d ((d / 2 - 1) * (r + 1) + 1) with h | h
  · rw [max_eq_right h]; exact h2
  · rw [max_eq_left h]; exact h1

theorem graphCapacityN_unified_lower (r d : ℕ) (hd : 2 ≤ d) : unifiedLower r d ≤ graphCapacityN r d :=
  (graphCapacityN_spec r d (by omega) _).mp (graph_unified_lower_achievable_N r d hd)

theorem graphCapacityZ_unified_lower (r d : ℕ) (hd : 2 ≤ d) : unifiedLower r d ≤ graphCapacityZ r d :=
  (graphCapacityZ_spec r d (by omega) _).mp (graph_unified_lower_achievable_Z r d hd)

/-- Known region on one line: ℓ(r,d) ≤ G_ℕ(r,d) ≤ C(d+r+1, r+2). -/
theorem graphCapacityN_known_region (r d : ℕ) (hd : 2 ≤ d) :
    unifiedLower r d ≤ graphCapacityN r d ∧ graphCapacityN r d ≤ capBound r d :=
  ⟨graphCapacityN_unified_lower r d hd, graphCapacityN_upper r d⟩

theorem graphCapacityZ_known_region (r d : ℕ) (hd : 2 ≤ d) :
    unifiedLower r d ≤ graphCapacityZ r d ∧ graphCapacityZ r d ≤ capBound r d :=
  ⟨graphCapacityZ_unified_lower r d hd, graphCapacityZ_upper r d⟩

end DiophCompression

#print axioms DiophCompression.graph_achievable_tree_form_Z
#print axioms DiophCompression.graph_unified_lower_achievable_N
#print axioms DiophCompression.graph_unified_lower_achievable_Z
#print axioms DiophCompression.graphCapacityN_unified_lower
#print axioms DiophCompression.graphCapacityZ_unified_lower
#print axioms DiophCompression.graphCapacityN_known_region
#print axioms DiophCompression.graphCapacityZ_known_region
