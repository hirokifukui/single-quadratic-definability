/-
  DiophCompression/CapacityBireduction.lean — r06 必須C (session 6, 2026-08-27, claude.ai direct, no CC).
  Statements frozen first: frozen statement file `CapacityBireduction_STATEMENTS.lean` (md5 b5574f27).
  The graph–universality comparison at capacity level, both rings:
    U_R(r,d) ≤ G_R(r,d) + 1                       (U(n+1) ⇒ G(n), Sandwich)
    G_R(r,d) ≤ U_R(r + ν₀ + 1, 2·max{d, δ₀})      (ℕ, graph_to_universality_N)
    G_ℤ(r,d) ≤ U_ℤ(r + ν₀ + 5, 2·max{d, δ₀, 2})   (ℤ, graph_to_universality_Z, four-square guard)
  given a single-parameter universal pair (ν₀, δ₀). This is a BI-REDUCTION WITH EXPLICIT RESOURCE
  DISTORTION (GPT r05 §2.3), not an equivalence at the same (n, r, d); the Lean names of the r05
  layer (`graph_universality_equivalence_{N,Z}`) are kept for reference stability, the prose says
  "comparison theorem". d ≥ 1 because `graphCapacity*_spec` is stated for d ≥ 1 (DegreeZero.lean).
-/
import DiophCompression.CapacityFunctions
import DiophCompression.GraphToUniversalityN
import DiophCompression.GraphToUniversalityZ

namespace DiophCompression

open MPUP

/-- U ≤ G + 1 in capacity form (sandwich, ℤ) — twin of `universalCapacityN_le_graphCapacityN_succ`. -/
theorem universalCapacityZ_le_graphCapacityZ_succ (r d : ℕ) (hd : 1 ≤ d) :
    universalCapacityZ r d ≤ graphCapacityZ r d + 1 := by
  have h := (universalCapacityZ_spec r d _).mpr (le_refl (universalCapacityZ r d))
  cases hu : universalCapacityZ r d with
  | zero => exact Nat.zero_le _
  | succ m =>
    rw [hu] at h
    have := (graphCapacityZ_spec r d hd m).mp (universal_implies_graph_Z h)
    omega

theorem graphCapacityN_le_shiftedUniversalCapacityN {ν₀ δ₀ : ℕ} (hU : UniversalPairN ν₀ δ₀)
    (r d : ℕ) (hd : 1 ≤ d) :
    graphCapacityN r d ≤ universalCapacityN (r + ν₀ + 1) (2 * max d δ₀) :=
  (universalCapacityN_spec _ _ _).mp
    (graph_to_universality_N hU ((graphCapacityN_spec r d hd _).mpr le_rfl))

theorem graphCapacityZ_le_shiftedUniversalCapacityZ {ν₀ δ₀ : ℕ} (hU : UniversalPairZ ν₀ δ₀)
    (r d : ℕ) (hd : 1 ≤ d) :
    graphCapacityZ r d ≤ universalCapacityZ (r + ν₀ + 5) (2 * max d (max δ₀ 2)) :=
  (universalCapacityZ_spec _ _ _).mp
    (graph_to_universality_Z hU ((graphCapacityZ_spec r d hd _).mpr le_rfl))

theorem graph_universality_capacity_bireduction_N {ν₀ δ₀ : ℕ} (hU : UniversalPairN ν₀ δ₀)
    (r d : ℕ) (hd : 1 ≤ d) :
    universalCapacityN r d ≤ graphCapacityN r d + 1 ∧
    graphCapacityN r d ≤ universalCapacityN (r + ν₀ + 1) (2 * max d δ₀) :=
  ⟨universalCapacityN_le_graphCapacityN_succ r d hd, graphCapacityN_le_shiftedUniversalCapacityN hU r d hd⟩

theorem graph_universality_capacity_bireduction_Z {ν₀ δ₀ : ℕ} (hU : UniversalPairZ ν₀ δ₀)
    (r d : ℕ) (hd : 1 ≤ d) :
    universalCapacityZ r d ≤ graphCapacityZ r d + 1 ∧
    graphCapacityZ r d ≤ universalCapacityZ (r + ν₀ + 5) (2 * max d (max δ₀ 2)) :=
  ⟨universalCapacityZ_le_graphCapacityZ_succ r d hd, graphCapacityZ_le_shiftedUniversalCapacityZ hU r d hd⟩

end DiophCompression

#print axioms DiophCompression.universalCapacityZ_le_graphCapacityZ_succ
#print axioms DiophCompression.graphCapacityN_le_shiftedUniversalCapacityN
#print axioms DiophCompression.graphCapacityZ_le_shiftedUniversalCapacityZ
#print axioms DiophCompression.graph_universality_capacity_bireduction_N
#print axioms DiophCompression.graph_universality_capacity_bireduction_Z
