/-
  DiophCompression/UniversalSpectrumLower.lean — r05 必須F (session 5, 2026-08-27, claude.ai direct, no CC).
  The chain lower bound carried to universality (GPT r04: "r05 の最も重要な統合定理"):
    UniversalPairN ν₀ δ₀, b ≥ 1 ⟹ UniversalAchievableN ((b−1)(r+1)+1) (r+ν₀+1) (2·max(2b, δ₀)),
  = graph_to_universality_N ∘ graph_achievable_tree_form. ℤ corollary with the 必須D resource cost
  (r+ν₀+5 witnesses, degree 2·max(2(β+1), δ₀, 2)). Capacity forms via universalCapacity*_spec.
  Together with universalCapacity*_upper (weighted obstruction) both regions live on one spectrum:
    (b−1)(r+1)+1 ≤ U_ℕ(r+ν₀+1, 2·max(2b,δ₀))  and  U_R(r,d) ≤ C(d+r+1,r+2)+1.
-/
import DiophCompression.GraphToUniversalityN
import DiophCompression.GraphToUniversalityZ
import DiophCompression.CapacityFunctions
import DiophCompression.TreeCoding

namespace DiophCompression

open MvPolynomial MPUP

theorem universal_spectrum_lower_N {ν₀ δ₀ : ℕ} (hU : UniversalPairN ν₀ δ₀) (r b : ℕ) (hb : 1 ≤ b) :
    UniversalAchievableN ((b - 1) * (r + 1) + 1) (r + ν₀ + 1) (2 * max (2 * b) δ₀) :=
  graph_to_universality_N hU (graph_achievable_tree_form r b hb)

theorem universal_spectrum_lower_Z {ν₀ δ₀ : ℕ} (hU : UniversalPairZ ν₀ δ₀) (r β : ℕ) :
    UniversalAchievableZ (leafCount r β) (r + ν₀ + 5) (2 * max (2 * (β + 1)) (max δ₀ 2)) :=
  graph_to_universality_Z hU (chain_graph_achievable_Z (r := r) (β := β))

theorem universalCapacityN_chain_lower {ν₀ δ₀ : ℕ} (hU : UniversalPairN ν₀ δ₀) (r b : ℕ) (hb : 1 ≤ b) :
    (b - 1) * (r + 1) + 1 ≤ universalCapacityN (r + ν₀ + 1) (2 * max (2 * b) δ₀) :=
  (universalCapacityN_spec _ _ _).mp (universal_spectrum_lower_N hU r b hb)

theorem universalCapacityZ_chain_lower {ν₀ δ₀ : ℕ} (hU : UniversalPairZ ν₀ δ₀) (r β : ℕ) :
    leafCount r β ≤ universalCapacityZ (r + ν₀ + 5) (2 * max (2 * (β + 1)) (max δ₀ 2)) :=
  (universalCapacityZ_spec _ _ _).mp (universal_spectrum_lower_Z hU r β)

/-- Both regions on one spectrum (ℕ): achievable arity ≥ (b−1)(r+1)+1 at (r+ν₀+1, 2·max(2b,δ₀)), and
    every achievable arity at (r', d') is ≤ C(d'+r'+1, r'+2) + 1. -/
theorem universal_spectrum_sandwich_N {ν₀ δ₀ : ℕ} (hU : UniversalPairN ν₀ δ₀) (r b : ℕ) (hb : 1 ≤ b) :
    (b - 1) * (r + 1) + 1 ≤ universalCapacityN (r + ν₀ + 1) (2 * max (2 * b) δ₀) ∧
    universalCapacityN (r + ν₀ + 1) (2 * max (2 * b) δ₀)
      ≤ capBound (r + ν₀ + 1) (2 * max (2 * b) δ₀) + 1 :=
  ⟨universalCapacityN_chain_lower hU r b hb, universalCapacityN_upper _ _⟩

end DiophCompression

#print axioms DiophCompression.universal_spectrum_lower_N
#print axioms DiophCompression.universal_spectrum_lower_Z
#print axioms DiophCompression.universalCapacityN_chain_lower
#print axioms DiophCompression.universalCapacityZ_chain_lower
#print axioms DiophCompression.universal_spectrum_sandwich_N
