/-
  DiophCompression/CapacityChainLower.lean — s15 (2026-08-29, claude.ai direct; GPT r14 §9 / 必須F).
  The constructive tree-coding lower bounds for the graph capacity functions, moved VERBATIM out of
  CapacityFunctions.lean so that the capacity definitions (and the Quadratic Witness Inertia closure)
  no longer depend on TreeCoding. Statements and names are unchanged (frozen names graphCapacity{N,Z}_chain_lower).
-/
import DiophCompression.CapacityFunctions
import DiophCompression.TreeCoding

namespace DiophCompression

open MvPolynomial MPUP Classical

/-! ### The chain lower bound, in capacity form -/

theorem graphCapacityN_chain_lower (r b : ℕ) (hb : 1 ≤ b) :
    (b - 1) * (r + 1) + 1 ≤ graphCapacityN r (2 * b) :=
  (graphCapacityN_spec r (2 * b) (by omega) _).mp (graph_achievable_tree_form r b hb)

theorem graphCapacityZ_chain_lower (r β : ℕ) :
    leafCount r β ≤ graphCapacityZ r (2 * (β + 1)) :=
  (graphCapacityZ_spec r (2 * (β + 1)) (by omega) _).mp (chain_graph_achievable_Z (r := r) (β := β))

end DiophCompression

#print axioms DiophCompression.graphCapacityN_chain_lower
#print axioms DiophCompression.graphCapacityZ_chain_lower
