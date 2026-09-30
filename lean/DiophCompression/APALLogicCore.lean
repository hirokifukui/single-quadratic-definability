/-
  DiophCompression/APALLogicCore.lean — APAL r20 Gate 5 (session 22, 2026-08-31, claude.ai direct).
  The dependency closure of THIS file's roots is the centre of the APAL artifact (GPT r19 reply-1 §10 Gate 5).
  One bundled statement plus the individual roots. No new mathematics; no sorry; std-3 expected.
-/
import DiophCompression.OneSortedPPFolding

namespace DiophCompression

/-- The APAL logic core over (ℤ,+,·), bundled:
    (1) no single quadratic equation (any number of integer witnesses) defines the graph of an injection ℤⁿ → ℤ
        for n ≥ 3 (Theorem E_ℤ, rank form);
    (2) a conjunction of quadratic equations does, at every arity (η-chain, 2n−2 witnesses, 2n−1 equations);
    (3) hence SE_2(k) ⊊ PP_2(k) ⊆ SE_4(k) at every relation arity k ≥ 4;
    (4) PP_2 has internal tuple coding: every pp-quadratic A ⊆ ℤⁿ is the preimage of a pp-quadratic B ⊆ ℤ;
    (5) the one-sorted single-quadratic coding arity is 1 or 2 (lower bound). -/
theorem apal_logic_core :
    (∀ n, AtomGraphZZ 2 n → n ≤ 2) ∧
    (∀ n, PPGraphZZ 2 n) ∧
    (∀ k, 4 ≤ k → SingleEqFragmentZZ 2 k ⊂ PPFragmentZZ 2 k ∧ PPFragmentZZ 2 k ⊆ SingleEqFragmentZZ 4 k) ∧
    (∀ (n : ℕ) (A : Set (Fin n → ℤ)), WithinPPZZ 2 A →
      ∃ B : Set (Fin 1 → ℤ), WithinPPZZ 2 B ∧ A = preimageRelZZ (@intTupleCode n) B) ∧
    AtomGraphZZ 1 1 :=
  ⟨atomGraphZZ_degree_two_le_two, ppGraphZZ_degree_two_all, fun _ hk => quadratic_fragment_chain hk,
    fun _ _ hA => pp_quadratic_internal_arity_collapse hA, atomGraphZZ_degree_one_one⟩


/-! ### ERRATA_r19 D3 bridge: binomial form of the universal-pair obstruction
    (frozen in frozen_statements/MPUPCapBound_STATEMENTS.lean) -/

open MPUP in
theorem multiUniversalN_capBound {ν δ : ℕ → ℕ} (h : MultiUniversalN ν δ) (n : ℕ) :
    n ≤ capBound (ν n) (δ n) + 1 := universalAchievableN_le (h n)

open MPUP in
theorem multiUniversalZ_capBound {ν δ : ℕ → ℕ} (h : MultiUniversalZ ν δ) (n : ℕ) :
    n ≤ capBound (ν n) (δ n) + 1 := universalAchievableZ_le (h n)

open MPUP in
theorem multiUniversalZ_choose {ν δ : ℕ → ℕ} (h : MultiUniversalZ ν δ) (n : ℕ) :
    n ≤ (δ n + ν n + 1).choose (ν n + 2) + 1 := multiUniversalZ_capBound h n

end DiophCompression

#print axioms DiophCompression.apal_logic_core
#print axioms DiophCompression.one_sorted_quadratic_no_injective_ternary_graph
#print axioms DiophCompression.atomGraphZZ_degree_two_le_two
#print axioms DiophCompression.ppGraphZZ_degree_two_all
#print axioms DiophCompression.quadratic_fragment_chain
#print axioms DiophCompression.pp_quadratic_internal_arity_collapse
#print axioms DiophCompression.ppZZ_degree_two_subset_singleEquationZZ_degree_four
#print axioms DiophCompression.multiUniversalZ_choose
