/-
  DiophCompression/HaltingTransport.lean — APAL Structural Theory Gate 2, kernel item 必須B part 1
  (session 25, 2026-09-01, claude.ai direct, 0 CC).
  REC(k) ⊊ RE(k) for every positive arity, UNCONDITIONALLY: mathlib's halting problem
  (ComputablePred.halting_problem, ComputablePred.halting_problem_re) transported along
  v ↦ ofNat Code (encode (v 0)), with the section c ↦ (fun _ => ofNat ℤ (encode c)).
  Statements frozen in frozen_statements/HaltingTransport_STATEMENTS.lean.
-/
import DiophCompression.ComputabilityFragments

namespace DiophCompression

open MvPolynomial MPUP

/-- The halting relation transported to ℤ^{k+1}: read coordinate 0 as the code of a partial recursive
    function (through the ℤ-encoding) and ask whether it halts on input 0. -/
def haltingRelZZ (k : ℕ) : Set (Fin (k + 1) → ℤ) :=
  {v | ((Denumerable.ofNat Nat.Partrec.Code (Encodable.encode (v 0))).eval 0).Dom}

/-- Decoding map ℤ^{k+1} → Code. -/
def codeOfVec (k : ℕ) (v : Fin (k + 1) → ℤ) : Nat.Partrec.Code :=
  Denumerable.ofNat Nat.Partrec.Code (Encodable.encode (v 0))

/-- Section Code → ℤ^{k+1} (constant vector). -/
def vecOfCode (k : ℕ) (c : Nat.Partrec.Code) : Fin (k + 1) → ℤ :=
  fun _ => Denumerable.ofNat ℤ (Encodable.encode c)

theorem codeOfVec_vecOfCode (k : ℕ) (c : Nat.Partrec.Code) : codeOfVec k (vecOfCode k c) = c := by
  show Denumerable.ofNat Nat.Partrec.Code (Encodable.encode (Denumerable.ofNat ℤ (Encodable.encode c))) = c
  rw [Denumerable.encode_ofNat, Denumerable.ofNat_encode]

theorem primrec_codeOfVec (k : ℕ) : Primrec (codeOfVec k) :=
  (Primrec.ofNat Nat.Partrec.Code).comp
    (Primrec.encode.comp (Primrec.fin_app.comp Primrec.id (Primrec.const 0)))

theorem primrec_vecOfCode (k : ℕ) : Primrec (vecOfCode k) := by
  refine Primrec.fin_curry.2 ?_
  exact (Primrec.ofNat ℤ).comp (Primrec.encode.comp Primrec.fst)

theorem mem_haltingRelZZ_iff (k : ℕ) (v : Fin (k + 1) → ℤ) :
    v ∈ haltingRelZZ k ↔ ((codeOfVec k v).eval 0).Dom := Iff.rfl

/-- The transported halting relation is r.e. -/
theorem haltingRelZZ_re (k : ℕ) : REPred fun v => v ∈ haltingRelZZ k := by
  have h : REPred fun c : Nat.Partrec.Code => (c.eval 0).Dom := ComputablePred.halting_problem_re 0
  exact Partrec.comp h (primrec_codeOfVec k).to_comp

/-- The transported halting relation is not recursive. -/
theorem haltingRelZZ_not_computablePred (k : ℕ) : ¬ ComputablePred fun v => v ∈ haltingRelZZ k := by
  intro hA
  refine ComputablePred.halting_problem 0 ?_
  obtain ⟨g, hg, hp⟩ := ComputablePred.computable_iff.1 hA
  refine ComputablePred.computable_iff.2 ⟨fun c => g (vecOfCode k c), hg.comp (primrec_vecOfCode k).to_comp, ?_⟩
  funext c
  have := congrFun hp (vecOfCode k c)
  simp only [mem_haltingRelZZ_iff, codeOfVec_vecOfCode] at this
  exact this

/-- Unconditional: REC(k) ⊊ RE(k) for every positive arity. -/
theorem recursive_strictly_contained_re (k : ℕ) : RecFragmentZZ (k + 1) ⊂ REFragmentZZ (k + 1) := by
  rw [Set.ssubset_def]
  refine ⟨recFragmentZZ_subset_reFragmentZZ _, fun hsub => ?_⟩
  have hmem : haltingRelZZ k ∈ REFragmentZZ (k + 1) := haltingRelZZ_re k
  exact haltingRelZZ_not_computablePred k (hsub hmem)

/-- The strict phase diagram at arity k ≥ 2 (GS + DPRM): SE_2(k) ⊊ REC(k) ⊊ RE(k) = PP_2(k) = SE_4(k). -/
theorem relation_phase_diagram_strict (hGS : QuadraticSolvabilityDecidableZZ) (hD : DPRM_ZZ) (k : ℕ) :
    SingleEqFragmentZZ 2 (k + 2) ⊂ RecFragmentZZ (k + 2) ∧
      RecFragmentZZ (k + 2) ⊂ REFragmentZZ (k + 2) ∧
      REFragmentZZ (k + 2) = PPFragmentZZ 2 (k + 2) ∧
      PPFragmentZZ 2 (k + 2) = SingleEqFragmentZZ 4 (k + 2) := by
  obtain ⟨h₁, _, h₃, h₄⟩ := relation_phase_diagram hGS hD k
  exact ⟨h₁, recursive_strictly_contained_re (k + 1), h₃, h₄⟩

#print axioms DiophCompression.haltingRelZZ_re
#print axioms DiophCompression.haltingRelZZ_not_computablePred
#print axioms DiophCompression.recursive_strictly_contained_re
#print axioms DiophCompression.relation_phase_diagram_strict

end DiophCompression
