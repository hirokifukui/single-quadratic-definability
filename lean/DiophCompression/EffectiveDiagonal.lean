/-
  DiophCompression/EffectiveDiagonal.lean — APAL Structural Theory Gate 3, 宿題群2 (Effective Fragment
  Diagonalization Lemma), session 26, 2026-09-01, claude.ai direct. Statements frozen in
  frozen_statements/EffectiveDiagonal_STATEMENTS.lean.

  The abstract principle behind UnaryDiagonal.lean: for ANY Primcodable code type `C` with an interpretation
  `interp : C → Set (ℤ^{k+1})`, if a family `F` of relations is coded (every member is some `interp e`) and
  membership `v ∈ interp e` is uniformly decidable in `(e, v)`, then the diagonal relation
    D := { v | the code read off `v 0` does not accept `v` }
  is recursive and lies outside `F`. Instances: SE_2 with the STANDARD quadratic codes (QuadraticCodes.lean)
  under the code-uniform Grunewald–Segal hypothesis — a re-derivation of SE_2 ⊊ REC at every positive arity.
  Invalid codes (`decode` = none) are accepted into D (fixed behaviour). No sorry; std-3 expected.
-/
import DiophCompression.QuadraticCodes

namespace DiophCompression

open MvPolynomial MPUP

/-- The effective diagonal of a coded family: `v ∈ D` iff the code decoded from `v 0` (if any) does not
    accept `v`. -/
def effDiagonal {C : Type} [Primcodable C] (k : ℕ) (interp : C → Set (Fin (k + 1) → ℤ)) :
    Set (Fin (k + 1) → ℤ) :=
  {v | ∀ e : C, (Encodable.decode (Encodable.encode (v 0)) : Option C) = some e → v ∉ interp e}

/-- A coded family: every member of `F` is `interp e` for some code `e`. -/
def CodedFamily {C : Type} (k : ℕ) (interp : C → Set (Fin (k + 1) → ℤ))
    (F : Set (Set (Fin (k + 1) → ℤ))) : Prop :=
  ∀ A ∈ F, ∃ e : C, interp e = A

/-- Uniform membership decidability of a coded family. -/
def UniformlyDecidable {C : Type} [Primcodable C] (k : ℕ) (interp : C → Set (Fin (k + 1) → ℤ)) : Prop :=
  ComputablePred fun p : C × (Fin (k + 1) → ℤ) => p.2 ∈ interp p.1

/-- Effective diagonalization, part 1: the diagonal is recursive under uniform decidability. -/
theorem effDiagonal_computablePred {C : Type} [Primcodable C] (k : ℕ) (interp : C → Set (Fin (k + 1) → ℤ))
    (h : UniformlyDecidable k interp) : ComputablePred fun v => v ∈ effDiagonal k interp := by
  obtain ⟨g, hg, hpg⟩ := ComputablePred.computable_iff.1 h
  have hdec : Computable fun v : Fin (k + 1) → ℤ => (Encodable.decode (Encodable.encode (v 0)) : Option C) :=
    Computable.decode.comp (Computable.encode.comp (Primrec.fin_app.comp Primrec.id (Primrec.const 0)).to_comp)
  have hf : Computable fun v : Fin (k + 1) → ℤ =>
      Option.casesOn (motive := fun _ => Bool) (Encodable.decode (Encodable.encode (v 0)) : Option C) true
        (fun e => !g (e, v)) := by
    refine Computable.option_casesOn hdec (Computable.const true) ?_
    exact Primrec.not.to_comp.comp (hg.comp (Computable.pair Computable.snd Computable.fst))
  refine ComputablePred.computable_iff.2 ⟨_, hf, ?_⟩
  funext v
  have hmem : ∀ e : C, (v ∈ interp e) = (g (e, v) = true) := fun e => congrFun hpg (e, v)
  simp only [effDiagonal, Set.mem_setOf_eq]
  rcases hd : (Encodable.decode (Encodable.encode (v 0)) : Option C) with _ | e
  · simp
  · simp only [Option.some.injEq, forall_eq', Bool.not_eq_eq_eq_not, Bool.not_true]
    rw [hmem e]
    simp

/-- Effective diagonalization, part 2: the diagonal is not in any coded family (self-application). -/
theorem effDiagonal_not_mem {C : Type} [Primcodable C] (k : ℕ) (interp : C → Set (Fin (k + 1) → ℤ))
    (F : Set (Set (Fin (k + 1) → ℤ))) (hF : CodedFamily k interp F) : effDiagonal k interp ∉ F := by
  intro hD
  obtain ⟨e, he⟩ := hF _ hD
  set v : Fin (k + 1) → ℤ := fun _ => Denumerable.ofNat ℤ (Encodable.encode e) with hv
  have hdec : (Encodable.decode (Encodable.encode (v 0)) : Option C) = some e := by
    simp only [hv, Denumerable.encode_ofNat]
    exact Encodable.encodek e
  by_cases hmem : v ∈ effDiagonal k interp
  · have := hmem e hdec
    rw [he] at this
    exact this hmem
  · apply hmem
    intro e' he'
    rw [hdec, Option.some.injEq] at he'
    subst he'
    rw [he]
    exact hmem

/-- Effective Fragment Diagonalization Lemma: a coded family with uniformly decidable membership that
    contains every recursive relation is impossible — i.e. it is a proper subfamily of REC. -/
theorem coded_family_ssubset_rec {C : Type} [Primcodable C] (k : ℕ) (interp : C → Set (Fin (k + 1) → ℤ))
    (F : Set (Set (Fin (k + 1) → ℤ))) (hF : CodedFamily k interp F) (h : UniformlyDecidable k interp)
    (hsub : F ⊆ RecFragmentZZ (k + 1)) : F ⊂ RecFragmentZZ (k + 1) := by
  rw [Set.ssubset_def]
  refine ⟨hsub, fun hsub' => ?_⟩
  have hmem : effDiagonal k interp ∈ RecFragmentZZ (k + 1) := effDiagonal_computablePred k interp h
  exact effDiagonal_not_mem k interp F hF (hsub' hmem)

/-! ### Instance: SE_2 with the standard quadratic codes -/

/-- Interpretation of a standard quadratic code as a relation on ℤ^{k+1} (parameter arity k+1). -/
def quadraticCodeRel (k : ℕ) (c : QuadraticCode) : Set (Fin (k + 1) → ℤ) :=
  {v | QuadraticCode.solvableZZ (k + 1) c v}

theorem singleEqFragment_two_codedFamily (k : ℕ) :
    CodedFamily k (quadraticCodeRel k) (SingleEqFragmentZZ 2 (k + 1)) := by
  intro A hA
  obtain ⟨r, P, hP, hrep⟩ := hA
  obtain ⟨c, hc⟩ := quadraticCode_surjective (k + 1) r P hP
  refine ⟨c, ?_⟩
  ext v
  simp only [quadraticCodeRel, Set.mem_setOf_eq]
  rw [quadraticCode_solvable_iff, hrep v]
  obtain ⟨hr, hP'⟩ := Sigma.mk.inj_iff.1 hc
  subst hr
  rw [eq_of_heq hP']

theorem quadraticCodeRel_uniformlyDecidable (h : UniformQuadraticSolvabilityOnCodes) (k : ℕ) :
    UniformlyDecidable k (quadraticCodeRel k) := h (k + 1)

/-- Re-derivation of the diagonal theorem through the generic lemma with the STANDARD codes:
    SE_2(k+1) ⊊ REC(k+1) under the code-uniform Grunewald–Segal hypothesis on standard codes. -/
theorem singleQuadratic_strict_recursive_of_codes (h : UniformQuadraticSolvabilityOnCodes) (k : ℕ) :
    SingleEqFragmentZZ 2 (k + 1) ⊂ RecFragmentZZ (k + 1) :=
  coded_family_ssubset_rec k (quadraticCodeRel k) _ (singleEqFragment_two_codedFamily k)
    (quadraticCodeRel_uniformlyDecidable h k)
    (singleEqFragmentZZ_two_subset_recFragmentZZ (uniformCodeGS_implies_perEquationGS h) _)

end DiophCompression

#print axioms DiophCompression.effDiagonal_computablePred
#print axioms DiophCompression.effDiagonal_not_mem
#print axioms DiophCompression.coded_family_ssubset_rec
#print axioms DiophCompression.singleQuadratic_strict_recursive_of_codes
