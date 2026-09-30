/-
  DiophCompression/GSCompilerComputable.lean — APAL Structural Theory Gate 5, 必須G (last item) /
  宿題群7-5 "solver input computability" (s29, 2026-09-02, claude.ai direct).

  The GS input compiler is primitive recursive. `GlobalQuadraticInstance.toConcreteEquation` folds the
  parameter list into the coefficient table; this file proves that the map from an instance to its
  parameter-free table is `Primrec` (hence `Computable`), so the reduction to the classical procedure is
  effective and not merely extensional. The code types are `ℕ × List (ℤ × (Option ℕ × Option ℕ))`, all
  `Primcodable`, and the arithmetic legs are the ℤ-primrec lemmas of `IntPrimrec.lean`.
  No sorry; std-3 expected.
-/
import DiophCompression.GSInputCompiler

namespace DiophCompression

/-- The variable-splitting step is primitive recursive. -/
theorem primrec₂_splitFactor : Primrec₂ splitFactor := by
  have hlen : Primrec fun q : (List ℤ × Option ℕ) × ℕ => q.1.1.length :=
    Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)
  have h : Primrec fun p : List ℤ × Option ℕ =>
      Option.casesOn (motive := fun _ => ℤ × Option ℕ) p.2 ((1 : ℤ), (none : Option ℕ))
        (fun i => if i < p.1.length then (varLookup p.1 i, (none : Option ℕ))
          else ((1 : ℤ), some (i - p.1.length))) := by
    refine Primrec.option_casesOn Primrec.snd (Primrec.const _) ?_
    refine Primrec.ite (PrimrecRel.comp Primrec.nat_lt Primrec.snd hlen) ?_ ?_
    · exact Primrec.pair
        (primrec₂_varLookup.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.const none)
    · exact Primrec.pair (Primrec.const 1)
        (Primrec.option_some.comp (Primrec.nat_sub.comp Primrec.snd hlen))
  refine h.of_eq ?_
  rintro ⟨a, o⟩
  cases o <;> rfl

/-- Substituting the parameters into one term is primitive recursive. -/
theorem primrec₂_substParamTerm : Primrec₂ substParamTerm := by
  have hsf1 : Primrec fun p : List ℤ × QuadraticTerm => splitFactor p.1 p.2.2.1 :=
    primrec₂_splitFactor.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hsf2 : Primrec fun p : List ℤ × QuadraticTerm => splitFactor p.1 p.2.2.2 :=
    primrec₂_splitFactor.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have h : Primrec fun p : List ℤ × QuadraticTerm =>
      ((p.2.1 * (splitFactor p.1 p.2.2.1).1 * (splitFactor p.1 p.2.2.2).1,
        (splitFactor p.1 p.2.2.1).2, (splitFactor p.1 p.2.2.2).2) : QuadraticTerm) :=
    Primrec.pair
      (primrec₂_int_mul.comp
        (primrec₂_int_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp hsf1))
        (Primrec.fst.comp hsf2))
      (Primrec.pair (Primrec.snd.comp hsf1) (Primrec.snd.comp hsf2))
  exact h.of_eq fun p => rfl

/-- Substituting the parameters into a whole code is primitive recursive. -/
theorem primrec₂_substParamCode : Primrec₂ substParamCode := by
  have h : Primrec fun p : List ℤ × QuadraticCode =>
      ((p.2.1, p.2.2.map (substParamTerm p.1)) : QuadraticCode) :=
    Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (primrec₂_substParamTerm.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
  exact h.of_eq fun p => rfl

/-- 必須G / 宿題群7-5: the GS input compiler is primitive recursive — an instance is turned into its
    parameter-free coefficient table by a primitive recursive function of the code. -/
theorem globalGS_input_compiler_computable :
    Primrec GlobalQuadraticInstance.toConcreteEquation :=
  primrec₂_substParamCode.comp Primrec.snd Primrec.fst

/-- The same in the Turing-computability vocabulary. -/
theorem globalGS_input_compiler_comp :
    Computable GlobalQuadraticInstance.toConcreteEquation :=
  globalGS_input_compiler_computable.to_comp

end DiophCompression

#print axioms DiophCompression.primrec₂_splitFactor
#print axioms DiophCompression.primrec₂_substParamTerm
#print axioms DiophCompression.primrec₂_substParamCode
#print axioms DiophCompression.globalGS_input_compiler_computable
#print axioms DiophCompression.globalGS_input_compiler_comp
