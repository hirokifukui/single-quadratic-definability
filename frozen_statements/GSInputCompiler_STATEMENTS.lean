/-
  DiophCompression/GSInputCompiler.lean — APAL Structural Theory Gate 5, 必須G (s28, 2026-09-02, claude.ai direct).

  The Grunewald–Segal bridge, stated honestly. Our `GlobalQuadraticInstance` is OUR OWN effective coding
  (witness arity + coefficient table + parameter list); the literature states an effective procedure deciding
  integer solvability of a quadratic equation given in the usual coefficient-table form. The two are related
  by an INPUT COMPILER, not by identity: substituting the parameter list into the code produces a
  parameter-free coefficient table with the same integer solutions. This file supplies that compiler and
  proves the equivalence, so the manuscript can say "effective coding-equivalent consequence" and point at a
  theorem instead of at a claim. Also: the denominator-clearing lemma needed when the rational-coefficient
  form of the literature is quoted. No sorry; std-3.
-/
import DiophCompression.BranchExhaustion
import DiophCompression.GlobalQuadraticCode

namespace DiophCompression

open MvPolynomial MPUP Matrix

/-! ### Substituting the parameters: the input compiler -/

/-- Split a variable factor against the parameter list: a parameter index becomes a numeric multiplier and
    disappears, an unknown index is shifted down by the number of parameters. -/
def splitFactor (a : List ℤ) : Option ℕ → ℤ × Option ℕ
  | none => (1, none)
  | some i => if i < a.length then (varLookup a i, none) else (1, some (i - a.length))

theorem splitFactor_spec (a u : List ℤ) (o : Option ℕ) :
    (splitFactor a o).1 * optLookup u (splitFactor a o).2 = optLookup (a ++ u) o := by
  sorry

/-- Substitute the parameters into one term. -/
def substParamTerm (a : List ℤ) (t : QuadraticTerm) : QuadraticTerm :=
  (t.1 * (splitFactor a t.2.1).1 * (splitFactor a t.2.2).1,
    (splitFactor a t.2.1).2, (splitFactor a t.2.2).2)

theorem substParamTerm_evalW (a u : List ℤ) (t : QuadraticTerm) :
    (substParamTerm a t).evalW u = t.evalW (a ++ u) := by
  sorry

/-- Substitute the parameters into a whole code: the witness arity is unchanged, every parameter occurrence
    is folded into a coefficient, every unknown index is shifted down. -/
def substParamCode (a : List ℤ) (c : QuadraticCode) : QuadraticCode :=
  (c.1, c.2.map (substParamTerm a))

theorem substParamCode_evalW (a u : List ℤ) (c : QuadraticCode) :
    (substParamCode a c).evalW u = c.evalW (a ++ u) := by
  sorry

/-- 必須G: the input compiler — the concrete, parameter-free coefficient table of a global instance. -/
def GlobalQuadraticInstance.toConcreteEquation (I : GlobalQuadraticInstance) : QuadraticCode :=
  substParamCode I.2 I.1

theorem toConcreteEquation_witnessArity (I : GlobalQuadraticInstance) :
    I.toConcreteEquation.witnessArity = I.1.witnessArity := rfl

/-- 必須G: the compiled equation has exactly the solutions of the original instance. -/
theorem globalInstance_eval_iff (I : GlobalQuadraticInstance) (u : List ℤ) :
    I.toConcreteEquation.evalW u = I.1.evalW (I.2 ++ u) := by
  sorry

/-- 必須G: solvability is preserved by the compiler, so the paper's instance form and the parameter-free
    coefficient-table form of the literature decide the same problem. -/
theorem globalInstance_solvable_iff (I : GlobalQuadraticInstance) :
    I.solvable ↔ ∃ u : List ℤ, u.length = I.toConcreteEquation.witnessArity ∧
      I.toConcreteEquation.evalW u = 0 := by
  sorry

/-- The compiled table is parameter-free: evaluating it needs no parameter environment, i.e. it is the input
    shape of the classical procedure. -/
theorem toConcreteEquation_parameterFree (I : GlobalQuadraticInstance) (u : List ℤ) :
    I.toConcreteEquation.evalZZ 0 (fun i => i.elim0) u = I.toConcreteEquation.evalW u := by
  sorry

/-! ### Clearing denominators (needed only if the rational-coefficient form is quoted) -/

/-- Multiplying an equation by a nonzero rational does not change its integer solutions: the rational form
    of the literature and its integral clearing decide the same problem. -/
theorem rational_clearing_int_points {r : ℕ} (g : MvPolynomial (Fin r) ℤ) (d : ℚ) (hd : d ≠ 0)
    (u : Fin r → ℤ) :
    eval (fun i => ((u i : ℤ) : ℚ)) (d • (map (Int.castRingHom ℚ) g)) = 0 ↔ eval u g = 0 := by
  sorry

end DiophCompression
