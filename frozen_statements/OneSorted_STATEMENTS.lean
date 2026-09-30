/-
  frozen_statements/OneSorted_STATEMENTS.lean — APAL Logic Pivot, Gate 3 (session 20, 2026-08-31, claude.ai direct).
  ONE-SORTED VERSION (desk r19b §3.1, §5.2(b); Dr. Fukui ruling s20 'go'): all variables range over ℤ.
  Theorem E_ℤ: no single integer polynomial equation of total degree ≤ 2, with any number of integer
  existential variables, defines in (ℤ,+,·) the graph of an injection ℤ³ → ℤ. Contrast: a conjunction of
  quadratic equations does (arity 3, explicit system). Proof of E_ℤ: restrict to ℕ³, apply Theorem D to
  H(c,u) and to H(−c,u), box-count. Statements only; sorry bodies; frozen before proof.
-/
import DiophCompression.QuadraticPPSeparation
import DiophCompression.SemanticQuadraticSingular.SingularAssembly

namespace DiophCompression

open MvPolynomial MPUP

/-! ### One-sorted definitions: parameters AND witnesses in ℤ -/

/-- One-sorted evaluation of `P ∈ ℤ[a, y]` at integer parameters `a` and integer witnesses `y`. -/
noncomputable def evalAtZZ {n r : ℕ} (P : Poly n r) (a : Fin n → ℤ) (y : Fin r → ℤ) : ℤ :=
  eval (Sum.elim a y) P

/-- `P` represents `A ⊆ ℤⁿ` in the one-sorted sense. -/
def RepresentsZZ {n r : ℕ} (P : Poly n r) (A : Set (Fin n → ℤ)) : Prop :=
  ∀ a, a ∈ A ↔ ∃ y : Fin r → ℤ, evalAtZZ P a y = 0

/-- The graph of `e : ℤⁿ → ℤ` as a subset of `ℤⁿ⁺¹` (output in the last coordinate). -/
def graphZZ {n : ℕ} (e : (Fin n → ℤ) → ℤ) : Set (Fin (n + 1) → ℤ) :=
  {v | v (Fin.last n) = e (Fin.init v)}

/-- One-sorted atomic fragment on injective graphs: some injection `ℤⁿ → ℤ` has its graph represented by
    one equation of total degree ≤ `d` with some number of integer existential variables. -/
def AtomGraphZZ (d n : ℕ) : Prop :=
  ∃ (r : ℕ) (e : (Fin n → ℤ) → ℤ), Function.Injective e ∧
    ∃ P : Poly (n + 1) r, P.totalDegree ≤ d ∧ RepresentsZZ P (graphZZ e)

/-- A system represents `A ⊆ ℤⁿ` in the one-sorted sense. -/
def SystemRepresentsZZ {n r m : ℕ} (S : PolySystem n r m) (A : Set (Fin n → ℤ)) : Prop :=
  ∀ a, a ∈ A ↔ ∃ y : Fin r → ℤ, ∀ i, evalAtZZ (S i) a y = 0

/-- One-sorted primitive-positive fragment on injective graphs. -/
def PPGraphZZ (d n : ℕ) : Prop :=
  ∃ (r m : ℕ) (e : (Fin n → ℤ) → ℤ), Function.Injective e ∧
    ∃ S : PolySystem (n + 1) r m, (∀ i, (S i).totalDegree ≤ d) ∧ SystemRepresentsZZ S (graphZZ e)

/-! ### Bridge to the ℕ-parameter semantics -/

theorem evalAtZZ_natCast {n r : ℕ} (P : Poly n r) (a : Fin n → ℕ) (y : Fin r → ℤ) :
    evalAtZZ P (fun i => (a i : ℤ)) y = evalAt P a y := by
  sorry

/-! ### Theorem E_ℤ (one-sorted) -/

theorem atomGraphZZ_degree_two_le_two : ∀ n, AtomGraphZZ 2 n → n ≤ 2 := by
  sorry

theorem one_sorted_quadratic_no_injective_ternary_graph :
    ∀ (r : ℕ) (P : Poly 4 r), P.totalDegree ≤ 2 →
      ∀ e : (Fin 3 → ℤ) → ℤ, Function.Injective e → ¬ RepresentsZZ P (graphZZ e) := by
  sorry

theorem atomGraphZZ_degree_one_one : AtomGraphZZ 1 1 := by
  sorry

/-! ### The one-sorted contrast at degree two -/

/-- `f(x) = 2x` for `x ≥ 0`, `−2x − 1` for `x < 0`: a bijection `ℤ → ℕ`. -/
def zToNat (x : ℤ) : ℤ := if 0 ≤ x then 2 * x else -2 * x - 1

theorem zToNat_injective : Function.Injective zToNat := by
  sorry

theorem zToNat_nonneg (x : ℤ) : 0 ≤ zToNat x := by
  sorry

/-- The injection `ℤ³ → ℤ`: `π(π(f a₀, f a₁), f a₂)` with `π` the doubled Cantor pairing on ℕ. -/
noncomputable def ternaryPairZZ (a : Fin 3 → ℤ) : ℤ :=
  ((cantorScaledPair (cantorScaledPair (zToNat (a 0)).toNat (zToNat (a 1)).toNat)
    (zToNat (a 2)).toNat : ℕ) : ℤ)

theorem ternaryPairZZ_injective : Function.Injective ternaryPairZZ := by
  sorry

/-- Theorem B_ℤ at arity 3: an injective `ℤ³ → ℤ` graph is defined by a conjunction of quadratic
    equations in (ℤ,+,·). -/
theorem ppGraphZZ_degree_two_three : PPGraphZZ 2 3 := by
  sorry

end DiophCompression
