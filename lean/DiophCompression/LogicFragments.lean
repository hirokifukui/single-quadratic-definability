/-
  DiophCompression/LogicFragments.lean — APAL Logic Pivot, Gate 1 (session 19, 2026-08-30, claude.ai direct).
  Standard formula fragments over the frozen Spec (MPUP/Spec.lean): parameters in ℕ, witnesses in ℤ,
  coefficients in ℤ, degree = totalDegree. Nothing here changes the Spec; every definition is a
  wrapper or a finite-system generalisation of `RepresentsZ` / `WithinZ`.

  Atom_d  : relations definable by ONE equation of total degree ≤ d with finitely many ℤ-witnesses
            (= `WithinZ r d` for some r).
  PP_d    : relations definable by a finite CONJUNCTION of equations, each of total degree ≤ d,
            with finitely many ℤ-witnesses (primitive-positive fragment; PPQuad = PP_2).
  The output variable c is a parameter (inl last), never a witness (GPT r18 §12 forbidden item 3).
-/
import DiophCompression.Definitions

namespace DiophCompression

open MvPolynomial MPUP

/-! ### Single-equation fragment Atom_d on injective graphs -/

/-- `Atom_d` at arity `n`: some injection `ℕ^n → ℕ` has its graph defined by a single integer
    equation of total degree ≤ `d`, with some finite number of ℤ-witnesses. -/
def AtomGraphZ (d n : ℕ) : Prop := ∃ r, GraphAchievableZ n r d

/-- The set of arities coded by `Atom_d`. -/
def AtomicCodingSpectrumZ (d : ℕ) : Set ℕ := {n | AtomGraphZ d n}

/-! ### Finite systems and the primitive-positive fragment -/

/-- A system of `m` integer polynomials in `n` parameters and `r` unknowns. -/
abbrev PolySystem (n r m : ℕ) := Fin m → Poly n r

/-- The system `S` represents `A ⊆ ℕ^n` with ℤ-unknowns: `a ∈ A` iff some `y ∈ ℤ^r` makes every
    equation vanish. The empty system (`m = 0`) represents `Set.univ`. -/
def SystemRepresentsZ {n r m : ℕ} (S : PolySystem n r m) (A : Set (Fin n → ℕ)) : Prop :=
  ∀ a, a ∈ A ↔ ∃ y : Fin r → ℤ, ∀ i, evalAt (S i) a y = 0

/-- `S` is a quadratic system representing `A`: every equation has total degree ≤ 2. -/
def QuadraticSystemRepresentsZ {n r m : ℕ} (S : PolySystem n r m) (A : Set (Fin n → ℕ)) : Prop :=
  (∀ i, (S i).totalDegree ≤ 2) ∧ SystemRepresentsZ S A

/-- `A` lies in the primitive-positive fragment of degree ≤ `d`: some finite system of equations,
    each of total degree ≤ `d`, with some finite number of ℤ-witnesses, represents `A`. -/
def WithinPPZ {n : ℕ} (d : ℕ) (A : Set (Fin n → ℕ)) : Prop :=
  ∃ r m, ∃ S : PolySystem n r m, (∀ i, (S i).totalDegree ≤ d) ∧ SystemRepresentsZ S A

/-- `PP_d` at arity `n`: some injection `ℕ^n → ℕ` has its graph in the degree-`d` primitive-positive
    fragment. -/
def PPGraphZ (d n : ℕ) : Prop :=
  ∃ e : (Fin n → ℕ) → ℕ, Function.Injective e ∧ WithinPPZ d (graph e)

/-- `PPQuad` at arity `n` (the fragment of the r18 review, §3.2). -/
def PPQuadraticGraphZ (n : ℕ) : Prop := PPGraphZ 2 n

/-! ### Characterization theorems (definitional; the reader's audit surface) -/

theorem atomGraphZ_iff (d n : ℕ) : AtomGraphZ d n ↔ ∃ r, GraphAchievableZ n r d := Iff.rfl

theorem atomGraphZ_unfold (d n : ℕ) :
    AtomGraphZ d n ↔ ∃ r, ∃ e : (Fin n → ℕ) → ℕ, Function.Injective e ∧
      ∃ r' ≤ r, ∃ P : Poly (n + 1) r', P.totalDegree ≤ d ∧
        ∀ v, v ∈ graph e ↔ ∃ y : Fin r' → ℤ, evalAt P v y = 0 := Iff.rfl

theorem mem_atomicCodingSpectrumZ (d n : ℕ) : n ∈ AtomicCodingSpectrumZ d ↔ AtomGraphZ d n := Iff.rfl

theorem systemRepresentsZ_iff {n r m : ℕ} (S : PolySystem n r m) (A : Set (Fin n → ℕ)) :
    SystemRepresentsZ S A ↔ ∀ a, a ∈ A ↔ ∃ y : Fin r → ℤ, ∀ i, evalAt (S i) a y = 0 := Iff.rfl

theorem quadraticSystemRepresentsZ_iff {n r m : ℕ} (S : PolySystem n r m) (A : Set (Fin n → ℕ)) :
    QuadraticSystemRepresentsZ S A ↔ (∀ i, (S i).totalDegree ≤ 2) ∧ SystemRepresentsZ S A := Iff.rfl

theorem withinPPZ_iff {n : ℕ} (d : ℕ) (A : Set (Fin n → ℕ)) :
    WithinPPZ d A ↔ ∃ r m, ∃ S : PolySystem n r m,
      (∀ i, (S i).totalDegree ≤ d) ∧ SystemRepresentsZ S A := Iff.rfl

theorem ppGraphZ_iff (d n : ℕ) :
    PPGraphZ d n ↔ ∃ e : (Fin n → ℕ) → ℕ, Function.Injective e ∧ WithinPPZ d (graph e) := Iff.rfl

theorem ppQuadraticGraphZ_iff (n : ℕ) : PPQuadraticGraphZ n ↔ PPGraphZ 2 n := Iff.rfl

/-- A single equation is a one-element system: `Atom_d ⊆ PP_d` on every relation. -/
theorem withinPPZ_of_withinZ {n : ℕ} {r d : ℕ} {A : Set (Fin n → ℕ)} (h : WithinZ r d A) :
    WithinPPZ d A := by
  obtain ⟨r', _, P, hP, hrep⟩ := h
  refine ⟨r', 1, fun _ => P, fun _ => hP, fun a => ?_⟩
  rw [hrep a]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, fun _ => hy⟩
  · rintro ⟨y, hy⟩; exact ⟨y, hy 0⟩

/-- The empty system represents everything (audit item: empty conjunction). -/
theorem systemRepresentsZ_empty (n r : ℕ) :
    SystemRepresentsZ (fun _ : Fin 0 => (0 : Poly n r)) Set.univ := by
  intro a
  simp only [Set.mem_univ, true_iff]
  exact ⟨fun _ => 0, fun i => i.elim0⟩

end DiophCompression

#print axioms DiophCompression.withinPPZ_of_withinZ
#print axioms DiophCompression.systemRepresentsZ_empty
