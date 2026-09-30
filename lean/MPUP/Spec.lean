/-
  mpup/spec/mpup.lean — FROZEN 2026-08-26 (statement freeze ruled by Dr. Fukui). Any change = new freeze + new md5.
  Canon: spec/definitions.md (Bayer–David–Hassler–Matiyasevich–Schleicher, arXiv 2506.20909v2,
  Def 0.1, Def 0.2, §6.2 open problem; AFP Diophantine_Universal_Pairs, Universal_Pairs.thy).

  Conventions (mirror the AFP): coefficients in ℤ; parameters are naturals; unknowns are in ℕ or ℤ
  (both variants defined, cf. definitions.md F2); "degree" = MvPolynomial.totalDegree;
  "at most ν unknowns" = ∃ r ≤ ν (AFP: max_vars P ≤ ν).
  Variables are indexed by `Fin n ⊕ Fin r`: `inl` = parameter, `inr` = unknown.
  No axioms. No sorry. Open statements are `def`s of propositions, never `axiom`s.
-/
import Mathlib

namespace MPUP

/-- Integer polynomial in `n` parameters and `r` unknowns. -/
abbrev Poly (n r : ℕ) := MvPolynomial (Fin n ⊕ Fin r) ℤ

/-- Evaluate `P` at parameters `a : Fin n → ℕ` and integer unknowns `y : Fin r → ℤ`. -/
noncomputable def evalAt {n r : ℕ} (P : Poly n r) (a : Fin n → ℕ) (y : Fin r → ℤ) : ℤ :=
  MvPolynomial.eval (Sum.elim (fun i => (a i : ℤ)) y) P

/-- `P` represents `A ⊆ ℕ^n` with unknowns ranging over ℤ (Def 0.1, "over Z", n parameters). -/
def RepresentsZ {n r : ℕ} (P : Poly n r) (A : Set (Fin n → ℕ)) : Prop :=
  ∀ a, a ∈ A ↔ ∃ y : Fin r → ℤ, evalAt P a y = 0

/-- `P` represents `A ⊆ ℕ^n` with unknowns ranging over ℕ (Def 0.1, "over N", n parameters). -/
def RepresentsN {n r : ℕ} (P : Poly n r) (A : Set (Fin n → ℕ)) : Prop :=
  ∀ a, a ∈ A ↔ ∃ y : Fin r → ℕ, evalAt P a (fun i => (y i : ℤ)) = 0

/-- Diophantine over ℕ (Def 0.1): some number of ℕ-unknowns and some integer polynomial. -/
def DiophN {n : ℕ} (A : Set (Fin n → ℕ)) : Prop :=
  ∃ r : ℕ, ∃ P : Poly n r, RepresentsN P A

/-- Diophantine over ℤ (Def 0.1): some number of ℤ-unknowns and some integer polynomial. -/
def DiophZ {n : ℕ} (A : Set (Fin n → ℕ)) : Prop :=
  ∃ r : ℕ, ∃ P : Poly n r, RepresentsZ P A

/-- `A ⊆ ℕ^n` is represented within complexity `(ν, δ)` with ℕ-unknowns:
    at most `ν` unknowns and total degree at most `δ`. -/
def WithinN {n : ℕ} (ν δ : ℕ) (A : Set (Fin n → ℕ)) : Prop :=
  ∃ r ≤ ν, ∃ P : Poly n r, P.totalDegree ≤ δ ∧ RepresentsN P A

/-- Same with ℤ-unknowns. -/
def WithinZ {n : ℕ} (ν δ : ℕ) (A : Set (Fin n → ℕ)) : Prop :=
  ∃ r ≤ ν, ∃ P : Poly n r, P.totalDegree ≤ δ ∧ RepresentsZ P A

/-! ## Single-parameter universal pairs (Def 0.2; AFP `universal_pair_N` / `universal_pair_Z`).
    Hypothesis is Diophantine over ℕ in both variants, as in the AFP. -/

def UniversalPairN (ν δ : ℕ) : Prop :=
  ∀ A : Set (Fin 1 → ℕ), DiophN A → WithinN ν δ A

def UniversalPairZ (ν δ : ℕ) : Prop :=
  ∀ A : Set (Fin 1 → ℕ), DiophN A → WithinZ ν δ A

/-! ## Multi-parameter universal pairs (§6.2, verbatim in definitions.md (d)).
    `ν δ : ℕ → ℕ` are maps of the number of parameters `n`. -/

def MultiUniversalN (ν δ : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, ∀ A : Set (Fin n → ℕ), DiophN A → WithinN (ν n) (δ n) A

def MultiUniversalZ (ν δ : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, ∀ A : Set (Fin n → ℕ), DiophN A → WithinZ (ν n) (δ n) A

/-- THE OPEN PROBLEM (§6.2): constants `ν δ` independent of `n`, ℕ-unknowns. Stated, not proved. -/
def MPUP_N : Prop := ∃ ν δ : ℕ, MultiUniversalN (fun _ => ν) (fun _ => δ)

/-- THE OPEN PROBLEM (§6.2): constants `ν δ` independent of `n`, ℤ-unknowns. Stated, not proved. -/
def MPUP_Z : Prop := ∃ ν δ : ℕ, MultiUniversalZ (fun _ => ν) (fun _ => δ)

/-! ## Diophantine tuple coder (GPT proposal 2026-08-26 §1; status [H]).
    A polynomial in `n + 1` parameters `(a₁..aₙ, c)` and `r` unknowns that represents the graph
    of an injective `e : ℕ^n → ℕ`. GPT's three conditions (totality, functionality in `c`,
    injectivity in `a`) are packaged as "represents the graph of an injective total function". -/

/-- Graph of `e : (Fin n → ℕ) → ℕ` as a subset of `ℕ^(n+1)`; the last coordinate is the code. -/
def graph {n : ℕ} (e : (Fin n → ℕ) → ℕ) : Set (Fin (n + 1) → ℕ) :=
  {v | v (Fin.last n) = e (Fin.init v)}

/-- Bounded-complexity tuple coder with ℕ-unknowns: fixed `(r, d)` and, for every `n`,
    an injective `e` whose graph is represented within `(r, d)`. -/
def TupleCoderN (r d : ℕ) : Prop :=
  ∀ n : ℕ, ∃ e : (Fin n → ℕ) → ℕ, Function.Injective e ∧ WithinN r d (graph e)

def TupleCoderZ (r d : ℕ) : Prop :=
  ∀ n : ℕ, ∃ e : (Fin n → ℕ) → ℕ, Function.Injective e ∧ WithinZ r d (graph e)

/-! ## GPT's proof architecture, as statements to be audited (Task 1). NOT theorems yet.
    Direction (⇐) consumes a single-parameter universal pair, which for explicit constants is
    Jones-conditional in the AFP (definitions.md F1) — hence it appears as a hypothesis. -/

def Arch_coder_to_MPUP_N : Prop :=
  (∃ ν δ, UniversalPairN ν δ) → (∃ r d, TupleCoderN r d) → MPUP_N

def Arch_MPUP_to_coder_N : Prop :=
  MPUP_N → ∃ r d, TupleCoderN r d

end MPUP

#print axioms MPUP.MPUP_N
#print axioms MPUP.MPUP_Z
#print axioms MPUP.TupleCoderN
#print axioms MPUP.Arch_coder_to_MPUP_N
#print axioms MPUP.Arch_MPUP_to_coder_N
