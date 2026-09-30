/-
  DiophCompression/Definitions.lean — r04 Task 5 skeleton (session 4, 2026-08-26, claude.ai direct).
  Degree–Witness–Arity spectra: achievability predicates only (no sup, no ∞), GPT r03 §3 / Task 5.
  The frozen MPUP files are imported, never modified. Parameters are ℕ (Spec.lean line 7);
  the ℕ/ℤ split refers to the unknowns only.
-/
import MPUP.Spec

namespace DiophCompression

open MvPolynomial MPUP

/-- Specialize the parameter variables (`inl`) of `P` at `a : Fin n → ℕ`, leaving the `σ`-variables. -/
noncomputable def specialize {n : ℕ} {σ : Type} (P : MvPolynomial (Fin n ⊕ σ) ℤ) (a : Fin n → ℕ) :
    MvPolynomial σ ℤ :=
  aeval (Sum.elim (fun i => C ((a i : ℕ) : ℤ)) X) P

/-- Syntactic specialization capacity (GPT r03 §3.1): `n` parameters can be injectively encoded
    as polynomials in `q` variables of total degree ≤ `d`. -/
def SpecializationAchievable (n q d : ℕ) : Prop :=
  ∃ P : MvPolynomial (Fin n ⊕ Fin q) ℤ, P.totalDegree ≤ d ∧ Function.Injective (specialize P)

/-- Semantic graph capacity, ℕ-unknowns (GPT r03 §3.2): the `n`-th instance of `TupleCoderN r d`. -/
def GraphAchievableN (n r d : ℕ) : Prop :=
  ∃ e : (Fin n → ℕ) → ℕ, Function.Injective e ∧ WithinN r d (graph e)

/-- Semantic graph capacity, ℤ-unknowns. -/
def GraphAchievableZ (n r d : ℕ) : Prop :=
  ∃ e : (Fin n → ℕ) → ℕ, Function.Injective e ∧ WithinZ r d (graph e)

/-- Universality capacity, ℕ-unknowns (GPT r03 §3.3): every Diophantine `A ⊆ ℕ^n` within `(r, d)`. -/
def UniversalAchievableN (n r d : ℕ) : Prop :=
  ∀ A : Set (Fin n → ℕ), DiophN A → WithinN r d A

/-- Universality capacity, ℤ-unknowns (hypothesis Diophantine over ℕ, as in Spec/AFP). -/
def UniversalAchievableZ (n r d : ℕ) : Prop :=
  ∀ A : Set (Fin n → ℕ), DiophN A → WithinZ r d A

/-! ## Bridges to the frozen Spec (definitional). -/

theorem tupleCoderN_iff (r d : ℕ) : TupleCoderN r d ↔ ∀ n, GraphAchievableN n r d := Iff.rfl
theorem tupleCoderZ_iff (r d : ℕ) : TupleCoderZ r d ↔ ∀ n, GraphAchievableZ n r d := Iff.rfl
theorem multiUniversalN_iff (ν δ : ℕ → ℕ) :
    MultiUniversalN ν δ ↔ ∀ n, UniversalAchievableN n (ν n) (δ n) := Iff.rfl
theorem multiUniversalZ_iff (ν δ : ℕ → ℕ) :
    MultiUniversalZ ν δ ↔ ∀ n, UniversalAchievableZ n (ν n) (δ n) := Iff.rfl

/-! ## Monotonicity in the resources (more witnesses / higher degree never hurts). -/

theorem withinN_mono {n : ℕ} {r r' d d' : ℕ} (hr : r ≤ r') (hd : d ≤ d') {A : Set (Fin n → ℕ)}
    (h : WithinN r d A) : WithinN r' d' A := by
  obtain ⟨s, hs, P, hP, hrep⟩ := h
  exact ⟨s, le_trans hs hr, P, le_trans hP hd, hrep⟩

theorem withinZ_mono {n : ℕ} {r r' d d' : ℕ} (hr : r ≤ r') (hd : d ≤ d') {A : Set (Fin n → ℕ)}
    (h : WithinZ r d A) : WithinZ r' d' A := by
  obtain ⟨s, hs, P, hP, hrep⟩ := h
  exact ⟨s, le_trans hs hr, P, le_trans hP hd, hrep⟩

theorem graphAchievableN_mono {n r r' d d' : ℕ} (hr : r ≤ r') (hd : d ≤ d')
    (h : GraphAchievableN n r d) : GraphAchievableN n r' d' := by
  obtain ⟨e, he, hw⟩ := h; exact ⟨e, he, withinN_mono hr hd hw⟩

theorem graphAchievableZ_mono {n r r' d d' : ℕ} (hr : r ≤ r') (hd : d ≤ d')
    (h : GraphAchievableZ n r d) : GraphAchievableZ n r' d' := by
  obtain ⟨e, he, hw⟩ := h; exact ⟨e, he, withinZ_mono hr hd hw⟩

theorem universalAchievableN_mono {n r r' d d' : ℕ} (hr : r ≤ r') (hd : d ≤ d')
    (h : UniversalAchievableN n r d) : UniversalAchievableN n r' d' :=
  fun A hA => withinN_mono hr hd (h A hA)

theorem universalAchievableZ_mono {n r r' d d' : ℕ} (hr : r ≤ r') (hd : d ≤ d')
    (h : UniversalAchievableZ n r d) : UniversalAchievableZ n r' d' :=
  fun A hA => withinZ_mono hr hd (h A hA)

/-! NOTE (GPT r03 Task 5 prohibition, verified false here): a polynomial representing `A` with
    ℕ-unknowns need not represent `A` with ℤ-unknowns (integer solutions may fall outside `A`).
    `GraphAchievableN → GraphAchievableZ` therefore requires a change of polynomial
    (four-squares substitution) and costs witnesses and degree; it is NOT stated here. -/

end DiophCompression

#print axioms DiophCompression.tupleCoderN_iff
#print axioms DiophCompression.universalAchievableN_mono
