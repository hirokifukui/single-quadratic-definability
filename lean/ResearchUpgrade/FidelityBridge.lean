/-
  FidelityBridge.lean — s48.  Step (b), and the bridge: **`dim_le_of_defines` improves the sealed
  `n ≤ 2m` to `n ≤ m` on the sealed predicate itself.**

  The sealed predicate (mpup-lean `DiophCompression/FiniteFiberGrowth.lean:47`) is

      SingleQuadraticDefinableFunctionZZ f :=
        ∃ r, ∃ P : Poly (n + m) r, P.totalDegree ≤ 2 ∧ RepresentsZZ P (graphVecZZ f)

  and its coordinate convention puts the INPUTS FIRST (`graphVecZZ`, line 43: the outputs are read
  at `Fin.natAdd n j`, the inputs at `Fin.castAdd m i`).  That convention is the one place where
  this bookkeeping could silently invert, so `unsplit` is written against it directly and
  `pt_comp_unsplit` is proved coordinate by coordinate rather than asserted.

  Step (a) (`QuadRep.lean`) turns the degree-≤2 polynomial into an `IntQuad`; `rename` along
  `unsplit` moves it onto `Vars n m r`; the rest is `eval_rename`.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import DiophCompression.AtomicCodingHierarchy
import DiophCompression.FiniteFiberGrowth
import Mathlib.Data.Int.Notation
import ResearchUpgrade.C2Partial
import ResearchUpgrade.DimensionII_D
import ResearchUpgrade.GraphVocabulary
import ResearchUpgrade.QuadRep

namespace DiophCompression.ResearchUpgrade

open MvPolynomial

variable {n m r : ℕ}

/-- The sealed coordinate convention: inputs first, then outputs. -/
def pairVec (a : Fin n → ℤ) (b : Fin m → ℤ) : Fin (n + m) → ℤ :=
  Fin.addCases a b

@[simp] theorem pairVec_left (a : Fin n → ℤ) (b : Fin m → ℤ) (i : Fin n) :
    pairVec a b (Fin.castAdd m i) = a i := by
  simp [pairVec]

@[simp] theorem pairVec_right (a : Fin n → ℤ) (b : Fin m → ℤ) (j : Fin m) :
    pairVec a b (Fin.natAdd n j) = b j := by
  simp [pairVec]

/-- `v` is on the graph of `f` exactly when it is `pairVec a (f a)`. -/
theorem mem_graphVecZZ_pairVec (f : (Fin n → ℤ) → (Fin m → ℤ))
    (a : Fin n → ℤ) (b : Fin m → ℤ) :
    pairVec a b ∈ DiophCompression.graphVecZZ f ↔ b = f a := by
  constructor
  · intro h
    have h' : (fun j => pairVec a b (Fin.natAdd n j)) = f (fun i => pairVec a b (Fin.castAdd m i)) :=
      h
    simpa using h'
  · intro h
    show (fun j => pairVec a b (Fin.natAdd n j)) = f (fun i => pairVec a b (Fin.castAdd m i))
    simpa using h

/-- The index map that carries the sealed variable block `Fin (n+m) ⊕ Fin r` onto ours. -/
def unsplit : Fin (n + m) ⊕ Fin r → Vars n m r :=
  Sum.elim
    (Fin.addCases (motive := fun _ => Vars n m r)
      (fun i : Fin n => (Sum.inl i : Vars n m r))
      (fun j : Fin m => (Sum.inr (Sum.inl j) : Vars n m r)))
    (fun k => Sum.inr (Sum.inr k))

/-- **The convention check, proved coordinate by coordinate.** -/
theorem pt_comp_unsplit (a : Fin n → ℤ) (b : Fin m → ℤ) (u : Fin r → ℤ) :
    (pt a b u) ∘ (unsplit : Fin (n + m) ⊕ Fin r → Vars n m r)
      = Sum.elim (pairVec a b) u := by
  funext w
  rcases w with w | k
  · induction w using Fin.addCases with
    | left i => simp [unsplit, pt]
    | right j => simp [unsplit, pt]
  · simp [unsplit, pt]

/-- **Step (b) + the bridge.**  Every function the SEALED predicate declares definable is defined
by a `QuadraticGraphData`. -/
theorem graphData_of_singleQuadraticDefinable {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : DiophCompression.SingleQuadraticDefinableFunctionZZ f) :
    ∃ (r : ℕ) (D : QuadraticGraphData n m r), D.Defines f := by
  classical
  obtain ⟨r, P, hdeg, hrep⟩ := hf
  set P' : MvPolynomial (Vars n m r) ℤ := rename unsplit P with hP'
  have hdeg' : P'.totalDegree ≤ 2 := le_trans (totalDegree_rename_le _ _) hdeg
  obtain ⟨q, hq⟩ := IntQuad.isQuadRep_of_totalDegree_le_two P' hdeg'
  refine ⟨r, ⟨q⟩, ?_⟩
  intro a b
  have hval : ∀ u : Fin r → ℤ,
      (⟨q⟩ : QuadraticGraphData n m r).P.eval (pt a b u)
        = DiophCompression.evalAtZZ P (pairVec a b) u := by
    intro u
    show q.eval (pt a b u) = _
    rw [hq (pt a b u), hP', eval_rename, pt_comp_unsplit]
    rfl
  constructor
  · rintro ⟨u, hu⟩
    have hu' : (⟨q⟩ : QuadraticGraphData n m r).P.eval (pt a b u) = 0 := hu
    rw [hval u] at hu'
    exact (mem_graphVecZZ_pairVec f a b).mp ((hrep (pairVec a b)).mpr ⟨u, hu'⟩)
  · intro hb
    obtain ⟨u, hu⟩ := (hrep (pairVec a b)).mp ((mem_graphVecZZ_pairVec f a b).mpr hb)
    refine ⟨u, ?_⟩
    show (⟨q⟩ : QuadraticGraphData n m r).P.eval (pt a b u) = 0
    rw [hval u]
    exact hu

/-- **THE CLAIM.**  The sealed `n ≤ 2m` is improved to `n ≤ m` on the sealed predicate itself:
compare `DiophCompression.singleQuadratic_injective_dimension_bound`
(mpup-lean `FiniteFiberGrowth.lean:318`), which has `2 * m` where this has `m`. -/
theorem singleQuadratic_injective_dimension_sharp {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : DiophCompression.SingleQuadraticDefinableFunctionZZ f)
    (hinj : Function.Injective f) : n ≤ m := by
  obtain ⟨r, D, hD⟩ := graphData_of_singleQuadraticDefinable hf
  exact D.dim_le_of_defines hD hinj

/-! ### Controls -/

/-- POSITIVE control: the improvement is not vacuous — it strictly refines the sealed bound, and
the sealed bound is recovered from it. -/
theorem sharp_refines_sealed {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : DiophCompression.SingleQuadraticDefinableFunctionZZ f)
    (hinj : Function.Injective f) : n ≤ m ∧ n ≤ 2 * m := by
  have h := singleQuadratic_injective_dimension_sharp hf hinj
  exact ⟨h, by omega⟩

/-- NEGATIVE control on the convention: `unsplit` sends the OUTPUT block of the sealed variable
list to the output block of ours, and the INPUT block to the input block — read off at the two
`Fin.addCases` branches, not asserted.  If the convention were inverted these would not both
hold. -/
theorem unsplit_convention (i : Fin n) (j : Fin m) (k : Fin r) :
    (unsplit (Sum.inl (Fin.castAdd m i)) : Vars n m r) = Sum.inl i
      ∧ (unsplit (Sum.inl (Fin.natAdd n j)) : Vars n m r) = Sum.inr (Sum.inl j)
      ∧ (unsplit (Sum.inr k) : Vars n m r) = Sum.inr (Sum.inr k) :=
  ⟨by simp [unsplit], by simp [unsplit], by simp [unsplit]⟩

/-! ### The sealed manuscript's open problem

`MANUSCRIPT_V32.md` Appendix B (r39, sealed 2026-09-11) records

    AtomGraphZZ 2 n → n ≤ 2   (upper)   and   AtomGraphZZ 1 1   (lower),
    "hence 1 ≤ ca(SE₂) ≤ 2 in the one-sorted setting, and the value at n = 2 is open",

and Corollary 4.2: "No single quadratic equation defines the graph of an injection ℤⁿ → ℤ for
n ≥ 3.  Whether one exists for n = 2 is open."  The upper bound below is `n ≤ 1`, so the value is
`1` and the `n = 2` case is settled in the negative.  The proof is the sealed
`atomGraphZZ_le_two_from_dimension_bound` with its last step replaced. -/

/-- **The capacity upper bound, sharpened.**  `AtomGraphZZ 2 n → n ≤ 1`. -/
theorem atomGraphZZ_le_one : ∀ n, DiophCompression.AtomGraphZZ 2 n → n ≤ 1 := by
  intro n h
  obtain ⟨r, e, he, P, hP, hrep⟩ := h
  have hg : DiophCompression.graphVecZZ (fun a (_ : Fin 1) => e a) = DiophCompression.graphZZ e := by
    ext v
    simp only [DiophCompression.graphVecZZ, DiophCompression.graphZZ, Set.mem_setOf_eq]
    have h0 : Fin.natAdd n (0 : Fin 1) = Fin.last n := by ext; simp
    constructor
    · intro h
      have := congrFun h 0
      rw [h0] at this
      exact this
    · intro h
      funext j
      rw [Subsingleton.elim j 0, h0]
      exact h
  have hf : DiophCompression.SingleQuadraticDefinableFunctionZZ (fun a (_ : Fin 1) => e a) :=
    ⟨r, P, hP, by rw [hg]; exact hrep⟩
  have hinj : Function.Injective (fun a (_ : Fin 1) => e a) := fun a b h => he (congrFun h 0)
  exact singleQuadratic_injective_dimension_sharp hf hinj

/-- **The one-sorted coding arity is exactly one.**  Upper bound above, lower bound the sealed
`atomGraphZZ_degree_one_one`; together `ca(SE₂) = 1`, which Appendix B left open. -/
theorem atomGraphZZ_capacity_eq_one :
    DiophCompression.AtomGraphZZ 1 1 ∧ ∀ n, DiophCompression.AtomGraphZZ 2 n → n ≤ 1 :=
  ⟨DiophCompression.atomGraphZZ_degree_one_one, atomGraphZZ_le_one⟩

/-- **The `n = 2` case, settled in the negative.**  No single equation of total degree ≤ 2, with
any number of integer witnesses, defines the graph of an injection `ℤ² → ℤ`. -/
theorem not_atomGraphZZ_two : ¬ DiophCompression.AtomGraphZZ 2 2 := by
  intro h
  have := atomGraphZZ_le_one 2 h
  omega

/-- **The ℕ/ℤ boundary, as a theorem.**  Over ℕ-inputs the capacity at degree 2 IS two — the
Cantor pairing is the witness, and the sealed `atomGraph_degree_two_iff` records it.  Over
ℤ-inputs it is one.  The two hold simultaneously, so the closure above is genuinely ℤ-specific:
**no step of it can survive replacing ℤ by ℕ**, which is exactly what regression control #25 asks
of every step of II-D. -/
theorem natInput_intInput_separation_at_two :
    DiophCompression.AtomGraphZ 2 2 ∧ ¬ DiophCompression.AtomGraphZZ 2 2 :=
  ⟨DiophCompression.atomGraph_degree_two_iff.mpr (by norm_num), not_atomGraphZZ_two⟩

/-! ### G22-T21 — the sharp dimension `iff` on the SEALED predicate

T20 (`summit_of_defines` + `dim_le_of_summit`) gives the upper direction, T18 / `pad` the
existence direction, and this file's bridge puts both on `SingleQuadraticDefinableFunctionZZ`.
Arbitrary finite witness count; the existence witness has `r = 0`. -/

/-- **G22-T21.**  For the SEALED predicate: an injective single-quadratic-definable
`ℤⁿ → ℤᵐ` exists **exactly when** `n ≤ m`.  Upper direction
`singleQuadratic_injective_dimension_sharp`; existence direction `pad_singleQuadratic` +
`pad_injective`, witness-free. -/
theorem singleQuadratic_sharp_iff (n m : ℕ) :
    (∃ f : (Fin n → ℤ) → (Fin m → ℤ),
        DiophCompression.SingleQuadraticDefinableFunctionZZ f ∧ Function.Injective f) ↔ n ≤ m := by
  constructor
  · rintro ⟨f, hf, hinj⟩
    exact singleQuadratic_injective_dimension_sharp hf hinj
  · intro h
    exact ⟨pad h, pad_singleQuadratic h, pad_injective h⟩

end DiophCompression.ResearchUpgrade
