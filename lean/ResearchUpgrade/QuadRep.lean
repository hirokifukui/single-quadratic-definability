/-
  QuadRep.lean — s48.  Step (a) of the statement-fidelity bridge: **a degree-≤2 integer
  polynomial IS an `IntQuad`.**

  This is what stands between `dim_le_of_defines` and the sealed predicate
  `SingleQuadraticDefinableFunctionZZ` (mpup-lean `FiniteFiberGrowth.lean:47`), and hence between
  the theorem and the sentence "we improved n ≤ 2m to n ≤ m".

  The only genuinely new content is the classification of the exponent vectors: a `Finsupp` of
  total degree ≤ 2 is `0`, `single i 1`, `single i 2`, or `single i 1 + single j 1` with `i ≠ j`.
  Everything else is closure bookkeeping — `IntQuad` is closed under `+`, `eval` is additive, and
  each of the four monomial shapes is an explicit `IntQuad`.

  Claim tags: all [P] (std-3).  Baseline read-only.
-/
import Mathlib
import ResearchUpgrade.GraphVocabulary

namespace DiophCompression.ResearchUpgrade

open Matrix MvPolynomial

namespace IntQuad

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### `IntQuad` is an additive monoid and `eval` is additive -/

instance : Zero (IntQuad ι) := ⟨⟨0, 0, 0⟩⟩
instance : Add (IntQuad ι) := ⟨fun a b => ⟨a.c + b.c, a.l + b.l, a.Q + b.Q⟩⟩

@[simp] theorem eval_zero (x : ι → ℤ) : (0 : IntQuad ι).eval x = 0 := by
  simp [IntQuad.eval, show (0 : IntQuad ι).c = 0 from rfl, show (0 : IntQuad ι).l = 0 from rfl,
    show (0 : IntQuad ι).Q = 0 from rfl]

theorem eval_add (a b : IntQuad ι) (x : ι → ℤ) :
    (a + b).eval x = a.eval x + b.eval x := by
  show (a.c + b.c) + (a.l + b.l) ⬝ᵥ x + x ⬝ᵥ ((a.Q + b.Q) *ᵥ x)
      = (a.c + a.l ⬝ᵥ x + x ⬝ᵥ (a.Q *ᵥ x)) + (b.c + b.l ⬝ᵥ x + x ⬝ᵥ (b.Q *ᵥ x))
  rw [add_dotProduct, Matrix.add_mulVec, dotProduct_add]
  ring

/-! ### The predicate, and its closure properties -/

/-- `P` is represented by an `IntQuad` on every integer point. -/
def IsQuadRep (P : MvPolynomial ι ℤ) : Prop :=
  ∃ q : IntQuad ι, ∀ x : ι → ℤ, q.eval x = MvPolynomial.eval x P

theorem isQuadRep_zero : IsQuadRep (0 : MvPolynomial ι ℤ) :=
  ⟨0, fun x => by simp⟩

theorem IsQuadRep.add {P R : MvPolynomial ι ℤ} (hP : IsQuadRep P) (hR : IsQuadRep R) :
    IsQuadRep (P + R) := by
  obtain ⟨q, hq⟩ := hP
  obtain ⟨s, hs⟩ := hR
  exact ⟨q + s, fun x => by rw [eval_add, hq, hs, map_add]⟩

/-! ### The four monomial shapes -/

theorem isQuadRep_const (c : ℤ) : IsQuadRep (MvPolynomial.monomial (0 : ι →₀ ℕ) c) := by
  refine ⟨⟨c, 0, 0⟩, fun x => ?_⟩
  simp [IntQuad.eval]

theorem isQuadRep_lin (i : ι) (c : ℤ) :
    IsQuadRep (MvPolynomial.monomial (Finsupp.single i 1) c) := by
  refine ⟨⟨0, fun k => if k = i then c else 0, 0⟩, fun x => ?_⟩
  have hl : (fun k => if k = i then c else 0) ⬝ᵥ x = c * x i := by
    rw [dotProduct, Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  simp only [IntQuad.eval, hl]
  rw [MvPolynomial.eval_monomial]
  simp [Finsupp.prod_single_index]

theorem isQuadRep_sq (i : ι) (c : ℤ) :
    IsQuadRep (MvPolynomial.monomial (Finsupp.single i 2) c) := by
  refine ⟨⟨0, 0, fun k k' => if k = i ∧ k' = i then c else 0⟩, fun x => ?_⟩
  have hq : x ⬝ᵥ ((fun k k' => if k = i ∧ k' = i then c else 0) *ᵥ x) = c * (x i * x i) := by
    rw [dotProduct, Finset.sum_eq_single i]
    · rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
      · simp; ring
      · intro b _ hb; simp [hb]
      · intro hcon; exact absurd (Finset.mem_univ i) hcon
    · intro b _ hb
      rw [Matrix.mulVec, dotProduct]
      simp [hb]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  have hz : (0 : ι → ℤ) ⬝ᵥ x = 0 := by simp
  simp only [IntQuad.eval, hq, hz]
  rw [MvPolynomial.eval_monomial, Finsupp.prod_single_index (by simp)]
  ring

theorem isQuadRep_cross (i j : ι) (hij : i ≠ j) (c : ℤ) :
    IsQuadRep (MvPolynomial.monomial (Finsupp.single i 1 + Finsupp.single j 1) c) := by
  refine ⟨⟨0, 0, fun k k' => if k = i ∧ k' = j then c else 0⟩, fun x => ?_⟩
  have hq : x ⬝ᵥ ((fun k k' => if k = i ∧ k' = j then c else 0) *ᵥ x) = c * (x i * x j) := by
    rw [dotProduct, Finset.sum_eq_single i]
    · rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
      · simp; ring
      · intro b _ hb; simp [hb]
      · intro hcon; exact absurd (Finset.mem_univ j) hcon
    · intro b _ hb
      rw [Matrix.mulVec, dotProduct]
      simp [hb]
    · intro hcon; exact absurd (Finset.mem_univ i) hcon
  have hz : (0 : ι → ℤ) ⬝ᵥ x = 0 := by simp
  have hd : Disjoint (Finsupp.single i (1 : ℕ)).support (Finsupp.single j (1 : ℕ)).support := by
    simp [hij]
  have hprod : (Finsupp.single i 1 + Finsupp.single j 1).prod (fun k e => x k ^ e)
      = x i * x j := by
    rw [Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_single_index (by simp),
      Finsupp.prod_single_index (by simp)]
    ring
  simp only [IntQuad.eval, hq, hz]
  rw [MvPolynomial.eval_monomial, hprod]
  ring

/-! ### The classification of exponent vectors of total degree ≤ 2 -/

theorem finsupp_deg_le_two (β : ι →₀ ℕ) (h : (β.sum fun _ e => e) ≤ 2) :
    β = 0 ∨ (∃ i, β = Finsupp.single i 1) ∨ (∃ i, β = Finsupp.single i 2)
      ∨ ∃ i j, i ≠ j ∧ β = Finsupp.single i 1 + Finsupp.single j 1 := by
  classical
  have hsum : ∑ i ∈ β.support, β i ≤ 2 := h
  have hcard : β.support.card ≤ 2 := by
    have h1 : β.support.card = ∑ _i ∈ β.support, 1 := by simp
    have h2 : ∑ _i ∈ β.support, 1 ≤ ∑ i ∈ β.support, β i :=
      Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    omega
  interval_cases hc : β.support.card
  · left
    exact Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp hc)
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    have hne : β i ≠ 0 := Finsupp.mem_support_iff.mp (by rw [hi]; exact Finset.mem_singleton_self i)
    have hbe : β = Finsupp.single i (β i) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · have hks : k ∉ β.support := by rw [hi]; simpa using hk
        have hk0 : β k = 0 := by
          by_contra hc0
          exact hks (Finsupp.mem_support_iff.mpr hc0)
        simp [hk0, Finsupp.single_apply, hk]
    have hle : β i ≤ 2 := by
      have hsi : ∑ k ∈ β.support, β k = β i := by rw [hi]; simp
      omega
    rcases (by omega : β i = 1 ∨ β i = 2) with hv | hv
    · exact Or.inr (Or.inl ⟨i, by rw [hbe, hv]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, by rw [hbe, hv]⟩))
  · obtain ⟨i, j, hij, hsupp⟩ := Finset.card_eq_two.mp hc
    have hbi : β i ≠ 0 :=
      Finsupp.mem_support_iff.mp (by rw [hsupp]; simp)
    have hbj : β j ≠ 0 :=
      Finsupp.mem_support_iff.mp (by rw [hsupp]; simp)
    have hs2 : β i + β j = ∑ k ∈ β.support, β k := by
      rw [hsupp, Finset.sum_pair hij]
    have hbi1 : β i = 1 := by omega
    have hbj1 : β j = 1 := by omega
    refine Or.inr (Or.inr (Or.inr ⟨i, j, hij, ?_⟩))
    ext k
    by_cases hki : k = i
    · subst hki
      simp [Finsupp.single_apply, hij, hbi1, Ne.symm hij]
    by_cases hkj : k = j
    · subst hkj
      simp [Finsupp.single_apply, hij, hbj1, Ne.symm hij]
    have hks : k ∉ β.support := by rw [hsupp]; simp [hki, hkj]
    have hk0 : β k = 0 := by
      by_contra hc0
      exact hks (Finsupp.mem_support_iff.mpr hc0)
    simp [hk0, Finsupp.single_apply, hki, hkj]

/-! ### Step (a) of the fidelity bridge -/

/-- **Every integer polynomial of total degree ≤ 2 is an `IntQuad`.**  This is what lets the
sealed predicate `SingleQuadraticDefinableFunctionZZ` be turned into a `QuadraticGraphData`. -/
theorem isQuadRep_of_totalDegree_le_two (P : MvPolynomial ι ℤ) (hP : P.totalDegree ≤ 2) :
    IsQuadRep P := by
  classical
  have hsum : IsQuadRep (∑ β ∈ P.support, MvPolynomial.monomial β (MvPolynomial.coeff β P)) := by
    refine Finset.sum_induction _ IsQuadRep (fun _ _ => IsQuadRep.add) isQuadRep_zero ?_
    intro β hβ
    have hdeg : (β.sum fun _ e => e) ≤ 2 :=
      le_trans (MvPolynomial.le_totalDegree hβ) hP
    rcases finsupp_deg_le_two β hdeg with h0 | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, j, hij, hi⟩
    · rw [h0]; exact isQuadRep_const _
    · rw [hi]; exact isQuadRep_lin i _
    · rw [hi]; exact isQuadRep_sq i _
    · rw [hi]; exact isQuadRep_cross i j hij _
  rwa [← MvPolynomial.as_sum] at hsum

/-! ### Controls -/

/-- POSITIVE control: the representation is not vacuous — it round-trips on a genuine degree-2
polynomial, and the value agreed on is the polynomial's own evaluation. -/
theorem isQuadRep_apply {P : MvPolynomial ι ℤ} (hP : P.totalDegree ≤ 2) (x : ι → ℤ) :
    ∃ q : IntQuad ι, q.eval x = MvPolynomial.eval x P := by
  obtain ⟨q, hq⟩ := isQuadRep_of_totalDegree_le_two P hP
  exact ⟨q, hq x⟩

/-- NEGATIVE control: the degree bound is load-bearing.  `x₀³` is NOT an `IntQuad`: an `IntQuad`
in one variable is `c + l·t + Q·t²`, and the three values at `t = 0, 1, −1` already pin
`c, l, Q`, after which `t = 2` disagrees with `8`.  So `IsQuadRep` is a genuine restriction and
not something every polynomial satisfies. -/
theorem not_isQuadRep_cube :
    ¬ IsQuadRep (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 3) (1 : ℤ)) := by
  classical
  rintro ⟨q, hq⟩
  have e : ∀ t : ℤ, q.eval (fun _ => t) = t ^ 3 := by
    intro t
    rw [hq (fun _ => t), MvPolynomial.eval_monomial, Finsupp.prod_single_index (by simp)]
    ring
  have hval : ∀ t : ℤ, q.eval (fun _ => t) = q.c + q.l default * t + q.Q default default * (t * t) := by
    intro t
    simp only [IntQuad.eval, dotProduct, Matrix.mulVec, Finset.univ_unique,
      Finset.sum_singleton]
    ring
  have h0 := (hval 0).symm.trans (e 0)
  have h1 := (hval 1).symm.trans (e 1)
  have h2 := (hval (-1)).symm.trans (e (-1))
  have h3 := (hval 2).symm.trans (e 2)
  norm_num at h0 h1 h2 h3
  linarith

end IntQuad

end DiophCompression.ResearchUpgrade
