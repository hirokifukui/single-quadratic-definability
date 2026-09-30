/-
  B3 (R40-B3) — the rank-one quotient, as far as it actually closes.

  Hypotheses: the radical has codimension one (`hcodim`: every vector is a rational multiple of a
  fixed `w₀` modulo the radical).  That is what "polar rank 1" says, stated without any rank
  machinery so that nothing is imported that could quietly assume finite-dimensionality of the
  wrong space.

  What is PROVED here, unconditionally:
    * `outCoord_w₀_ne_zero`     — with an output present, `π(w₀) ≠ 0`;
    * `m_le_one_of_polarRankOne`— `m ≤ 1`.  `m ≥ 2` is impossible, by an explicit pair of
                                  coordinate indicators, not by a dimension count;
    * `witnessDir_inRadicalQ`   — EVERY vector whose output coordinates all vanish lies in the
                                  radical.  In particular the witness coordinate directions do.
                                  This is the step the reviewer asked for first, and it is proved
                                  in the ORIGINAL coordinates: no quotient coordinate is ever
                                  treated as an integer coordinate.
    * `weakVectorCosetNF_of_polarRankOne_m_zero` — the `m = 0` leaf, trivial and separated.

  What is NOT proved, and is stated as a `def` rather than asserted: the `m = 1` compiler that
  moves the graph to a no-witness scalar graph and applies `nInputNoWitness_full`.  The three
  ingredients it needs are named in `RankOneNoWitnessCompiler`.  Nothing downstream assumes it,
  and the rank-one conclusion is NOT promoted to general rank.

  s51.
-/
import ResearchUpgrade.RadicalBridge
import ResearchUpgrade.Summit
import ResearchUpgrade.AffineNormalForm

namespace DiophCompression.ResearchUpgrade

/-- The output-coordinate indicator of `j`. -/
noncomputable def outIndicator {m r : ℕ} (j : Fin m) : OutWit m r → ℚ :=
  fun k => if k = Sum.inl j then 1 else 0

@[simp] theorem outIndicator_inl {m r : ℕ} (j j' : Fin m) :
    (outIndicator (r := r) j) (Sum.inl j') = if j' = j then 1 else 0 := by
  simp only [outIndicator]
  by_cases h : j' = j
  · subst h; simp
  · simp [h, Sum.inl.injEq]

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-- With at least one output, the fixed direction `w₀` is seen by the output projection.
Otherwise the indicator of an output coordinate would be radical, and radical vectors have zero
output coordinates. -/
theorem outCoord_w₀_ne_zero
    (hm : 0 < m) (hOU : D.OutputUnique) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {a₀ : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hz : D.SolZ a₀ z₀)
    {w₀ : OutWit m r → ℚ}
    (hcodim : ∀ x : OutWit m r → ℚ, ∃ t : ℚ, D.InRadicalQ (x - t • w₀)) :
    ∃ j : Fin m, w₀ (Sum.inl j) ≠ 0 := by
  classical
  by_contra hall
  push_neg at hall
  let j₀ : Fin m := ⟨0, hm⟩
  obtain ⟨t, ht⟩ := hcodim (outIndicator j₀)
  have h0 := D.outCoordQ_radicalQ_eq_zero hm hOU hz hQ ht j₀
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, outIndicator_inl,
    hall j₀, mul_zero, sub_zero] at h0
  exact one_ne_zero h0

/-- **B3, first half.**  Rank one forces at most one output.  `m ≥ 2` is refuted by two explicit
coordinate indicators; no dimension theory is used. -/
theorem m_le_one_of_polarRankOne
    (hOU : D.OutputUnique) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {a₀ : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hz : D.SolZ a₀ z₀)
    {w₀ : OutWit m r → ℚ}
    (hcodim : ∀ x : OutWit m r → ℚ, ∃ t : ℚ, D.InRadicalQ (x - t • w₀)) :
    m ≤ 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hm : 0 < m := by omega
  let j₀ : Fin m := ⟨0, by omega⟩
  let j₁ : Fin m := ⟨1, by omega⟩
  have hne : j₀ ≠ j₁ := by
    intro h
    have := congrArg Fin.val h
    simp [j₀, j₁] at this
  obtain ⟨t₀, ht₀⟩ := hcodim (outIndicator j₀)
  obtain ⟨t₁, ht₁⟩ := hcodim (outIndicator j₁)
  have e00 := D.outCoordQ_radicalQ_eq_zero hm hOU hz hQ ht₀ j₀
  have e01 := D.outCoordQ_radicalQ_eq_zero hm hOU hz hQ ht₀ j₁
  have e10 := D.outCoordQ_radicalQ_eq_zero hm hOU hz hQ ht₁ j₀
  have e11 := D.outCoordQ_radicalQ_eq_zero hm hOU hz hQ ht₁ j₁
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, outIndicator_inl, sub_eq_zero] at e00 e01 e10 e11
  -- e00 : 1 = t₀ * w₀ (inl j₀),  e01 : 0 = t₀ * w₀ (inl j₁)
  -- e10 : 0 = t₁ * w₀ (inl j₀),  e11 : 1 = t₁ * w₀ (inl j₁)
  have hw0 : w₀ (Sum.inl j₀) ≠ 0 := by
    intro h
    rw [h, mul_zero] at e00
    exact one_ne_zero e00
  have ht1z : t₁ = 0 := by
    rcases mul_eq_zero.mp e10.symm with h | h
    · exact h
    · exact absurd h hw0
  rw [ht1z, zero_mul] at e11
  exact one_ne_zero e11

/-- **B3, the step the reviewer asked for first.**  Under rank one, a vector all of whose OUTPUT
coordinates vanish is radical.  The witness coordinate directions are of that kind, so the form
and the linear part lose their witness dependence — proved in the original coordinates. -/
theorem witnessDir_inRadicalQ
    (hm : 0 < m) (hOU : D.OutputUnique) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    {a₀ : Fin n → ℤ} {z₀ : OutWit m r → ℤ} (hz : D.SolZ a₀ z₀)
    {w₀ : OutWit m r → ℚ}
    (hcodim : ∀ x : OutWit m r → ℚ, ∃ t : ℚ, D.InRadicalQ (x - t • w₀))
    {x : OutWit m r → ℚ} (hx : ∀ j : Fin m, x (Sum.inl j) = 0) :
    D.InRadicalQ x := by
  classical
  obtain ⟨j, hj⟩ := D.outCoord_w₀_ne_zero hm hOU hQ hz hcodim
  obtain ⟨t, ht⟩ := hcodim x
  have hcoord := D.outCoordQ_radicalQ_eq_zero hm hOU hz hQ ht j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hx j, zero_sub, neg_eq_zero] at hcoord
  have htz : t = 0 := by
    rcases mul_eq_zero.mp hcoord with h | h
    · exact h
    · exact absurd h hj
  have : x - t • w₀ = x := by rw [htz]; simp
  rwa [this] at ht

/-- The `m = 0` leaf, separated as the reviewer required. -/
theorem weakVectorCosetNF_of_polarRankOne_m_zero
    {D' : QuadraticGraphData n 0 r} {f : (Fin n → ℤ) → (Fin 0 → ℤ)} :
    WeakVectorCosetNF f := weakVectorCosetNF_of_m_zero

end QuadraticGraphData

/-- **OPEN.**  The remaining rank-one leaf, stated as a predicate and never asserted: at `m = 1`,
the witness-free re-presentation of the graph in the ORIGINAL coordinates, whose three ingredients
are (i) `witnessDir_inRadicalQ` above, (ii) the resulting disappearance of the witness variables
from `zQuadQ` and `zLinQ`, and (iii) the transfer of `Defines` to the resulting `r = 0` datum so
that `nInputNoWitness_full` applies.  Item (i) is proved; (ii) and (iii) are not. -/
def RankOneNoWitnessCompiler : Prop :=
  ∀ (n r : ℕ) (D : QuadraticGraphData n 1 r) (f : (Fin n → ℤ) → (Fin 1 → ℤ)),
    D.Defines f →
    (∀ x : OutWit 1 r → ℚ, (∀ j : Fin 1, x (Sum.inl j) = 0) → D.InRadicalQ x) →
    WeakVectorCosetNF f

end DiophCompression.ResearchUpgrade
