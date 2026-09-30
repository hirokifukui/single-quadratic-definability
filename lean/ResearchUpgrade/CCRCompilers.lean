/-
  CCRCompilers.lean — s56.  GPT R44 A1 steps 3–5 (GATE26) in GPT's own form.

  * `lineData` (A1.3) — the line compiler: restrict the input to `a₀ + t v`; `QuadraticGraphData 1 m r`, integer
    coefficients and total degree ≤ 2 by construction.  Preserves solutions (`lineData_solZ`), the output/witness
    form (`lineData_zQuadQ`), the polar rank, centres, the residual, totality and output-uniqueness; the affine centre
    restricts to an affine centre (`lineData_centreAt`).
  * `reindexOut` (A1.4) — re-index outputs/witnesses by an equivalence; with `σ (inl 0) = inl j₀`
    (`exists_outSelect`) it keeps the single output `j₀` and moves the other outputs to the witnesses.  Solutions,
    the form, centres, residual and totality transport; vector output-uniqueness gives scalar output-uniqueness
    (`reindexOut_outputUnique_one`).
  * `CCR_oneInputOneOutput`, `ccr_iff_oneInputOneOutput` (A1.5) — general CCR ⟺ its one-input, one-output case.
  Helpers (not frozen): `lineData_zLin`, `lineData_aPart`, `reindexOut_eval`.

  Statements frozen before proof (`~/lean/s56_evidence/freeze/A1C_FREEZE_s56.lean`, Dr. Fukui 2026-09-25 15:51);
  frozen = installed by `#check`/`#print` output, planted control caught.
  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.SectionRigidity
namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadraticGraphData

variable {n m r : ℕ}

/-- **A1.3 (line compiler).**  Restrict the input to the line `a₀ + t v` (`t ∈ ℤ`), keeping every output and
witness.  Coefficients: those of `P(a₀ + t v, z)` expanded in `t` and `z`. -/
def lineData (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) : QuadraticGraphData 1 m r where
  P :=
  { c := D.aPart a0
    l := Sum.elim
      (fun _ => ∑ i, D.P.l (Sum.inl i) * v i
        + ∑ i, ∑ j, (a0 i * D.P.Q (Sum.inl i) (Sum.inl j) * v j + v i * D.P.Q (Sum.inl i) (Sum.inl j) * a0 j))
      (fun k => D.zLin a0 k)
    Q := Sum.elim
      (fun _ => Sum.elim (fun _ => ∑ i, ∑ j, v i * D.P.Q (Sum.inl i) (Sum.inl j) * v j)
        (fun k => ∑ i, v i * D.P.Q (Sum.inl i) (Sum.inr k)))
      (fun k => Sum.elim (fun _ => ∑ i, D.P.Q (Sum.inr k) (Sum.inl i) * v i)
        (fun k' => D.P.Q (Sum.inr k) (Sum.inr k'))) }

/-- The line compiler's linear coefficient (not frozen; a helper). -/
theorem lineData_zLin (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (t : Fin 1 → ℤ) (k : OutWit m r) :
    (D.lineData a0 v).zLin t k = D.zLin (a0 + t 0 • v) k := by
  have h3 : ∀ i, (a0 + t 0 • v) i * (D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i))
      = a0 i * (D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i))
        + t 0 * (v i * D.P.Q (Sum.inl i) (Sum.inr k) + D.P.Q (Sum.inr k) (Sum.inl i) * v i) := by
    intro i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp only [zLin, lineData, Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr, h3, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- The line compiler's input part (not frozen; a helper). -/
theorem lineData_aPart (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (t : Fin 1 → ℤ) :
    (D.lineData a0 v).aPart t = D.aPart (a0 + t 0 • v) := by
  have h1 : ∀ i, D.P.l (Sum.inl i) * (a0 + t 0 • v) i
      = D.P.l (Sum.inl i) * a0 i + t 0 * (D.P.l (Sum.inl i) * v i) := by
    intro i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have h2 : ∀ i j, (a0 + t 0 • v) i * (D.P.Q (Sum.inl i) (Sum.inl j) * (a0 + t 0 • v) j)
      = a0 i * (D.P.Q (Sum.inl i) (Sum.inl j) * a0 j)
        + t 0 * (a0 i * D.P.Q (Sum.inl i) (Sum.inl j) * v j + v i * D.P.Q (Sum.inl i) (Sum.inl j) * a0 j)
        + t 0 ^ 2 * (v i * D.P.Q (Sum.inl i) (Sum.inl j) * v j) := by
    intro i j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp only [aPart, lineData, Fin.sum_univ_one, Sum.elim_inl, h1, h2, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

theorem lineData_solZ (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (t : Fin 1 → ℤ)
    (z : OutWit m r → ℤ) : (D.lineData a0 v).SolZ t z ↔ D.SolZ (a0 + t 0 • v) z := by
  unfold SolZ
  rw [D.evalZ, (D.lineData a0 v).evalZ]
  have hq : (D.lineData a0 v).zQuad z = D.zQuad z := rfl
  have hl : (D.lineData a0 v).zLinEval t z = D.zLinEval (a0 + t 0 • v) z := by
    simp only [zLinEval, D.lineData_zLin]
  rw [hq, hl, D.lineData_aPart]

theorem lineData_zQuadQ (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (u : OutWit m r → ℚ) :
    (D.lineData a0 v).zQuadQ u = D.zQuadQ u := by
  rfl

theorem lineData_polarRank (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) :
    (D.lineData a0 v).polarRank = D.polarRank := by
  rfl

theorem lineData_isCentre (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (t : Fin 1 → ℤ)
    (c : OutWit m r → ℚ) : (D.lineData a0 v).IsCentre t c ↔ D.IsCentre (a0 + t 0 • v) c := by
  have hL : ∀ w, (D.lineData a0 v).zLinQ t w = D.zLinQ (a0 + t 0 • v) w := by
    intro w; simp only [zLinQ, D.lineData_zLin]
  have hP : ∀ c w, (D.lineData a0 v).zPolarQ c w = D.zPolarQ c w := fun _ _ => rfl
  simp only [IsCentre, hL, hP]

theorem lineData_residual (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (t : Fin 1 → ℤ)
    (c : OutWit m r → ℚ) : (D.lineData a0 v).residual t c = D.residual (a0 + t 0 • v) c := by
  simp only [residual, D.lineData_zQuadQ, D.lineData_aPart]

theorem lineData_centreAt (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) (a0 v : Fin n → ℤ)
    (t : Fin 1 → ℤ) :
    centreAt (centreAt c0 C a0) (fun k _ => ∑ i, C k i * (v i : ℚ)) t = centreAt c0 C (a0 + t 0 • v) := by
  funext k
  simp only [centreAt, Fin.sum_univ_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [Finset.sum_mul, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem lineData_total (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (hT : D.Total) :
    (D.lineData a0 v).Total := by
  intro t
  obtain ⟨b, u, hu⟩ := hT (a0 + t 0 • v)
  exact ⟨b, u, (D.lineData_solZ a0 v t (Sum.elim b u)).mpr hu⟩

theorem lineData_outputUnique (D : QuadraticGraphData n m r) (a0 v : Fin n → ℤ) (hOU : D.OutputUnique) :
    (D.lineData a0 v).OutputUnique := by
  intro t b b' hb hb'
  obtain ⟨u, hu⟩ := hb
  obtain ⟨u', hu'⟩ := hb'
  exact hOU _ b b' ⟨u, (D.lineData_solZ a0 v t (Sum.elim b u)).mp hu⟩
    ⟨u', (D.lineData_solZ a0 v t (Sum.elim b' u')).mp hu'⟩

/-- **A1.4 (output compiler).**  Re-index the output/witness block by an equivalence `σ`; with `m' = 1` and
`σ (inl 0) = inl j₀` it keeps the single output `j₀` and moves every other output to the witnesses. -/
def reindexOut (D : QuadraticGraphData n m r) {m' r' : ℕ} (σ : OutWit m' r' ≃ OutWit m r) :
    QuadraticGraphData n m' r' where
  P :=
  { c := D.P.c
    l := fun x => D.P.l (Sum.map id σ x)
    Q := fun x y => D.P.Q (Sum.map id σ x) (Sum.map id σ y) }

/-- Evaluation of the re-indexed polynomial (not frozen; a helper). -/
theorem reindexOut_eval (D : QuadraticGraphData n m r) {m' r' : ℕ} (σ : OutWit m' r' ≃ OutWit m r)
    (x : Vars n m' r' → ℤ) :
    (D.reindexOut σ).P.eval x = D.P.eval (x ∘ (Equiv.sumCongr (Equiv.refl (Fin n)) σ).symm) := by
  set ψ : Vars n m' r' ≃ Vars n m r := Equiv.sumCongr (Equiv.refl (Fin n)) σ with hψ
  have hmap : ∀ y, Sum.map id σ y = ψ y := fun y => by cases y <;> rfl
  simp only [IntQuad.eval, dotProduct, mulVec, reindexOut, hmap]
  congr 1
  · congr 1
    exact Fintype.sum_equiv ψ _ _ (fun y => by simp)
  · refine Fintype.sum_equiv ψ _ _ (fun y => ?_)
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    congr 1
    exact Fintype.sum_equiv ψ _ _ (fun y2 => by simp)

theorem reindexOut_solZ (D : QuadraticGraphData n m r) {m' r' : ℕ} (σ : OutWit m' r' ≃ OutWit m r)
    (a : Fin n → ℤ) (z : OutWit m' r' → ℤ) : (D.reindexOut σ).SolZ a z ↔ D.SolZ a (z ∘ σ.symm) := by
  unfold SolZ
  rw [D.reindexOut_eval σ]
  have e : (Sum.elim a z ∘ (Equiv.sumCongr (Equiv.refl (Fin n)) σ).symm) = Sum.elim a (z ∘ σ.symm) := by
    funext y; cases y <;> rfl
  rw [e]

theorem reindexOut_zQuadQ (D : QuadraticGraphData n m r) {m' r' : ℕ} (σ : OutWit m' r' ≃ OutWit m r)
    (u : OutWit m' r' → ℚ) : (D.reindexOut σ).zQuadQ u = D.zQuadQ (u ∘ σ.symm) := by
  simp only [zQuadQ]
  refine Fintype.sum_equiv σ _ _ (fun k => ?_)
  refine (Fintype.sum_equiv σ _ _ (fun k' => ?_))
  simp [reindexOut]

theorem reindexOut_isCentre (D : QuadraticGraphData n m r) {m' r' : ℕ} (σ : OutWit m' r' ≃ OutWit m r)
    (a : Fin n → ℤ) (c : OutWit m' r' → ℚ) :
    (D.reindexOut σ).IsCentre a c ↔ D.IsCentre a (c ∘ σ.symm) := by
  have hP : ∀ v w : OutWit m' r' → ℚ, (D.reindexOut σ).zPolarQ v w = D.zPolarQ (v ∘ σ.symm) (w ∘ σ.symm) := by
    intro v w
    simp only [zPolarQ]
    refine Fintype.sum_equiv σ _ _ (fun k => ?_)
    refine (Fintype.sum_equiv σ _ _ (fun k' => ?_))
    simp [reindexOut]
  have hL : ∀ w : OutWit m' r' → ℚ, (D.reindexOut σ).zLinQ a w = D.zLinQ a (w ∘ σ.symm) := by
    intro w
    simp only [zLinQ]
    refine Fintype.sum_equiv σ _ _ (fun k => ?_)
    simp [zLin, reindexOut]
  simp only [IsCentre, hP, hL]
  constructor
  · intro h w
    have := h (w ∘ σ)
    simpa [Function.comp_def] using this
  · intro h w
    exact h (w ∘ σ.symm)

theorem reindexOut_residual (D : QuadraticGraphData n m r) {m' r' : ℕ} (σ : OutWit m' r' ≃ OutWit m r)
    (a : Fin n → ℤ) (c : OutWit m' r' → ℚ) :
    (D.reindexOut σ).residual a c = D.residual a (c ∘ σ.symm) := by
  have ha : (D.reindexOut σ).aPart a = D.aPart a := rfl
  simp only [residual, D.reindexOut_zQuadQ, ha]

theorem reindexOut_total (D : QuadraticGraphData n m r) {m' r' : ℕ} (σ : OutWit m' r' ≃ OutWit m r)
    (hT : D.Total) : (D.reindexOut σ).Total := by
  intro a
  obtain ⟨b, u, hu⟩ := hT a
  have hz : (D.reindexOut σ).SolZ a (Sum.elim b u ∘ σ) := by
    rw [D.reindexOut_solZ]
    have e : (Sum.elim b u ∘ σ) ∘ σ.symm = Sum.elim b u := by funext k; simp
    rw [e]; exact hu
  exact ⟨_, (D.reindexOut σ).graph_of_solZ hz⟩

/-- Vector output-uniqueness gives SCALAR output-uniqueness for the kept output `j₀`. -/
theorem reindexOut_outputUnique_one (D : QuadraticGraphData n m r) {r' : ℕ} (σ : OutWit 1 r' ≃ OutWit m r)
    (j0 : Fin m) (hσ : σ (Sum.inl 0) = Sum.inl j0) (hOU : D.OutputUnique) :
    (D.reindexOut σ).OutputUnique := by
  intro a b1 b2 hb1 hb2
  obtain ⟨u1, h1⟩ := hb1
  obtain ⟨u2, h2⟩ := hb2
  have g1 := D.graph_of_solZ ((D.reindexOut_solZ σ a (Sum.elim b1 u1)).mp h1)
  have g2 := D.graph_of_solZ ((D.reindexOut_solZ σ a (Sum.elim b2 u2)).mp h2)
  have e := congrFun (hOU a _ _ g1 g2) j0
  have hs : σ.symm (Sum.inl j0) = Sum.inl 0 := by rw [← hσ]; simp
  simp only [outProj, Function.comp_apply, hs, Sum.elim_inl] at e
  funext i
  fin_cases i
  exact e

theorem exists_outSelect (j0 : Fin m) :
    ∃ σ : OutWit 1 (m - 1 + r) ≃ OutWit m r, σ (Sum.inl 0) = Sum.inl j0 := by
  have hm : 1 ≤ m := Nat.succ_le_of_lt j0.pos
  have hcard : Fintype.card (OutWit 1 (m - 1 + r)) = Fintype.card (OutWit m r) := by
    simp only [Fintype.card_sum, Fintype.card_fin]; omega
  let τ : OutWit 1 (m - 1 + r) ≃ OutWit m r := Fintype.equivOfCardEq hcard
  refine ⟨τ.trans (Equiv.swap (τ (Sum.inl 0)) (Sum.inl j0)), ?_⟩
  simp

end QuadraticGraphData

/-- CCR with one input and one output (any number of witnesses). -/
def CCR_oneInputOneOutput : Prop :=
  ∀ (r : ℕ) (D : QuadraticGraphData 1 1 r) (c0 : OutWit 1 r → ℚ) (C : Matrix (OutWit 1 r) (Fin 1) ℚ),
    (∀ u : OutWit 1 r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) → 2 ≤ D.polarRank →
      (∀ a, D.IsCentre a (QuadraticGraphData.centreAt c0 C a)) → D.Total → D.OutputUnique →
        ∃ R0 : ℚ, ∀ a, D.residual a (QuadraticGraphData.centreAt c0 C a) = R0

/-- **A1.5.**  General CCR is equivalent to its one-input, one-output case, through the two compilers. -/
theorem ccr_iff_oneInputOneOutput : ConstantResidualRigidity ↔ CCR_oneInputOneOutput := by
  constructor
  · intro h r D c0 C hpos hrank hc hT hOU
    exact h 1 1 r D c0 C Nat.one_pos hpos hrank hc hT hOU
  · intro h n m r D c0 C hm hpos hrank hc hT hOU
    by_contra hnc
    obtain ⟨a0, v, A, B, hA, hl⟩ := D.residual_line_of_nonconstant hpos c0 C hc hT hnc
    obtain ⟨σ, hσ⟩ := QuadraticGraphData.exists_outSelect (m := m) (r := r) ⟨0, hm⟩
    let c0' : OutWit 1 (m - 1 + r) → ℚ := fun k => QuadraticGraphData.centreAt c0 C a0 (σ k)
    let C' : Matrix (OutWit 1 (m - 1 + r)) (Fin 1) ℚ := fun k _ => ∑ i, C (σ k) i * (v i : ℚ)
    have hce : ∀ t : Fin 1 → ℤ, QuadraticGraphData.centreAt c0' C' t ∘ σ.symm
        = QuadraticGraphData.centreAt c0 C (a0 + t 0 • v) := by
      intro t
      rw [← QuadraticGraphData.lineData_centreAt]
      funext k
      simp [QuadraticGraphData.centreAt, c0', C']
    have hcen1 : ∀ t, ((D.lineData a0 v).reindexOut σ).IsCentre t (QuadraticGraphData.centreAt c0' C' t) := by
      intro t
      rw [QuadraticGraphData.reindexOut_isCentre, QuadraticGraphData.lineData_isCentre, hce]
      exact hc _
    have hpos1 : ∀ u : OutWit 1 (m - 1 + r) → ℚ, u ≠ 0 → 0 < ((D.lineData a0 v).reindexOut σ).zQuadQ u := by
      intro u hu
      rw [QuadraticGraphData.reindexOut_zQuadQ, QuadraticGraphData.lineData_zQuadQ]
      apply hpos
      intro h0
      apply hu
      funext k
      have := congrFun h0 (σ k)
      simpa using this
    have hrank1 : 2 ≤ ((D.lineData a0 v).reindexOut σ).polarRank := by
      rw [QuadraticGraphData.sr_polarRank_eq _ hpos1]
      have := QuadraticGraphData.sr_polarRank_eq D hpos
      omega
    have hT1 := QuadraticGraphData.reindexOut_total _ σ (QuadraticGraphData.lineData_total D a0 v hT)
    have hOU1 := QuadraticGraphData.reindexOut_outputUnique_one _ σ ⟨0, hm⟩ hσ
      (QuadraticGraphData.lineData_outputUnique D a0 v hOU)
    obtain ⟨R0, hR0⟩ := h (m - 1 + r) _ c0' C' hpos1 hrank1 hcen1 hT1 hOU1
    have key : ∀ t : ℤ, A * (t : ℚ) ^ 2 + B * t
        + D.residual a0 (QuadraticGraphData.centreAt c0 C a0) = R0 := by
      intro t
      have h1 := hR0 (fun _ => t)
      rw [QuadraticGraphData.reindexOut_residual, QuadraticGraphData.lineData_residual, hce] at h1
      rw [← hl t]
      simpa using h1
    have e0 := key 0
    have e1 := key 1
    have e2 := key (-1)
    push_cast at e0 e1 e2
    linarith

end DiophCompression.ResearchUpgrade
