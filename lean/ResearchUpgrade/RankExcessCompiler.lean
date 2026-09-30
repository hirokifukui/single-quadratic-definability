/-
  RankExcessCompiler.lean — s53.  R41-C2: the witness-only rank-excess compiler.

  `D.Defines f`, `m ≥ 1`, `Q ≠ 0`, `d` = rational rank of the polar form on ℚ^(m+r).
  * `m_le_polarRank`: π(rad Q) = 0 gives `m ≤ d` (and `polarRank_le`: `d ≤ m + r`).
  * `witRadLattice` L = {u ∈ ℤ^r : (0,u) ∈ rad Q} is saturated; its Smith normal form
    generators lie in L (`snf_mem`) and span it (`snf_span`).
  * `polarRank_add_snfRank`: the SNF rank of L equals dim_ℚ rad Q, so `d + k = m + r`.
    The ℤ→ℚ step is done by hand with `exists_int_clear` (no new general library).
  * `exists_witnessCompiler`: an integer linear equivalence `U` of the WITNESS coordinates only,
    `ℤ^(d−m) × ℤ^(m+r−d) ≃ ℤ^r`, whose second block is radical, with
    `P(a, b, U(v, w)) = P(a, b, U(v, 0))`.
  * `compiledData U : QuadraticGraphData n m (d − m)` — same inputs, same outputs, integer
    coefficients (`IntQuad.pull`); graph iff, `Defines` / `Total` / `OutputUnique` transport,
    total degree ≤ 2 via `intQuad_iff_totalDegree_le_two`.
  * capstone `rankExcess_compiler`.

  `d − m` is the witness count of THIS presentation, not a semantic minimum
  (see RankExcessControl.lean).

  mathlib beyond C1's five (all #check'd against the working-zone mathlib d46bd45 — the release pin — s53_evidence/C2_coverage_probe_s53.log):
  Module.Basis.reindex / equivFun / equivFun_symm_apply, LinearMap.toMatrix' / toMatrix'_mulVec,
  Fintype.equivFinOfCardEq, Equiv.sumCompl, Matrix.dotProduct_mulVec / mulVec_mulVec,
  rank–nullity (already used by PolarAnnihilator.lean).

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.SaturatedLattice
import ResearchUpgrade.NoWitnessCompiler
import ResearchUpgrade.ReverseCompiler

namespace DiophCompression.ResearchUpgrade

open Matrix

def IntQuad.pull {ι κ : Type*} [Fintype ι] [Fintype κ] (P : IntQuad ι) (M : Matrix ι κ ℤ) :
    IntQuad κ where
  c := P.c
  l := P.l ᵥ* M
  Q := M.transpose * P.Q * M

theorem IntQuad.eval_pull {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : IntQuad ι) (M : Matrix ι κ ℤ) (y : κ → ℤ) :
    (P.pull M).eval y = P.eval (M *ᵥ y) := by
  simp only [IntQuad.eval, IntQuad.pull]
  rw [dotProduct_mulVec P.l M y, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec y,
    vecMul_transpose]

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

noncomputable def polarRank : ℕ := Module.finrank ℚ (LinearMap.range D.polarMapQ)

theorem finrank_outWit : Module.finrank ℚ (OutWit m r → ℚ) = m + r := by
  simp [Module.finrank_fintype_fun_eq_card]

theorem polarRank_le : D.polarRank ≤ m + r := by
  have := LinearMap.finrank_range_le D.polarMapQ
  rw [finrank_outWit] at this
  exact this

/-- The output projection `π`, over ℚ. -/
def outProjQ : (OutWit m r → ℚ) →ₗ[ℚ] (Fin m → ℚ) := LinearMap.funLeft ℚ ℚ Sum.inl

theorem ker_polar_le_ker_outProjQ (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) :
    LinearMap.ker D.polarMapQ ≤ LinearMap.ker (outProjQ (m := m) (r := r)) := by
  intro e he
  obtain ⟨z₀, hz⟩ := D.exists_solZ_of_defines hf 0
  have hrad := D.mem_ker_polarMapQ.mp he
  refine LinearMap.mem_ker.mpr (funext fun j => ?_)
  exact D.outCoordQ_radicalQ_eq_zero hm (D.outputUnique_of_defines hf) hz hQ hrad j

/-- **`π(rad Q) = 0` gives `m ≤ d`.** -/
theorem m_le_polarRank (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) : m ≤ D.polarRank := by
  have hle := Submodule.finrank_mono (D.ker_polar_le_ker_outProjQ hm hf hQ)
  have h1 := LinearMap.finrank_range_add_finrank_ker D.polarMapQ
  have h2 := LinearMap.finrank_range_add_finrank_ker (outProjQ (m := m) (r := r))
  have hsurj : LinearMap.range (outProjQ (m := m) (r := r)) = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.funLeft_surjective_of_injective _ _ _ Sum.inl_injective)
  rw [hsurj, finrank_top] at h2
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1 h2
  unfold polarRank
  omega

/-! ### The witness radical lattice -/

/-- A witness vector, seen in the rational output/witness space with zero outputs. -/
def witQ (u : Fin r → ℤ) : OutWit m r → ℚ := toQ (Sum.elim (0 : Fin m → ℤ) u)

theorem witQ_add (u u' : Fin r → ℤ) : witQ (m := m) (u + u') = witQ u + witQ u' := by
  funext k; cases k <;> simp [witQ, toQ]

theorem witQ_zsmul (c : ℤ) (u : Fin r → ℤ) : witQ (m := m) (c • u) = (c : ℚ) • witQ u := by
  funext k; cases k <;> simp [witQ, toQ]

theorem witQ_zero : witQ (m := m) (0 : Fin r → ℤ) = 0 := by
  funext k; cases k <;> simp [witQ, toQ]

theorem inRadicalQ_add {v w : OutWit m r → ℚ} (hv : D.InRadicalQ v) (hw : D.InRadicalQ w) :
    D.InRadicalQ (v + w) := fun x => by rw [D.zPolarQ_add_left, hv x, hw x, add_zero]

theorem inRadicalQ_smul (lam : ℚ) {v : OutWit m r → ℚ} (hv : D.InRadicalQ v) :
    D.InRadicalQ (lam • v) := fun x => by rw [D.zPolarQ_smul_left, hv x, mul_zero]

/-- `L = {u ∈ ℤ^r : (0,u) ∈ rad Q}`. -/
def witRadLattice : Submodule ℤ (Fin r → ℤ) where
  carrier := {u | D.InRadicalQ (witQ (m := m) u)}
  add_mem' := by
    intro u u' hu hu'
    simp only [Set.mem_setOf_eq, witQ_add] at *
    exact D.inRadicalQ_add hu hu'
  zero_mem' := by
    simp only [Set.mem_setOf_eq, witQ_zero]
    intro x; simpa using D.zPolarQ_smul_left 0 0 x
  smul_mem' := by
    intro c u hu
    simp only [Set.mem_setOf_eq, witQ_zsmul] at *
    exact D.inRadicalQ_smul _ hu

theorem mem_witRadLattice {u : Fin r → ℤ} :
    u ∈ D.witRadLattice ↔ D.InRadicalQ (witQ (m := m) u) := Iff.rfl

theorem witRadLattice_saturated : SaturatedLattice.Saturated D.witRadLattice := by
  intro c u hc hu
  rw [mem_witRadLattice, witQ_zsmul] at hu
  rw [mem_witRadLattice]
  intro x
  have h := hu x
  rw [D.zPolarQ_smul_left] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hc)

/-- **Generalised B1.**  Adding a radical witness vector does not change the evaluation. -/
theorem eval_add_radWit (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    (a : Fin n → ℤ) (b : Fin m → ℤ) (u u' : Fin r → ℤ) (hu' : u' ∈ D.witRadLattice) :
    D.P.eval (pt a b (u + u')) = D.P.eval (pt a b u) := by
  classical
  set x : OutWit m r → ℤ := Sum.elim (fun _ => (0 : ℤ)) u' with hxdef
  set y : OutWit m r → ℤ := Sum.elim b u with hydef
  have hxrad : D.InRadicalQ (toQ x) := hu'
  have hdec : (Sum.elim b (u + u') : OutWit m r → ℤ) = y + x := by
    funext k; cases k <;> simp [hxdef, hydef]
  obtain ⟨z₀, hz⟩ := D.exists_solZ_of_defines hf a
  have hOU := D.outputUnique_of_defines hf
  have hadd : toQ (y + x) = toQ y + toQ x := by funext k; simp [toQ]
  have hquadQ : D.zQuadQ (toQ (y + x)) = D.zQuadQ (toQ y) := by
    rw [hadd, D.zQuadQ_add, D.zQuadQ_eq_zero_of_inRadicalQ hxrad,
        D.zPolarQ_symm, hxrad (toQ y)]
    ring
  have hquad : D.zQuad (y + x) = D.zQuad y := by
    have := hquadQ
    rw [D.zQuadQ_toQ, D.zQuadQ_toQ] at this
    exact_mod_cast this
  have hlinQ : D.zLinQ a (toQ (y + x)) = D.zLinQ a (toQ y) := by
    rw [hadd, D.zLinQ_add, D.zLinQ_radicalQ_eq_zero hm hOU hz hQ hxrad]
    ring
  have hlin : D.zLinEval a (y + x) = D.zLinEval a y := by
    have := hlinQ
    rw [D.zLinQ_toQ, D.zLinQ_toQ] at this
    exact_mod_cast this
  rw [D.eval_split a b (u + u'), D.eval_split a b u, hdec, ← hydef, hquad]
  have : (∑ k, D.zLin a k * (y + x) k) = ∑ k, D.zLin a k * y k := by
    simpa [zLinEval] using hlin
  rw [this]

/-! ### Smith normal form of `L`: generators, and the rank identification -/

theorem witQ_injective : Function.Injective (witQ (m := m) (r := r)) := by
  intro u u' h
  funext t
  have := congrFun h (Sum.inr t)
  simpa [witQ, toQ] using this

/-- `witQ` as an additive map. -/
def witQHom : (Fin r → ℤ) →+ (OutWit m r → ℚ) where
  toFun := witQ
  map_zero' := witQ_zero
  map_add' := witQ_add

theorem witQ_sum {k : ℕ} (c : Fin k → ℤ) (v : Fin k → Fin r → ℤ) :
    witQ (m := m) (∑ i, c i • v i) = ∑ i, (c i : ℚ) • witQ (m := m) (v i) := by
  have h := map_sum (witQHom (m := m) (r := r)) (fun i => c i • v i) Finset.univ
  simp only [witQHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => witQ_zsmul _ _

variable {k : ℕ} (S : Module.Basis.SmithNormalForm D.witRadLattice (Fin r) k)

theorem snf_mem (i : Fin k) : S.bM (S.f i) ∈ D.witRadLattice := by
  have ha0 : S.a i ≠ 0 := by
    intro h
    have hb := S.snf i
    rw [h, zero_smul] at hb
    exact S.bN.ne_zero i (Submodule.coe_eq_zero.mp hb)
  refine D.witRadLattice_saturated (S.a i) _ ha0 ?_
  rw [← S.snf i]
  exact (S.bN i).2

theorem snf_span {u : Fin r → ℤ} (hu : u ∈ D.witRadLattice) :
    ∃ c : Fin k → ℤ, u = ∑ i, c i • S.bM (S.f i) := by
  set y : ↥D.witRadLattice := ⟨u, hu⟩
  refine ⟨fun j => S.bN.repr y j * S.a j, ?_⟩
  have h := S.bN.sum_repr y
  have h2 := congrArg D.witRadLattice.subtype h
  simp only [map_sum, map_smul, Submodule.subtype_apply] at h2
  exact h2.symm.trans (Finset.sum_congr rfl fun j _ => by rw [S.snf j, smul_smul])

/-- The rational span map of the SNF generators of `L`. -/
noncomputable def snfSpanQ : (Fin k → ℚ) →ₗ[ℚ] (OutWit m r → ℚ) where
  toFun c := ∑ i, c i • witQ (m := m) (S.bM (S.f i))
  map_add' c c' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' t c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

theorem snfSpanQ_injective : Function.Injective (D.snfSpanQ S) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  obtain ⟨w, d, hd, hw⟩ := exists_int_clear c
  have hsum : witQ (m := m) (∑ i, w i • S.bM (S.f i)) = 0 := by
    rw [witQ_sum]
    have : (∑ i, (w i : ℚ) • witQ (m := m) (S.bM (S.f i))) = (d : ℚ) • D.snfSpanQ S c := by
      simp only [snfSpanQ, LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum, smul_smul, hw]
    rw [this, hc, smul_zero]
  have h0 : (∑ i, w i • S.bM (S.f i)) = 0 := by
    apply witQ_injective (m := m)
    rw [hsum, witQ_zero]
  have hli : LinearIndependent ℤ (S.bM ∘ S.f) :=
    S.bM.linearIndependent.comp S.f S.f.injective
  have hw0 := Fintype.linearIndependent_iff.mp hli w (by simpa using h0)
  funext i
  have := hw i
  rw [hw0 i] at this
  have hd0 : ((d : ℚ)) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Int.cast_zero] at this
  exact (mul_eq_zero.mp this.symm).resolve_left hd0

theorem range_snfSpanQ (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) :
    LinearMap.range (D.snfSpanQ S) = LinearMap.ker D.polarMapQ := by
  classical
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    show (∑ i, c i • witQ (m := m) (S.bM (S.f i))) ∈ LinearMap.ker D.polarMapQ
    refine Submodule.sum_mem (LinearMap.ker D.polarMapQ) fun i _ => ?_
    exact Submodule.smul_mem _ _ (D.mem_ker_polarMapQ.mpr (D.snf_mem S i))
  · intro e he
    have hout : ∀ j, e (Sum.inl j) = 0 := fun j =>
      congrFun (LinearMap.mem_ker.mp (D.ker_polar_le_ker_outProjQ hm hf hQ he)) j
    obtain ⟨w, d, hd, hw⟩ := exists_int_clear e
    set u : Fin r → ℤ := fun t => w (Sum.inr t)
    have hwu : witQ (m := m) u = (d : ℚ) • e := by
      funext x
      cases x with
      | inl j => simp [witQ, toQ, hout j]
      | inr t => simp [witQ, toQ, u, hw (Sum.inr t)]
    have hu : u ∈ D.witRadLattice := by
      rw [mem_witRadLattice, hwu]
      exact D.inRadicalQ_smul _ (D.mem_ker_polarMapQ.mp he)
    obtain ⟨c, hc⟩ := D.snf_span S hu
    have hd0 : ((d : ℚ)) ≠ 0 := by exact_mod_cast hd.ne'
    refine ⟨fun i => (d : ℚ)⁻¹ * (c i : ℚ), ?_⟩
    have hφ : D.snfSpanQ S (fun i => (c i : ℚ)) = (d : ℚ) • e := by
      rw [← hwu, hc, witQ_sum]
      rfl
    have : (fun i => (d : ℚ)⁻¹ * (c i : ℚ)) = (d : ℚ)⁻¹ • (fun i => (c i : ℚ)) := by
      funext i; simp
    rw [this, map_smul, hφ, smul_smul, inv_mul_cancel₀ hd0, one_smul]

include S in
/-- **Rank identification.**  The SNF rank of `L` is the dimension of the radical, hence
`d + k = m + r`. -/
theorem polarRank_add_snfRank (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) :
    D.polarRank + k = m + r := by
  have hk : Module.finrank ℚ (LinearMap.ker D.polarMapQ) = k := by
    rw [← D.range_snfSpanQ S hm hf hQ, LinearMap.finrank_range_of_inj (D.snfSpanQ_injective S)]
    simp
  have h1 := LinearMap.finrank_range_add_finrank_ker D.polarMapQ
  rw [hk, finrank_outWit] at h1
  exact h1

omit S

/-! ### The witness-only unimodular change -/

/-- `U` moves witnesses only; its last block is radical and invisible to `P`. -/
def WitnessCompiler
    (U : ((Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank)) → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) : Prop :=
  (∀ w : Fin (m + r - D.polarRank) → ℤ,
      D.InRadicalQ (toQ (Sum.elim (0 : Fin m → ℤ) (U (Sum.elim 0 w))))) ∧
  (∀ (a : Fin n → ℤ) (b : Fin m → ℤ) (v : Fin (D.polarRank - m) → ℤ)
      (w : Fin (m + r - D.polarRank) → ℤ),
      D.P.eval (pt a b (U (Sum.elim v w))) = D.P.eval (pt a b (U (Sum.elim v 0))))

/-- **R41-C2, existence of the witness-only unimodular change.** -/
theorem exists_witnessCompiler (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) :
    ∃ U, D.WitnessCompiler U := by
  classical
  obtain ⟨k, S⟩ := D.witRadLattice.smithNormalForm (Pi.basisFun ℤ (Fin r))
  have hk := D.polarRank_add_snfRank S hm hf hQ
  let p : Fin r → Prop := fun i => i ∈ Set.range S.f
  let eW₀ : {i // p i} ≃ Fin k := (Equiv.ofInjective S.f S.f.injective).symm
  let eW : {i // p i} ≃ Fin (m + r - D.polarRank) := eW₀.trans (finCongr (by omega))
  have hcardK : Fintype.card {i // ¬ p i} = D.polarRank - m := by
    rw [Fintype.card_subtype_compl, Fintype.card_congr eW₀, Fintype.card_fin, Fintype.card_fin]
    omega
  let eK : {i // ¬ p i} ≃ Fin (D.polarRank - m) := Fintype.equivFinOfCardEq hcardK
  let e : Fin r ≃ (Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank)) :=
    (Equiv.sumCompl p).symm.trans ((Equiv.sumComm _ _).trans (Equiv.sumCongr eK eW))
  have he : ∀ t, p (e.symm (Sum.inr t)) := by
    intro t
    have : e.symm (Sum.inr t) = ((eW.symm t : {i // p i}) : Fin r) := by
      simp [e, Equiv.sumCompl_apply_inl]
    rw [this]
    exact (eW.symm t).2
  let U := (S.bM.reindex e).equivFun.symm
  have hmem : ∀ w : Fin (m + r - D.polarRank) → ℤ, U (Sum.elim 0 w) ∈ D.witRadLattice := by
    intro w
    rw [Module.Basis.equivFun_symm_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    rcases j with j | t
    · simp
    · refine Submodule.smul_mem _ _ ?_
      rw [Module.Basis.reindex_apply]
      obtain ⟨i, hi⟩ := he t
      rw [← hi]
      exact D.snf_mem S i
  refine ⟨U, fun w => hmem w, fun a b v w => ?_⟩
  have hsplit : (Sum.elim v w : Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank) → ℤ)
      = Sum.elim v (0 : Fin (m + r - D.polarRank) → ℤ)
        + Sum.elim (0 : Fin (D.polarRank - m) → ℤ) w := by
    funext x; cases x <;> simp
  rw [hsplit, map_add]
  exact D.eval_add_radWit hm hf hQ a b _ _ (hmem w)

/-! ### The compiled datum -/

/-- The linear substitution `(a, b, v) ↦ (a, b, U(v, 0))`. -/
noncomputable def substMap
    (U : ((Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank)) → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) :
    (Vars n m (D.polarRank - m) → ℤ) →ₗ[ℤ] (Vars n m r → ℤ) where
  toFun z := pt (fun i => z (Sum.inl i)) (fun j => z (Sum.inr (Sum.inl j)))
      (U (Sum.elim (fun t => z (Sum.inr (Sum.inr t))) 0))
  map_add' z z' := by
    have h : (Sum.elim (fun t => (z + z') (Sum.inr (Sum.inr t))) 0 :
          Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank) → ℤ)
        = Sum.elim (fun t => z (Sum.inr (Sum.inr t))) 0
          + Sum.elim (fun t => z' (Sum.inr (Sum.inr t))) 0 := by
      funext x; cases x <;> simp
    rw [h, map_add]
    funext x; rcases x with i | j | t <;> simp [pt]
  map_smul' c z := by
    have h : (Sum.elim (fun t => (c • z) (Sum.inr (Sum.inr t))) 0 :
          Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank) → ℤ)
        = c • Sum.elim (fun t => z (Sum.inr (Sum.inr t))) 0 := by
      funext x; cases x <;> simp
    rw [h, map_smul]
    funext x; rcases x with i | j | t <;> simp [pt]

/-- The compiled datum: same `n`, same `m`, `d − m` witnesses, integer coefficients. -/
noncomputable def compiledData
    (U : ((Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank)) → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) :
    QuadraticGraphData n m (D.polarRank - m) where
  P := D.P.pull (LinearMap.toMatrix' (D.substMap U))

variable (U : ((Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank)) → ℤ) ≃ₗ[ℤ] (Fin r → ℤ))

theorem compiledData_eval (a : Fin n → ℤ) (b : Fin m → ℤ) (v : Fin (D.polarRank - m) → ℤ) :
    (D.compiledData U).P.eval (pt a b v) = D.P.eval (pt a b (U (Sum.elim v 0))) := by
  simp only [compiledData]
  rw [IntQuad.eval_pull, LinearMap.toMatrix'_mulVec]
  rfl

theorem compiledData_graph_iff (hU : D.WitnessCompiler U) (a : Fin n → ℤ) (b : Fin m → ℤ) :
    D.Graph a b ↔ (D.compiledData U).Graph a b := by
  constructor
  · rintro ⟨u, hu⟩
    set x := U.symm u
    refine ⟨fun t => x (Sum.inl t), ?_⟩
    have hx : (Sum.elim (fun t => x (Sum.inl t)) (fun t => x (Sum.inr t)) :
        Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank) → ℤ) = x := by
      funext y; cases y <;> rfl
    show (D.compiledData U).P.eval _ = 0
    rw [D.compiledData_eval, ← hU.2 a b _ (fun t => x (Sum.inr t)), hx,
      LinearEquiv.apply_symm_apply]
    exact hu
  · rintro ⟨v, hv⟩
    refine ⟨U (Sum.elim v 0), ?_⟩
    show D.P.eval _ = 0
    rw [← D.compiledData_eval]
    exact hv

theorem compiledData_defines (hU : D.WitnessCompiler U) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) : (D.compiledData U).Defines f := by
  intro a b
  rw [← D.compiledData_graph_iff U hU a b]
  exact hf a b

theorem compiledData_total (hU : D.WitnessCompiler U) (hT : D.Total) :
    (D.compiledData U).Total := by
  intro a
  obtain ⟨b, hb⟩ := hT a
  exact ⟨b, (D.compiledData_graph_iff U hU a b).mp hb⟩

theorem compiledData_outputUnique (hU : D.WitnessCompiler U) (hOU : D.OutputUnique) :
    (D.compiledData U).OutputUnique := by
  intro a b b' hb hb'
  exact hOU a b b' ((D.compiledData_graph_iff U hU a b).mpr hb)
    ((D.compiledData_graph_iff U hU a b').mpr hb')

theorem compiledData_totalDegree_le_two :
    ∃ Pm : MvPolynomial (Vars n m (D.polarRank - m)) ℤ, Pm.totalDegree ≤ 2 ∧
      ∀ x, MvPolynomial.eval x Pm = (D.compiledData U).P.eval x :=
  (intQuad_iff_totalDegree_le_two _).mp ⟨_, fun _ => rfl⟩

omit U

/-- **R41-C2 capstone — the witness-only rank-excess compiler.**  With `d` the rational rank of
the polar form: `m ≤ d ≤ m + r`, and there is an integer-unimodular change of the WITNESS
coordinates only, whose last `m + r − d` directions are radical and invisible to `P`; restricting
them to zero gives an integer datum of degree ≤ 2 with `d − m` witnesses, the same inputs, the same
outputs and the same graph, which defines the same `f`.  `d − m` is the witness count of THIS
presentation, not a semantic minimum. -/
theorem rankExcess_compiler (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) :
    m ≤ D.polarRank ∧ D.polarRank ≤ m + r ∧
    ∃ U, D.WitnessCompiler U ∧
      (∀ a b, D.Graph a b ↔ (D.compiledData U).Graph a b) ∧
      (D.compiledData U).Defines f ∧
      ∃ Pm : MvPolynomial (Vars n m (D.polarRank - m)) ℤ, Pm.totalDegree ≤ 2 ∧
        ∀ x, MvPolynomial.eval x Pm = (D.compiledData U).P.eval x := by
  obtain ⟨U, hU⟩ := D.exists_witnessCompiler hm hf hQ
  exact ⟨D.m_le_polarRank hm hf hQ, D.polarRank_le, U, hU, D.compiledData_graph_iff U hU,
    D.compiledData_defines U hU hf, D.compiledData_totalDegree_le_two U⟩

end QuadraticGraphData
end DiophCompression.ResearchUpgrade
