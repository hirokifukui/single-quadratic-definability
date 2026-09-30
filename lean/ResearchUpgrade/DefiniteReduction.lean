/-
  DefiniteReduction.lean — s53.  R41-C3: the semidefinite weak NF reduces EXACTLY to the
  positive definite one.

  * `exists_exactWitnessCompiler`: C2's construction, with the extra clause that every radical
    witness vector comes from the radical block (`ExactWitnessCompiler`).
  * `compiled_zQuad` / `compiled_zPolar`: the compiled form is the original one read through
    `outMap : (b, v) ↦ (b, U(v, 0))` (quadratic part recovered from three evaluations at input 0).
  * `compiledData_nondegQ`: the compiled polar form has ZERO radical over ℚ.
  * `compiledData_polarRank`: its rank is still `d` (the rank of the polar form, not of the
    non-symmetric coefficient matrix).
  * `compiledData_posDef`: a semidefinite form compiles to a positive definite one.
  * `semidefiniteWeakNF_iff_definiteWeakNF`, `generalWeakNF_iff_definiteWeakNF`: PROVED
    equivalences.  `DefiniteWeakNF` is a `def` marked OPEN; nothing here asserts it.
  * `DefiniteWeakNF_oneOut_oneWit`: the exact type of the next arithmetic residue (m = 1,
    one witness, any n, positive definite).  Not a condition of anything proved here.  PROVED
    downstream (s54) as `definiteWeakNF_oneOut_oneWit_holds` in `DefiniteBinary.lean`, together
    with the polar-rank-≤-2 case `lowRankSemidefiniteWeakNF_holds`; `DefiniteWeakNF` itself (all
    ranks) stays OPEN.
    Full-residue NF is not reduced here.
  * Control: `exD_definite_reduction` — the (b − a)² + (u₀ + u₁)² example compiles to a
    positive definite datum of rank 2.

  Claim tags: reductions [P] (std-3); `DefiniteWeakNF` [OPEN]; `DefiniteWeakNF_oneOut_oneWit`
  is a `def` here and is proved in `DefiniteBinary.lean` (s54).
-/
import ResearchUpgrade.RankExcessControl
import ResearchUpgrade.Reduction
import ResearchUpgrade.OutputCoercivity
import ResearchUpgrade.IsotropicDirection

namespace DiophCompression.ResearchUpgrade

/-- The definite residue.  OPEN. -/
def DefiniteWeakNF : Prop :=
  ∀ (n m r : ℕ) (D : QuadraticGraphData n m r) (f : (Fin n → ℤ) → (Fin m → ℤ)),
    0 < m → (∀ u : OutWit m r → ℚ, u ≠ 0 → 0 < D.zQuadQ u) → D.Defines f → WeakVectorCosetNF f

/-- The first arithmetic residue: one output, one witness, any `n`, positive definite.  Its
resolution is not a condition of anything proved here.  Proved for every `n` in
`DefiniteBinary.lean` (`definiteWeakNF_oneOut_oneWit_holds`, s54), by a norm lift that does not go
through `Unconditional.rgen_weakCosetNF_definite` (that theorem is stated for the explicit relation
`Rgen` with `WeakScalarCosetNF`, and no bridge to `QuadraticGraphData 1 1 1` is used). -/
def DefiniteWeakNF_oneOut_oneWit : Prop :=
  ∀ (n : ℕ) (D : QuadraticGraphData n 1 1) (f : (Fin n → ℤ) → (Fin 1 → ℤ)),
    (∀ u : OutWit 1 1 → ℚ, u ≠ 0 → 0 < D.zQuadQ u) → D.Defines f → WeakVectorCosetNF f

theorem definiteWeakNF_oneOut_oneWit_of_definiteWeakNF (H : DefiniteWeakNF) :
    DefiniteWeakNF_oneOut_oneWit :=
  fun n D f hdef hf => H n 1 1 D f Nat.one_pos hdef hf

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

/-! ### Integer algebra of the form -/

theorem toQ_zsmul (c : ℤ) (z : OutWit m r → ℤ) : toQ (c • z) = (c : ℚ) • toQ z := by
  funext k; simp [toQ]

theorem toQ_add' (z z' : OutWit m r → ℤ) : toQ (z + z') = toQ z + toQ z' := by
  funext k; simp [toQ]

theorem zQuad_zsmul (c : ℤ) (z : OutWit m r → ℤ) : D.zQuad (c • z) = c ^ 2 * D.zQuad z := by
  have h := D.zQuadQ_smul (c : ℚ) (toQ z)
  rw [← toQ_zsmul, D.zQuadQ_toQ, D.zQuadQ_toQ] at h
  exact_mod_cast h

theorem zLinEval_zsmul (a : Fin n → ℤ) (c : ℤ) (z : OutWit m r → ℤ) :
    D.zLinEval a (c • z) = c * D.zLinEval a z := by
  simp only [zLinEval, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The quadratic part is read off three evaluations at input `0`. -/
theorem two_zQuad_eq (z : OutWit m r → ℤ) :
    2 * D.zQuad z = D.P.eval (Sum.elim 0 ((2 : ℤ) • z)) - 2 * D.P.eval (Sum.elim 0 z)
      + D.P.eval (Sum.elim 0 ((0 : ℤ) • z)) := by
  rw [D.evalZ, D.evalZ, D.evalZ, D.zQuad_zsmul, D.zQuad_zsmul, D.zLinEval_zsmul,
    D.zLinEval_zsmul]
  ring

theorem zPolar_eq (v w : OutWit m r → ℤ) :
    D.zPolar v w = D.zQuad (v + w) - D.zQuad v - D.zQuad w := by
  have h := D.zQuadQ_add (toQ v) (toQ w)
  rw [← toQ_add', D.zQuadQ_toQ, D.zQuadQ_toQ, D.zQuadQ_toQ, D.zPolarQ_toQ] at h
  have h' : D.zQuad (v + w) = D.zQuad v + D.zPolar v w + D.zQuad w := by exact_mod_cast h
  omega

/-- A rational vector orthogonal to every INTEGER vector is radical. -/
theorem inRadicalQ_of_int {v : OutWit m r → ℚ} (h : ∀ x : OutWit m r → ℤ, D.zPolarQ v (toQ x) = 0) :
    D.InRadicalQ v := by
  classical
  intro w
  obtain ⟨x, d, hd, hx⟩ := exists_int_clear w
  have hxw : toQ x = (d : ℚ) • w := by funext k; simp [toQ, hx k]
  have h1 := h x
  rw [hxw, D.zPolarQ_smul_right] at h1
  have hd0 : ((d : ℚ)) ≠ 0 := by exact_mod_cast hd.ne'
  exact (mul_eq_zero.mp h1).resolve_left hd0

/-! ### The exact compiler: `L` is exactly the image of the radical block -/

variable (U : ((Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank)) → ℤ) ≃ₗ[ℤ] (Fin r → ℤ))

/-- `U` is a witness compiler AND every radical witness vector comes from the radical block. -/
def ExactWitnessCompiler : Prop :=
  D.WitnessCompiler U ∧ ∀ u ∈ D.witRadLattice, ∃ w, u = U (Sum.elim 0 w)

omit U in
theorem exists_exactWitnessCompiler (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0) :
    ∃ U, D.ExactWitnessCompiler U := by
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
  have heK : ∀ s, ¬ p (e.symm (Sum.inl s)) := by
    intro s
    have : e.symm (Sum.inl s) = ((eK.symm s : {i // ¬ p i}) : Fin r) := by
      simp [e, Equiv.sumCompl_apply_inr]
    rw [this]
    exact (eK.symm s).2
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
  refine ⟨U, ⟨fun w => hmem w, fun a b v w => ?_⟩, fun u hu => ?_⟩
  · have hsplit : (Sum.elim v w : Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank) → ℤ)
        = Sum.elim v (0 : Fin (m + r - D.polarRank) → ℤ)
          + Sum.elim (0 : Fin (D.polarRank - m) → ℤ) w := by
      funext x; cases x <;> simp
    rw [hsplit, map_add]
    exact D.eval_add_radWit hm hf hQ a b _ _ (hmem w)
  · obtain ⟨c, hc⟩ := D.snf_span S hu
    set x := U.symm u with hxdef
    have hx0 : ∀ s, x (Sum.inl s) = 0 := by
      intro s
      have hxs : x (Sum.inl s) = S.bM.repr u (e.symm (Sum.inl s)) := by
        simp [hxdef, U, Module.Basis.equivFun_apply]
      rw [hxs, hc]
      simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
        Finset.sum_apply, Finsupp.smul_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Finsupp.single_apply, if_neg]
      · simp
      · intro h
        exact heK s ⟨i, h⟩
    refine ⟨fun t => x (Sum.inr t), ?_⟩
    have hxe : (Sum.elim 0 (fun t => x (Sum.inr t)) :
        Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank) → ℤ) = x := by
      funext y; rcases y with s | t
      · simp [hx0 s]
      · rfl
    rw [hxe, hxdef, LinearEquiv.apply_symm_apply]

/-! ### Transport of the form through the compiled substitution -/

/-- The output/witness part of the substitution: `(b, v) ↦ (b, U(v, 0))`. -/
def outMap (z : OutWit m (D.polarRank - m) → ℤ) : OutWit m r → ℤ :=
  Sum.elim (fun j => z (Sum.inl j)) (U (Sum.elim (fun t => z (Sum.inr t)) 0))

theorem outMap_add (z z' : OutWit m (D.polarRank - m) → ℤ) :
    D.outMap U (z + z') = D.outMap U z + D.outMap U z' := by
  have h : (Sum.elim (fun t => (z + z') (Sum.inr t)) 0 :
        Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank) → ℤ)
      = Sum.elim (fun t => z (Sum.inr t)) 0 + Sum.elim (fun t => z' (Sum.inr t)) 0 := by
    funext x; cases x <;> simp
  unfold outMap
  rw [h, map_add]
  funext x; cases x <;> simp

theorem outMap_zsmul (c : ℤ) (z : OutWit m (D.polarRank - m) → ℤ) :
    D.outMap U (c • z) = c • D.outMap U z := by
  have h : (Sum.elim (fun t => (c • z) (Sum.inr t)) 0 :
        Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank) → ℤ)
      = c • Sum.elim (fun t => z (Sum.inr t)) 0 := by
    funext x; cases x <;> simp
  unfold outMap
  rw [h, map_smul]
  funext x; cases x <;> simp

theorem compiled_evalZero (z : OutWit m (D.polarRank - m) → ℤ) :
    (D.compiledData U).P.eval (Sum.elim 0 z) = D.P.eval (Sum.elim 0 (D.outMap U z)) := by
  have hz : z = Sum.elim (fun j => z (Sum.inl j)) (fun t => z (Sum.inr t)) := by
    funext x; cases x <;> rfl
  conv_lhs => rw [hz]
  exact D.compiledData_eval U 0 _ _

theorem compiled_zQuad (z : OutWit m (D.polarRank - m) → ℤ) :
    (D.compiledData U).zQuad z = D.zQuad (D.outMap U z) := by
  have h1 := (D.compiledData U).two_zQuad_eq z
  have h2 := D.two_zQuad_eq (D.outMap U z)
  rw [D.compiled_evalZero U, D.compiled_evalZero U, D.compiled_evalZero U,
    D.outMap_zsmul, D.outMap_zsmul] at h1
  omega

theorem compiled_zPolar (z z' : OutWit m (D.polarRank - m) → ℤ) :
    (D.compiledData U).zPolar z z' = D.zPolar (D.outMap U z) (D.outMap U z') := by
  rw [zPolar_eq, zPolar_eq, D.compiled_zQuad, D.compiled_zQuad, D.compiled_zQuad, D.outMap_add]

/-! ### C3: the compiled form has zero radical -/

theorem compiled_intRadical_eq_zero (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    (hU : D.ExactWitnessCompiler U) {z : OutWit m (D.polarRank - m) → ℤ}
    (hz : ∀ z', (D.compiledData U).zPolar z z' = 0) : z = 0 := by
  classical
  -- `outMap z` is radical for `D`
  have hrad : D.InRadicalQ (toQ (D.outMap U z)) := by
    refine D.inRadicalQ_of_int fun x => ?_
    set s := U.symm (fun t => x (Sum.inr t)) with hs
    set y : OutWit m (D.polarRank - m) → ℤ :=
      Sum.elim (fun j => x (Sum.inl j)) (fun t => s (Sum.inl t))
    set ℓ : Fin r → ℤ := U (Sum.elim 0 (fun t => s (Sum.inr t)))
    have hℓ : D.InRadicalQ (toQ (Sum.elim (0 : Fin m → ℤ) ℓ)) := hU.1.1 _
    have hsplit : x = D.outMap U y + Sum.elim (0 : Fin m → ℤ) ℓ := by
      have hs' : (Sum.elim (fun t => s (Sum.inl t)) (0 : Fin (m + r - D.polarRank) → ℤ) :
            Fin (D.polarRank - m) ⊕ Fin (m + r - D.polarRank) → ℤ)
          + Sum.elim (0 : Fin (D.polarRank - m) → ℤ) (fun t => s (Sum.inr t)) = s := by
        funext q; rcases q with q | q <;> simp
      have hU' : U (Sum.elim (fun t => s (Sum.inl t)) 0) + ℓ = fun t => x (Sum.inr t) := by
        rw [← map_add, hs', hs, LinearEquiv.apply_symm_apply]
      funext q
      rcases q with j | t
      · simp [outMap, y]
      · have := congrFun hU' t
        simp only [Pi.add_apply] at this
        simp [outMap, y, this]
    rw [hsplit, toQ_add', D.zPolarQ_add_right, D.zPolarQ_toQ, ← D.compiled_zPolar, hz y,
      D.zPolarQ_symm, hℓ]
    simp
  -- its output block vanishes
  obtain ⟨z₀, hz₀⟩ := D.exists_solZ_of_defines hf 0
  have hout : ∀ j, z (Sum.inl j) = 0 := by
    intro j
    have h := D.outCoordQ_radicalQ_eq_zero hm (D.outputUnique_of_defines hf) hz₀ hQ hrad j
    simpa [toQ, outMap] using h
  -- so its witness block is a radical witness vector, hence zero
  set v : Fin (D.polarRank - m) → ℤ := fun t => z (Sum.inr t)
  have hL : U (Sum.elim v 0) ∈ D.witRadLattice := by
    rw [mem_witRadLattice]
    have hmap : D.outMap U z = Sum.elim (0 : Fin m → ℤ) (U (Sum.elim v 0)) := by
      funext q; rcases q with j | t
      · simp [outMap, hout j]
      · rfl
    rw [hmap] at hrad
    exact hrad
  obtain ⟨w, hw⟩ := hU.2 _ hL
  have hvw := U.injective hw
  have hv0 : v = 0 := by
    funext t
    have := congrFun hvw (Sum.inl t)
    simpa using this
  funext q
  rcases q with j | t
  · exact hout j
  · exact congrFun hv0 t

/-- **R41-C3, first half.**  The compiled form is nondegenerate over ℚ. -/
theorem compiledData_nondegQ (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    (hU : D.ExactWitnessCompiler U) : (D.compiledData U).NondegQ := by
  classical
  intro v hv
  by_contra hall
  simp only [not_exists, not_not] at hall
  obtain ⟨z, d, hd, hzv⟩ := exists_int_clear v
  have hd0 : ((d : ℚ)) ≠ 0 := by exact_mod_cast hd.ne'
  have htoQ : toQ z = (d : ℚ) • v := by funext k; simp [toQ, hzv k]
  have hz : ∀ z', (D.compiledData U).zPolar z z' = 0 := by
    intro z'
    have h := (D.compiledData U).zPolarQ_toQ z z'
    rw [htoQ, (D.compiledData U).zPolarQ_smul_left, hall, mul_zero] at h
    exact_mod_cast h.symm
  have h0 := D.compiled_intRadical_eq_zero U hm hf hQ hU hz
  apply hv
  funext k
  have := hzv k
  rw [h0] at this
  simp only [Pi.zero_apply, Int.cast_zero] at this
  exact (mul_eq_zero.mp this.symm).resolve_left hd0

/-- The compiled form has rank `d`: nothing was lost. -/
theorem compiledData_polarRank (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    (hU : D.ExactWitnessCompiler U) : (D.compiledData U).polarRank = D.polarRank := by
  have hnd := D.compiledData_nondegQ U hm hf hQ hU
  have hker : LinearMap.ker (D.compiledData U).polarMapQ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    by_contra hv0
    exact (D.compiledData U).not_inRadicalQ_of_nondegQ hnd hv0
      ((D.compiledData U).mem_ker_polarMapQ.mp hv)
  have h1 := LinearMap.finrank_range_add_finrank_ker (D.compiledData U).polarMapQ
  rw [hker, finrank_bot, finrank_outWit] at h1
  have hle := D.m_le_polarRank hm hf hQ
  unfold polarRank at h1 ⊢
  unfold polarRank at hle
  omega

/-- **R41-C3, second half.**  A semidefinite form compiles to a positive definite one. -/
theorem compiledData_posDef (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    (hU : D.ExactWitnessCompiler U) (hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) :
    ∀ u : OutWit m (D.polarRank - m) → ℚ, u ≠ 0 → 0 < (D.compiledData U).zQuadQ u := by
  classical
  have hsemi : ∀ u : OutWit m (D.polarRank - m) → ℚ, 0 ≤ (D.compiledData U).zQuadQ u := by
    intro u
    obtain ⟨z, d, hd, hzu⟩ := exists_int_clear u
    have hd0 : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
    have htoQ : toQ z = (d : ℚ) • u := by funext k; simp [toQ, hzu k]
    have h := (D.compiledData U).zQuadQ_toQ z
    rw [htoQ, (D.compiledData U).zQuadQ_smul, D.compiled_zQuad, ← D.zQuadQ_toQ] at h
    have hge := hpos (toQ (D.outMap U z))
    rw [← h] at hge
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp hge
  have hnd := D.compiledData_nondegQ U hm hf hQ hU
  intro u hu
  refine lt_of_le_of_ne (hsemi u) fun h => ?_
  exact (D.compiledData U).not_inRadicalQ_of_nondegQ hnd hu
    ((D.compiledData U).polar_eq_zero_of_zQuadQ_eq_zero hsemi h.symm)

/-- **The exact reduction, for one datum.**  A semidefinite, nonzero datum defining `f` compiles
to a POSITIVE DEFINITE datum with the same inputs and outputs, `d − m` witnesses, the same polar
rank `d`, which defines the same `f`. -/
theorem definite_reduction (hm : 0 < m) {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (hf : D.Defines f) (hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0)
    (hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u) :
    ∃ U, D.ExactWitnessCompiler U ∧ (D.compiledData U).Defines f ∧
      (D.compiledData U).polarRank = D.polarRank ∧
      ∀ u : OutWit m (D.polarRank - m) → ℚ, u ≠ 0 → 0 < (D.compiledData U).zQuadQ u := by
  obtain ⟨U, hU⟩ := D.exists_exactWitnessCompiler hm hf hQ
  exact ⟨U, hU, D.compiledData_defines U hU.1 hf, D.compiledData_polarRank U hm hf hQ hU,
    D.compiledData_posDef U hm hf hQ hU hpos⟩

end QuadraticGraphData

/-- **R41-C3.**  PROVED: the semidefinite residue and the definite residue are EQUIVALENT.
Neither side is proved; the definite NF remains OPEN. -/
theorem semidefiniteWeakNF_iff_definiteWeakNF : SemidefiniteWeakNF ↔ DefiniteWeakNF := by
  constructor
  · intro H n m r D f hm hdef hf
    have hQ : ∃ v : OutWit m r → ℤ, D.zQuad v ≠ 0 := by
      let v : OutWit m r → ℤ := Sum.elim (fun _ => 1) 0
      refine ⟨v, fun h0 => ?_⟩
      have hv : toQ v ≠ 0 := by
        intro h
        have := congrFun h (Sum.inl ⟨0, hm⟩)
        simp [toQ, v] at this
      have := hdef (toQ v) hv
      rw [D.zQuadQ_toQ, h0] at this
      simp at this
    have hpos : ∀ u : OutWit m r → ℚ, 0 ≤ D.zQuadQ u := by
      intro u
      by_cases hu : u = 0
      · subst hu
        have := D.zQuadQ_smul 0 0
        simp at this
        simp [this]
      · exact (hdef u hu).le
    exact H n m r D f hm hQ hpos hf
  · intro H n m r D f hm hQ hpos hf
    obtain ⟨U, -, hdef', -, hposdef⟩ := D.definite_reduction hm hf hQ hpos
    exact H n m (D.polarRank - m) (D.compiledData U) f hm hposdef hdef'

/-- **R41-C3 with r41.**  The general weak vector normal form is EXACTLY the positive definite
one.  PROVED as an equivalence; `DefiniteWeakNF` itself is OPEN. -/
theorem generalWeakNF_iff_definiteWeakNF : GeneralWeakNF ↔ DefiniteWeakNF :=
  generalWeakNF_iff_semidefiniteWeakNF.trans semidefiniteWeakNF_iff_definiteWeakNF

/-! ### The control, compiled -/

namespace RankExcessControl

open QuadraticGraphData

theorem exD_semidefinite : ∀ u : OutWit 1 2 → ℚ, 0 ≤ exD.zQuadQ u := by
  intro u
  have h := exD.zQuadQ_add u u
  have h2 : exD.zQuadQ (u + u) = 4 * exD.zQuadQ u := by
    have : u + u = (2 : ℚ) • u := by funext k; simp; ring
    rw [this, exD.zQuadQ_smul]; norm_num
  rw [h2, exD_zPolarQ] at h
  nlinarith [sq_nonneg (u (Sum.inl 0)), sq_nonneg (u (Sum.inr 0) + u (Sum.inr 1))]

/-- The control compiles to a positive definite datum with one output and one witness. -/
theorem exD_definite_reduction :
    ∃ U, exD.ExactWitnessCompiler U ∧ (exD.compiledData U).Defines id ∧
      (exD.compiledData U).polarRank = 2 ∧
      ∀ u : OutWit 1 (exD.polarRank - 1) → ℚ, u ≠ 0 → 0 < (exD.compiledData U).zQuadQ u := by
  obtain ⟨U, hU, hD, hr, hp⟩ :=
    exD.definite_reduction Nat.one_pos exD_defines exD_zQuad_ne_zero exD_semidefinite
  exact ⟨U, hU, hD, hr.trans exD_polarRank, hp⟩

end RankExcessControl

end DiophCompression.ResearchUpgrade
