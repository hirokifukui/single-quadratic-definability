/-
  SaturatedExtension.lean — s53.  R41-C1 as a standalone statement, for an ARBITRARY rational
  subspace K ⊆ ℚʳ (the radical case is inside RankExcessCompiler.lean).

  * `intPart K` = K ∩ ℤʳ; `intPart_saturated`.
  * `finrank_intPart`: rank_ℤ (K ∩ ℤʳ) = dim_ℚ K (ℤ→ℚ by hand with `exists_int_clear`).
  * `exists_unimodular_extension`: an integer linear equivalence
    U : ℤ^(r − dim K) × ℤ^(dim K) ≃ ℤʳ whose second block is EXACTLY K ∩ ℤʳ — a basis of the
    lattice extended to a basis of ℤʳ.  Clearing denominators of a rational basis would give a
    finite-index sublattice, not this.
  * Boundaries: `intPart_bot` (K = 0: L = 0, rank 0), `intPart_top` (K = ℚʳ: L = ℤʳ, rank r).

  mathlib: Submodule.smithNormalForm, Module.Basis.{reindex, equivFun, repr_self, sum_repr},
  Module.finrank_eq_card_basis, LinearMap.finrank_range_of_inj — checked against the working-zone
  mathlib (d46bd45, `git -C ~/lean/mathlib-latest rev-parse HEAD`).

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.SaturatedLattice
import ResearchUpgrade.RadicalBridge

namespace DiophCompression.ResearchUpgrade
namespace SaturatedLattice

variable {r : ℕ}

/-- `L = K ∩ ℤʳ` for a rational subspace `K`. -/
def intPart (K : Submodule ℚ (Fin r → ℚ)) : Submodule ℤ (Fin r → ℤ) where
  carrier := {u | (fun i => (u i : ℚ)) ∈ K}
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq] at *
    have : (fun i => ((u + v) i : ℚ)) = (fun i => (u i : ℚ)) + (fun i => (v i : ℚ)) := by
      funext i; simp
    rw [this]; exact K.add_mem hu hv
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have : (fun i => ((0 : Fin r → ℤ) i : ℚ)) = 0 := by funext i; simp
    rw [this]; exact K.zero_mem
  smul_mem' := by
    intro c u hu
    simp only [Set.mem_setOf_eq] at *
    have : (fun i => ((c • u) i : ℚ)) = (c : ℚ) • (fun i => (u i : ℚ)) := by
      funext i; simp
    rw [this]; exact K.smul_mem _ hu

/-- The rational image of an integer vector. -/
def latticeQ (u : Fin r → ℤ) : Fin r → ℚ := fun i => (u i : ℚ)

theorem mem_intPart {K : Submodule ℚ (Fin r → ℚ)} {u : Fin r → ℤ} :
    u ∈ intPart K ↔ latticeQ u ∈ K := Iff.rfl

theorem latticeQ_injective : Function.Injective (latticeQ (r := r)) := by
  intro u v h; funext i
  have hi := congrFun h i
  simp only [latticeQ] at hi
  exact_mod_cast hi

theorem latticeQ_zsmul (c : ℤ) (u : Fin r → ℤ) : latticeQ (c • u) = (c : ℚ) • latticeQ u := by
  funext i; simp [latticeQ]

theorem latticeQ_sum {k : ℕ} (c : Fin k → ℤ) (v : Fin k → Fin r → ℤ) :
    latticeQ (∑ i, c i • v i) = ∑ i, (c i : ℚ) • latticeQ (v i) := by
  funext t; simp [latticeQ, Finset.sum_apply]

theorem intPart_saturated (K : Submodule ℚ (Fin r → ℚ)) : Saturated (intPart K) := by
  intro c u hc hu
  rw [mem_intPart, latticeQ_zsmul] at hu
  exact (K.smul_mem_iff (by exact_mod_cast hc)).mp hu

section SNF

variable {N : Submodule ℤ (Fin r → ℤ)} {k : ℕ} (S : Module.Basis.SmithNormalForm N (Fin r) k)

theorem snf_mem_of_saturated (hsat : Saturated N) (i : Fin k) : S.bM (S.f i) ∈ N := by
  have ha0 : S.a i ≠ 0 := by
    intro h
    have hb := S.snf i
    rw [h, zero_smul] at hb
    exact S.bN.ne_zero i (Submodule.coe_eq_zero.mp hb)
  refine hsat (S.a i) _ ha0 ?_
  rw [← S.snf i]
  exact (S.bN i).2

theorem snf_span_of {u : Fin r → ℤ} (hu : u ∈ N) :
    ∃ c : Fin k → ℤ, u = ∑ i, c i • S.bM (S.f i) := by
  set y : ↥N := ⟨u, hu⟩
  refine ⟨fun j => S.bN.repr y j * S.a j, ?_⟩
  have h := S.bN.sum_repr y
  have h2 := congrArg N.subtype h
  simp only [map_sum, map_smul, Submodule.subtype_apply] at h2
  exact h2.symm.trans (Finset.sum_congr rfl fun j _ => by rw [S.snf j, smul_smul])

/-- The rational span map of the Smith generators. -/
noncomputable def spanQ : (Fin k → ℚ) →ₗ[ℚ] (Fin r → ℚ) where
  toFun c := ∑ i, c i • latticeQ (S.bM (S.f i))
  map_add' c c' := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' t c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

theorem spanQ_injective : Function.Injective (spanQ S) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  obtain ⟨w, d, hd, hw⟩ := exists_int_clear c
  have hsum : latticeQ (∑ i, w i • S.bM (S.f i)) = 0 := by
    rw [latticeQ_sum]
    have : (∑ i, (w i : ℚ) • latticeQ (S.bM (S.f i))) = (d : ℚ) • spanQ S c := by
      simp only [spanQ, LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum, smul_smul, hw]
    rw [this, hc, smul_zero]
  have h0 : (∑ i, w i • S.bM (S.f i)) = 0 := by
    apply latticeQ_injective
    rw [hsum]; funext t; simp [latticeQ]
  have hli : LinearIndependent ℤ (S.bM ∘ S.f) := S.bM.linearIndependent.comp S.f S.f.injective
  have hw0 := Fintype.linearIndependent_iff.mp hli w (by simpa using h0)
  funext i
  have := hw i
  rw [hw0 i] at this
  have hd0 : ((d : ℚ)) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Int.cast_zero] at this
  exact (mul_eq_zero.mp this.symm).resolve_left hd0

end SNF

theorem range_spanQ (K : Submodule ℚ (Fin r → ℚ)) {k : ℕ}
    (S : Module.Basis.SmithNormalForm (intPart K) (Fin r) k) :
    LinearMap.range (spanQ S) = K := by
  classical
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    show (∑ i, c i • latticeQ (S.bM (S.f i))) ∈ K
    exact K.sum_mem fun i _ => K.smul_mem _
      (mem_intPart.mp (snf_mem_of_saturated S (intPart_saturated K) i))
  · intro x hx
    obtain ⟨w, d, hd, hw⟩ := exists_int_clear x
    have hwx : latticeQ w = (d : ℚ) • x := by funext t; simp [latticeQ, hw t]
    have hu : w ∈ intPart K := by rw [mem_intPart, hwx]; exact K.smul_mem _ hx
    obtain ⟨c, hc⟩ := snf_span_of S hu
    have hd0 : ((d : ℚ)) ≠ 0 := by exact_mod_cast hd.ne'
    refine ⟨(d : ℚ)⁻¹ • (fun i => (c i : ℚ)), ?_⟩
    have hφ : spanQ S (fun i => (c i : ℚ)) = (d : ℚ) • x := by
      rw [← hwx, hc, latticeQ_sum]; rfl
    rw [map_smul, hφ, smul_smul, inv_mul_cancel₀ hd0, one_smul]

theorem snfRank_eq (K : Submodule ℚ (Fin r → ℚ)) {k : ℕ}
    (S : Module.Basis.SmithNormalForm (intPart K) (Fin r) k) :
    k = Module.finrank ℚ K := by
  have h := LinearMap.finrank_range_of_inj (spanQ_injective S)
  rw [range_spanQ K S] at h
  simpa using h.symm

/-- `rank_ℤ L = dim_ℚ K`. -/
theorem finrank_intPart (K : Submodule ℚ (Fin r → ℚ)) :
    Module.finrank ℤ (intPart K) = Module.finrank ℚ K := by
  obtain ⟨k, S⟩ := (intPart K).smithNormalForm (Pi.basisFun ℤ (Fin r))
  rw [Module.finrank_eq_card_basis S.bN, Fintype.card_fin]
  exact snfRank_eq K S

/-- **R41-C1.**  An integer linear equivalence of `ℤʳ` whose second block is exactly `L`. -/
theorem exists_unimodular_extension (K : Submodule ℚ (Fin r → ℚ)) :
    ∃ U : ((Fin (r - Module.finrank ℚ K) ⊕ Fin (Module.finrank ℚ K)) → ℤ) ≃ₗ[ℤ] (Fin r → ℤ),
      (∀ w, U (Sum.elim 0 w) ∈ intPart K) ∧ (∀ u ∈ intPart K, ∃ w, u = U (Sum.elim 0 w)) := by
  classical
  obtain ⟨k, S⟩ := (intPart K).smithNormalForm (Pi.basisFun ℤ (Fin r))
  have hk := snfRank_eq K S
  have hsat := intPart_saturated K
  let p : Fin r → Prop := fun i => i ∈ Set.range S.f
  let eW₀ : {i // p i} ≃ Fin k := (Equiv.ofInjective S.f S.f.injective).symm
  let eW : {i // p i} ≃ Fin (Module.finrank ℚ K) := eW₀.trans (finCongr hk)
  have hcardK : Fintype.card {i // ¬ p i} = r - Module.finrank ℚ K := by
    rw [Fintype.card_subtype_compl, Fintype.card_congr eW₀, Fintype.card_fin, Fintype.card_fin, hk]
  let eK : {i // ¬ p i} ≃ Fin (r - Module.finrank ℚ K) := Fintype.equivFinOfCardEq hcardK
  let e : Fin r ≃ (Fin (r - Module.finrank ℚ K) ⊕ Fin (Module.finrank ℚ K)) :=
    (Equiv.sumCompl p).symm.trans ((Equiv.sumComm _ _).trans (Equiv.sumCongr eK eW))
  have he : ∀ t, p (e.symm (Sum.inr t)) := by
    intro t
    have : e.symm (Sum.inr t) = ((eW.symm t : {i // p i}) : Fin r) := by
      simp [e, Equiv.sumCompl_apply_inl]
    rw [this]; exact (eW.symm t).2
  have heK : ∀ s, ¬ p (e.symm (Sum.inl s)) := by
    intro s
    have : e.symm (Sum.inl s) = ((eK.symm s : {i // ¬ p i}) : Fin r) := by
      simp [e, Equiv.sumCompl_apply_inr]
    rw [this]; exact (eK.symm s).2
  let U := (S.bM.reindex e).equivFun.symm
  refine ⟨U, fun w => ?_, fun u hu => ?_⟩
  · rw [Module.Basis.equivFun_symm_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    rcases j with j | t
    · simp
    · refine Submodule.smul_mem _ _ ?_
      rw [Module.Basis.reindex_apply]
      obtain ⟨i, hi⟩ := he t
      rw [← hi]
      exact snf_mem_of_saturated S hsat i
  · obtain ⟨c, hc⟩ := snf_span_of S hu
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
      · intro h; exact heK s ⟨i, h⟩
    refine ⟨fun t => x (Sum.inr t), ?_⟩
    have hxe : (Sum.elim 0 (fun t => x (Sum.inr t)) :
        Fin (r - Module.finrank ℚ K) ⊕ Fin (Module.finrank ℚ K) → ℤ) = x := by
      funext y; rcases y with s | t
      · simp [hx0 s]
      · rfl
    rw [hxe, hxdef, LinearEquiv.apply_symm_apply]

/-- Boundary `K = 0`: `L = 0`, rank `0`. -/
theorem intPart_bot : intPart (⊥ : Submodule ℚ (Fin r → ℚ)) = ⊥ ∧
    Module.finrank ℚ (⊥ : Submodule ℚ (Fin r → ℚ)) = 0 := by
  refine ⟨?_, finrank_bot ℚ _⟩
  ext u
  rw [mem_intPart, Submodule.mem_bot, Submodule.mem_bot]
  constructor
  · intro h; apply latticeQ_injective; rw [h]; funext i; simp [latticeQ]
  · rintro rfl; funext i; simp [latticeQ]

/-- Boundary `K = ℚʳ`: `L = ℤʳ`, rank `r`. -/
theorem intPart_top : intPart (⊤ : Submodule ℚ (Fin r → ℚ)) = ⊤ ∧
    Module.finrank ℚ (⊤ : Submodule ℚ (Fin r → ℚ)) = r := by
  refine ⟨?_, ?_⟩
  · ext u; simp [mem_intPart]
  · rw [finrank_top]; simp

end SaturatedLattice
end DiophCompression.ResearchUpgrade
