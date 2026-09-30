/-
  RadicalDecomposition.lean — r11 (GPT r10 必須E + 必須F.4): integral block decomposition of a
  singular symmetric Gram matrix, and the unimodular completion of a primitive affine direction.
  Statements frozen in RadicalDecomposition_STATEMENTS.lean (md5 97120d2f) and
  RadicalAffine_STATEMENTS.lean (md5 24b913ab, T4) before proofs.
  Proof production: Claude Code job s11_raddecomp (2026-08-28), independently re-verified by
  claude.ai (kernel EXIT=0, all six theorems std-3, statements verbatim vs freeze).
  Route: SNF-free — saturation of integer kernels, torsion-free quotient over the PID ℤ gives a
  projective splitting (complement), basis concatenation gives the unimodular congruence U with
  trailing kernel columns; nondegeneracy of the leading block by contradiction inside ℤ; the
  affine completion is the unimodular inverse of a section matrix built from a Bezout vector.
-/
import DiophCompression.SemanticQuadraticMatrix.FullRankGeneric
import DiophCompression.SemanticQuadraticSingular.RadicalAffine

namespace DiophCompression.SemanticQuadraticSingular
open Matrix
variable {r : ℕ}

theorem integer_kernel_is_saturated (G : Matrix (Fin r) (Fin r) ℤ) (k : ℤ) (hk : k ≠ 0)
    (v : Fin r → ℤ) (h : G *ᵥ (k • v) = 0) : G *ᵥ v = 0 := by
  have h2 : k • (G *ᵥ v) = 0 := by rw [← Matrix.mulVec_smul]; exact h
  funext i
  have := congrFun h2 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  rcases mul_eq_zero.mp this with hk' | hv
  · exact absurd hk' hk
  · exact hv

theorem kernel_has_integral_basis (G : Matrix (Fin r) (Fin r) ℤ) :
    ∃ s : ℕ, Nonempty (Module.Basis (Fin s) ℤ (LinearMap.ker G.mulVecLin)) := by
  classical
  let b := Module.Free.chooseBasis ℤ (LinearMap.ker G.mulVecLin)
  let e := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (LinearMap.ker G.mulVecLin))
  exact ⟨_, ⟨b.reindex e⟩⟩

theorem saturated_submodule_has_complement (N : Submodule ℤ (Fin r → ℤ))
    (hsat : ∀ (k : ℤ) (v : Fin r → ℤ), k ≠ 0 → k • v ∈ N → v ∈ N) :
    ∃ C : Submodule ℤ (Fin r → ℤ), IsCompl N C := by
  classical
  haveI hfin : Module.Finite ℤ ((Fin r → ℤ) ⧸ N) :=
    Module.Finite.of_surjective N.mkQ N.mkQ_surjective
  haveI htf : Module.IsTorsionFree ℤ ((Fin r → ℤ) ⧸ N) := by
    constructor
    intro a ha
    rw [isRegular_iff_ne_zero] at ha
    intro x y hxy
    obtain ⟨v, rfl⟩ := N.mkQ_surjective x
    obtain ⟨w, rfl⟩ := N.mkQ_surjective y
    simp only at hxy
    rw [← map_smul, ← map_smul, N.mkQ_apply, N.mkQ_apply, Submodule.Quotient.eq] at hxy
    have hmem : a • (v - w) ∈ N := by rw [smul_sub]; exact hxy
    have hvw := hsat a (v - w) ha hmem
    rw [N.mkQ_apply, N.mkQ_apply, Submodule.Quotient.eq]
    exact hvw
  haveI hp : Module.Projective ℤ ((Fin r → ℤ) ⧸ N) := inferInstance
  obtain ⟨σ, hσ⟩ := @LinearMap.exists_rightInverse_of_surjective ℤ _ ((Fin r → ℤ) ⧸ N)
    _ _ _ _ _ hp N.mkQ (Submodule.range_mkQ N)
  refine ⟨LinearMap.range σ, ?_⟩
  have hsplit : ∀ q, N.mkQ (σ q) = q := fun q => LinearMap.congr_fun hσ q
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxN hxC
    obtain ⟨q, rfl⟩ := hxC
    have h1 : N.mkQ (σ q) = 0 := by
      rw [N.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hxN
    rw [hsplit q] at h1
    rw [h1, map_zero]
  · rw [codisjoint_iff_le_sup]
    intro x _
    have hx : x = (x - σ (N.mkQ x)) + σ (N.mkQ x) := by abel
    rw [hx]
    apply Submodule.add_mem_sup
    · apply (Submodule.Quotient.mk_eq_zero N).mp
      rw [← N.mkQ_apply, map_sub, hsplit, sub_self]
    · exact ⟨N.mkQ x, rfl⟩

private theorem sum_extend {k : ℕ} (hk : k ≤ r) (F : Fin r → ℤ) (v : Fin k → ℤ) :
    ∑ j : Fin r, F j * (if h : (j:ℕ) < k then v ⟨j, h⟩ else 0)
      = ∑ b : Fin k, F (Fin.castLE hk b) * v b := by
  have hf : ∀ x ∈ (Finset.univ : Finset (Fin r)),
      x ∉ Finset.univ.map (Fin.castLEEmb hk) →
      F x * (if h : (x:ℕ) < k then v ⟨x, h⟩ else 0) = 0 := by
    intro x _ hx
    have hjk : ¬ (x:ℕ) < k := by
      intro hlt; apply hx
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Fin.castLEEmb_apply]
      exact ⟨⟨x, hlt⟩, by ext; simp [Fin.castLE]⟩
    simp [hjk]
  rw [show (∑ j : Fin r, F j * (if h : (j:ℕ) < k then v ⟨j, h⟩ else 0))
        = ∑ j ∈ Finset.univ.map (Fin.castLEEmb hk),
            F j * (if h : (j:ℕ) < k then v ⟨j, h⟩ else 0)
      from (Finset.sum_subset (Finset.subset_univ _) hf).symm]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Fin.castLEEmb_apply]
  have hx : ((Fin.castLE hk x : Fin r) : ℕ) < k := by simp [x.isLt]
  rw [dif_pos hx]
  have hxx : (⟨(Fin.castLE hk x : Fin r), hx⟩ : Fin k) = x := by ext; simp
  rw [hxx]

open Module in
private theorem blockData (G : Matrix (Fin r) (Fin r) ℤ) :
    ∃ (k : ℕ) (_ : k ≤ r) (U : Matrix (Fin r) (Fin r) ℤ)
      (C : Submodule ℤ (Fin r → ℤ)),
      IsUnit U.det ∧
      IsCompl (LinearMap.ker G.mulVecLin) C ∧
      (∀ j : Fin r, k ≤ (j:ℕ) → (fun i => U i j) ∈ LinearMap.ker G.mulVecLin) ∧
      (∀ j : Fin r, (j:ℕ) < k → (fun i => U i j) ∈ C) := by
  classical
  set N := LinearMap.ker G.mulVecLin with hNdef
  have hsat : ∀ (c : ℤ) (v : Fin r → ℤ), c ≠ 0 → c • v ∈ N → v ∈ N := by
    intro c v hc hcv
    rw [hNdef, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hcv ⊢
    exact integer_kernel_is_saturated G c hc v hcv
  obtain ⟨C, hNC⟩ := saturated_submodule_has_complement N hsat
  obtain ⟨s, ⟨bN'⟩⟩ : ∃ s, Nonempty (Basis (Fin s) ℤ N) :=
    ⟨_, ⟨(Module.Free.chooseBasis ℤ N).reindex (Fintype.equivFin _)⟩⟩
  obtain ⟨k, ⟨bC'⟩⟩ : ∃ k, Nonempty (Basis (Fin k) ℤ C) :=
    ⟨_, ⟨(Module.Free.chooseBasis ℤ C).reindex (Fintype.equivFin _)⟩⟩
  let hCN : IsCompl C N := hNC.symm
  let eqv := Submodule.prodEquivOfIsCompl C N hCN
  let b0 : Basis (Fin k ⊕ Fin s) ℤ (Fin r → ℤ) := (bC'.prod bN').map eqv
  have hks : k + s = r := by
    have e1 : Module.finrank ℤ (Fin r → ℤ) = k + s := by
      rw [Module.finrank_eq_card_basis b0]; simp [Fintype.card_sum]
    have e2 : Module.finrank ℤ (Fin r → ℤ) = r := by
      rw [Module.finrank_pi, Fintype.card_fin]
    omega
  let e : (Fin k ⊕ Fin s) ≃ Fin r := finSumFinEquiv.trans (finCongr hks)
  have heval_inl : ∀ a : Fin k, ((e (Sum.inl a) : Fin r) : ℕ) = (a:ℕ) := by
    intro a; simp [e, finSumFinEquiv_apply_left]
  have heval_inr : ∀ t : Fin s, ((e (Sum.inr t) : Fin r) : ℕ) = k + (t:ℕ) := by
    intro t; simp [e, finSumFinEquiv_apply_right]
  let b' : Basis (Fin r) ℤ (Fin r → ℤ) := b0.reindex e
  let U : Matrix (Fin r) (Fin r) ℤ := (Pi.basisFun ℤ (Fin r)).toMatrix b'
  have hUcol : ∀ (i j : Fin r), U i j = b' j i := by
    intro i j
    simp only [U, Basis.toMatrix_apply, Pi.basisFun_repr]
  have hb0inr : ∀ t : Fin s, (b0 (Sum.inr t) : Fin r → ℤ) = ((bN' t : Fin r → ℤ)) := by
    intro t
    simp only [b0, eqv, Basis.map_apply, Basis.prod_apply, Sum.elim_inr, Function.comp_apply,
      LinearMap.inr_apply, Submodule.coe_prodEquivOfIsCompl']; simp
  have hb0inl : ∀ a : Fin k, (b0 (Sum.inl a) : Fin r → ℤ) = ((bC' a : Fin r → ℤ)) := by
    intro a
    simp only [b0, eqv, Basis.map_apply, Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
      LinearMap.inl_apply, Submodule.coe_prodEquivOfIsCompl']; simp
  refine ⟨k, hks ▸ Nat.le_add_right k s, U, C, ?_, hNC, ?_, ?_⟩
  · haveI := (Pi.basisFun ℤ (Fin r)).invertibleToMatrix b'
    exact Matrix.isUnit_det_of_invertible _
  · intro j hj
    have hcoleq : (fun i => U i j) = b' j := funext (fun i => hUcol i j)
    rw [hcoleq]
    show b' j ∈ N
    rw [show b' j = b0 (e.symm j) from Basis.reindex_apply b0 e j]
    rcases he : e.symm j with a | t
    · exfalso
      have hj2 : j = e (Sum.inl a) := by rw [← he, e.apply_symm_apply]
      have hval : (j:ℕ) = (a:ℕ) := by rw [hj2]; exact heval_inl a
      have := a.isLt; omega
    · have := hb0inr t
      rw [this]
      exact Submodule.coe_mem (bN' t)
  · intro j hj
    have hcoleq : (fun i => U i j) = b' j := funext (fun i => hUcol i j)
    rw [hcoleq]
    show b' j ∈ C
    rw [show b' j = b0 (e.symm j) from Basis.reindex_apply b0 e j]
    rcases he : e.symm j with a | t
    · have := hb0inl a
      rw [this]
      exact Submodule.coe_mem (bC' a)
    · exfalso
      have hj2 : j = e (Sum.inr t) := by rw [← he, e.apply_symm_apply]
      have hval : (j:ℕ) = k + (t:ℕ) := by rw [hj2]; exact heval_inr t
      omega

theorem singular_symmetric_congruent_block (G : Matrix (Fin r) (Fin r) ℤ) (hs : Gᵀ = G) :
    ∃ (k : ℕ) (_ : k ≤ r) (U : Matrix (Fin r) (Fin r) ℤ), IsUnit U.det ∧
      (∀ i j : Fin r, k ≤ (j : ℕ) → (Uᵀ * G * U) i j = 0) ∧
      (∀ i j : Fin r, k ≤ (i : ℕ) → (Uᵀ * G * U) i j = 0) := by
  obtain ⟨k, hk, U, C, hdet, hcompl, hColN, hColC⟩ := blockData G
  have hzero_j : ∀ i j : Fin r, k ≤ (j:ℕ) → (Uᵀ * G * U) i j = 0 := by
    intro i j hj
    have hcol0 : G *ᵥ (fun i => U i j) = 0 := by
      rw [← Matrix.mulVecLin_apply]; exact LinearMap.mem_ker.mp (hColN j hj)
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    have h1 : (G * U) a j = (G *ᵥ (fun b => U b j)) a := rfl
    have hGU : (G * U) a j = 0 := by rw [h1, hcol0]; rfl
    rw [hGU, mul_zero]
  have hsymm : (Uᵀ * G * U)ᵀ = Uᵀ * G * U := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hs,
      ← Matrix.mul_assoc]
  refine ⟨k, hk, U, hdet, hzero_j, ?_⟩
  intro i j hi
  have h2 := congrFun (congrFun hsymm i) j
  rw [Matrix.transpose_apply] at h2
  rw [← h2]
  exact hzero_j j i hi

theorem nondegenerate_quotient_block (G : Matrix (Fin r) (Fin r) ℤ) (hs : Gᵀ = G) :
    ∃ (k : ℕ) (hk : k ≤ r) (U : Matrix (Fin r) (Fin r) ℤ), IsUnit U.det ∧
      (∀ i j : Fin r, k ≤ (j : ℕ) → (Uᵀ * G * U) i j = 0) ∧
      (∀ i j : Fin r, k ≤ (i : ℕ) → (Uᵀ * G * U) i j = 0) ∧
      ((Uᵀ * G * U).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
  obtain ⟨k, hk, U, C, hdet, hcompl, hColN, hColC⟩ := blockData G
  have hzero_j : ∀ i j : Fin r, k ≤ (j:ℕ) → (Uᵀ * G * U) i j = 0 := by
    intro i j hj
    have hcol0 : G *ᵥ (fun i => U i j) = 0 := by
      rw [← Matrix.mulVecLin_apply]; exact LinearMap.mem_ker.mp (hColN j hj)
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    have h1 : (G * U) a j = (G *ᵥ (fun b => U b j)) a := rfl
    have hGU : (G * U) a j = 0 := by rw [h1, hcol0]; rfl
    rw [hGU, mul_zero]
  have hsymm : (Uᵀ * G * U)ᵀ = Uᵀ * G * U := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hs,
      ← Matrix.mul_assoc]
  have hzero_i : ∀ i j : Fin r, k ≤ (i:ℕ) → (Uᵀ * G * U) i j = 0 := by
    intro i j hi
    have h2 := congrFun (congrFun hsymm i) j
    rw [Matrix.transpose_apply] at h2
    rw [← h2]; exact hzero_j j i hi
  refine ⟨k, hk, U, hdet, hzero_j, hzero_i, ?_⟩
  intro hdet0
  obtain ⟨v, hv_ne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  set ve : Fin r → ℤ := fun j => if h : (j:ℕ) < k then v ⟨j, h⟩ else 0 with hve_def
  have hUdet0 : U.det ≠ 0 := hdet.ne_zero
  have hve_cast : ∀ a : Fin k, ve (Fin.castLE hk a) = v a := by
    intro a
    have hlt : ((Fin.castLE hk a : Fin r) : ℕ) < k := by simp [a.isLt]
    simp [hve_def, dif_pos hlt]
  have hM2ve : (Uᵀ * G * U) *ᵥ ve = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    by_cases hik : (i:ℕ) < k
    · have hcast : Fin.castLE hk ⟨(i:ℕ), hik⟩ = i := by ext; simp
      rw [show (∑ j, (Uᵀ * G * U) i j * ve j)
            = ∑ b : Fin k, (Uᵀ * G * U) i (Fin.castLE hk b) * v b
          from sum_extend hk (fun j => (Uᵀ * G * U) i j) v]
      have : (∑ b : Fin k, (Uᵀ * G * U) i (Fin.castLE hk b) * v b)
          = ((Uᵀ * G * U).submatrix (Fin.castLE hk) (Fin.castLE hk) *ᵥ v) ⟨(i:ℕ), hik⟩ := by
        simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, hcast]
      rw [this, hv0]; rfl
    · apply Finset.sum_eq_zero
      intro j _
      rw [hzero_i i j (not_lt.mp hik), zero_mul]
  have hvhat_ker : G *ᵥ (U *ᵥ ve) = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero (M := Uᵀ) (by rw [Matrix.det_transpose]; exact hUdet0)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact hM2ve
  have hvhat_C : (U *ᵥ ve) ∈ C := by
    rw [show (U *ᵥ ve) = ∑ j, ve j • (fun i => U i j)
        from by funext i; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]]
    apply Submodule.sum_mem
    intro j _
    by_cases hjk : (j:ℕ) < k
    · exact Submodule.smul_mem _ _ (hColC j hjk)
    · have : ve j = 0 := by simp [hve_def, hjk]
      rw [this, zero_smul]; exact Submodule.zero_mem _
  have hvhat0 : U *ᵥ ve = 0 := by
    have hmemN : (U *ᵥ ve) ∈ LinearMap.ker G.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hvhat_ker
    exact (Submodule.disjoint_def.mp hcompl.disjoint) _ hmemN hvhat_C
  have hve0 : ve = 0 := Matrix.eq_zero_of_mulVec_eq_zero hUdet0 hvhat0
  apply hv_ne
  funext a
  have := congrFun hve0 (Fin.castLE hk a)
  rw [hve_cast a] at this
  simpa using this

open Module in
theorem affine_direction_unimodular_completion {s : ℕ} (hs : 0 < s) (lam : Fin s → ℤ)
    (hprim : Finset.univ.gcd lam = 1) :
    ∃ V : Matrix (Fin s) (Fin s) ℤ, IsUnit V.det ∧
      ∀ w : Fin s → ℤ, (V *ᵥ w) ⟨0, hs⟩ = lam ⬝ᵥ w := by
  classical
  obtain ⟨w0, hw0sum⟩ := exists_sum_eq_finset_gcd lam
  have hw0 : lam ⬝ᵥ w0 = 1 := by show (∑ i, lam i * w0 i) = 1; rw [hw0sum, hprim]
  let φ : (Fin s → ℤ) →ₗ[ℤ] ℤ :=
    { toFun := fun w => lam ⬝ᵥ w
      map_add' := fun a b => dotProduct_add lam a b
      map_smul' := fun c w => by simp only [RingHom.id_apply]; exact dotProduct_smul c lam w }
  have hφ : ∀ w, φ w = lam ⬝ᵥ w := fun w => rfl
  set K := LinearMap.ker φ with hKdef
  have hmemK : ∀ w, w ∈ K ↔ lam ⬝ᵥ w = 0 := by
    intro w; rw [hKdef, LinearMap.mem_ker, hφ]
  have hli : LinearIndependent ℤ (fun _ : Fin 1 => w0) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h2 := congrArg (fun z => lam ⬝ᵥ z) hg
    simp only [Fin.sum_univ_one, dotProduct_smul, hw0, smul_eq_mul, mul_one,
      dotProduct_zero] at h2
    fin_cases i; exact h2
  have hPeq : Submodule.span ℤ (Set.range (fun _ : Fin 1 => w0)) = Submodule.span ℤ {w0} := by
    rw [Set.range_const]
  have hCompl : IsCompl (Submodule.span ℤ (Set.range (fun _ : Fin 1 => w0))) K := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxP hxK
      rw [hPeq] at hxP
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxP
      rw [hmemK, dotProduct_smul, hw0, smul_eq_mul, mul_one] at hxK
      rw [hxK, zero_smul]
    · rw [codisjoint_iff_le_sup]
      intro x _
      have hx : x = (lam ⬝ᵥ x) • w0 + (x - (lam ⬝ᵥ x) • w0) := by abel
      rw [hx]
      apply Submodule.add_mem_sup
      · rw [hPeq]; exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
      · rw [hmemK, dotProduct_sub, dotProduct_smul, hw0, smul_eq_mul, mul_one, sub_self]
  obtain ⟨t, ⟨bK⟩⟩ : ∃ t, Nonempty (Basis (Fin t) ℤ K) :=
    ⟨_, ⟨(Module.Free.chooseBasis ℤ K).reindex (Fintype.equivFin _)⟩⟩
  let bP := Basis.span hli
  let eqv := Submodule.prodEquivOfIsCompl _ K hCompl
  let b0 : Basis (Fin 1 ⊕ Fin t) ℤ (Fin s → ℤ) := (bP.prod bK).map eqv
  have h1t : 1 + t = s := by
    have e1 : Module.finrank ℤ (Fin s → ℤ) = 1 + t := by
      rw [Module.finrank_eq_card_basis b0]; simp [Fintype.card_sum]
    have e2 : Module.finrank ℤ (Fin s → ℤ) = s := by rw [Module.finrank_pi, Fintype.card_fin]
    omega
  let e : (Fin 1 ⊕ Fin t) ≃ Fin s := finSumFinEquiv.trans (finCongr h1t)
  have heval_inl : ∀ a : Fin 1, ((e (Sum.inl a) : Fin s) : ℕ) = (a:ℕ) := by
    intro a; simp [e, finSumFinEquiv_apply_left]
  let b' : Basis (Fin s) ℤ (Fin s → ℤ) := b0.reindex e
  let W : Matrix (Fin s) (Fin s) ℤ := (Pi.basisFun ℤ (Fin s)).toMatrix b'
  have hWcol : ∀ (i j : Fin s), W i j = b' j i := by
    intro i j; simp only [W, Basis.toMatrix_apply, Pi.basisFun_repr]
  have hWdet : IsUnit W.det := by
    haveI := (Pi.basisFun ℤ (Fin s)).invertibleToMatrix b'
    exact Matrix.isUnit_det_of_invertible _
  have hb0inl : (b0 (Sum.inl 0) : Fin s → ℤ) = w0 := by
    simp only [b0, eqv, Basis.map_apply, Basis.prod_apply, Sum.elim_inl,
      Function.comp_apply, LinearMap.inl_apply, Submodule.coe_prodEquivOfIsCompl', bP,
      Basis.span_apply]
    simp
  have hb0inr : ∀ u : Fin t, (b0 (Sum.inr u) : Fin s → ℤ) ∈ K := by
    intro u
    have hh : (b0 (Sum.inr u) : Fin s → ℤ) = (bK u : Fin s → ℤ) := by
      simp only [b0, eqv, Basis.map_apply, Basis.prod_apply, Sum.elim_inr,
        Function.comp_apply, LinearMap.inr_apply, Submodule.coe_prodEquivOfIsCompl']; simp
    rw [hh]; exact Submodule.coe_mem (bK u)
  have he0 : e.symm ⟨0, hs⟩ = Sum.inl 0 := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; simp [heval_inl]
  have hlamW : lam ᵥ* W = Pi.single (⟨0, hs⟩ : Fin s) (1:ℤ) := by
    funext j
    have hvj : (lam ᵥ* W) j = lam ⬝ᵥ (b' j) := by
      simp only [Matrix.vecMul, dotProduct]
      apply Finset.sum_congr rfl; intro l _; rw [hWcol l j]
    rw [hvj, show b' j = b0 (e.symm j) from Basis.reindex_apply b0 e j]
    by_cases hj0 : j = ⟨0, hs⟩
    · subst hj0
      rw [he0, hb0inl, hw0, Pi.single_eq_same]
    · rcases he : e.symm j with a | u
      · exfalso
        have haa : a = 0 := Subsingleton.elim _ _
        subst haa
        have hja : j = e (Sum.inl (0:Fin 1)) := by rw [← he]; exact (e.apply_symm_apply j).symm
        have h00 : (⟨0,hs⟩ : Fin s) = e (Sum.inl 0) := by
          rw [← he0]; exact (e.apply_symm_apply _).symm
        exact hj0 (hja.trans h00.symm)
      · have hmem := hb0inr u
        rw [hmemK] at hmem
        rw [hmem, Pi.single_eq_of_ne hj0]
  refine ⟨W⁻¹, Matrix.isUnit_nonsing_inv_det W hWdet, ?_⟩
  intro w
  have hrow : (fun j => (W⁻¹) ⟨0,hs⟩ j) = lam := by
    have h1 : lam ᵥ* (W * W⁻¹) = lam := by rw [Matrix.mul_nonsing_inv W hWdet, Matrix.vecMul_one]
    rw [← Matrix.vecMul_vecMul, hlamW] at h1
    rw [← h1]; funext j
    simp only [Matrix.vecMul, dotProduct, Pi.single_apply]
    rw [Finset.sum_eq_single (⟨0,hs⟩ : Fin s)]
    · simp
    · intro l _ hl; simp [hl]
    · intro h; exact absurd (Finset.mem_univ _) h
  show (W⁻¹ *ᵥ w) ⟨0,hs⟩ = lam ⬝ᵥ w
  have hfin : (W⁻¹ *ᵥ w) ⟨0,hs⟩ = (W⁻¹ ⟨0,hs⟩) ⬝ᵥ w := rfl
  rw [hfin]
  exact congrArg (· ⬝ᵥ w) hrow

#print axioms integer_kernel_is_saturated
#print axioms kernel_has_integral_basis
#print axioms saturated_submodule_has_complement
#print axioms singular_symmetric_congruent_block
#print axioms nondegenerate_quotient_block
#print axioms affine_direction_unimodular_completion
