/-
  ConstResidual.lean — s55.  R43 Packet B1–B2 (GATE25 #68): constant residual along an affine
  centre, for ANY numbers of inputs, outputs and witnesses and with NO sign, rank or
  nondegeneracy hypothesis on the quadratic form.  The centre `c(a) = c0 + C a` is data.

  * `WeakIntAffineCosetNF`, `CommonSlopeIntNF`: integer affine normal forms (one coset; one
    modulus and one slope on every class), with bridges to the existing weak / full vocabularies.
  * B1: `constResidual_transport` — a modulus `M ≥ 1` and an integer `G = M·C` with
    `P(a + Mt, z + Gt) = P(a, z)` for all integer `a, z, t`; `constResidual_solEquiv` — the induced
    bijection of integer solution sets.
  * B2: `constResidual_translate` (`f(a + Mt) = f(a) + (Gt)|outputs`),
    `constResidual_commonSlopeIntNF`, `constResidual_fullVectorCosetNF`, and `affineSlope_unique`
    (the slope of such a translation law is determined by `f`).
  * Bridge: `FourSquareSlack.Family.familyData_constResidualCentre` — the compiled four-square datum
    has an explicit affine centre with constant residual; the constancy is DERIVED from `R_const`.
  * Control (B1 Step 5): `ConstResidualControl.ctlB1`, `b² + (u − v)² = 0`: centre 0, residual 0,
    `f = 0`, infinitely many witnesses at every input.

  Not claimed: existence of an affine centre or constancy of the residual for a general datum.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.RationalCentre
import ResearchUpgrade.CosetNormalForm
import ResearchUpgrade.AffineNormalForm
import ResearchUpgrade.FamilySE2Bridge

namespace DiophCompression.ResearchUpgrade

open Matrix

def WeakIntAffineCosetNF {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop :=
  ∃ (M : ℕ) (ρ : Fin n → ℤ) (b0 : Fin m → ℤ) (B : Matrix (Fin m) (Fin n) ℤ),
    1 ≤ M ∧ ∀ t : Fin n → ℤ, f (ρ + (M : ℤ) • t) = b0 + B *ᵥ t

def CommonSlopeIntNF {n m : ℕ} (f : (Fin n → ℤ) → (Fin m → ℤ)) : Prop :=
  ∃ (M : ℕ) (B : Matrix (Fin m) (Fin n) ℤ),
    1 ≤ M ∧ ∀ a t : Fin n → ℤ, f (a + (M : ℤ) • t) = f a + B *ᵥ t

theorem cr_exists_common_den {ι : Type*} [Fintype ι] (x : ι → ℚ) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ i, ∃ g : ℤ, (g : ℚ) = (M : ℚ) * x i := by
  classical
  refine ⟨∏ i, (x i).den, ?_, fun i => ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => (x i).den_nz)
  · obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun i => (x i).den) (Finset.mem_univ i)
    refine ⟨(e : ℤ) * (x i).num, ?_⟩
    rw [he]
    push_cast
    rw [mul_comm ((x i).den : ℚ) (e : ℚ), mul_assoc, Rat.den_mul_eq_num]

theorem cr_mulVec_apply {ι κ : Type*} [Fintype κ] (G : Matrix ι κ ℤ) (t : κ → ℤ) (k : ι) :
    (G *ᵥ t) k = ∑ i, G k i * t i := rfl

theorem weakVectorCosetNF_of_weakIntAffine {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (h : WeakIntAffineCosetNF f) : WeakVectorCosetNF f := by
  obtain ⟨M, ρ, b0, B, hM, h⟩ := h
  refine ⟨M, ρ, fun j => ⟨(b0 j : ℚ), fun i => (B j i : ℚ), 0⟩, hM, fun t j => ?_⟩
  rw [h t]
  simp [QuadForm.eval, castQ, dotProduct, cr_mulVec_apply]

theorem fullVectorCosetNF_of_commonSlope {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (h : CommonSlopeIntNF f) : FullVectorCosetNF f := by
  obtain ⟨M, B, hM, h⟩ := h
  refine ⟨M, hM, fun ρ => ⟨fun j => ⟨(f ρ j : ℚ), fun i => (B j i : ℚ), 0⟩, fun t j => ?_⟩⟩
  rw [h ρ t]
  simp [QuadForm.eval, castQ, dotProduct, cr_mulVec_apply]

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

def centreAt (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ) (a : Fin n → ℤ) :
    OutWit m r → ℚ :=
  fun k => c0 k + ∑ i, C k i * (a i : ℚ)

theorem cr_toQ_add (z w : OutWit m r → ℤ) : toQ (z + w) = toQ z + toQ w := by
  funext k; simp [toQ]

theorem cr_eval_cast {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    (z : OutWit m r → ℤ) :
    ((D.P.eval (Sum.elim a z) : ℤ) : ℚ) = D.zQuadQ (toQ z - c) - D.residual a c := by
  rw [D.evalZ]
  push_cast
  rw [← D.zQuadQ_toQ, ← D.zLinQ_toQ]
  exact D.completeSquare hc (toQ z)

theorem cr_zQuadQ_neg (v : OutWit m r → ℚ) : D.zQuadQ (-v) = D.zQuadQ v := by
  have := D.zQuadQ_smul (-1) v
  simpa using this

theorem cr_centreAt_add_smul (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (a t : Fin n → ℤ) (M : ℕ) (k : OutWit m r) :
    centreAt c0 C (a + (M : ℤ) • t) k
      = centreAt c0 C a k + (M : ℚ) * ∑ i, C k i * (t i : ℚ) := by
  simp only [centreAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem constResidual_transport (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (R0 : ℚ) (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0) :
    ∃ (M : ℕ) (G : Matrix (OutWit m r) (Fin n) ℤ), 1 ≤ M ∧
      (∀ k i, (G k i : ℚ) = (M : ℚ) * C k i) ∧
      ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ) (t : Fin n → ℤ),
        D.P.eval (Sum.elim (a + (M : ℤ) • t) (z + G *ᵥ t)) = D.P.eval (Sum.elim a z) := by
  obtain ⟨M, hM, hg⟩ := cr_exists_common_den (fun p : OutWit m r × Fin n => C p.1 p.2)
  choose g hg using hg
  have hG : ∀ k i, ((Matrix.of fun k i => g (k, i)) k i : ℚ) = (M : ℚ) * C k i :=
    fun k i => by simpa using hg (k, i)
  refine ⟨M, Matrix.of fun k i => g (k, i), hM, hG, fun a z t => ?_⟩
  apply Int.cast_injective (α := ℚ)
  have hshift : toQ (z + (Matrix.of fun k i => g (k, i)) *ᵥ t) - centreAt c0 C (a + (M : ℤ) • t)
      = toQ z - centreAt c0 C a := by
    funext k
    rw [cr_toQ_add]
    simp only [Pi.sub_apply, Pi.add_apply, cr_centreAt_add_smul, toQ, cr_mulVec_apply]
    push_cast
    simp only [hG]
    rw [Finset.mul_sum]
    have : ∑ i, (M : ℚ) * C k i * (t i : ℚ) = ∑ i, (M : ℚ) * (C k i * (t i : ℚ)) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    ring
  rw [D.cr_eval_cast (hcen (a + (M : ℤ) • t)), D.cr_eval_cast (hcen a), hR, hR, hshift]

theorem constResidual_solEquiv (M : ℕ) (G : Matrix (OutWit m r) (Fin n) ℤ)
    (hT : ∀ (a : Fin n → ℤ) (z : OutWit m r → ℤ) (t : Fin n → ℤ),
      D.P.eval (Sum.elim (a + (M : ℤ) • t) (z + G *ᵥ t)) = D.P.eval (Sum.elim a z))
    (a t : Fin n → ℤ) :
    ∃ e : {z : OutWit m r → ℤ // D.SolZ a z} ≃ {z : OutWit m r → ℤ // D.SolZ (a + (M : ℤ) • t) z},
      (∀ z, (e z : OutWit m r → ℤ) = z.1 + G *ᵥ t) ∧
      (∀ z, (e.symm z : OutWit m r → ℤ) = z.1 - G *ᵥ t) := by
  refine ⟨{ toFun := fun z => ⟨z.1 + G *ᵥ t, ?_⟩
            invFun := fun z => ⟨z.1 - G *ᵥ t, ?_⟩
            left_inv := fun z => Subtype.ext (add_sub_cancel_right _ _)
            right_inv := fun z => Subtype.ext (sub_add_cancel _ _) }, fun _ => rfl, fun _ => rfl⟩
  · show D.P.eval _ = 0
    rw [hT]
    exact z.2
  · show D.P.eval _ = 0
    have h := hT a (z.1 - G *ᵥ t) t
    rw [sub_add_cancel] at h
    rw [← h]
    exact z.2

theorem constResidual_translate (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (R0 : ℚ) (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    ∃ (M : ℕ) (G : Matrix (OutWit m r) (Fin n) ℤ), 1 ≤ M ∧
      (∀ k i, (G k i : ℚ) = (M : ℚ) * C k i) ∧
      ∀ a t : Fin n → ℤ, f (a + (M : ℤ) • t) = fun j => f a j + (G *ᵥ t) (Sum.inl j) := by
  obtain ⟨M, G, hM, hG, hT⟩ := D.constResidual_transport c0 C R0 hcen hR
  refine ⟨M, G, hM, hG, fun a t => ?_⟩
  obtain ⟨u, hu⟩ := (hf a (f a)).mpr rfl
  have hz : D.SolZ a (Sum.elim (f a) u) := (D.solZ_iff_sol a (f a) u).mpr hu
  have hz' : D.SolZ (a + (M : ℤ) • t) (Sum.elim (f a) u + G *ᵥ t) := by
    show D.P.eval _ = 0
    rw [hT]
    exact hz
  have hg := (hf _ _).mp (D.graph_of_solZ hz')
  rw [← hg]
  rfl

theorem constResidual_commonSlopeIntNF (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (R0 : ℚ) (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    CommonSlopeIntNF f := by
  obtain ⟨M, G, hM, -, h⟩ := D.constResidual_translate c0 C R0 hcen hR hf
  refine ⟨M, Matrix.of fun j i => G (Sum.inl j) i, hM, fun a t => ?_⟩
  rw [h a t]
  rfl

theorem constResidual_fullVectorCosetNF (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (R0 : ℚ) (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    (hR : ∀ a, D.residual a (centreAt c0 C a) = R0)
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f) :
    FullVectorCosetNF f :=
  fullVectorCosetNF_of_commonSlope (D.constResidual_commonSlopeIntNF c0 C R0 hcen hR hf)

end QuadraticGraphData

theorem affineSlope_unique {n m : ℕ} {f : (Fin n → ℤ) → (Fin m → ℤ)}
    (M M' : ℕ) (hM : 1 ≤ M) (hM' : 1 ≤ M') (A A' : Matrix (Fin m) (Fin n) ℚ)
    (h : ∀ (a t : Fin n → ℤ) (j : Fin m),
      (f (a + (M : ℤ) • t) j : ℚ) = f a j + (M : ℚ) * ∑ i, A j i * (t i : ℚ))
    (h' : ∀ (a t : Fin n → ℤ) (j : Fin m),
      (f (a + (M' : ℤ) • t) j : ℚ) = f a j + (M' : ℚ) * ∑ i, A' j i * (t i : ℚ)) :
    A = A' := by
  ext j i
  have e1 := h 0 ((M' : ℤ) • Pi.single i (1 : ℤ)) j
  have e2 := h' 0 ((M : ℤ) • Pi.single i (1 : ℤ)) j
  have hc : (M : ℤ) • ((M' : ℤ) • (Pi.single i (1 : ℤ) : Fin n → ℤ))
      = (M' : ℤ) • ((M : ℤ) • (Pi.single i (1 : ℤ) : Fin n → ℤ)) := smul_comm _ _ _
  rw [hc] at e1
  rw [e1] at e2
  simp [Pi.single_apply] at e2
  have hM0 : (0 : ℚ) < M := by exact_mod_cast hM
  have hM0' : (0 : ℚ) < M' := by exact_mod_cast hM'
  have key : ((M : ℚ) * M') * A j i = ((M : ℚ) * M') * A' j i := by
    nlinarith [e2]
  exact mul_left_cancel₀ (ne_of_gt (mul_pos hM0 hM0')) key

namespace FourSquareSlack.Family

variable {n m : ℕ} (F : Family n m) (PR : IntQuad (Fin n))

theorem familyData_constResidualCentre (hm : 0 < m) (hR : ∀ a, F.R a = PR.eval a)
    (hT : F.Total) (hU : F.OutputUnique) :
    ∃ (c0 : OutWit m 4 → ℚ) (C : Matrix (OutWit m 4) (Fin n) ℚ) (R0 : ℚ),
      (∀ a, (F.familyData PR).IsCentre a (QuadraticGraphData.centreAt c0 C a)) ∧
      (∀ a, (F.familyData PR).residual a (QuadraticGraphData.centreAt c0 C a) = R0) := by
  have hk0 : (F.k : ℚ) ≠ 0 := by
    have := F.hk
    exact_mod_cast (show F.k ≠ 0 by omega)
  refine ⟨(Sum.elim (fun j : Fin m => (F.c j : ℚ) / F.k) (fun _ : Fin 4 => (0 : ℚ)) :
      OutWit m 4 → ℚ),
    (Matrix.of fun (k : OutWit m 4) (i : Fin n) =>
      Sum.elim (fun j : Fin m => (F.B j i : ℚ) / F.k) (fun _ : Fin 4 => (0 : ℚ)) k),
    (F.R 0 : ℚ), ?_, ?_⟩
  all_goals
    have hcA : ∀ a : Fin n → ℤ, QuadraticGraphData.centreAt
        (Sum.elim (fun j : Fin m => (F.c j : ℚ) / F.k) (fun _ : Fin 4 => (0 : ℚ)))
        (Matrix.of fun (k : OutWit m 4) (i : Fin n) =>
          Sum.elim (fun j : Fin m => (F.B j i : ℚ) / F.k) (fun _ : Fin 4 => (0 : ℚ)) k) a
        = Sum.elim (fun j : Fin m => (F.lin a j : ℚ) / F.k) (fun _ : Fin 4 => (0 : ℚ)) := by
      intro a
      funext k
      cases k with
      | inl j =>
        simp only [QuadraticGraphData.centreAt, Matrix.of_apply, Sum.elim_inl, Family.lin]
        push_cast
        rw [add_div, Finset.sum_div]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
      | inr i => simp [QuadraticGraphData.centreAt]
  · intro a w
    rw [hcA a]
    have hlin : (F.familyData PR).zLinQ a w
        = ∑ j, (-(2 * (F.k : ℚ) * F.lin a j)) * w (Sum.inl j) := by
      simp only [QuadraticGraphData.zLinQ, Fintype.sum_sum_type, familyData_zLin_out,
        familyData_zLin_wit]
      push_cast
      simp
    have hpol : (F.familyData PR).zPolarQ
        (Sum.elim (fun j : Fin m => (F.lin a j : ℚ) / F.k) (fun _ : Fin 4 => (0 : ℚ))) w
        = ∑ j, 2 * ((F.k : ℚ) ^ 2 * ((F.lin a j : ℚ) / F.k)) * w (Sum.inl j) := by
      simp only [QuadraticGraphData.zPolarQ, familyData, Fintype.sum_sum_type]
      simp [mul_ite, ite_mul, Finset.sum_add_distrib, Finset.sum_ite_eq]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hlin, hpol, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    field_simp
    ring
  · intro a
    rw [hcA a, QuadraticGraphData.residual, familyData_aPart, ← hR a, F.R_const hm hT hU hR a]
    simp only [QuadraticGraphData.zQuadQ, familyData, Fintype.sum_sum_type]
    simp [mul_ite, ite_mul, Finset.sum_ite_eq]
    have : ∀ j : Fin m, (F.lin a j : ℚ) / F.k * ((F.k : ℚ) ^ 2 * ((F.lin a j : ℚ) / F.k))
        = (F.lin a j : ℚ) ^ 2 := fun j => by field_simp
    simp only [this]
    ring

end FourSquareSlack.Family

namespace ConstResidualControl

def ctlB1 : QuadraticGraphData 1 1 2 where
  P :=
    { c := 0
      l := 0
      Q := fun p q => match p, q with
        | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 1
        | Sum.inr (Sum.inr i), Sum.inr (Sum.inr i') =>
            if i = i' then 1 else if (i : ℕ) = 0 then -2 else 0
        | _, _ => 0 }

theorem ctlB1_hyp :
    (∀ a, ctlB1.IsCentre a (QuadraticGraphData.centreAt 0 0 a)) ∧
    (∀ a, ctlB1.residual a (QuadraticGraphData.centreAt 0 0 a) = 0) := by
  have h0 : ∀ a : Fin 1 → ℤ, QuadraticGraphData.centreAt (0 : OutWit 1 2 → ℚ) 0 a = 0 := by
    intro a; funext k; simp [QuadraticGraphData.centreAt]
  refine ⟨fun a w => ?_, fun a => ?_⟩
  · rw [h0]
    simp [QuadraticGraphData.zPolarQ, QuadraticGraphData.zLinQ, QuadraticGraphData.zLin, ctlB1]
  · rw [h0]
    simp [QuadraticGraphData.residual, QuadraticGraphData.zQuadQ, QuadraticGraphData.aPart, ctlB1]

theorem ctlB1_eval (a : Fin 1 → ℤ) (b : Fin 1 → ℤ) (u : Fin 2 → ℤ) :
    ctlB1.P.eval (pt a b u) = b 0 ^ 2 + (u 0 - u 1) ^ 2 := by
  simp [ctlB1, IntQuad.eval, pt, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem ctlB1_defines : ctlB1.Defines (fun _ => 0) := by
  intro a b
  constructor
  · rintro ⟨u, hu⟩
    have h := hu
    unfold QuadraticGraphData.Sol at h
    rw [ctlB1_eval] at h
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have hb : b 0 = 0 := by nlinarith [sq_nonneg (b 0), sq_nonneg (u 0 - u 1)]
    exact hb
  · rintro rfl
    refine ⟨0, ?_⟩
    unfold QuadraticGraphData.Sol
    rw [ctlB1_eval]
    simp

theorem ctlB1_witnesses_infinite (a : Fin 1 → ℤ) : Set.Infinite {z | ctlB1.SolZ a z} := by
  refine Set.infinite_of_injective_forall_mem (f := fun s : ℤ => Sum.elim (0 : Fin 1 → ℤ) (fun _ => s))
    ?_ ?_
  · intro s s' hs
    have := congrFun hs (Sum.inr 0)
    simpa using this
  · intro s
    show ctlB1.SolZ a _
    rw [QuadraticGraphData.solZ_iff_sol]
    unfold QuadraticGraphData.Sol
    rw [ctlB1_eval]
    simp

end ConstResidualControl

end DiophCompression.ResearchUpgrade
