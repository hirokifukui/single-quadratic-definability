/-
  IsometryCertificate.lean — s55.  R43 D3–D4 (GATE25 #72): rational isometries and finite symmetry
  certificates.

  * D3: `isometry_solZ` — an isometry of `Q` about the centre maps solutions to solutions, and an
    integral image is an integer solution; `isometry_output_zero` — only then, output-uniqueness
    gives `π(T − I)(z − c) = 0`; `isometry_integral_iff` — integrality of the image as an explicit
    congruence modulo `N²`.
  * D4: `affineIntegral_coset` (integrality at one point plus `M·D` integral ⇒ on the coset);
    `symmetry_certificate_NF` — finitely many integer isometries, finite integrality data and a
    rational certificate `π = Σ Aᵢ π(Tᵢ − I)` give a weak integer affine coset NF (the NF is not a
    hypothesis); `negIdentity_shift`, `negIdentity_certificate` — `T = −I` is the doubled-centre
    condition of B4.
  * Controls, `(2b − 2a)² + (3u − 1)² + v² = 1`: centre `(a, 1/3, 0)`, residual 1, `f(a) = a`; the
    doubled centre is never integral (`ctlD4_not_reflectable`); the output flip passes the
    certificate (`ctlD4_certificate_NF`); the witness flip sends an integer solution to a
    non-integral rational one (`ctlD4_T2_not_integral`).  The residual here is constant, so this
    example does not touch the open non-constant case.

  Claim tags: [P] (std-3).
-/
import ResearchUpgrade.AffineSection

namespace DiophCompression.ResearchUpgrade

open Matrix

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

theorem isometry_solZ {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    (T : Matrix (OutWit m r) (OutWit m r) ℚ) (hT : ∀ w, D.zQuadQ (T *ᵥ w) = D.zQuadQ w)
    {z : OutWit m r → ℤ} (hz : D.SolZ a z)
    (z' : OutWit m r → ℤ) (hz' : toQ z' = c + T *ᵥ (toQ z - c)) :
    D.SolZ a z' := by
  have hz0 : D.P.eval (Sum.elim a z) = 0 := hz
  show D.P.eval _ = 0
  apply Int.cast_injective (α := ℚ)
  rw [D.cr_eval_cast hc, hz', add_sub_cancel_left, hT, ← D.cr_eval_cast hc, hz0]

theorem isometry_output_zero {a : Fin n → ℤ} {c : OutWit m r → ℚ} (hc : D.IsCentre a c)
    (T : Matrix (OutWit m r) (OutWit m r) ℚ) (hT : ∀ w, D.zQuadQ (T *ᵥ w) = D.zQuadQ w)
    (hU : D.OutputUnique) {z : OutWit m r → ℤ} (hz : D.SolZ a z)
    (z' : OutWit m r → ℤ) (hz' : toQ z' = c + T *ᵥ (toQ z - c)) (j : Fin m) :
    (T *ᵥ (toQ z - c) - (toQ z - c)) (Sum.inl j) = 0 := by
  have hz'' := D.isometry_solZ hc T hT hz z' hz'
  have e := hU a _ _ (D.graph_of_solZ hz) (D.graph_of_solZ hz'')
  have ej : z (Sum.inl j) = z' (Sum.inl j) := congrFun e j
  have hk := congrFun hz' (Sum.inl j)
  have ejq : (z (Sum.inl j) : ℚ) = z' (Sum.inl j) := by exact_mod_cast ej
  simp only [Pi.add_apply] at hk
  simp only [Pi.sub_apply]
  have hz1 : toQ z (Sum.inl j) = (z (Sum.inl j) : ℚ) := rfl
  have hz2 : toQ z' (Sum.inl j) = (z' (Sum.inl j) : ℚ) := rfl
  rw [hz2] at hk
  rw [hz1]
  linarith

end QuadraticGraphData

theorem isometry_integral_iff {s : Type*} [Fintype s] (c : s → ℚ) (T : Matrix s s ℚ) (z : s → ℤ)
    (N : ℕ) (hN : 1 ≤ N) (cN : s → ℤ) (TN : Matrix s s ℤ)
    (hcN : ∀ k, (cN k : ℚ) = (N : ℚ) * c k) (hTN : ∀ k l, (TN k l : ℚ) = (N : ℚ) * T k l) :
    (∃ z' : s → ℤ, (fun k => (z' k : ℚ)) = c + T *ᵥ ((fun k => (z k : ℚ)) - c)) ↔
      ∀ k, ((N : ℤ) ^ 2) ∣ ((N : ℤ) • cN + (N : ℤ) • (TN *ᵥ z) - TN *ᵥ cN) k := by
  have hN0 : (N : ℚ) ≠ 0 := by
    have : (0 : ℚ) < N := by exact_mod_cast hN
    exact ne_of_gt this
  have key : ∀ k, ((((N : ℤ) • cN + (N : ℤ) • (TN *ᵥ z) - TN *ᵥ cN) k : ℤ) : ℚ)
      = (N : ℚ) ^ 2 * (c + T *ᵥ ((fun k => (z k : ℚ)) - c)) k := by
    intro k
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    push_cast
    simp only [hcN, hTN]
    rw [add_sub_assoc, Finset.mul_sum, ← Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun l _ => by ring
  constructor
  · rintro ⟨z', hz'⟩ k
    refine ⟨z' k, ?_⟩
    apply Int.cast_injective (α := ℚ)
    rw [key k, ← congrFun hz' k]
    push_cast
    ring
  · intro hd
    refine ⟨fun k => ((N : ℤ) • cN + (N : ℤ) • (TN *ᵥ z) - TN *ᵥ cN) k / ((N : ℤ) ^ 2), ?_⟩
    funext k
    rw [Int.cast_div (hd k) (by push_cast; exact pow_ne_zero 2 hN0), key k]
    push_cast
    field_simp

theorem affineIntegral_coset {n : ℕ} {s : Type*} [Fintype s] (d0 : s → ℚ) (Dm : Matrix s (Fin n) ℚ)
    (M : ℕ) (hMD : ∀ k i, ∃ g : ℤ, (g : ℚ) = (M : ℚ) * Dm k i) (ρ : Fin n → ℤ)
    (h0 : ∃ h : s → ℤ, (fun k => (h k : ℚ)) = d0 + Dm *ᵥ castQ ρ) :
    ∀ t : Fin n → ℤ, ∃ h : s → ℤ,
      (fun k => (h k : ℚ)) = d0 + Dm *ᵥ castQ (ρ + (M : ℤ) • t) := by
  choose g hg using hMD
  obtain ⟨h, hh⟩ := h0
  intro t
  refine ⟨h + (Matrix.of fun k i => g k i) *ᵥ t, ?_⟩
  funext k
  have hk := congrFun hh k
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, castQ, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul] at hk ⊢
  push_cast at hk ⊢
  rw [hk]
  simp only [hg, mul_add, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

namespace QuadraticGraphData

variable {n m r : ℕ} (D : QuadraticGraphData n m r)

theorem ic_centreAt_eq (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (a : Fin n → ℤ) : centreAt c0 C a = c0 + C *ᵥ castQ a := rfl

theorem ic_toQ_mulVec (T : Matrix (OutWit m r) (OutWit m r) ℤ) (z : OutWit m r → ℤ) :
    toQ (T *ᵥ z) = T.map (Int.cast : ℤ → ℚ) *ᵥ toQ z := by
  funext k
  simp [toQ, Matrix.mulVec, dotProduct, Matrix.map_apply]

theorem symmetry_certificate_NF {ι : Type*} [Fintype ι]
    (c0 : OutWit m r → ℚ) (C : Matrix (OutWit m r) (Fin n) ℚ)
    (hcen : ∀ a, D.IsCentre a (centreAt c0 C a))
    {f : (Fin n → ℤ) → (Fin m → ℤ)} (hf : D.Defines f)
    (T : ι → Matrix (OutWit m r) (OutWit m r) ℤ)
    (hT : ∀ i w, D.zQuadQ ((T i).map (Int.cast : ℤ → ℚ) *ᵥ w) = D.zQuadQ w)
    (M : ℕ) (hM : 1 ≤ M) (ρ : Fin n → ℤ)
    (hMint : ∀ i k l, ∃ g : ℤ,
      (g : ℚ) = (M : ℚ) * (((1 - (T i).map (Int.cast : ℤ → ℚ) : Matrix (OutWit m r) (OutWit m r) ℚ) * C :
        Matrix (OutWit m r) (Fin n) ℚ) k l))
    (h0 : ∀ i, ∃ h : OutWit m r → ℤ,
      toQ h = (1 - (T i).map (Int.cast : ℤ → ℚ)) *ᵥ centreAt c0 C ρ)
    (A : ι → Matrix (Fin m) (Fin m) ℚ)
    (hA : ∀ w : OutWit m r → ℚ, (fun j => w (Sum.inl j)) =
      ∑ i, A i *ᵥ (fun j => (((T i).map (Int.cast : ℤ → ℚ) - 1) *ᵥ w) (Sum.inl j))) :
    WeakIntAffineCosetNF f := by
  classical
  have hU : D.OutputUnique := fun a b b' hb hb' =>
    ((hf a b).mp hb).trans ((hf a b').mp hb').symm
  have hint : ∀ i (t : Fin n → ℤ), ∃ h : OutWit m r → ℤ,
      toQ h = (1 - (T i).map (Int.cast : ℤ → ℚ)) *ᵥ centreAt c0 C (ρ + (M : ℤ) • t) := by
    intro i t
    set U : Matrix (OutWit m r) (OutWit m r) ℚ := 1 - (T i).map (Int.cast : ℤ → ℚ) with hUdef
    have hsplit : ∀ a : Fin n → ℤ, U *ᵥ centreAt c0 C a = U *ᵥ c0 + (U * C) *ᵥ castQ a := by
      intro a
      rw [ic_centreAt_eq, Matrix.mulVec_add, Matrix.mulVec_mulVec]
    obtain ⟨h, hh⟩ := affineIntegral_coset (U *ᵥ c0) (U * C) M (hMint i) ρ
      (by obtain ⟨h, hh⟩ := h0 i; exact ⟨h, by rw [← hsplit]; exact hh⟩) t
    exact ⟨h, by rw [hsplit]; exact hh⟩
  have hval : ∀ (t : Fin n → ℤ) (j : Fin m),
      (f (ρ + (M : ℤ) • t) j : ℚ) = centreAt c0 C (ρ + (M : ℤ) • t) (Sum.inl j) := by
    intro t j
    set a := ρ + (M : ℤ) • t with ha
    obtain ⟨u, hu⟩ := (hf a (f a)).mpr rfl
    have hz : D.SolZ a (Sum.elim (f a) u) := (D.solZ_iff_sol a (f a) u).mpr hu
    set z : OutWit m r → ℤ := Sum.elim (f a) u with hzdef
    set w : OutWit m r → ℚ := toQ z - centreAt c0 C a with hw
    have hzero : ∀ i, (fun j => (((T i).map (Int.cast : ℤ → ℚ) - 1) *ᵥ w) (Sum.inl j)) = 0 := by
      intro i
      obtain ⟨h, hh⟩ := hint i t
      have hz'q : toQ (T i *ᵥ z + h) = centreAt c0 C a
          + (T i).map (Int.cast : ℤ → ℚ) *ᵥ (toQ z - centreAt c0 C a) := by
        rw [cr_toQ_add, ic_toQ_mulVec, hh, Matrix.sub_mulVec, Matrix.one_mulVec,
          Matrix.mulVec_sub]
        abel
      have := D.isometry_output_zero (hcen a) _ (hT i) hU hz _ hz'q
      funext j
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact this j
    have hw0 := congrFun (hA w) j
    simp only [hzero, Matrix.mulVec_zero, Finset.sum_const_zero, Pi.zero_apply] at hw0
    simp only [hw, Pi.sub_apply, sub_eq_zero] at hw0
    rw [← hw0]
    rfl
  refine weakIntAffine_of_affineCoset M hM ρ (fun j => centreAt c0 C ρ (Sum.inl j))
    (Matrix.of fun j i => (M : ℚ) * C (Sum.inl j) i) fun t j => ?_
  rw [hval t j, cr_centreAt_add_smul, Finset.mul_sum]
  simp only [Matrix.of_apply]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

end QuadraticGraphData

theorem negIdentity_shift {s : Type*} [Fintype s] [DecidableEq s] (x : s → ℚ) :
    (1 - (-1 : Matrix s s ℤ).map (Int.cast : ℤ → ℚ)) *ᵥ x = 2 • x := by
  have hm : (-1 : Matrix s s ℤ).map (Int.cast : ℤ → ℚ) = -1 := by
    rw [Matrix.map_neg _ (fun a => Int.cast_neg a), Matrix.map_one _ Int.cast_zero Int.cast_one]
  rw [hm, sub_neg_eq_add, Matrix.add_mulVec, Matrix.one_mulVec]
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
  push_cast
  ring

theorem negIdentity_certificate {m r : ℕ} (w : OutWit m r → ℚ) :
    (fun j => w (Sum.inl j)) =
      ((-1 / 2 : ℚ) • (1 : Matrix (Fin m) (Fin m) ℚ)) *ᵥ
        (fun j => (((-1 : Matrix (OutWit m r) (OutWit m r) ℤ).map (Int.cast : ℤ → ℚ) - 1) *ᵥ w)
          (Sum.inl j)) := by
  have hm : (-1 : Matrix (OutWit m r) (OutWit m r) ℤ).map (Int.cast : ℤ → ℚ) = -1 := by
    rw [Matrix.map_neg _ (fun a => Int.cast_neg a), Matrix.map_one _ Int.cast_zero Int.cast_one]
  rw [hm, Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec]
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Pi.sub_apply, Pi.neg_apply]
  simp [Finset.sum_ite_eq]
  ring

namespace IsometryControl

def ctlD4 : QuadraticGraphData 1 1 2 where
  P :=
    { c := 0
      l := fun p => match p with
        | Sum.inr (Sum.inr i) => if (i : ℕ) = 0 then -6 else 0
        | _ => 0
      Q := fun p q => match p, q with
        | Sum.inl _, Sum.inl _ => 4
        | Sum.inl _, Sum.inr (Sum.inl _) => -8
        | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 4
        | Sum.inr (Sum.inr i), Sum.inr (Sum.inr i') =>
            if i = i' then (if (i : ℕ) = 0 then 9 else 1) else 0
        | _, _ => 0 }

def c0D4 : OutWit 1 2 → ℚ := Sum.elim (fun _ => 0) (fun i => if (i : ℕ) = 0 then 1 / 3 else 0)
def cD4 : Matrix (OutWit 1 2) (Fin 1) ℚ := Matrix.of fun k _ => Sum.elim (fun _ => 1) (fun _ => 0) k

def T1D4 : Matrix (OutWit 1 2) (OutWit 1 2) ℤ := Matrix.diagonal (Sum.elim (fun _ => -1) (fun _ => 1))
def T2D4 : Matrix (OutWit 1 2) (OutWit 1 2) ℤ :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun i => if (i : ℕ) = 0 then -1 else 1))

theorem c0D4_b : c0D4 (Sum.inl 0) = 0 := rfl
theorem c0D4_u : c0D4 (Sum.inr 0) = 1 / 3 := rfl
theorem c0D4_v : c0D4 (Sum.inr 1) = 0 := rfl
theorem cD4_b (i : Fin 1) : cD4 (Sum.inl 0) i = 1 := rfl
theorem cD4_u (i : Fin 1) : cD4 (Sum.inr 0) i = 0 := rfl
theorem cD4_v (i : Fin 1) : cD4 (Sum.inr 1) i = 0 := rfl

theorem ctlD4_eval (a b : Fin 1 → ℤ) (u : Fin 2 → ℤ) :
    ctlD4.P.eval (pt a b u) = (2 * b 0 - 2 * a 0) ^ 2 + (3 * u 0 - 1) ^ 2 + u 1 ^ 2 - 1 := by
  simp [ctlD4, IntQuad.eval, pt, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem ctlD4_zQuadQ (w : OutWit 1 2 → ℚ) :
    ctlD4.zQuadQ w = 4 * w (Sum.inl 0) ^ 2 + 9 * w (Sum.inr 0) ^ 2 + w (Sum.inr 1) ^ 2 := by
  simp [QuadraticGraphData.zQuadQ, ctlD4, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem ctlD4_centre_residual :
    (∀ a, ctlD4.IsCentre a (QuadraticGraphData.centreAt c0D4 cD4 a)) ∧
    (∀ a, ctlD4.residual a (QuadraticGraphData.centreAt c0D4 cD4 a) = 1) := by
  refine ⟨fun a w => ?_, fun a => ?_⟩
  · simp only [QuadraticGraphData.zPolarQ, QuadraticGraphData.zLinQ, QuadraticGraphData.zLin,
      QuadraticGraphData.centreAt, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one,
      c0D4_b, c0D4_u, c0D4_v, cD4_b, cD4_u, cD4_v]
    simp [ctlD4]
    ring
  · simp only [QuadraticGraphData.residual, QuadraticGraphData.zQuadQ, QuadraticGraphData.aPart,
      QuadraticGraphData.centreAt, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one,
      c0D4_b, c0D4_u, c0D4_v, cD4_b, cD4_u, cD4_v]
    simp [ctlD4]
    ring

theorem ctlD4_defines : ctlD4.Defines (fun a _ => a 0) := by
  intro a b
  have hb : b = (fun _ => a 0 : Fin 1 → ℤ) ↔ b 0 = a 0 := by
    constructor
    · intro h; rw [h]
    · intro h
      funext j
      fin_cases j
      exact h
  simp only
  rw [hb]
  constructor
  · rintro ⟨u, hu⟩
    have h := hu
    unfold QuadraticGraphData.Sol at h
    rw [ctlD4_eval] at h
    have hne : 3 * u 0 - 1 ≠ 0 := by omega
    have hp : 0 < (3 * u 0 - 1) ^ 2 := by positivity
    have h1 : 0 + 1 ≤ (3 * u 0 - 1) ^ 2 := Int.add_one_le_iff.mpr hp
    have h2 : (2 * b 0 - 2 * a 0) ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * b 0 - 2 * a 0), sq_nonneg (u 1)]
    have h3 : 2 * b 0 - 2 * a 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    omega
  · intro hb0
    refine ⟨![0, 0], ?_⟩
    unfold QuadraticGraphData.Sol
    rw [ctlD4_eval, hb0]
    simp

theorem ctlD4_not_reflectable (a : Fin 1 → ℤ) :
    ¬ ∃ h : OutWit 1 2 → ℤ, toQ h = 2 • QuadraticGraphData.centreAt c0D4 cD4 a := by
  rintro ⟨h, hh⟩
  have hk := congrFun hh (Sum.inr 0)
  simp only [toQ, Pi.smul_apply, nsmul_eq_mul, QuadraticGraphData.centreAt, Fin.sum_univ_one,
    c0D4_u, cD4_u, zero_mul, add_zero] at hk
  have : ((3 * h (Sum.inr 0) : ℤ) : ℚ) = ((2 : ℤ) : ℚ) := by push_cast; rw [hk]; norm_num
  have := Int.cast_injective (α := ℚ) this
  omega

theorem ctlD4_T1_isometry (w : OutWit 1 2 → ℚ) :
    ctlD4.zQuadQ (T1D4.map (Int.cast : ℤ → ℚ) *ᵥ w) = ctlD4.zQuadQ w := by
  rw [ctlD4_zQuadQ, ctlD4_zQuadQ, T1D4, Matrix.diagonal_map Int.cast_zero]
  simp only [Matrix.mulVec_diagonal, Sum.elim_inl, Sum.elim_inr]
  push_cast
  ring

theorem ctlD4_T2_isometry (w : OutWit 1 2 → ℚ) :
    ctlD4.zQuadQ (T2D4.map (Int.cast : ℤ → ℚ) *ᵥ w) = ctlD4.zQuadQ w := by
  rw [ctlD4_zQuadQ, ctlD4_zQuadQ, T2D4, Matrix.diagonal_map Int.cast_zero]
  simp only [Matrix.mulVec_diagonal, Sum.elim_inl, Sum.elim_inr]
  simp

theorem ctlD4_T2_not_integral (a : Fin 1 → ℤ) :
    ¬ ∃ z' : OutWit 1 2 → ℤ, toQ z' =
      QuadraticGraphData.centreAt c0D4 cD4 a +
        T2D4.map (Int.cast : ℤ → ℚ) *ᵥ
          (toQ (Sum.elim (fun _ => a 0) (0 : Fin 2 → ℤ)) - QuadraticGraphData.centreAt c0D4 cD4 a) := by
  rintro ⟨z', hz'⟩
  have hk := congrFun hz' (Sum.inr 0)
  rw [T2D4, Matrix.diagonal_map Int.cast_zero] at hk
  simp only [Pi.add_apply, Matrix.mulVec_diagonal, Pi.sub_apply, toQ, Sum.elim_inr,
    QuadraticGraphData.centreAt, Fin.sum_univ_one, c0D4_u, cD4_u, zero_mul, add_zero,
    Pi.zero_apply] at hk
  have h3 : ((3 * z' (Sum.inr 0) : ℤ) : ℚ) = ((2 : ℤ) : ℚ) := by
    push_cast
    rw [hk]
    norm_num
  have := Int.cast_injective (α := ℚ) h3
  omega

theorem ctlD4_certificate_NF :
    WeakIntAffineCosetNF (fun a : Fin 1 → ℤ => fun _ : Fin 1 => a 0) := by
  classical
  have hdata := ctlD4_centre_residual
  have hdiag : (1 - T1D4.map (Int.cast : ℤ → ℚ) : Matrix (OutWit 1 2) (OutWit 1 2) ℚ)
      = Matrix.diagonal (Sum.elim (fun _ => 2) (fun _ => 0)) := by
    rw [T1D4, Matrix.diagonal_map Int.cast_zero, ← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext k
    rcases k with k | k <;> norm_num
  have hdiag2 : (T1D4.map (Int.cast : ℤ → ℚ) - 1 : Matrix (OutWit 1 2) (OutWit 1 2) ℚ)
      = Matrix.diagonal (Sum.elim (fun _ => -2) (fun _ => 0)) := by
    rw [T1D4, Matrix.diagonal_map Int.cast_zero, ← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext k
    rcases k with k | k <;> norm_num
  refine ctlD4.symmetry_certificate_NF (ι := Unit) c0D4 cD4 hdata.1 ctlD4_defines
    (fun _ => T1D4) (fun _ w => ctlD4_T1_isometry w) 1 le_rfl 0 ?_ ?_
    (fun _ => (-1 / 2 : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ)) ?_
  · intro _ k l
    rw [hdiag, Matrix.diagonal_mul]
    rcases k with k | k
    · refine ⟨2, ?_⟩
      obtain rfl : k = 0 := Subsingleton.elim _ _
      rw [cD4_b]; norm_num
    · refine ⟨0, ?_⟩
      simp only [Sum.elim_inr]
      norm_num
  · intro _
    refine ⟨0, ?_⟩
    rw [hdiag]
    funext k
    simp only [toQ, Pi.zero_apply, Int.cast_zero, Matrix.mulVec_diagonal]
    rcases k with k | k
    · obtain rfl : k = 0 := Subsingleton.elim _ _
      simp only [Sum.elim_inl, QuadraticGraphData.centreAt, Fin.sum_univ_one, c0D4_b, cD4_b]
      norm_num
    · simp only [Sum.elim_inr, zero_mul]
  · intro w
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [hdiag2]
    simp only [Matrix.mulVec_diagonal, Sum.elim_inl, Finset.univ_unique, Finset.sum_singleton]
    simp [Matrix.mulVec, dotProduct]
    ring

end IsometryControl

end DiophCompression.ResearchUpgrade
