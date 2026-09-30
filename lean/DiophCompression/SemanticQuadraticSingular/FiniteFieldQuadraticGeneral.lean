/-
  FiniteFieldQuadraticGeneral.lean — r11 (GPT r10 必須I): finite-field universality of a
  nondegenerate quadratic in k ≥ 2 variables, and the affine root theorem.
  Statements frozen in FiniteFieldQuadraticGeneral_STATEMENTS.lean (md5 c1564388) before proofs.
  Proof production: Claude Code job s11_ffq (2026-08-28), independently re-verified by claude.ai
  (kernel EXIT=0, both theorems std-3, statements verbatim vs freeze, full re-reading).
  Route: no diagonalization — a nondegenerate two-dimensional restriction is extracted by
  polarization (all 2×2 Gram minors vanish ⇒ the symmetric form has rank ≤ 1 ⇒ contradiction
  with det ≠ 0), then the r10 binary theorem closes; the affine case by parallel translation
  s = −G⁻¹ m.
-/
import DiophCompression.SemanticQuadraticSingular.FiniteFieldQuadratic

namespace DiophCompression.SemanticQuadraticSingular
open Matrix

/-- The explicit double sum equals the matrix bilinear evaluation `x ⬝ᵥ C *ᵥ x`. -/
private lemma qbridge {k p : ℕ} (C : Matrix (Fin k) (Fin k) (ZMod p)) (x : Fin k → ZMod p) :
    (∑ i, ∑ j, C i j * x i * x j) = x ⬝ᵥ C *ᵥ x := by
  rw [dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- Bilinear expansion in two scalar parameters. -/
private lemma qexpand_smul {k p : ℕ} (C : Matrix (Fin k) (Fin k) (ZMod p))
    (u v : Fin k → ZMod p) (X Y : ZMod p) :
    (X • u + Y • v) ⬝ᵥ C *ᵥ (X • u + Y • v)
      = X ^ 2 * (u ⬝ᵥ C *ᵥ u) + X * Y * (u ⬝ᵥ C *ᵥ v + v ⬝ᵥ C *ᵥ u) + Y ^ 2 * (v ⬝ᵥ C *ᵥ v) := by
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

/-- Bilinear expansion for an additive shift. -/
private lemma qexpand_add {k p : ℕ} (C : Matrix (Fin k) (Fin k) (ZMod p))
    (u v : Fin k → ZMod p) :
    (u + v) ⬝ᵥ C *ᵥ (u + v)
      = u ⬝ᵥ C *ᵥ u + (u ⬝ᵥ C *ᵥ v + v ⬝ᵥ C *ᵥ u) + v ⬝ᵥ C *ᵥ v := by
  simp only [mulVec_add, dotProduct_add, add_dotProduct]
  ring

/-- The symmetric (Gram) bilinear form of `C + Cᵀ` splits into the two `C`-forms. -/
private lemma cross_eq {k p : ℕ} (C : Matrix (Fin k) (Fin k) (ZMod p))
    (a b : Fin k → ZMod p) :
    a ⬝ᵥ (C + Cᵀ) *ᵥ b = a ⬝ᵥ C *ᵥ b + b ⬝ᵥ C *ᵥ a := by
  rw [add_mulVec, dotProduct_add, mulVec_transpose]
  congr 1
  rw [dotProduct_comm, ← dotProduct_mulVec]

theorem nondegenerate_quadratic_represents_all {k : ℕ} (hk : 2 ≤ k)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (C : Matrix (Fin k) (Fin k) (ZMod p))
    (hC : (C + Cᵀ).det ≠ 0) (ρ : ZMod p) :
    ∃ x : Fin k → ZMod p,
      (∑ i, ∑ j, C i j * x i * x j) = ρ := by
  classical
  set G := C + Cᵀ with hG
  have hsymm : Gᵀ = G := by rw [hG, transpose_add, transpose_transpose, add_comm]
  have hGunit : IsUnit G := by rw [isUnit_iff_isUnit_det]; exact isUnit_iff_ne_zero.mpr hC
  have h2 : (2 : ZMod p) ≠ 0 := aux_two_ne_zero p hp2
  -- symmetry of the bilinear form of G
  have hSsymm : ∀ u v : Fin k → ZMod p, u ⬝ᵥ G *ᵥ v = v ⬝ᵥ G *ᵥ u := by
    intro u v; rw [dotProduct_mulVec, ← mulVec_transpose, hsymm, dotProduct_comm]
  -- relate the G-form to the C-form
  have hbG : ∀ u v : Fin k → ZMod p, u ⬝ᵥ G *ᵥ v = u ⬝ᵥ C *ᵥ v + v ⬝ᵥ C *ᵥ u := by
    intro u v
    rw [hG, add_mulVec, dotProduct_add, mulVec_transpose]
    congr 1
    rw [dotProduct_comm, ← dotProduct_mulVec]
  have haG : ∀ u : Fin k → ZMod p, u ⬝ᵥ G *ᵥ u = 2 * (u ⬝ᵥ C *ᵥ u) := by
    intro u; rw [hbG u u]; ring
  -- KEY: there exist u v whose G-Gram is nonsingular
  have keyG : ∃ u v : Fin k → ZMod p,
      (u ⬝ᵥ G *ᵥ v) ^ 2 - (u ⬝ᵥ G *ᵥ u) * (v ⬝ᵥ G *ᵥ v) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    -- hcon : ∀ u v, (u ⬝ᵥ G *ᵥ v)^2 - (u ⬝ᵥ G *ᵥ u)*(v ⬝ᵥ G *ᵥ v) = 0
    by_cases hdiag : ∃ u : Fin k → ZMod p, u ⬝ᵥ G *ᵥ u ≠ 0
    · obtain ⟨u, hu⟩ := hdiag
      -- polarization (stated with the literal diagonal form)
      have hpol : ∀ v w : Fin k → ZMod p,
          (u ⬝ᵥ G *ᵥ v) * (u ⬝ᵥ G *ᵥ w) = (u ⬝ᵥ G *ᵥ u) * (v ⬝ᵥ G *ᵥ w) := by
        intro v w
        have hv := hcon u v
        have hw := hcon u w
        have hvw := hcon u (v + w)
        rw [mulVec_add, dotProduct_add, dotProduct_add, add_dotProduct,
          add_dotProduct, hSsymm w v] at hvw
        have h2eq : 2 * ((u ⬝ᵥ G *ᵥ v) * (u ⬝ᵥ G *ᵥ w))
            = 2 * ((u ⬝ᵥ G *ᵥ u) * (v ⬝ᵥ G *ᵥ w)) := by
          linear_combination hvw - hv - hw
        exact mul_left_cancel₀ h2 h2eq
      set cu := u ⬝ᵥ G *ᵥ u with hcu
      set g := G *ᵥ u with hgdef
      have hgi : ∀ i : Fin k, u ⬝ᵥ G *ᵥ Pi.single i (1 : ZMod p) = g i := by
        intro i; rw [hSsymm u (Pi.single i 1), ← hgdef]; simp
      -- extract the rank-one matrix identity
      have hM : ∀ i j : Fin k, g i * g j = cu * G i j := by
        intro i j
        have h := hpol (Pi.single i 1) (Pi.single j 1)
        rw [hgi i, hgi j] at h
        rw [h]
        congr 1
        simp
      -- g ≠ 0
      have hg_ne : g ≠ 0 := by
        intro h
        apply hu
        show cu = 0
        rw [hcu, dotProduct_comm, h, zero_dotProduct]
      obtain ⟨t0, ht0⟩ : ∃ t0, g t0 ≠ 0 := by
        by_contra h; push Not at h; exact hg_ne (funext h)
      haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
      obtain ⟨t1, ht1⟩ := exists_ne t0
      set w0 : Fin k → ZMod p := g t1 • Pi.single t0 (1 : ZMod p) - g t0 • Pi.single t1 (1 : ZMod p)
        with hw0
      have hgw0 : g ⬝ᵥ w0 = 0 := by
        rw [hw0, dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_single,
          dotProduct_single, smul_eq_mul, smul_eq_mul]
        ring
      have hGw0 : G *ᵥ w0 = 0 := by
        funext i
        have hkey0 : cu * ((G *ᵥ w0) i) = 0 := by
          rw [mulVec, dotProduct, Finset.mul_sum]
          have : ∀ j ∈ Finset.univ, cu * (G i j * w0 j) = g i * (g j * w0 j) := by
            intro j _; rw [← mul_assoc, ← hM i j]; ring
          rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
          have : (∑ j, g j * w0 j) = g ⬝ᵥ w0 := rfl
          rw [this, hgw0, mul_zero]
        have := mul_eq_zero.mp hkey0
        rcases this with h | h
        · exact absurd h hu
        · simpa using h
      have hw0ne : w0 ≠ 0 := by
        intro h
        have : w0 t1 = 0 := by rw [h]; rfl
        rw [hw0] at this
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
        rw [Pi.single_eq_of_ne ht1, Pi.single_eq_same] at this
        simp at this
        exact ht0 this
      have : w0 = 0 := by
        have h00 : G *ᵥ w0 = G *ᵥ 0 := by rw [hGw0, mulVec_zero]
        exact mulVec_injective_of_isUnit hGunit h00
      exact hw0ne this
    · push Not at hdiag
      -- every diagonal is zero, so G = 0, contradicting det ≠ 0
      have hGzero : G = 0 := by
        funext i j
        have hij := hcon (Pi.single i 1) (Pi.single j 1)
        rw [hdiag (Pi.single i 1)] at hij
        simp only [zero_mul, sub_zero] at hij
        have : (Pi.single i (1 : ZMod p)) ⬝ᵥ G *ᵥ (Pi.single j 1) = G i j := by simp
        rw [this] at hij
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hij
        simpa using this
      rw [hGzero] at hC
      exact hC (det_zero (Fin.pos_iff_nonempty.mp (by omega)))
  -- convert keyG into the (a,b,c) discriminant form and finish
  obtain ⟨u, v, hkeyG⟩ := keyG
  have hkey : (u ⬝ᵥ C *ᵥ v + v ⬝ᵥ C *ᵥ u) ^ 2
      - 4 * (u ⬝ᵥ C *ᵥ u) * (v ⬝ᵥ C *ᵥ v) ≠ 0 := by
    have e1 := hbG u v
    have e2 := haG u
    have e3 := haG v
    rw [e1, e2, e3] at hkeyG
    intro h; apply hkeyG; linear_combination h
  obtain ⟨X, Y, hXY⟩ := nondegenerate_binary_quad_universal_zmod p hp2
    (u ⬝ᵥ C *ᵥ u) (u ⬝ᵥ C *ᵥ v + v ⬝ᵥ C *ᵥ u) (v ⬝ᵥ C *ᵥ v) hkey ρ
  refine ⟨X • u + Y • v, ?_⟩
  rw [qbridge C (X • u + Y • v), qexpand_smul C u v X Y]
  linear_combination hXY

theorem nondegenerate_affine_quadratic_has_root_general {k : ℕ} (hk : 2 ≤ k)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (C : Matrix (Fin k) (Fin k) (ZMod p))
    (hC : (C + Cᵀ).det ≠ 0) (m : Fin k → ZMod p) (q : ZMod p) :
    ∃ x : Fin k → ZMod p,
      (∑ i, ∑ j, C i j * x i * x j) + (∑ i, m i * x i) + q = 0 := by
  classical
  set G := C + Cᵀ with hG
  have hGdet : IsUnit G.det := isUnit_iff_ne_zero.mpr hC
  set s : Fin k → ZMod p := -(G⁻¹ *ᵥ m) with hs
  have hGs : G *ᵥ s = -m := by
    rw [hs, mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hGdet, Matrix.one_mulVec]
  -- obtain a solution of the homogeneous form via T1
  obtain ⟨y, hy0⟩ := nondegenerate_quadratic_represents_all hk p hp2 C hC
    (-(s ⬝ᵥ C *ᵥ s + (∑ i, m i * s i) + q))
  have hy : y ⬝ᵥ C *ᵥ y = -(s ⬝ᵥ C *ᵥ s + (∑ i, m i * s i) + q) := by
    rw [← qbridge C y]; exact hy0
  -- the cross term cancels the linear part
  have hcrs : y ⬝ᵥ C *ᵥ s + s ⬝ᵥ C *ᵥ y = -(∑ i, m i * y i) := by
    have h1 : y ⬝ᵥ G *ᵥ s = y ⬝ᵥ C *ᵥ s + s ⬝ᵥ C *ᵥ y := by rw [hG]; exact cross_eq C y s
    rw [← h1, hGs, dotProduct_neg, dotProduct_comm]
    rfl
  have hlin : (∑ i, m i * (y + s) i) = (∑ i, m i * y i) + (∑ i, m i * s i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [Pi.add_apply, mul_add]
  refine ⟨y + s, ?_⟩
  rw [qbridge C (y + s), qexpand_add C y s, hlin]
  linear_combination hy + hcrs

end DiophCompression.SemanticQuadraticSingular

#print axioms DiophCompression.SemanticQuadraticSingular.nondegenerate_quadratic_represents_all
#print axioms DiophCompression.SemanticQuadraticSingular.nondegenerate_affine_quadratic_has_root_general
