/-
  MovingPowerRay.lean — Gate-18 research program, Packet B2/B3 for the rank ≥ 2 moving branch.
  ONE good prime p (chosen once, Dirichlet existence only — no density), then the prime-POWER ray
  c_E = c₀ + t₀·(p^E − 1)/b, b c_E + μ = t₀ p^E, E ≥ 1. The witness at level E is the CRT of the old
  modulus t₀ (u ≡ u₀) with p^E, where the mod-p^E root of the moving-remainder polynomial g comes
  from an integral completion of the square G (with D = det(C + Cᵀ)) plus elementary Hensel (B1):
  a level-1 root of G mod p from `nondegenerate_affine_quadratic_has_root_general`, lifted along a
  coordinate direction chosen by the smoothness fact Q(y₁ − y₀) ≡ −W ≢ 0. When W = G(y₀) = 0 the
  vertex y₀ is already a root at every level. The outputs are injective in E with envelope
  |c_E| ≤ (|c₀| + t₀)·p·p^E, hence `ExponentialInjection (movingOutputSet …)` — UNCONDITIONAL:
  no FixedAPPrimeLowerBound, no analytic input.
-/
import ResearchUpgrade.Hensel
import ResearchUpgrade.Shadow.FamilyR

namespace DiophCompression.ResearchUpgrade

open Matrix Polynomial DiophCompression.SemanticQuadraticMatrix DiophCompression.SemanticQuadraticSingular
variable {k : ℕ}

/-! ### The integral completed form `G` of the moving-remainder polynomial

`g(x) := movingRemainderPolyG A B C b l m μ q x = xᵀCx + v·x + w` with `v = b•m − μ•B`,
`w = Aμ² − blμ + b²q`.  Its integral completion of the square (avoiding the inverse of `2C`) is
`G(y) := yᵀCy + D·(v·y) + D²·w`, `D = det(C + Cᵀ)`.  `G(D • x) = D²·g(x)`. -/
def movingCompletedG (C : Matrix (Fin k) (Fin k) ℤ) (D : ℤ) (v : Fin k → ℤ) (w : ℤ)
    (y : Fin k → ℤ) : ℤ :=
  witnessQuad C y + D * (v ⬝ᵥ y) + D ^ 2 * w

/-- The value `W = G(y₀)` at the vertex `y₀ = −(adj(C+Cᵀ) *ᵥ v)`; when `W ≠ 0` it is forced into the
prime modulus so the mod-`p` root is smooth (see `vertex_only_control` for why). -/
def wVertex (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ)
    (μ q : ℤ) : ℤ :=
  movingCompletedG C (C + Cᵀ).det (b • m - μ • B) (A * μ ^ 2 - b * l * μ + b ^ 2 * q)
    (-((C + Cᵀ).adjugate *ᵥ (b • m - μ • B)))

/-- The moving prime-power modulus `M = 2·max(1,|W|)·|D|·b·t₀`, independent of `p`. -/
def movingPowModulusNat (D b t₀ W : ℤ) : ℕ :=
  2 * (max 1 |W|).natAbs * D.natAbs * b.natAbs * t₀.natAbs

/-! ### Helpers re-declared verbatim from the baseline (there `private`), prefix `rb_` -/

theorem rb_dvd_dotProduct_sub (d : ℤ) (a x y : Fin k → ℤ)
    (h : ∀ i, d ∣ x i - y i) : d ∣ a ⬝ᵥ x - a ⬝ᵥ y := by
  have he : a ⬝ᵥ x - a ⬝ᵥ y = ∑ i, a i * (x i - y i) := by
    rw [dotProduct, dotProduct, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [he]
  exact Finset.dvd_sum (fun i _ => (h i).mul_left _)

theorem rb_dvd_witnessQuad_sub (d : ℤ) (C : Matrix (Fin k) (Fin k) ℤ) (x y : Fin k → ℤ)
    (h : ∀ i, d ∣ x i - y i) : d ∣ witnessQuad C x - witnessQuad C y := by
  have he : witnessQuad C x - witnessQuad C y
      = ∑ i, ∑ j, C i j * (x i * (x j - y j) + (x i - y i) * y j) := by
    simp only [witnessQuad, dotProduct, mulVec]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [he]
  refine Finset.dvd_sum (fun i _ => Finset.dvd_sum (fun j _ => ?_))
  exact Dvd.dvd.mul_left (dvd_add ((h j).mul_left _) ((h i).mul_right _)) _

theorem rb_fqM_dvd_sub (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (l : ℤ) (m : Fin k → ℤ) (q : ℤ) (c c₀ : ℤ) (u u₀ : Fin k → ℤ) (d : ℤ)
    (hc : d ∣ c - c₀) (hu : ∀ i, d ∣ u i - u₀ i) :
    d ∣ fqM A B C l m q c u - fqM A B C l m q c₀ u₀ := by
  have he : fqM A B C l m q c u - fqM A B C l m q c₀ u₀
      = A * ((c - c₀) * (c + c₀)) + ((c - c₀) * (B ⬝ᵥ u₀) + c * (B ⬝ᵥ u - B ⬝ᵥ u₀))
        + (witnessQuad C u - witnessQuad C u₀) + l * (c - c₀) + (m ⬝ᵥ u - m ⬝ᵥ u₀) := by
    simp only [fqM]; ring
  rw [he]
  have hBd : d ∣ B ⬝ᵥ u - B ⬝ᵥ u₀ := rb_dvd_dotProduct_sub d B u u₀ hu
  have hmd : d ∣ m ⬝ᵥ u - m ⬝ᵥ u₀ := rb_dvd_dotProduct_sub d m u u₀ hu
  have hWd : d ∣ witnessQuad C u - witnessQuad C u₀ := rb_dvd_witnessQuad_sub d C u u₀ hu
  refine dvd_add (dvd_add (dvd_add (dvd_add ?_ ?_) hWd) ?_) hmd
  · exact Dvd.dvd.mul_left (hc.mul_right _) _
  · exact dvd_add (hc.mul_right _) (hBd.mul_left _)
  · exact hc.mul_left _

theorem rb_mrpG_dvd_sub (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (x x₀ : Fin k → ℤ) (d : ℤ)
    (hx : ∀ i, d ∣ x i - x₀ i) :
    d ∣ movingRemainderPolyG A B C b l m μ q x - movingRemainderPolyG A B C b l m μ q x₀ := by
  have he : movingRemainderPolyG A B C b l m μ q x - movingRemainderPolyG A B C b l m μ q x₀
      = (witnessQuad C x - witnessQuad C x₀)
        + ((b • m - μ • B) ⬝ᵥ x - (b • m - μ • B) ⬝ᵥ x₀) := by
    simp only [movingRemainderPolyG]; ring
  rw [he]
  exact dvd_add (rb_dvd_witnessQuad_sub d C x x₀ hx)
    (rb_dvd_dotProduct_sub d (b • m - μ • B) x x₀ hx)

theorem rb_prime_not_dvd_of_dvd_pred (p : ℕ) (hp : p.Prime) (x : ℤ)
    (hx : x ∣ (p : ℤ) - 1) : ¬ (p : ℤ) ∣ x := by
  intro hc
  have := dvd_trans hc hx
  have h1 : (p : ℤ) ∣ 1 := by
    have := dvd_sub (dvd_refl (p : ℤ)) this; simpa using this
  have := Int.eq_one_of_dvd_one (by positivity) h1
  have := hp.one_lt; omega

theorem rb_isCoprime_prime_of_not_dvd (p : ℕ) (hp : p.Prime) (x : ℤ) (h : ¬ (p : ℤ) ∣ x) :
    IsCoprime (p : ℤ) x :=
  (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr h

/-! ### Bilinear algebra of `witnessQuad` and the four identities for `G` -/

theorem rb_sym_cross (C : Matrix (Fin k) (Fin k) ℤ) (x y : Fin k → ℤ) :
    x ⬝ᵥ C *ᵥ y + y ⬝ᵥ C *ᵥ x = x ⬝ᵥ (C + Cᵀ) *ᵥ y := by
  rw [Matrix.add_mulVec, dotProduct_add]; congr 1
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]

theorem rb_wq_add (C : Matrix (Fin k) (Fin k) ℤ) (x y : Fin k → ℤ) :
    witnessQuad C (x + y) = witnessQuad C x + x ⬝ᵥ (C + Cᵀ) *ᵥ y + witnessQuad C y := by
  unfold witnessQuad
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, ← rb_sym_cross]; ring

theorem rb_Ssym (C : Matrix (Fin k) (Fin k) ℤ) : (C + Cᵀ)ᵀ = C + Cᵀ := by
  rw [transpose_add, transpose_transpose, add_comm]

theorem rb_wq_single (C : Matrix (Fin k) (Fin k) ℤ) (i : Fin k) (t : ℤ) :
    witnessQuad C (Pi.single i t) = t ^ 2 * C i i := by
  unfold witnessQuad
  rw [single_dotProduct]
  have : (C *ᵥ Pi.single i t) i = C i i * t := by simp [mulVec_single, Matrix.col_apply]
  rw [this]; ring

theorem rb_cross_single (C : Matrix (Fin k) (Fin k) ℤ) (y : Fin k → ℤ) (i : Fin k) (t : ℤ) :
    y ⬝ᵥ (C + Cᵀ) *ᵥ (Pi.single i t) = t * ((C + Cᵀ) *ᵥ y) i := by
  rw [dotProduct_mulVec, dotProduct_single, ← mulVec_transpose, rb_Ssym]; ring

theorem rb_movingCompletedG_dvd_sub (C : Matrix (Fin k) (Fin k) ℤ) (D : ℤ) (v : Fin k → ℤ) (w : ℤ)
    (x x₀ : Fin k → ℤ) (d : ℤ) (h : ∀ i, d ∣ x i - x₀ i) :
    d ∣ movingCompletedG C D v w x - movingCompletedG C D v w x₀ := by
  have he : movingCompletedG C D v w x - movingCompletedG C D v w x₀
      = (witnessQuad C x - witnessQuad C x₀) + D * (v ⬝ᵥ x - v ⬝ᵥ x₀) := by
    simp only [movingCompletedG]; ring
  rw [he]
  exact dvd_add (rb_dvd_witnessQuad_sub d C x x₀ h) ((rb_dvd_dotProduct_sub d v x x₀ h).mul_left D)

/-- (i) `G(D • x) = D² · g(x)`. -/
theorem mcG_smul (C : Matrix (Fin k) (Fin k) ℤ) (x : Fin k → ℤ) (D : ℤ) (v : Fin k → ℤ) (w : ℤ) :
    movingCompletedG C D v w (D • x) = D ^ 2 * (witnessQuad C x + v ⬝ᵥ x + w) := by
  unfold movingCompletedG witnessQuad
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]; ring

/-- (ii) `(C+Cᵀ) *ᵥ y₀ = −(D • v)` at the vertex `y₀ = −(adj *ᵥ v)`. -/
theorem mcG_vertex (C : Matrix (Fin k) (Fin k) ℤ) (v : Fin k → ℤ) :
    (C + Cᵀ) *ᵥ (-((C + Cᵀ).adjugate *ᵥ v)) = -((C + Cᵀ).det • v) := by
  rw [mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_adjugate]
  congr 1
  rw [Matrix.smul_mulVec, one_mulVec]

/-- (iii) `G(y) = Q(y − y₀) + G(y₀)` with `Q(z) = zᵀCz`, whenever `(C+Cᵀ) *ᵥ y₀ = −(D • v)`. -/
theorem mcG_center (C : Matrix (Fin k) (Fin k) ℤ) (y y₀ : Fin k → ℤ) (D : ℤ) (v : Fin k → ℤ) (w : ℤ)
    (hS : (C + Cᵀ) *ᵥ y₀ = -(D • v)) :
    movingCompletedG C D v w y = witnessQuad C (y - y₀) + movingCompletedG C D v w y₀ := by
  have hadd := rb_wq_add C (y - y₀) y₀
  rw [sub_add_cancel] at hadd
  rw [hS] at hadd
  unfold movingCompletedG
  rw [hadd, dotProduct_neg, dotProduct_smul, sub_dotProduct]
  rw [dotProduct_comm v y, dotProduct_comm v y₀]
  simp only [smul_eq_mul]; ring

/-- (iv) gradient identity: `G(y + t•e_i) = G(y) + t·((S y + D•v) i) + t²·(C i i)`, `S = C+Cᵀ`. -/
theorem mcG_step (C : Matrix (Fin k) (Fin k) ℤ) (y : Fin k → ℤ) (D : ℤ) (v : Fin k → ℤ) (w : ℤ)
    (i : Fin k) (t : ℤ) :
    movingCompletedG C D v w (y + Pi.single i t)
      = movingCompletedG C D v w y + t * ((C + Cᵀ) *ᵥ y + D • v) i + t ^ 2 * C i i := by
  unfold movingCompletedG
  rw [rb_wq_add, rb_cross_single, rb_wq_single, dotProduct_add, dotProduct_single]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-! ### Root of `G` (hence of `g`) modulo `p^E` -/

/-- General affine quadratic root mod `p` (mirror of `moving_remainder_root_mod_prime_general`). -/
theorem affine_root_mod_prime (hk : 2 ≤ k) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (C : Matrix (Fin k) (Fin k) ℤ) (ν : Fin k → ℤ) (e : ℤ)
    (hC : ¬ (p : ℤ) ∣ (C + Cᵀ).det) :
    ∃ x : Fin k → ℤ, (p : ℤ) ∣ (witnessQuad C x + ν ⬝ᵥ x + e) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Cp : Matrix (Fin k) (Fin k) (ZMod p) := C.map (Int.cast : ℤ → ZMod p) with hCp
  have hdet : (Cp + Cpᵀ).det ≠ 0 := by
    have h1 : Cp + Cpᵀ = (Int.castRingHom (ZMod p)).mapMatrix (C + Cᵀ) := by
      rw [hCp]; ext i j; simp [Matrix.map_apply, Matrix.transpose_apply]
    rw [h1, ← RingHom.map_det]
    intro h0
    exact hC ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0)
  obtain ⟨xp, hxp⟩ := nondegenerate_affine_quadratic_has_root_general hk p hp2 Cp hdet
    (fun i => ((ν i : ℤ) : ZMod p)) ((e : ℤ) : ZMod p)
  set xl : Fin k → ℤ := fun i => ((xp i).val : ℤ) with hxl
  have hlift : ∀ i : Fin k, (((xp i).val : ℕ) : ZMod p) = xp i := by
    intro i; simp [ZMod.natCast_val, ZMod.cast_id]
  refine ⟨xl, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hwq : ((witnessQuad C xl : ℤ) : ZMod p) = ∑ i, ∑ j, Cp i j * xp i * xp j := by
    simp only [witnessQuad, dotProduct, Matrix.mulVec, hxl]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hCp]; simp only [Matrix.map_apply]; rw [hlift i, hlift j]; ring
  have hlin : ((ν ⬝ᵥ xl : ℤ) : ZMod p) = ∑ i, (((ν i) : ℤ) : ZMod p) * xp i := by
    simp only [dotProduct, hxl]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hlift i]
  have key : ((witnessQuad C xl + ν ⬝ᵥ xl + e : ℤ) : ZMod p)
      = (∑ i, ∑ j, Cp i j * xp i * xp j) + (∑ i, (((ν i) : ℤ) : ZMod p) * xp i)
        + ((e : ℤ) : ZMod p) := by
    push_cast [hwq, hlin]; ring
  rw [key]; exact hxp

theorem rb_wq_dvd_of_forall (p : ℤ) (C : Matrix (Fin k) (Fin k) ℤ) (z : Fin k → ℤ)
    (h : ∀ i, p ∣ z i) : p ∣ witnessQuad C z := by
  have he : witnessQuad C z = ∑ i, ∑ j, C i j * (z i * z j) := by
    simp only [witnessQuad, dotProduct, mulVec]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [he]
  exact Finset.dvd_sum (fun i _ => Finset.dvd_sum (fun j _ => ((h i).mul_right _).mul_left _))

theorem rb_adj_S_mulVec (C : Matrix (Fin k) (Fin k) ℤ) (z : Fin k → ℤ) :
    (C + Cᵀ).adjugate *ᵥ ((C + Cᵀ) *ᵥ z) = (C + Cᵀ).det • z := by
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, one_mulVec]

/-- Smoothness: if `p ∤ det(C+Cᵀ)` and `p ∤ Q(z)` then some coordinate of `(C+Cᵀ) *ᵥ z` is a unit. -/
theorem exists_index_not_dvd (p : ℕ) (hp : p.Prime) (C : Matrix (Fin k) (Fin k) ℤ) (z : Fin k → ℤ)
    (hD : ¬ (p : ℤ) ∣ (C + Cᵀ).det) (hz : ¬ (p : ℤ) ∣ witnessQuad C z) :
    ∃ i, ¬ (p : ℤ) ∣ ((C + Cᵀ) *ᵥ z) i := by
  by_contra hcon
  push Not at hcon
  have hDz : ∀ i, (p : ℤ) ∣ (C + Cᵀ).det * z i := by
    intro i
    have h1 : ((C + Cᵀ).det • z) i = ((C + Cᵀ).adjugate *ᵥ ((C + Cᵀ) *ᵥ z)) i := by
      rw [rb_adj_S_mulVec]
    have h2 : ((C + Cᵀ).adjugate *ᵥ ((C + Cᵀ) *ᵥ z)) i
        = ∑ j, (C + Cᵀ).adjugate i j * ((C + Cᵀ) *ᵥ z) j := by simp [mulVec, dotProduct]
    have h3 : (p : ℤ) ∣ ∑ j, (C + Cᵀ).adjugate i j * ((C + Cᵀ) *ᵥ z) j :=
      Finset.dvd_sum (fun j _ => (hcon j).mul_left _)
    have h4 : ((C + Cᵀ).det • z) i = (C + Cᵀ).det * z i := by simp [Pi.smul_apply]
    rw [h4] at h1; rw [h1, h2]; exact h3
  have hzi : ∀ i, (p : ℤ) ∣ z i := by
    intro i
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpp.dvd_mul.mp (hDz i) with h | h
    · exact absurd h hD
    · exact h
  exact hz (rb_wq_dvd_of_forall (p : ℤ) C z hzi)

/-- From a completed root `p^E ∣ G(y)` to a `g`-root: invert `D` modulo `p^E` and use
`G(D • x) = D² g(x)`. -/
theorem g_root_of_completedG_root (p : ℕ) (hp : p.Prime) (E : ℕ)
    (C : Matrix (Fin k) (Fin k) ℤ) (D : ℤ) (v : Fin k → ℤ) (w : ℤ) (hpD : ¬ (p : ℤ) ∣ D)
    (y : Fin k → ℤ) (hy : (p : ℤ) ^ E ∣ movingCompletedG C D v w y) :
    ∃ x : Fin k → ℤ, (p : ℤ) ^ E ∣ (witnessQuad C x + v ⬝ᵥ x + w) := by
  obtain ⟨d, ε, hde⟩ := (rb_isCoprime_prime_of_not_dvd p hp D hpD).symm.pow_right (n := E)
  refine ⟨d • y, ?_⟩
  have hcong : ∀ i, (p : ℤ) ^ E ∣ (D • (d • y)) i - y i := by
    intro i
    refine ⟨-ε * y i, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (y i) * hde
  have hsub := rb_movingCompletedG_dvd_sub C D v w (D • (d • y)) y ((p : ℤ) ^ E) hcong
  have h2 : (p : ℤ) ^ E ∣ movingCompletedG C D v w (D • (d • y)) := by
    have := dvd_add hy hsub; simpa using this
  rw [mcG_smul] at h2
  have hcop2 : IsCoprime ((p : ℤ) ^ E) (D ^ 2) :=
    ((rb_isCoprime_prime_of_not_dvd p hp D hpD).pow_left).pow_right
  exact hcop2.dvd_of_dvd_mul_left h2

/-- The mod-`p^E` root of the moving-remainder polynomial `g` for a good prime `p`
(`p ≠ 2`, `p ∤ D`, and `p ∤ W` when `W ≠ 0`). The polynomial `g` does not depend on `c`. -/
theorem moving_g_root_pow (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpD : ¬ (p : ℤ) ∣ (C + Cᵀ).det)
    (hpW : wVertex A B C b l m μ q ≠ 0 → ¬ (p : ℤ) ∣ wVertex A B C b l m μ q)
    (E : ℕ) (hE : 1 ≤ E) :
    ∃ x : Fin k → ℤ, (p : ℤ) ^ E ∣ movingRemainderPolyG A B C b l m μ q x := by
  haveI := Fact.mk hp
  set D := (C + Cᵀ).det with hDdef
  set v : Fin k → ℤ := b • m - μ • B with hvdef
  set w : ℤ := A * μ ^ 2 - b * l * μ + b ^ 2 * q with hwdef
  set y₀ : Fin k → ℤ := -((C + Cᵀ).adjugate *ᵥ v) with hy₀def
  have hWeq : movingCompletedG C D v w y₀ = wVertex A B C b l m μ q := rfl
  have hS : (C + Cᵀ) *ᵥ y₀ = -(D • v) := mcG_vertex C v
  -- always produce a completed root `p^E ∣ G(y)`
  have hmain : ∃ y : Fin k → ℤ, (p : ℤ) ^ E ∣ movingCompletedG C D v w y := by
    by_cases hW : wVertex A B C b l m μ q = 0
    · exact ⟨y₀, by rw [hWeq, hW]; exact dvd_zero _⟩
    · have hpWne : ¬ (p : ℤ) ∣ movingCompletedG C D v w y₀ := by rw [hWeq]; exact hpW hW
      -- level-1 root of G mod p
      obtain ⟨y₁, hy₁0⟩ := affine_root_mod_prime hk p hp hp2 C (D • v) (D ^ 2 * w) hpD
      have hy₁ : (p : ℤ) ∣ movingCompletedG C D v w y₁ := by
        have heq : witnessQuad C y₁ + (D • v) ⬝ᵥ y₁ + D ^ 2 * w = movingCompletedG C D v w y₁ := by
          simp only [movingCompletedG, smul_dotProduct, smul_eq_mul]
        rw [← heq]; exact hy₁0
      -- smoothness
      have hcenter := mcG_center C y₁ y₀ D v w hS
      have hpwq : ¬ (p : ℤ) ∣ witnessQuad C (y₁ - y₀) := by
        have hwq : witnessQuad C (y₁ - y₀) = movingCompletedG C D v w y₁
            - movingCompletedG C D v w y₀ := by rw [hcenter]; ring
        rw [hwq]; intro hc; apply hpWne
        have := dvd_sub hy₁ hc; simpa using this
      obtain ⟨i, hi⟩ := exists_index_not_dvd p hp C (y₁ - y₀) hpD hpwq
      have hLeq : (C + Cᵀ) *ᵥ (y₁ - y₀) = (C + Cᵀ) *ᵥ y₁ + D • v := by
        rw [Matrix.mulVec_sub, hS, sub_neg_eq_add]
      have hLnd : ¬ (p : ℤ) ∣ ((C + Cᵀ) *ᵥ y₁ + D • v) i := by rw [← hLeq]; exact hi
      -- Hensel along e_i
      set f : ℤ[X] := Polynomial.C (movingCompletedG C D v w y₁)
        + Polynomial.C (((C + Cᵀ) *ᵥ y₁ + D • v) i) * X + Polynomial.C (C i i) * X ^ 2 with hf
      have hev : ∀ t, f.eval t = movingCompletedG C D v w (y₁ + Pi.single i t) := by
        intro t
        rw [mcG_step C y₁ D v w i t]
        simp only [hf, eval_add, eval_mul, eval_pow, eval_C, eval_X]; ring
      have hev0 : f.eval 0 = movingCompletedG C D v w y₁ := by
        rw [hev]; rw [Pi.single_zero, add_zero]
      have hderiv : f.derivative.eval 0 = ((C + Cᵀ) *ᵥ y₁ + D • v) i := by
        simp [hf, derivative_add, derivative_mul, derivative_C, derivative_X,
          eval_add, eval_mul, eval_C, eval_X]
      obtain ⟨tE, htE, -⟩ := hensel_lift f p hp 0 (by rw [hev0]; exact hy₁)
        (by rw [hderiv]; exact hLnd) E hE
      exact ⟨y₁ + Pi.single i tE, by rw [← hev tE]; exact htE⟩
  obtain ⟨y, hy⟩ := hmain
  obtain ⟨x, hx⟩ := g_root_of_completedG_root p hp E C D v w hpD y hy
  exact ⟨x, hx⟩

/-! ### Good-prime facts for the prime-power modulus -/

/-- For any prime `p ≡ 1 (mod M)` with `M = 2·max(1,|W|)·|D|·b·t₀`:
`b ∣ p−1`, `t₀ ∣ p−1`, `p ∤ b`, `p ∤ t₀`, `p ≠ 2`, `p ∤ D`, and `p ∤ W` when `W ≠ 0`. -/
theorem powGoodPrime_facts (D b t₀ W : ℤ) (hD : D ≠ 0) (hb : 0 < b) (ht₀ : 0 < t₀)
    (p : ℕ) (hp : p.Prime) (hpmod : p ≡ 1 [MOD movingPowModulusNat D b t₀ W]) :
    b ∣ (p : ℤ) - 1 ∧ t₀ ∣ (p : ℤ) - 1 ∧ ¬ (p : ℤ) ∣ b ∧ ¬ (p : ℤ) ∣ t₀ ∧ p ≠ 2 ∧
      ¬ (p : ℤ) ∣ D ∧ (W ≠ 0 → ¬ (p : ℤ) ∣ W) := by
  have hmax1 : (1 : ℤ) ≤ max 1 |W| := le_max_left _ _
  have hmaxnn : (0 : ℤ) ≤ max 1 |W| := by linarith
  have hMcast : (movingPowModulusNat D b t₀ W : ℤ) = 2 * (max 1 |W|) * |D| * b * t₀ := by
    unfold movingPowModulusNat; push_cast
    rw [abs_of_pos hb, abs_of_pos ht₀, abs_of_nonneg hmaxnn]
  have hMdvd : (movingPowModulusNat D b t₀ W : ℤ) ∣ (p : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd' (by have := hp.one_lt; omega : 1 ≤ p)).mp hpmod.symm
    have h' := Int.natCast_dvd_natCast.mpr h
    rwa [Nat.cast_sub (by have := hp.one_lt; omega), Nat.cast_one] at h'
  have hbdvd : b ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd; rw [hMcast]; exact ⟨2 * max 1 |W| * |D| * t₀, by ring⟩
  have ht₀dvd : t₀ ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd; rw [hMcast]; exact ⟨2 * max 1 |W| * |D| * b, by ring⟩
  have h2dvd : (2 : ℤ) ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd; rw [hMcast]; exact ⟨max 1 |W| * |D| * b * t₀, by ring⟩
  have hDdvd : D ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact (self_dvd_abs D).trans ⟨2 * max 1 |W| * b * t₀, by ring⟩
  have hp2' : ¬ (p : ℤ) ∣ 2 := rb_prime_not_dvd_of_dvd_pred p hp 2 h2dvd
  refine ⟨hbdvd, ht₀dvd, rb_prime_not_dvd_of_dvd_pred p hp b hbdvd,
    rb_prime_not_dvd_of_dvd_pred p hp t₀ ht₀dvd, ?_,
    rb_prime_not_dvd_of_dvd_pred p hp D hDdvd, ?_⟩
  · intro h; apply hp2'; rw [h]; norm_num
  · intro hW
    apply rb_prime_not_dvd_of_dvd_pred p hp W
    refine dvd_trans ?_ hMdvd
    rw [hMcast, show max 1 |W| = |W| from max_eq_right (Int.one_le_abs hW)]
    exact (self_dvd_abs W).trans ⟨2 * |D| * b * t₀, by ring⟩

/-! ### The level-`E` witness (copy of `moving_modulus_prime_step_allGoodPrime`, `p ↦ p^E`) -/

/-- Level-`E` witness: given the good prime facts, a level `E ≥ 1`, and `c` with
`b c + μ = t₀ p^E` and `t₀ ∣ c − c₀`, there is a witness `u` with `(b c + μ) ∣ fqM(c, u)`. -/
theorem moving_level_witness (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q c₀ : ℤ) (u₀ : Fin k → ℤ) (hb : 0 < b) (hN : (C + Cᵀ).det ≠ 0)
    (ht₀ : 0 < b * c₀ + μ) (hdiv : (b * c₀ + μ) ∣ fqM A B C l m q c₀ u₀)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpb : ¬ (p : ℤ) ∣ b) (hpt₀ : ¬ (p : ℤ) ∣ b * c₀ + μ)
    (hpD : ¬ (p : ℤ) ∣ (C + Cᵀ).det)
    (hpW : wVertex A B C b l m μ q ≠ 0 → ¬ (p : ℤ) ∣ wVertex A B C b l m μ q)
    (E : ℕ) (hE : 1 ≤ E) (c : ℤ) (hc : b * c + μ = (b * c₀ + μ) * (p : ℤ) ^ E)
    (hcc : (b * c₀ + μ) ∣ c - c₀) :
    ∃ u : Fin k → ℤ, (b * c + μ) ∣ fqM A B C l m q c u := by
  set t₀ := b * c₀ + μ with ht₀def
  set pn : ℤ := (p : ℤ) ^ E with hpndef
  obtain ⟨x, hx⟩ := moving_g_root_pow hk A B C b l m μ q p hp hp2 hpD hpW E hE
  -- CRT data
  obtain ⟨α, β, hαβ⟩ := (rb_isCoprime_prime_of_not_dvd p hp b hpb).symm.pow_right (n := E)
  obtain ⟨a', b', hab⟩ := (rb_isCoprime_prime_of_not_dvd p hp t₀ hpt₀).symm.pow_right (n := E)
  set u : Fin k → ℤ := fun i => (α * x i) * (a' * t₀) + u₀ i * (b' * pn) with hudef
  have hui : ∀ i, u i = (α * x i) * (a' * t₀) + u₀ i * (b' * pn) := fun i => rfl
  have hu₀ : ∀ i, t₀ ∣ u i - u₀ i := fun i =>
    ⟨a' * (α * x i - u₀ i), by rw [hui]; linear_combination (u₀ i) * hab⟩
  have hup' : ∀ i, pn ∣ u i - α * x i := fun i =>
    ⟨b' * (u₀ i - α * x i), by rw [hui]; linear_combination (α * x i) * hab⟩
  have hbup : ∀ i, pn ∣ b * (α * x i) - x i := fun i =>
    ⟨-(β * x i), by linear_combination (x i) * hαβ⟩
  have hx' : ∀ i, pn ∣ (b • u) i - x i := by
    intro i
    have e : (b • u) i - x i = b * (u i - α * x i) + (b * (α * x i) - x i) := by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]; exact dvd_add ((hup' i).mul_left b) (hbup i)
  refine ⟨u, ?_⟩
  rw [hc]
  apply IsCoprime.mul_dvd ⟨a', b', hab⟩
  · have := dvd_add hdiv (rb_fqM_dvd_sub A B C l m q c c₀ u u₀ t₀ hcc hu₀)
    simpa using this
  · have hpR : pn ∣ movingRemainderPolyG A B C b l m μ q (b • u) := by
      have := dvd_add hx (rb_mrpG_dvd_sub A B C b l m μ q (b • u) x pn hx')
      simpa using this
    have hpt : pn ∣ b * c + μ := ⟨t₀, by rw [hc]; ring⟩
    have hpb2 : pn ∣ b ^ 2 * fqM A B C l m q c u := by
      rw [moving_remainder_identity_general A B C b l m μ q c u]
      exact dvd_add hpR (hpt.mul_right _)
    have hcopb : IsCoprime pn b := (rb_isCoprime_prime_of_not_dvd p hp b hpb).pow_left
    exact (hcopb.pow_right).dvd_of_dvd_mul_left hpb2

/-! ### B2/B3: the prime-power ray gives an exponential injection, unconditionally -/

/-- B2/B3 (rank ≥ 2 moving branch): one good prime, then the prime-power ray
`c_E = c₀ + t₀·(p^E − 1)/b` produces an injective exponential family inside `movingOutputSet`. -/
theorem moving_exponentialInjection (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q c₀ : ℤ) (u₀ : Fin k → ℤ)
    (hb : 0 < b) (hN : (C + Cᵀ).det ≠ 0) (ht₀ : 0 < b * c₀ + μ)
    (hdiv : (b * c₀ + μ) ∣ fqM A B C l m q c₀ u₀) :
    ExponentialInjection (movingOutputSet A B C b l m μ q) := by
  set t₀ := b * c₀ + μ with ht₀def
  set D := (C + Cᵀ).det with hDdef
  set W := wVertex A B C b l m μ q with hWdef
  set Mn : ℕ := movingPowModulusNat D b t₀ W with hMn
  have hM0 : Mn ≠ 0 := by
    rw [hMn]; unfold movingPowModulusNat
    have h1 : (max 1 |W|).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (by have := le_max_left 1 |W|; omega)
    have h2 : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hN
    have h3 : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb.ne'
    have h4 : t₀.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht₀.ne'
    positivity
  obtain ⟨p, hp, hpM, hpmod⟩ := Nat.exists_prime_gt_modEq_one Mn hM0
  haveI := Fact.mk hp
  obtain ⟨hbdvd, ht₀dvd, hpb, hpt₀, hp2, hpD, hpW⟩ :=
    powGoodPrime_facts D b t₀ W hN hb ht₀ p hp (hMn ▸ hpmod)
  have hpow : ∀ E : ℕ, b ∣ (p : ℤ) ^ E - 1 := fun E =>
    hbdvd.trans (by simpa using sub_dvd_pow_sub_pow (p : ℤ) 1 E)
  set g : ℕ → ℤ := fun e => c₀ + t₀ * (((p : ℤ) ^ (e + 1) - 1) / b) with hg
  have hmod : ∀ e, b * g e + μ = t₀ * (p : ℤ) ^ (e + 1) := by
    intro e
    obtain ⟨j, hj⟩ := hpow (e + 1)
    have : ((p : ℤ) ^ (e + 1) - 1) / b = j := by rw [hj]; exact Int.mul_ediv_cancel_left j hb.ne'
    simp only [hg]; rw [this]; linear_combination (-t₀) * hj - ht₀def
  have hpR : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  have hjpos : ∀ e, 0 ≤ ((p : ℤ) ^ (e + 1) - 1) / b := fun e =>
    Int.ediv_nonneg (by have := one_le_pow₀ (n := e + 1) hpR.le; linarith) hb.le
  refine ⟨((|c₀| + t₀) * p).toNat, p, g, ?_, hp.two_le, ?_, ?_, ?_⟩
  · have : (1 : ℤ) ≤ (|c₀| + t₀) * p := by nlinarith [abs_nonneg c₀]
    have h' : (1 : ℤ) ≤ ((|c₀| + t₀) * p).toNat := by
      rw [Int.toNat_of_nonneg (by linarith)]; exact this
    exact_mod_cast h'
  · intro e e' h
    have h1 := hmod e; have h2 := hmod e'
    rw [h] at h1
    have : (p : ℤ) ^ (e + 1) = (p : ℤ) ^ (e' + 1) := by
      have := h1.symm.trans h2; exact mul_left_cancel₀ ht₀.ne' this
    have := pow_right_injective₀ (by positivity) (ne_of_gt hpR) this
    omega
  · intro e
    have hE : 1 ≤ e + 1 := by omega
    have hcc : t₀ ∣ g e - c₀ := ⟨((p : ℤ) ^ (e + 1) - 1) / b, by rw [hg]; ring⟩
    obtain ⟨u, hu⟩ := moving_level_witness hk A B C b l m μ q c₀ u₀ hb hN ht₀ hdiv p hp hp2 hpb
      hpt₀ hpD hpW (e + 1) hE (g e) (by rw [hmod e]) hcc
    exact ⟨u, hu⟩
  · intro e
    have hj := hjpos e
    have hjle : ((p : ℤ) ^ (e + 1) - 1) / b ≤ (p : ℤ) ^ (e + 1) := by
      have h1 : ((p : ℤ) ^ (e + 1) - 1) / b ≤ (p : ℤ) ^ (e + 1) - 1 :=
        Int.ediv_le_self _ (by have := one_le_pow₀ (n := e + 1) hpR.le; linarith)
      linarith
    have hA : (((|c₀| + t₀) * p).toNat : ℤ) = (|c₀| + t₀) * p := Int.toNat_of_nonneg (by positivity)
    rw [hA]
    have hge : |g e| ≤ |c₀| + t₀ * (p : ℤ) ^ (e + 1) := by
      calc |g e| = |c₀ + t₀ * (((p : ℤ) ^ (e + 1) - 1) / b)| := rfl
        _ ≤ |c₀| + |t₀ * (((p : ℤ) ^ (e + 1) - 1) / b)| := abs_add_le _ _
        _ = |c₀| + t₀ * (((p : ℤ) ^ (e + 1) - 1) / b) := by
            rw [abs_of_nonneg (mul_nonneg ht₀.le hj)]
        _ ≤ |c₀| + t₀ * (p : ℤ) ^ (e + 1) := by nlinarith
    have hpe : (1 : ℤ) ≤ (p : ℤ) ^ (e + 1) := one_le_pow₀ hpR.le
    calc |g e| ≤ |c₀| + t₀ * (p : ℤ) ^ (e + 1) := hge
      _ ≤ (|c₀| + t₀) * (p : ℤ) ^ (e + 1) := by nlinarith [abs_nonneg c₀, hpe]
      _ = (|c₀| + t₀) * p * (p : ℤ) ^ e := by ring

/-- The same exponential injection landing in the ℕ-fibre `castSet (fiberSetSG …)`, with `(c₀ : ℕ)`
so that every ray output is `≥ c₀ ≥ 0`. -/
theorem moving_exponentialInjection_castSet (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (c₀ : ℕ) (u₀ : Fin k → ℤ)
    (hb : 0 < b) (hN : (C + Cᵀ).det ≠ 0) (ht₀ : 0 < b * (c₀ : ℤ) + μ)
    (hdiv : (b * (c₀ : ℤ) + μ) ∣ fqM A B C l m q (c₀ : ℤ) u₀) :
    ExponentialInjection (castSet (fiberSetSG A B C b l m μ q)) := by
  set t₀ := b * (c₀ : ℤ) + μ with ht₀def
  set D := (C + Cᵀ).det with hDdef
  set W := wVertex A B C b l m μ q with hWdef
  set Mn : ℕ := movingPowModulusNat D b t₀ W with hMn
  have hM0 : Mn ≠ 0 := by
    rw [hMn]; unfold movingPowModulusNat
    have h1 : (max 1 |W|).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (by have := le_max_left 1 |W|; omega)
    have h2 : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hN
    have h3 : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb.ne'
    have h4 : t₀.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht₀.ne'
    positivity
  obtain ⟨p, hp, hpM, hpmod⟩ := Nat.exists_prime_gt_modEq_one Mn hM0
  haveI := Fact.mk hp
  obtain ⟨hbdvd, ht₀dvd, hpb, hpt₀, hp2, hpD, hpW⟩ :=
    powGoodPrime_facts D b t₀ W hN hb ht₀ p hp (hMn ▸ hpmod)
  have hpow : ∀ E : ℕ, b ∣ (p : ℤ) ^ E - 1 := fun E =>
    hbdvd.trans (by simpa using sub_dvd_pow_sub_pow (p : ℤ) 1 E)
  set g : ℕ → ℤ := fun e => (c₀ : ℤ) + t₀ * (((p : ℤ) ^ (e + 1) - 1) / b) with hg
  have hmod : ∀ e, b * g e + μ = t₀ * (p : ℤ) ^ (e + 1) := by
    intro e
    obtain ⟨j, hj⟩ := hpow (e + 1)
    have : ((p : ℤ) ^ (e + 1) - 1) / b = j := by rw [hj]; exact Int.mul_ediv_cancel_left j hb.ne'
    simp only [hg]; rw [this]; linear_combination (-t₀) * hj - ht₀def
  have hpR : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  have hjpos : ∀ e, 0 ≤ ((p : ℤ) ^ (e + 1) - 1) / b := fun e =>
    Int.ediv_nonneg (by have := one_le_pow₀ (n := e + 1) hpR.le; linarith) hb.le
  have hgnn : ∀ e, 0 ≤ g e := fun e => by
    rw [hg]; have := hjpos e; positivity
  refine ⟨((|(c₀ : ℤ)| + t₀) * p).toNat, p, g, ?_, hp.two_le, ?_, ?_, ?_⟩
  · have : (1 : ℤ) ≤ (|(c₀ : ℤ)| + t₀) * p := by nlinarith [abs_nonneg (c₀ : ℤ)]
    have h' : (1 : ℤ) ≤ ((|(c₀ : ℤ)| + t₀) * p).toNat := by
      rw [Int.toNat_of_nonneg (by linarith)]; exact this
    exact_mod_cast h'
  · intro e e' h
    have h1 := hmod e; have h2 := hmod e'
    rw [h] at h1
    have : (p : ℤ) ^ (e + 1) = (p : ℤ) ^ (e' + 1) := by
      have := h1.symm.trans h2; exact mul_left_cancel₀ ht₀.ne' this
    have := pow_right_injective₀ (by positivity) (ne_of_gt hpR) this
    omega
  · intro e
    have hE : 1 ≤ e + 1 := by omega
    have hcc : t₀ ∣ g e - (c₀ : ℤ) := ⟨((p : ℤ) ^ (e + 1) - 1) / b, by rw [hg]; ring⟩
    obtain ⟨u, hu⟩ := moving_level_witness hk A B C b l m μ q (c₀ : ℤ) u₀ hb hN ht₀ hdiv p hp hp2
      hpb hpt₀ hpD hpW (e + 1) hE (g e) (by rw [hmod e]) hcc
    refine ⟨(g e).toNat, ?_, Int.toNat_of_nonneg (hgnn e)⟩
    apply mem_fiberSetSG_of_dvd A B C b l m μ q (g e).toNat u
    rw [Int.toNat_of_nonneg (hgnn e)]; exact hu
  · intro e
    have hj := hjpos e
    have hjle : ((p : ℤ) ^ (e + 1) - 1) / b ≤ (p : ℤ) ^ (e + 1) := by
      have h1 : ((p : ℤ) ^ (e + 1) - 1) / b ≤ (p : ℤ) ^ (e + 1) - 1 :=
        Int.ediv_le_self _ (by have := one_le_pow₀ (n := e + 1) hpR.le; linarith)
      linarith
    have hA : (((|(c₀ : ℤ)| + t₀) * p).toNat : ℤ) = (|(c₀ : ℤ)| + t₀) * p :=
      Int.toNat_of_nonneg (by positivity)
    rw [hA]
    have hge : |g e| ≤ |(c₀ : ℤ)| + t₀ * (p : ℤ) ^ (e + 1) := by
      calc |g e| = |(c₀ : ℤ) + t₀ * (((p : ℤ) ^ (e + 1) - 1) / b)| := rfl
        _ ≤ |(c₀ : ℤ)| + |t₀ * (((p : ℤ) ^ (e + 1) - 1) / b)| := abs_add_le _ _
        _ = |(c₀ : ℤ)| + t₀ * (((p : ℤ) ^ (e + 1) - 1) / b) := by
            rw [abs_of_nonneg (mul_nonneg ht₀.le hj)]
        _ ≤ |(c₀ : ℤ)| + t₀ * (p : ℤ) ^ (e + 1) := by nlinarith
    have hpe : (1 : ℤ) ≤ (p : ℤ) ^ (e + 1) := one_le_pow₀ hpR.le
    calc |g e| ≤ |(c₀ : ℤ)| + t₀ * (p : ℤ) ^ (e + 1) := hge
      _ ≤ (|(c₀ : ℤ)| + t₀) * (p : ℤ) ^ (e + 1) := by nlinarith [abs_nonneg (c₀ : ℤ), hpe]
      _ = (|(c₀ : ℤ)| + t₀) * p * (p : ℤ) ^ e := by ring

/-! ### Negative control: for `Q = x² + y²`, the only mod-3 root of `W ≡ 0` is the singular vertex -/

/-- For the isotropic-looking form `Q = x² + y²` over `𝔽₃`, the only zero is the vertex `(0,0)`:
when `W ≡ 0 (mod p)` the mod-`p` root of the completed quadratic is forced to the singular vertex,
which lifts to no smooth Hensel step. Forcing `p ∤ W` (when `W ≠ 0`) into the modulus sidesteps this. -/
theorem vertex_only_control : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide

end DiophCompression.ResearchUpgrade
