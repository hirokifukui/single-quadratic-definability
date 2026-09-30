/-
  MovingModulusGeneral.lean — r11 (GPT r10 必須J): the moving-modulus machinery in the general
  matrix vocabulary. Statements frozen in MovingModulusGeneral_STATEMENTS.lean (md5 bf43635d)
  before proofs. J1/J2 produced directly by claude.ai (probes, verbatim); J3/J4 by Claude Code
  job s11_mmg (2026-08-28), independently re-verified by claude.ai (kernel EXIT=0, all four
  theorems std-3, statements verbatim vs freeze, full re-reading incl. the r10 line-by-line
  correspondence of the prime step and the CRT coefficient identities).
-/
import DiophCompression.SemanticQuadraticSingular.DefsSingularGeneral
import DiophCompression.PeriodicProgressionCore
import DiophCompression.SemanticQuadraticSingular.FiniteFieldQuadratic
import DiophCompression.SemanticQuadraticSingular.FiniteFieldQuadraticGeneral
import DiophCompression.SemanticQuadraticSingular.QuotientRankZero
import DiophCompression.SemanticQuadraticMatrix.FullRankAssemblyData

namespace DiophCompression.SemanticQuadraticSingular
open Matrix DiophCompression.SemanticQuadraticMatrix
open DiophCompression.SemanticQuadraticTwoWitness (periodic_infinite_or_empty)
variable {k : ℕ}

def movingRemainderPolyG (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (x : Fin k → ℤ) : ℤ :=
  witnessQuad C x + ((b • m - μ • B) ⬝ᵥ x) + (A * μ ^ 2 - b * l * μ + b ^ 2 * q)

-- J1 (probe_J1, verbatim)
theorem moving_remainder_identity_general (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q c : ℤ) (u : Fin k → ℤ) :
    b ^ 2 * fqM A B C l m q c u =
      movingRemainderPolyG A B C b l m μ q (b • u)
        + (b * c + μ) * (A * (b * c - μ) + b * (B ⬝ᵥ u) + b * l) := by
  simp only [movingRemainderPolyG, fqM, witnessQuad, Matrix.mulVec_smul, dotProduct_smul,
    smul_dotProduct, sub_dotProduct, smul_eq_mul]
  ring

-- J2 (probe_J2, verbatim)
theorem moving_remainder_root_mod_prime_general (hk : 2 ≤ k) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ)
    (hC : ¬ (p : ℤ) ∣ (C + Cᵀ).det) :
    ∃ x : Fin k → ℤ, (p : ℤ) ∣ movingRemainderPolyG A B C b l m μ q x := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Cp : Matrix (Fin k) (Fin k) (ZMod p) := C.map (Int.cast : ℤ → ZMod p) with hCp
  have hdet : (Cp + Cpᵀ).det ≠ 0 := by
    have h1 : Cp + Cpᵀ = (Int.castRingHom (ZMod p)).mapMatrix (C + Cᵀ) := by
      rw [hCp]
      ext i j
      simp [Matrix.map_apply, Matrix.transpose_apply]
    rw [h1, ← RingHom.map_det]
    intro h0
    exact hC ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0)
  obtain ⟨xp, hxp⟩ := nondegenerate_affine_quadratic_has_root_general hk p hp2 Cp hdet
    (fun i => (((b • m - μ • B) i : ℤ) : ZMod p))
    ((A * μ ^ 2 - b * l * μ + b ^ 2 * q : ℤ) : ZMod p)
  set xl : Fin k → ℤ := fun i => ((xp i).val : ℤ) with hxl
  have hlift : ∀ i : Fin k, (((xp i).val : ℕ) : ZMod p) = xp i := by
    intro i
    simp [ZMod.natCast_val, ZMod.cast_id]
  refine ⟨xl, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hwq : ((witnessQuad C xl : ℤ) : ZMod p) = ∑ i, ∑ j, Cp i j * xp i * xp j := by
    simp only [witnessQuad, dotProduct, Matrix.mulVec, hxl]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hCp]
    simp only [Matrix.map_apply]
    rw [hlift i, hlift j]
    ring
  have hlin : (((b • m - μ • B) ⬝ᵥ xl : ℤ) : ZMod p)
      = ∑ i, (((b • m - μ • B) i : ℤ) : ZMod p) * xp i := by
    simp only [dotProduct, hxl]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hlift i]
  have key : ((movingRemainderPolyG A B C b l m μ q xl : ℤ) : ZMod p)
      = (∑ i, ∑ j, Cp i j * xp i * xp j)
        + (∑ i, (((b • m - μ • B) i : ℤ) : ZMod p) * xp i)
        + ((A * μ ^ 2 - b * l * μ + b ^ 2 * q : ℤ) : ZMod p) := by
    rw [movingRemainderPolyG]
    push_cast [hwq, hlin]
    ring
  rw [key]
  exact hxp

/-! ## J3 helper lemmas (k-variable difference / congruence transport) -/

private theorem aux_dvd_dotProduct_sub (d : ℤ) (a x y : Fin k → ℤ)
    (h : ∀ i, d ∣ x i - y i) : d ∣ a ⬝ᵥ x - a ⬝ᵥ y := by
  have he : a ⬝ᵥ x - a ⬝ᵥ y = ∑ i, a i * (x i - y i) := by
    rw [dotProduct, dotProduct, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [he]
  exact Finset.dvd_sum (fun i _ => (h i).mul_left _)

private theorem aux_dvd_witnessQuad_sub (d : ℤ) (C : Matrix (Fin k) (Fin k) ℤ) (x y : Fin k → ℤ)
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

private theorem aux_fqM_dvd_sub (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (l : ℤ) (m : Fin k → ℤ) (q : ℤ) (c c₀ : ℤ) (u u₀ : Fin k → ℤ) (d : ℤ)
    (hc : d ∣ c - c₀) (hu : ∀ i, d ∣ u i - u₀ i) :
    d ∣ fqM A B C l m q c u - fqM A B C l m q c₀ u₀ := by
  have he : fqM A B C l m q c u - fqM A B C l m q c₀ u₀
      = A * ((c - c₀) * (c + c₀)) + ((c - c₀) * (B ⬝ᵥ u₀) + c * (B ⬝ᵥ u - B ⬝ᵥ u₀))
        + (witnessQuad C u - witnessQuad C u₀) + l * (c - c₀) + (m ⬝ᵥ u - m ⬝ᵥ u₀) := by
    simp only [fqM]; ring
  rw [he]
  have hBd : d ∣ B ⬝ᵥ u - B ⬝ᵥ u₀ := aux_dvd_dotProduct_sub d B u u₀ hu
  have hmd : d ∣ m ⬝ᵥ u - m ⬝ᵥ u₀ := aux_dvd_dotProduct_sub d m u u₀ hu
  have hWd : d ∣ witnessQuad C u - witnessQuad C u₀ := aux_dvd_witnessQuad_sub d C u u₀ hu
  refine dvd_add (dvd_add (dvd_add (dvd_add ?_ ?_) hWd) ?_) hmd
  · exact Dvd.dvd.mul_left (hc.mul_right _) _
  · exact dvd_add (hc.mul_right _) (hBd.mul_left _)
  · exact hc.mul_left _

private theorem aux_mrpG_dvd_sub (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (x x₀ : Fin k → ℤ) (d : ℤ)
    (hx : ∀ i, d ∣ x i - x₀ i) :
    d ∣ movingRemainderPolyG A B C b l m μ q x - movingRemainderPolyG A B C b l m μ q x₀ := by
  have he : movingRemainderPolyG A B C b l m μ q x - movingRemainderPolyG A B C b l m μ q x₀
      = (witnessQuad C x - witnessQuad C x₀)
        + ((b • m - μ • B) ⬝ᵥ x - (b • m - μ • B) ⬝ᵥ x₀) := by
    simp only [movingRemainderPolyG]; ring
  rw [he]
  exact dvd_add (aux_dvd_witnessQuad_sub d C x x₀ hx)
    (aux_dvd_dotProduct_sub d (b • m - μ • B) x x₀ hx)

/-- p ∣ (p − 1) forces p ∣ 1: a prime cannot divide a positive multiple of itself minus one. -/
private theorem aux_prime_not_dvd_of_dvd_pred (p : ℕ) (hp : p.Prime) (x : ℤ)
    (hx : x ∣ (p : ℤ) - 1) : ¬ (p : ℤ) ∣ x := by
  intro hc
  have := dvd_trans hc hx
  have h1 : (p : ℤ) ∣ 1 := by
    have := dvd_sub (dvd_refl (p : ℤ)) this; simpa using this
  have := Int.eq_one_of_dvd_one (by positivity) h1
  have := hp.one_lt; omega

/-! ## J3 : prime-progression step (k-variable port of r10 `moving_modulus_prime_step`) -/

theorem moving_modulus_prime_step_general (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q c₀ : ℤ)
    (u₀ : Fin k → ℤ) (hb : 0 < b) (hN : (C + Cᵀ).det ≠ 0) (ht₀ : 0 < b * c₀ + μ)
    (hdiv : (b * c₀ + μ) ∣ fqM A B C l m q c₀ u₀) :
    ∃ (c : ℤ) (u : Fin k → ℤ), c₀ < c ∧ (b * c + μ) ∣ fqM A B C l m q c u := by
  obtain ⟨t₀, ht₀def⟩ : ∃ t₀ : ℤ, t₀ = b * c₀ + μ := ⟨_, rfl⟩
  rw [← ht₀def] at ht₀ hdiv
  obtain ⟨D', hD'⟩ : ∃ D' : ℤ, D' = (C + Cᵀ).det := ⟨_, rfl⟩
  have hD'ne : D' ≠ 0 := by rw [hD']; exact hN
  obtain ⟨Mn, hMn⟩ : ∃ Mn : ℕ, Mn = 2 * D'.natAbs * b.natAbs * t₀.natAbs := ⟨_, rfl⟩
  have h1 : D'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD'ne
  have h2 : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb.ne'
  have h4 : t₀.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht₀.ne'
  have hM0 : Mn ≠ 0 := by rw [hMn]; positivity
  have hMpos : 0 < Mn := Nat.pos_of_ne_zero hM0
  obtain ⟨p, hp, hpM, hpmod⟩ := Nat.exists_prime_gt_modEq_one Mn hM0
  haveI := Fact.mk hp
  have hMdvd : (Mn : ℤ) ∣ (p : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd' (by omega : 1 ≤ p)).mp hpmod.symm
    have h' := Int.natCast_dvd_natCast.mpr h
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at h'
  have hMcast : (Mn : ℤ) = 2 * |D'| * b * t₀ := by
    rw [hMn]; push_cast
    rw [abs_of_pos hb, abs_of_pos ht₀]
  have hbdvd : b ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact ⟨2 * |D'| * t₀, by ring⟩
  have ht₀dvd : t₀ ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact ⟨2 * |D'| * b, by ring⟩
  have h2dvd : (2 : ℤ) ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact ⟨|D'| * b * t₀, by ring⟩
  have hD'dvd : D' ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact (self_dvd_abs D').trans ⟨2 * b * t₀, by ring⟩
  have hpb : ¬ (p : ℤ) ∣ b := aux_prime_not_dvd_of_dvd_pred p hp b hbdvd
  have hpt₀ : ¬ (p : ℤ) ∣ t₀ := aux_prime_not_dvd_of_dvd_pred p hp t₀ ht₀dvd
  have hp2' : ¬ (p : ℤ) ∣ 2 := aux_prime_not_dvd_of_dvd_pred p hp 2 h2dvd
  have hpD : ¬ (p : ℤ) ∣ (C + Cᵀ).det := by
    rw [← hD']; exact aux_prime_not_dvd_of_dvd_pred p hp D' hD'dvd
  have hp2 : p ≠ 2 := by
    intro h; apply hp2'; rw [h]; norm_num
  obtain ⟨j, hj⟩ := hbdvd
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = c₀ + t₀ * j := ⟨_, rfl⟩
  have hj1 : 1 ≤ j := by
    have hpB : b ≤ (p : ℤ) - 1 := by
      have : b.natAbs ≤ Mn := Nat.le_of_dvd hMpos ⟨2 * D'.natAbs * t₀.natAbs, by rw [hMn]; ring⟩
      have : (b.natAbs : ℤ) = b := by rw [Int.natCast_natAbs, abs_of_pos hb]
      omega
    by_contra hcon; push Not at hcon
    have : b * j ≤ b * 0 := mul_le_mul_of_nonneg_left (by omega) hb.le
    linarith
  have hct : b * c + μ = t₀ * p := by rw [hc]; linear_combination (-t₀) * hj - ht₀def
  have hc₀c : c₀ < c := by rw [hc]; nlinarith
  obtain ⟨x, hxy⟩ := moving_remainder_root_mod_prime_general hk p hp hp2 A B C b l m μ q hpD
  have hcopbp : IsCoprime b (p : ℤ) := by
    have hnat : b.natAbs.Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hc'
      apply hpb
      have := Int.natCast_dvd_natCast.mpr hc'
      rwa [Int.natCast_natAbs, abs_of_pos hb] at this
    have := hnat.isCoprime
    rwa [Int.natCast_natAbs, abs_of_pos hb] at this
  obtain ⟨α, β, hαβ⟩ := hcopbp
  have hcop : IsCoprime t₀ (p : ℤ) := by
    have hnat : t₀.natAbs.Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hc'
      apply hpt₀
      have := Int.natCast_dvd_natCast.mpr hc'
      rwa [Int.natCast_natAbs, abs_of_pos ht₀] at this
    have := hnat.isCoprime
    rwa [Int.natCast_natAbs, abs_of_pos ht₀] at this
  obtain ⟨a', b', hab⟩ := hcop
  set u : Fin k → ℤ := fun i => (α * x i) * (a' * t₀) + u₀ i * (b' * (p : ℤ)) with hudef
  have hui : ∀ i, u i = (α * x i) * (a' * t₀) + u₀ i * (b' * (p : ℤ)) := fun i => rfl
  have hu₀ : ∀ i, t₀ ∣ u i - u₀ i := fun i =>
    ⟨a' * (α * x i - u₀ i), by rw [hui]; linear_combination (u₀ i) * hab⟩
  have hup' : ∀ i, (p : ℤ) ∣ u i - α * x i := fun i =>
    ⟨b' * (u₀ i - α * x i), by rw [hui]; linear_combination (α * x i) * hab⟩
  have hbup : ∀ i, (p : ℤ) ∣ b * (α * x i) - x i := fun i =>
    ⟨-(β * x i), by linear_combination (x i) * hαβ⟩
  refine ⟨c, u, hc₀c, ?_⟩
  rw [hct]
  apply IsCoprime.mul_dvd ⟨a', b', hab⟩
  · -- t₀ ∣ fqM(c,u): congruent to fqM(c₀,u₀)
    have hcc : t₀ ∣ c - c₀ := ⟨j, by rw [hc]; ring⟩
    have := dvd_add hdiv (aux_fqM_dvd_sub A B C l m q c c₀ u u₀ t₀ hcc hu₀)
    simpa using this
  · -- p ∣ fqM(c,u): via J1 identity, p ∣ (b c + μ), p ∣ mrpG(b•u)
    have hx' : ∀ i, (p : ℤ) ∣ (b • u) i - x i := by
      intro i
      have e : (b • u) i - x i = b * (u i - α * x i) + (b * (α * x i) - x i) := by
        simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      exact dvd_add ((hup' i).mul_left b) (hbup i)
    have hpR : (p : ℤ) ∣ movingRemainderPolyG A B C b l m μ q (b • u) := by
      have := dvd_add hxy (aux_mrpG_dvd_sub A B C b l m μ q (b • u) x p hx')
      simpa using this
    have hpt : (p : ℤ) ∣ b * c + μ := ⟨t₀, by rw [hct]; ring⟩
    have hpb2 : (p : ℤ) ∣ b ^ 2 * fqM A B C l m q c u := by
      rw [moving_remainder_identity_general A B C b l m μ q c u]
      exact dvd_add hpR (hpt.mul_right _)
    have hcopb : IsCoprime (p : ℤ) b := ⟨β, α, by linear_combination hαβ⟩
    exact (hcopb.pow_right).dvd_of_dvd_mul_left hpb2

/-- s27 (Gate 4 必須E/F): the prime step with its ARITHMETIC DATA exposed — the good prime `p` (≡ 1 modulo the moving
    modulus `2|D'|·b·(b c₀ + μ)`, above it), the finite-field root `x` of the moving-remainder polynomial, the CRT
    congruences of the new witness, and the modulus recurrence `b c + μ = (b c₀ + μ)·p`. Same proof as
    `moving_modulus_prime_step_general` (sealed, unchanged); this is its data-carrying form for the certificate. -/
theorem moving_modulus_prime_step_data (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q c₀ : ℤ)
    (u₀ : Fin k → ℤ) (hb : 0 < b) (hN : (C + Cᵀ).det ≠ 0) (ht₀ : 0 < b * c₀ + μ)
    (hdiv : (b * c₀ + μ) ∣ fqM A B C l m q c₀ u₀) :
    ∃ (p : ℕ) (c : ℤ) (u x : Fin k → ℤ), p.Prime ∧
      (2 * |(C + Cᵀ).det| * b * (b * c₀ + μ) : ℤ) < p ∧
      (p : ℤ) ≡ 1 [ZMOD 2 * |(C + Cᵀ).det| * b * (b * c₀ + μ)] ∧
      b * c + μ = (b * c₀ + μ) * p ∧
      (p : ℤ) ∣ movingRemainderPolyG A B C b l m μ q x ∧
      (∀ i, (b * c₀ + μ) ∣ u i - u₀ i) ∧ (∀ i, (p : ℤ) ∣ b * u i - x i) ∧
      (b * c + μ) ∣ fqM A B C l m q c u := by
  obtain ⟨t₀, ht₀def⟩ : ∃ t₀ : ℤ, t₀ = b * c₀ + μ := ⟨_, rfl⟩
  rw [← ht₀def] at ht₀ hdiv
  obtain ⟨D', hD'⟩ : ∃ D' : ℤ, D' = (C + Cᵀ).det := ⟨_, rfl⟩
  have hD'ne : D' ≠ 0 := by rw [hD']; exact hN
  obtain ⟨Mn, hMn⟩ : ∃ Mn : ℕ, Mn = 2 * D'.natAbs * b.natAbs * t₀.natAbs := ⟨_, rfl⟩
  have h1 : D'.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD'ne
  have h2 : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb.ne'
  have h4 : t₀.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ht₀.ne'
  have hM0 : Mn ≠ 0 := by rw [hMn]; positivity
  have hMpos : 0 < Mn := Nat.pos_of_ne_zero hM0
  obtain ⟨p, hp, hpM, hpmod⟩ := Nat.exists_prime_gt_modEq_one Mn hM0
  haveI := Fact.mk hp
  have hMdvd : (Mn : ℤ) ∣ (p : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd' (by omega : 1 ≤ p)).mp hpmod.symm
    have h' := Int.natCast_dvd_natCast.mpr h
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at h'
  have hMcast : (Mn : ℤ) = 2 * |D'| * b * t₀ := by
    rw [hMn]; push_cast
    rw [abs_of_pos hb, abs_of_pos ht₀]
  have hbdvd : b ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact ⟨2 * |D'| * t₀, by ring⟩
  have ht₀dvd : t₀ ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact ⟨2 * |D'| * b, by ring⟩
  have h2dvd : (2 : ℤ) ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact ⟨|D'| * b * t₀, by ring⟩
  have hD'dvd : D' ∣ (p : ℤ) - 1 := by
    refine dvd_trans ?_ hMdvd
    rw [hMcast]; exact (self_dvd_abs D').trans ⟨2 * b * t₀, by ring⟩
  have hpb : ¬ (p : ℤ) ∣ b := aux_prime_not_dvd_of_dvd_pred p hp b hbdvd
  have hpt₀ : ¬ (p : ℤ) ∣ t₀ := aux_prime_not_dvd_of_dvd_pred p hp t₀ ht₀dvd
  have hp2' : ¬ (p : ℤ) ∣ 2 := aux_prime_not_dvd_of_dvd_pred p hp 2 h2dvd
  have hpD : ¬ (p : ℤ) ∣ (C + Cᵀ).det := by
    rw [← hD']; exact aux_prime_not_dvd_of_dvd_pred p hp D' hD'dvd
  have hp2 : p ≠ 2 := by
    intro h; apply hp2'; rw [h]; norm_num
  obtain ⟨j, hj⟩ := hbdvd
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = c₀ + t₀ * j := ⟨_, rfl⟩
  have hj1 : 1 ≤ j := by
    have hpB : b ≤ (p : ℤ) - 1 := by
      have : b.natAbs ≤ Mn := Nat.le_of_dvd hMpos ⟨2 * D'.natAbs * t₀.natAbs, by rw [hMn]; ring⟩
      have : (b.natAbs : ℤ) = b := by rw [Int.natCast_natAbs, abs_of_pos hb]
      omega
    by_contra hcon; push Not at hcon
    have : b * j ≤ b * 0 := mul_le_mul_of_nonneg_left (by omega) hb.le
    linarith
  have hct : b * c + μ = t₀ * p := by rw [hc]; linear_combination (-t₀) * hj - ht₀def
  have hc₀c : c₀ < c := by rw [hc]; nlinarith
  obtain ⟨x, hxy⟩ := moving_remainder_root_mod_prime_general hk p hp hp2 A B C b l m μ q hpD
  have hcopbp : IsCoprime b (p : ℤ) := by
    have hnat : b.natAbs.Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hc'
      apply hpb
      have := Int.natCast_dvd_natCast.mpr hc'
      rwa [Int.natCast_natAbs, abs_of_pos hb] at this
    have := hnat.isCoprime
    rwa [Int.natCast_natAbs, abs_of_pos hb] at this
  obtain ⟨α, β, hαβ⟩ := hcopbp
  have hcop : IsCoprime t₀ (p : ℤ) := by
    have hnat : t₀.natAbs.Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hc'
      apply hpt₀
      have := Int.natCast_dvd_natCast.mpr hc'
      rwa [Int.natCast_natAbs, abs_of_pos ht₀] at this
    have := hnat.isCoprime
    rwa [Int.natCast_natAbs, abs_of_pos ht₀] at this
  obtain ⟨a', b', hab⟩ := hcop
  set u : Fin k → ℤ := fun i => (α * x i) * (a' * t₀) + u₀ i * (b' * (p : ℤ)) with hudef
  have hui : ∀ i, u i = (α * x i) * (a' * t₀) + u₀ i * (b' * (p : ℤ)) := fun i => rfl
  have hu₀ : ∀ i, t₀ ∣ u i - u₀ i := fun i =>
    ⟨a' * (α * x i - u₀ i), by rw [hui]; linear_combination (u₀ i) * hab⟩
  have hup' : ∀ i, (p : ℤ) ∣ u i - α * x i := fun i =>
    ⟨b' * (u₀ i - α * x i), by rw [hui]; linear_combination (α * x i) * hab⟩
  have hbup : ∀ i, (p : ℤ) ∣ b * (α * x i) - x i := fun i =>
    ⟨-(β * x i), by linear_combination (x i) * hαβ⟩
  have hpMZ : (2 * |D'| * b * t₀ : ℤ) < p := by
    have : ((Mn : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast hpM
    rwa [hMcast] at this
  have hpmodZ : (p : ℤ) ≡ 1 [ZMOD 2 * |D'| * b * t₀] := by
    rw [← hMcast]; exact (Int.modEq_iff_dvd.mpr hMdvd).symm
  have hbux : ∀ i, (p : ℤ) ∣ b * u i - x i := by
    intro i
    have e : b * u i - x i = b * (u i - α * x i) + (b * (α * x i) - x i) := by ring
    rw [e]
    exact dvd_add ((hup' i).mul_left b) (hbup i)
  rw [← ht₀def, ← hD']
  refine ⟨p, c, u, x, hp, hpMZ, hpmodZ, hct, hxy, hu₀, hbux, ?_⟩
  rw [hct]
  apply IsCoprime.mul_dvd ⟨a', b', hab⟩
  · -- t₀ ∣ fqM(c,u): congruent to fqM(c₀,u₀)
    have hcc : t₀ ∣ c - c₀ := ⟨j, by rw [hc]; ring⟩
    have := dvd_add hdiv (aux_fqM_dvd_sub A B C l m q c c₀ u u₀ t₀ hcc hu₀)
    simpa using this
  · -- p ∣ fqM(c,u): via J1 identity, p ∣ (b c + μ), p ∣ mrpG(b•u)
    have hx' : ∀ i, (p : ℤ) ∣ (b • u) i - x i := by
      intro i
      have e : (b • u) i - x i = b * (u i - α * x i) + (b * (α * x i) - x i) := by
        simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      exact dvd_add ((hup' i).mul_left b) (hbup i)
    have hpR : (p : ℤ) ∣ movingRemainderPolyG A B C b l m μ q (b • u) := by
      have := dvd_add hxy (aux_mrpG_dvd_sub A B C b l m μ q (b • u) x p hx')
      simpa using this
    have hpt : (p : ℤ) ∣ b * c + μ := ⟨t₀, by rw [hct]; ring⟩
    have hpb2 : (p : ℤ) ∣ b ^ 2 * fqM A B C l m q c u := by
      rw [moving_remainder_identity_general A B C b l m μ q c u]
      exact dvd_add hpR (hpt.mul_right _)
    have hcopb : IsCoprime (p : ℤ) b := ⟨β, α, by linear_combination hαβ⟩
    exact (hcopb.pow_right).dvd_of_dvd_mul_left hpb2

/-! ## J4 helper lemmas -/

private theorem aux_nonpositive_bound (b μ c : ℤ) (hb : 0 < b) (h : b * c + μ ≤ 0) : c ≤ |μ| := by
  have hμ : -μ ≤ |μ| := neg_le_abs μ
  rcases le_or_gt c 0 with hc | hc
  · exact le_trans hc (abs_nonneg μ)
  · have : c ≤ b * c := by nlinarith
    linarith

private theorem mem_fiberSetSG_iff_dvd (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (c : ℕ) :
    c ∈ fiberSetSG A B C b l m μ q ↔
      ∃ u : Fin k → ℤ, (b * (c : ℤ) + μ) ∣ fqM A B C l m q (c : ℤ) u := by
  simp only [fiberSetSG, Set.mem_setOf_eq, fqSG]
  constructor
  · rintro ⟨u, w, hw⟩
    exact ⟨u, (exists_w_iff_dvd _ _).mp ⟨w, hw⟩⟩
  · rintro ⟨u, hu⟩
    obtain ⟨w, hw⟩ := (exists_w_iff_dvd _ _).mpr hu
    exact ⟨u, w, hw⟩

/-! ## J4 : b > 0 branch (K = 1, J3 chain) -/

private theorem dichotomySG_pos (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b : ℤ) (hk : 2 ≤ k) (hN : (C + Cᵀ).det ≠ 0) (hb : 0 < b) :
    DichotomySG A B C b := by
  refine ⟨1, fun l m μ q => ?_⟩
  by_cases hex : ∃ c₀ : ℕ,
      (∃ u : Fin k → ℤ, (b * (c₀ : ℤ) + μ) ∣ fqM A B C l m q (c₀ : ℤ) u)
        ∧ 0 < b * (c₀ : ℤ) + μ
  · left
    obtain ⟨c₀, ⟨u₀, hdiv₀⟩, hpos₀⟩ := hex
    have key : ∀ n : ℕ, ∃ c : ℕ, (n : ℤ) ≤ c ∧ 0 < b * (c : ℤ) + μ ∧
        ∃ u : Fin k → ℤ, (b * (c : ℤ) + μ) ∣ fqM A B C l m q (c : ℤ) u := by
      intro n
      induction n with
      | zero => exact ⟨c₀, by positivity, hpos₀, u₀, hdiv₀⟩
      | succ n ih =>
        obtain ⟨c, hnc, hpos, u, hdiv⟩ := ih
        obtain ⟨c', u', hlt, hdiv'⟩ := moving_modulus_prime_step_general hk A B C b l m μ q
          c u hb hN hpos hdiv
        have hc'nn : 0 ≤ c' := by
          have : (0 : ℤ) ≤ c := by positivity
          omega
        refine ⟨c'.toNat, ?_, ?_, u', ?_⟩
        · rw [Int.toNat_of_nonneg hc'nn]; push_cast; omega
        · rw [Int.toNat_of_nonneg hc'nn]; nlinarith
        · rw [Int.toNat_of_nonneg hc'nn]; exact hdiv'
    apply Set.infinite_of_forall_exists_gt
    intro n
    obtain ⟨c, hnc, _, hmem⟩ := key (n + 1)
    refine ⟨c, (mem_fiberSetSG_iff_dvd A B C b l m μ q c).mpr hmem, ?_⟩
    push_cast at hnc; omega
  · right
    push Not at hex
    intro c hc
    rw [mem_fiberSetSG_iff_dvd] at hc
    have hle : b * (c : ℤ) + μ ≤ 0 := hex c hc
    have h1 := aux_nonpositive_bound b μ c hb hle
    unfold fboundSG
    have hsum : (0 : ℤ) ≤ ∑ i, |m i| := Finset.sum_nonneg (fun i _ => abs_nonneg (m i))
    have h2 : |μ| ≤ (1 + |l| + ∑ i, |m i| + |μ|) ^ 2 + |q| := by
      nlinarith [abs_nonneg l, hsum, abs_nonneg μ, abs_nonneg q]
    simp only [Nat.cast_one, one_mul]
    linarith

/-! ## J4 : b < 0 branch (symmetry w ↦ −w) -/

private theorem aux_fiberSetSG_neg (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) :
    fiberSetSG A B C b l m μ q = fiberSetSG A B C (-b) l m (-μ) q := by
  ext c
  simp only [fiberSetSG, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, w, h⟩
    exact ⟨u, -w, by simp only [fqSG] at h ⊢; linear_combination h⟩
  · rintro ⟨u, w, h⟩
    exact ⟨u, -w, by simp only [fqSG] at h ⊢; linear_combination h⟩

private theorem aux_dichotomySG_neg (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b : ℤ) (h : DichotomySG A B C (-b)) : DichotomySG A B C b := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun l m μ q => ?_⟩
  rw [aux_fiberSetSG_neg]
  rcases hK l m (-μ) q with hInf | hBd
  · exact Or.inl hInf
  · right
    intro c hc
    have := hBd c hc
    unfold fboundSG at this ⊢
    rwa [abs_neg] at this


/-! ### 必須A (Gate 5): branch B4 is a WITNESS reflection, not an output reflection

  ERRATUM (s28). Earlier prose (LETTER_GATE4, GATE4_F_BRANCH_INVENTORY, the docstrings of
  `StructuredCertificates.lean`) described branch B4 (`b < 0`) as a reflection `c ↦ -c` producing a
  DECREASING family. That is wrong. The block polynomial `fqSG = fqM(c,u) + (b·c + μ)·w` is invariant
  under `(b, μ, w) ↦ (-b, -μ, -w)`: the output `c` and the block witnesses `u` are untouched, only the
  radical witness `w` changes sign. The fibre is a `Set ℕ`, so an output reflection is not even
  expressible here. The theorems below state this at the level of the polynomial, of the fibre set and
  of individual divisibility solutions. -/

/-- B4 identity: the singular-block polynomial is invariant under `(b, μ, w) ↦ (-b, -μ, -w)`. -/
theorem movingModulus_negSlope_witnessEquiv (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q c : ℤ) (u : Fin k → ℤ) (w : ℤ) :
    fqSG A B C b l m μ q c u w = fqSG A B C (-b) l m (-μ) q c u (-w) := by
  simp only [fqSG]; ring

/-- B4 on fibres: the `b < 0` instance and its positive-slope partner have the SAME fibre — the same
    set of natural outputs. (Public form of the transport used by `aux_dichotomySG_neg`.) -/
theorem fiberSetSG_negSlope (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) :
    fiberSetSG A B C b l m μ q = fiberSetSG A B C (-b) l m (-μ) q :=
  aux_fiberSetSG_neg A B C b l m μ q

/-- B4 on solutions: a divisibility solution of the positive-slope instance `(-b, -μ)` is a solution
    of the original instance `(b, μ)` with the SAME output `c` and the SAME block witnesses `u`; the
    radical witness is the cofactor. -/
theorem movingModulus_negSlope_dvd_transfer (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q c : ℤ) (u : Fin k → ℤ) (t : ℤ)
    (h : fqM A B C l m q c u = ((-b) * c + (-μ)) * t) :
    fqSG A B C b l m μ q c u t = 0 := by
  simp only [fqSG, h]; ring

/-- B4 preserves growth: a strictly increasing family of outputs for `(-b, -μ)` is a strictly
    increasing family of outputs for `(b, μ)`. No decreasing family arises in branch B4. -/
theorem movingModulus_negSlope_strictMono_transfer (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (f : ℕ → ℕ)
    (hmono : StrictMono f) (hmem : ∀ j, f j ∈ fiberSetSG A B C (-b) l m (-μ) q) :
    StrictMono f ∧ ∀ j, f j ∈ fiberSetSG A B C b l m μ q :=
  ⟨hmono, fun j => by rw [fiberSetSG_negSlope]; exact hmem j⟩

/-! ## J4 : b = 0 branch (μ ≠ 0 periodic, μ = 0 transfer from FullRankGeneric) -/

private theorem dichotomySG_zero (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (hk : 2 ≤ k) (hN : (C + Cᵀ).det ≠ 0) : DichotomySG A B C 0 := by
  obtain ⟨K₀, hK₀⟩ := full_rank_projection_dichotomy_of_direction_property hk A B C hN
  refine ⟨K₀ + 1, fun l m μ q => ?_⟩
  by_cases hμ : μ = 0
  · subst hμ
    have hset : fiberSetSG A B C 0 l m 0 q = fiberSetM A B C l m q := by
      ext c
      simp only [fiberSetSG, fiberSetM, Set.mem_setOf_eq, fqSG]
      constructor
      · rintro ⟨u, w, h⟩; exact ⟨u, by simpa using h⟩
      · rintro ⟨u, h⟩; exact ⟨u, 0, by simpa using h⟩
    rw [hset]
    rcases hK₀ l m q with hInf | hBd
    · exact Or.inl hInf
    · right
      intro c hc
      have hcb := hBd c hc
      have hb1 : fboundM K₀ l m q ≤ fboundSG (K₀ + 1) l m 0 q := by
        unfold fboundM fboundSG
        simp only [abs_zero, add_zero]
        have hshape : (0 : ℤ) ≤ (1 + |l| + ∑ i, |m i|) ^ 2 + |q| := by positivity
        push_cast
        nlinarith [hshape, Int.natCast_nonneg K₀]
      linarith [hcb, hb1]
  · have hM : 1 ≤ μ.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hμ)
    have hμd : μ ∣ |μ| := (dvd_abs μ μ).mpr dvd_rfl
    have hper : ∀ c : ℕ, c ∈ fiberSetSG A B C 0 l m μ q ↔
        c + μ.natAbs ∈ fiberSetSG A B C 0 l m μ q := by
      intro c
      rw [mem_fiberSetSG_iff_dvd, mem_fiberSetSG_iff_dvd]
      simp only [zero_mul, zero_add, Nat.cast_add, Int.natCast_natAbs]
      constructor
      · rintro ⟨u, hu⟩
        refine ⟨u, ?_⟩
        have hEq : fqM A B C l m q ((c : ℤ) + |μ|) u
            = |μ| * (A * (2 * (c : ℤ) + |μ|) + B ⬝ᵥ u + l) + fqM A B C l m q (c : ℤ) u := by
          simp only [fqM]; ring
        rw [hEq]
        exact dvd_add (hμd.mul_right _) hu
      · rintro ⟨u, hu⟩
        refine ⟨u, ?_⟩
        have hEq : fqM A B C l m q (c : ℤ) u
            = fqM A B C l m q ((c : ℤ) + |μ|) u - |μ| * (A * (2 * (c : ℤ) + |μ|) + B ⬝ᵥ u + l) := by
          simp only [fqM]; ring
        rw [hEq]
        exact dvd_sub hu (hμd.mul_right _)
    rcases periodic_infinite_or_empty (fiberSetSG A B C 0 l m μ q) μ.natAbs hM hper with hinf | hemp
    · exact Or.inl hinf
    · right
      rw [hemp]
      intro c hc
      exact absurd hc (Set.notMem_empty c)

/-! ## J4 : the moving-modulus dichotomy for rank ≥ 2 general singular blocks -/

theorem quotient_rank_ge_two_moving_dichotomy (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b : ℤ) (hC : (C + Cᵀ).det ≠ 0) :
    DichotomySG A B C b := by
  rcases lt_trichotomy b 0 with hneg | hzero | hpos
  · exact aux_dichotomySG_neg A B C b
      (dichotomySG_pos A B C (-b) hk hC (by linarith))
  · subst hzero; exact dichotomySG_zero A B C hk hC
  · exact dichotomySG_pos A B C b hk hC hpos


/-- 必須F step 2 (branch B3, s28): the fixed-modulus branch in DATA-CARRYING form — the fibre is empty, or
    it contains the explicit progression of period `|μ|`. The periodicity argument is the one inside
    `dichotomySG_zero`; only the discarding call to `periodic_infinite_or_empty` is replaced. -/
theorem dichotomySG_zero_periodic_data (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (hμ : μ ≠ 0) :
    Nonempty (DiophCompression.PeriodicProgression (fiberSetSG A B C 0 l m μ q)) ∨
      fiberSetSG A B C 0 l m μ q = ∅ := by
  have hM : 1 ≤ μ.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hμ)
  have hμd : μ ∣ |μ| := (dvd_abs μ μ).mpr dvd_rfl
  have hper : ∀ c : ℕ, c ∈ fiberSetSG A B C 0 l m μ q ↔
      c + μ.natAbs ∈ fiberSetSG A B C 0 l m μ q := by
    intro c
    rw [mem_fiberSetSG_iff_dvd, mem_fiberSetSG_iff_dvd]
    simp only [zero_mul, zero_add, Nat.cast_add, Int.natCast_natAbs]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨u, ?_⟩
      have hEq : fqM A B C l m q ((c : ℤ) + |μ|) u
          = |μ| * (A * (2 * (c : ℤ) + |μ|) + B ⬝ᵥ u + l) + fqM A B C l m q (c : ℤ) u := by
        simp only [fqM]; ring
      rw [hEq]
      exact dvd_add (hμd.mul_right _) hu
    · rintro ⟨u, hu⟩
      refine ⟨u, ?_⟩
      have hEq : fqM A B C l m q (c : ℤ) u
          = fqM A B C l m q ((c : ℤ) + |μ|) u - |μ| * (A * (2 * (c : ℤ) + |μ|) + B ⬝ᵥ u + l) := by
        simp only [fqM]; ring
      rw [hEq]
      exact dvd_sub hu (hμd.mul_right _)
  exact DiophCompression.periodicProgression_or_empty _ _ hM hper



/-! ### s28 必須F step 3: the b > 0 branch as an explicit moving-modulus orbit -/

theorem sg_pos_orbit (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b l : ℤ) (m : Fin k → ℤ) (μ q : ℤ) (hb : 0 < b) (hN : (C + Cᵀ).det ≠ 0)
    (c₀ : ℕ) (u₀ : Fin k → ℤ) (hdiv₀ : (b * (c₀ : ℤ) + μ) ∣ fqM A B C l m q (c₀ : ℤ) u₀)
    (hpos₀ : 0 < b * (c₀ : ℤ) + μ) :
    ∃ (cf : ℕ → ℕ) (pr : ℕ → ℕ), (∀ n, (pr n).Prime) ∧
      (∀ n, b * (cf (n + 1) : ℤ) + μ = (b * (cf n : ℤ) + μ) * (pr n)) ∧
      (∀ n, cf n ∈ fiberSetSG A B C b l m μ q) ∧ StrictMono cf ∧
      (∀ n, 0 < b * (cf n : ℤ) + μ) ∧
      (∀ n, (2 * |(C + Cᵀ).det| * b * (b * (cf n : ℤ) + μ) : ℤ) < (pr n : ℤ)) ∧
      (∀ n, ((pr n : ℤ)) ≡ 1 [ZMOD 2 * |(C + Cᵀ).det| * b * (b * (cf n : ℤ) + μ)]) := by
  classical
  have step : ∀ x : {c : ℕ // (∃ u : Fin k → ℤ, (b * (c : ℤ) + μ) ∣ fqM A B C l m q (c : ℤ) u)
        ∧ 0 < b * (c : ℤ) + μ},
      ∃ (y : {c : ℕ // (∃ u : Fin k → ℤ, (b * (c : ℤ) + μ) ∣ fqM A B C l m q (c : ℤ) u)
        ∧ 0 < b * (c : ℤ) + μ}) (p : ℕ),
        p.Prime ∧ (x : ℕ) < (y : ℕ) ∧
        b * (((y : ℕ) : ℕ) : ℤ) + μ = (b * (((x : ℕ) : ℕ) : ℤ) + μ) * p ∧
        (2 * |(C + Cᵀ).det| * b * (b * (((x : ℕ) : ℕ) : ℤ) + μ) : ℤ) < (p : ℤ) ∧
        ((p : ℤ)) ≡ 1 [ZMOD 2 * |(C + Cᵀ).det| * b * (b * (((x : ℕ) : ℕ) : ℤ) + μ)] := by
    rintro ⟨c, ⟨u, hdiv⟩, hpos⟩
    obtain ⟨p, c', u', x', hp, hplt, hpmod, hrec, hdvdrem, hcrt1, hcrt2, hdiv'⟩ :=
      moving_modulus_prime_step_data hk A B C b l m μ q (c : ℤ) u hb hN hpos hdiv
    have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    have hgt : b * (c : ℤ) + μ < b * c' + μ := by nlinarith
    have hcc : (c : ℤ) < c' := by nlinarith
    have hc'nn : (0 : ℤ) ≤ c' := by
      have : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
      linarith
    have hcast : ((c'.toNat : ℕ) : ℤ) = c' := Int.toNat_of_nonneg hc'nn
    refine ⟨⟨c'.toNat, ⟨u', by rw [hcast]; exact hdiv'⟩, by rw [hcast]; linarith⟩, p, hp, ?_, ?_,
      ?_, ?_⟩
    · have : (c : ℤ) < ((c'.toNat : ℕ) : ℤ) := by rw [hcast]; exact hcc
      exact_mod_cast this
    · simp only
      rw [hcast, hrec]
    · simpa only using hplt
    · simpa only using hpmod
  choose f pr hprime hlt hrec hpgt hpmod using step
  set x₀ : {c : ℕ // (∃ u : Fin k → ℤ, (b * (c : ℤ) + μ) ∣ fqM A B C l m q (c : ℤ) u)
      ∧ 0 < b * (c : ℤ) + μ} := ⟨c₀, ⟨u₀, hdiv₀⟩, hpos₀⟩ with hx₀
  set orb : ℕ → {c : ℕ // (∃ u : Fin k → ℤ, (b * (c : ℤ) + μ) ∣ fqM A B C l m q (c : ℤ) u)
      ∧ 0 < b * (c : ℤ) + μ} := fun n => Nat.rec x₀ (fun _ x => f x) n with horb
  refine ⟨fun n => (orb n : ℕ), fun n => pr (orb n), fun n => hprime (orb n), fun n => ?_,
    fun n => ?_, ?_, fun n => ?_, fun n => ?_, fun n => ?_⟩
  · exact hrec (orb n)
  · exact (mem_fiberSetSG_iff_dvd A B C b l m μ q _).mpr (orb n).2.1
  · exact strictMono_nat_of_lt_succ (fun n => hlt (orb n))
  · exact (orb n).2.2
  · exact hpgt (orb n)
  · exact hpmod (orb n)

/-- Branch b > 0 of the singular block, in data form. -/
theorem dichotomySG_pos_data (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b : ℤ) (hk : 2 ≤ k) (hN : (C + Cᵀ).det ≠ 0) (hb : 0 < b) : DichotomySGData A B C b := by
  refine ⟨1, fun l m μ q => ?_⟩
  by_cases hex : ∃ c₀ : ℕ,
      (∃ u : Fin k → ℤ, (b * (c₀ : ℤ) + μ) ∣ fqM A B C l m q (c₀ : ℤ) u)
        ∧ 0 < b * (c₀ : ℤ) + μ
  · left
    obtain ⟨c₀, ⟨u₀, hdiv₀⟩, hpos₀⟩ := hex
    obtain ⟨cf, pr, hprime, hrec, hmem, hmono, hmpos, hpgt, hpmod⟩ :=
      sg_pos_orbit hk A B C b l m μ q hb hN c₀ u₀ hdiv₀ hpos₀
    have hmf : (0 : ℤ) < 2 * |(C + Cᵀ).det| := by
      have : (0 : ℤ) < |(C + Cᵀ).det| := abs_pos.mpr hN
      positivity
    exact ⟨DiophCompression.StructuredFamily.movingModulus b μ (2 * |(C + Cᵀ).det|) hb hmf
      cf pr hprime hmpos hpgt hpmod hrec hmem hmono⟩
  · right
    push_neg at hex
    intro c hc
    rw [mem_fiberSetSG_iff_dvd] at hc
    have hle : b * (c : ℤ) + μ ≤ 0 := hex c hc
    have h1 := aux_nonpositive_bound b μ c hb hle
    unfold fboundSG
    have hsum : (0 : ℤ) ≤ ∑ i, |m i| := Finset.sum_nonneg (fun i _ => abs_nonneg (m i))
    have h2 : |μ| ≤ (1 + |l| + ∑ i, |m i| + |μ|) ^ 2 + |q| := by
      nlinarith [abs_nonneg l, hsum, abs_nonneg μ, abs_nonneg q]
    simp only [Nat.cast_one, one_mul]
    linarith

/-- Branch b < 0, in data form: the witness reflection `w ↦ −w` is a set equality. -/
theorem aux_dichotomySG_neg_data (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (b : ℤ) (h : DichotomySGData A B C (-b)) : DichotomySGData A B C b := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun l m μ q => ?_⟩
  rw [aux_fiberSetSG_neg]
  rcases hK l m (-μ) q with hF | hBd
  · exact Or.inl hF
  · right
    intro c hc
    have := hBd c hc
    unfold fboundSG at this ⊢
    rw [abs_neg] at this
    exact this


/-- Branch b = 0, in data form: `μ = 0` is the matrix-level fibre (a set equality, and the full-rank
    block is unconditional since s28), `μ ≠ 0` is the periodic family. -/
theorem dichotomySG_zero_data (A : ℤ) (B : Fin k → ℤ) (C : Matrix (Fin k) (Fin k) ℤ)
    (hk : 2 ≤ k) (hN : (C + Cᵀ).det ≠ 0) : DichotomySGData A B C 0 := by
  have hNw : (DiophCompression.SemanticQuadraticMatrix.witnessGram C).det ≠ 0 := by
    simpa [DiophCompression.SemanticQuadraticMatrix.witnessGram] using hN
  have hij : (⟨0, by omega⟩ : Fin k) ≠ (⟨1, by omega⟩ : Fin k) := by
    simp [Fin.ext_iff]
  obtain ⟨K₀, hK₀⟩ :=
    DiophCompression.SemanticQuadraticMatrix.full_rank_dichotomy_all_data_full A B C hNw
      (⟨0, by omega⟩ : Fin k) (⟨1, by omega⟩ : Fin k) hij
  refine ⟨K₀ + 1, fun l m μ q => ?_⟩
  by_cases hμ : μ = 0
  · subst hμ
    have hset : fiberSetSG A B C 0 l m 0 q
        = DiophCompression.SemanticQuadraticMatrix.fiberSetM A B C l m q := by
      ext c
      simp only [fiberSetSG, DiophCompression.SemanticQuadraticMatrix.fiberSetM,
        Set.mem_setOf_eq, fqSG]
      constructor
      · rintro ⟨u, w, h⟩; exact ⟨u, by simpa using h⟩
      · rintro ⟨u, h⟩; exact ⟨u, 0, by simpa using h⟩
    rw [hset]
    rcases hK₀ l m q with hF | hBd
    · exact Or.inl hF
    · right
      intro c hc
      have hcb := hBd c hc
      have hb1 : (K₀ : ℤ) * ((1 + |l| + ∑ i, |m i|) ^ 2 + |q|)
          ≤ fboundSG (K₀ + 1) l m 0 q := by
        unfold fboundSG
        simp only [abs_zero, add_zero]
        have hshape : (0 : ℤ) ≤ (1 + |l| + ∑ i, |m i|) ^ 2 + |q| := by positivity
        push_cast
        nlinarith [hshape, Int.natCast_nonneg K₀]
      linarith [hcb, hb1]
  · rcases dichotomySG_zero_periodic_data A B C l m μ q hμ with hF | hE
    · exact Or.inl (hF.elim fun F => ⟨DiophCompression.PeriodicProgression.toStructuredFamily F⟩)
    · right
      rw [hE]
      intro c hc
      exact absurd hc (Set.notMem_empty c)

/-! ### s28 必須F step 3: the k₀ ≥ 2 quotient, at the data level.

    `dichotomySG_pos`, `aux_dichotomySG_neg` and `dichotomySG_zero` are private to this file, so their
    data versions have to live here too. The dispatch is proved now and the three sub-branches are
    exposed as hypotheses; `dichotomySG_zero_periodic_data` (B3, s28) already supplies the material for
    the `b = 0` one. -/

theorem quotient_rank_ge_two_moving_dichotomy_data (hk : 2 ≤ k) (A : ℤ) (B : Fin k → ℤ)
    (C : Matrix (Fin k) (Fin k) ℤ) (b : ℤ) (hC : (C + Cᵀ).det ≠ 0) :
    DichotomySGData A B C b := by
  rcases lt_trichotomy b 0 with hn | hz | hp
  · exact aux_dichotomySG_neg_data A B C b (dichotomySG_pos_data A B C (-b) hk hC (by linarith))
  · subst hz; exact dichotomySG_zero_data A B C hk hC
  · exact dichotomySG_pos_data A B C b hk hC hp

end DiophCompression.SemanticQuadraticSingular
#print axioms DiophCompression.SemanticQuadraticSingular.moving_remainder_identity_general
#print axioms DiophCompression.SemanticQuadraticSingular.moving_remainder_root_mod_prime_general
#print axioms DiophCompression.SemanticQuadraticSingular.moving_modulus_prime_step_general
#print axioms DiophCompression.SemanticQuadraticSingular.moving_modulus_prime_step_data
#print axioms DiophCompression.SemanticQuadraticSingular.quotient_rank_ge_two_moving_dichotomy

#print axioms DiophCompression.SemanticQuadraticSingular.movingModulus_negSlope_witnessEquiv
#print axioms DiophCompression.SemanticQuadraticSingular.fiberSetSG_negSlope
#print axioms DiophCompression.SemanticQuadraticSingular.movingModulus_negSlope_dvd_transfer
#print axioms DiophCompression.SemanticQuadraticSingular.movingModulus_negSlope_strictMono_transfer
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomySG_zero_periodic_data
#print axioms DiophCompression.SemanticQuadraticSingular.quotient_rank_ge_two_moving_dichotomy_data
#print axioms DiophCompression.SemanticQuadraticSingular.sg_pos_orbit
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomySG_pos_data
#print axioms DiophCompression.SemanticQuadraticSingular.aux_dichotomySG_neg_data
#print axioms DiophCompression.SemanticQuadraticSingular.dichotomySG_zero_data
